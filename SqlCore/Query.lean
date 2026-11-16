/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module

public import SqlCore.Except
public import SqlCore.Schema
public import SqlCore.Typing
public import SqlCore.Aggregate
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.ProdSigma

/-!
# SQL queries with bag semantics

`Query S n` is a query over the database schema `S` whose result rows have `n` columns: a table,
`WHERE` (`Query.select`), a `SELECT` list (`Query.project`), an inner join `ON θ`
(`Query.join`; a cross join is `ON TRUE`), `UNION ALL` (`Query.unionAll`) and `DISTINCT`
(`Query.distinct`). The output arity is the type index, so a projection list or a join predicate
cannot refer to a column its input lacks.

`Query.eval D q` evaluates `q` on the instance `D` and returns a list of rows or an error. The
list is a bag: projection, join and `UNION ALL` keep duplicates, and only `DISTINCT` removes them,
treating rows with `NULL` in the same places as duplicates, as SQL's `DISTINCT` does (Mathlib's
`List.dedup`, which keeps the last copy). The list order is a property of this representation,
not of SQL, which promises no order without `ORDER BY`: here a table keeps its list order,
`WHERE` keeps the order of its input, a join enumerates pairs with the left row outermost, and
`UNION ALL` lists its left input first. The equivalences in `SqlCore.Query.Equiv` decide how
much of the order a law may rely on.

Evaluation is strict. A `WHERE` or `ON` predicate is evaluated on every input row or pair, and a
projection on every input row, from left to right; the first error fails the whole query, even
when an engine might never have reached the failing row. On an empty input nothing is evaluated,
so the same query succeeds (`Expr.filterRows`, `Expr.evalRow`).

`Query.typeOf q` is the typing context of the result, if `q` is well-typed: predicates are
boolean in the context of their input, projections are well-typed, and `UNION ALL` combines two
inputs of the same types. Type soundness (`Query.eval_ok_or_divisionByZero`): on a conforming
instance, a well-typed query returns rows conforming to its type, or fails with
`divisionByZero`, which requires a division that is not `divSafe`; it never raises
`typeMismatch`. The decidable check `Query.IsSafe` (well-typed, every division by a nonzero
literal) guarantees that evaluation succeeds on every conforming instance.

Typed core phase 4 (#293), re-derived from cslib-frontier's `Languages/SQL/Query.lean` (pinned
`e78796a1`) onto `SqlCore`'s expressions, so that queries see decimals. In `SqlEquiv`, queries
were untyped syntax whose column names were looked up in the rows at run time, and the
evaluator for the richer fragment (aggregates, subqueries, set operations) was partial. Here the
fragment is the select–project–join–union core with `DISTINCT`, columns are positions checked by
the type index, evaluation is structural and total, and errors are results rather than rows
silently dropped.

## Main definitions

* `SqlCore.Query`: queries over a schema, indexed by their output arity.
* `SqlCore.Query.eval`: strict evaluation on a database instance.
* `SqlCore.Expr.filterRows`, `SqlCore.Expr.evalRow`: `WHERE` and `SELECT` lists on a list of
  rows and on one row.
* `SqlCore.Row.product`: the rows of a cross join.
* `SqlCore.Expr.eqCols`: the equijoin predicate `q₁.i = q₂.j` over a joined row.
* `SqlCore.Query.typeOf`: the typing context of a query's result.
* `SqlCore.Query.divSafe`, `SqlCore.Query.IsSafe`: the decidable safety check.

## Main results

* `SqlCore.Expr.toOption_filterRows`, `SqlCore.Expr.evalRow_eq_ok_iff`: what `WHERE` and a
  `SELECT` list compute when they succeed, and when they do.
* `SqlCore.Expr.mem_of_filterRows_eq_ok`: `WHERE` keeps some of its input rows.
* `SqlCore.Query.eval_join_eq_ok_of_forall`: a join whose predicate succeeds on every pair
  returns the joined pairs on which it is `TRUE`.
* `SqlCore.Expr.evalTruth_eqCols_eq_ok_true_iff`, `SqlCore.Expr.isSafePredicate_eqCols_iff`:
  over keys of one type the equijoin predicate keeps the pairs with the same non-null key, and it
  is safe exactly when the key columns have comparable types.
* `SqlCore.Query.eval_ok_or_divisionByZero`: type soundness.
* `SqlCore.Query.eval_ne_typeMismatch`, `SqlCore.Query.conforms_of_eval_eq_ok`: a well-typed
  query never raises a type error, and its rows have its types.
* `SqlCore.Query.IsSafe.exists_eval_eq_ok`: a safe query succeeds on every conforming instance.
-/

@[expose] public section

namespace SqlCore

variable {n m k : ℕ}

/-- The rows of the cross join of `rs` and `ss`: every row `r` of `rs` followed by every row `s` of
`ss` gives the joined row `Fin.append r s`, with the left row outermost. -/
def Row.product (rs : List (Row n)) (ss : List (Row m)) : List (Row (n + m)) :=
  (rs ×ˢ ss).map fun (r, s) => Fin.append r s

/-- A row of the cross join is a left row joined with a right row. -/
theorem Row.mem_product {rs : List (Row n)} {ss : List (Row m)} {t : Row (n + m)} :
    t ∈ Row.product rs ss ↔ ∃ r ∈ rs, ∃ s ∈ ss, Fin.append r s = t := by
  simp only [Row.product, List.mem_map, List.mem_product, Prod.exists]
  constructor
  · rintro ⟨r, s, ⟨hr, hs⟩, rfl⟩
    exact ⟨r, hr, s, hs, rfl⟩
  · rintro ⟨r, hr, s, hs, rfl⟩
    exact ⟨r, s, ⟨hr, hs⟩, rfl⟩

/-- The rows of a cross join of conforming rows conform to the joined typing context. -/
theorem Row.conforms_of_mem_product {Γ : Fin n → SqlType} {Δ : Fin m → SqlType}
    {rs : List (Row n)} {ss : List (Row m)} (hrs : ∀ r ∈ rs, r.Conforms Γ)
    (hss : ∀ s ∈ ss, s.Conforms Δ) {t : Row (n + m)} (ht : t ∈ Row.product rs ss) :
    t.Conforms (Fin.append Γ Δ) := by
  obtain ⟨r, hr, s, hs, rfl⟩ := Row.mem_product.mp ht
  exact Row.conforms_append_iff.mpr ⟨hrs r hr, hss s hs⟩

namespace Expr

/-! ### `SELECT` lists and `WHERE` on rows -/

/-- Evaluate a `SELECT` list on a row, from left to right: the row of results, or the first
error. -/
def evalRow : {k : ℕ} → (Fin k → Expr n) → Row n → Except EvalError (Row k)
  | 0, _, _ => .ok ![]
  | _ + 1, es, r => do
    let d ← (es 0).eval r
    let ds ← evalRow (fun i => es i.succ) r
    return Matrix.vecCons d ds

/-- Keep the rows on which the predicate is `TRUE`, in order, as `WHERE` and `ON` do. The predicate
is evaluated on every row, and the first error fails the whole filter. -/
def filterRows (p : Expr n) (rs : List (Row n)) : Except EvalError (List (Row n)) :=
  rs.filterMapM fun r => do return if (← p.evalTruth r).isTrue then some r else none

/-- A `SELECT` list succeeds with the row `d` exactly when each expression succeeds with its cell
of `d`. -/
theorem evalRow_eq_ok_iff {es : Fin k → Expr n} {r : Row n} {d : Row k} :
    evalRow es r = .ok d ↔ ∀ i, (es i).eval r = .ok (d i) := by
  induction k with
  | zero =>
    simp only [evalRow, Except.ok.injEq, IsEmpty.forall_iff, iff_true]
    exact Subsingleton.elim _ _
  | succ k ih =>
    simp only [evalRow, Fin.forall_fin_succ]
    constructor
    · intro h
      obtain ⟨d₀, h₀, h⟩ := Except.bind_eq_ok.mp h
      obtain ⟨ds, hds, h⟩ := Except.bind_eq_ok.mp h
      cases h
      exact ⟨h₀, ih.mp hds⟩
    · rintro ⟨h₀, hs⟩
      rw [h₀, Except.ok_bind, ih.mpr hs, Except.ok_bind]
      exact congrArg Except.ok (Matrix.cons_head_tail d)

/-- A `SELECT` list succeeds exactly when each of its expressions does. -/
theorem exists_evalRow_eq_ok_iff {es : Fin k → Expr n} {r : Row n} :
    (∃ d, evalRow es r = .ok d) ↔ ∀ i, ∃ d, (es i).eval r = .ok d := by
  simp only [evalRow_eq_ok_iff]
  exact (Classical.skolem (p := fun i d => (es i).eval r = .ok d)).symm

/-- When a `SELECT` list fails, one of its expressions fails with that error. -/
theorem exists_eval_eq_error_of_evalRow_eq_error {es : Fin k → Expr n} {r : Row n}
    {e : EvalError} (h : evalRow es r = .error e) : ∃ i, (es i).eval r = .error e := by
  induction k with
  | zero => simp [evalRow] at h
  | succ k ih =>
    rcases h₀ : (es 0).eval r with e₀ | d₀
    · simp only [evalRow, h₀, Except.error_bind, Except.error.injEq] at h
      exact ⟨0, h ▸ h₀⟩
    · rcases hs : evalRow (fun i => es i.succ) r with e' | ds
      · simp only [evalRow, h₀, hs, Except.ok_bind, Except.error_bind, Except.error.injEq] at h
        obtain ⟨i, hi⟩ := ih (h ▸ hs)
        exact ⟨i.succ, hi⟩
      · simp [evalRow, h₀, hs, pure, Except.pure] at h

/-- `SELECT` lists whose expressions have the same observations on a row have the same
observation on it. -/
theorem toOption_evalRow_congr {es es' : Fin k → Expr n} {r : Row n}
    (h : ∀ i, ((es i).eval r).toOption = ((es' i).eval r).toOption) :
    (evalRow es r).toOption = (evalRow es' r).toOption := by
  refine Option.ext fun d => ?_
  rw [Except.toOption_eq_some_iff, Except.toOption_eq_some_iff, evalRow_eq_ok_iff,
    evalRow_eq_ok_iff]
  simp only [← Except.toOption_eq_some_iff, h]

/-- `WHERE` succeeds exactly when the predicate succeeds on every row, and then keeps the rows on
which it is `TRUE`, in order. -/
theorem toOption_filterRows (p : Expr n) (rs : List (Row n)) :
    (p.filterRows rs).toOption =
      if ∀ r ∈ rs, (p.evalTruth r).toOption.isSome then
        some (rs.filter fun r => (p.evalTruth r).toOption = some .true)
      else none := by
  have key : ∀ r : Row n,
      ((do return if (← p.evalTruth r).isTrue then some r else none :
        Except EvalError (Option (Row n)))).toOption =
        (p.evalTruth r).toOption.map fun t => if t.isTrue then some r else none := by
    intro r
    cases p.evalTruth r <;> rfl
  rw [filterRows, Except.toOption_filterMapM]
  simp only [key, Option.isSome_map]
  split_ifs
  · rw [← List.filterMap_eq_filter]
    refine congrArg some (List.filterMap_congr fun r _ => ?_)
    rcases h : p.evalTruth r with e | t
    · simp [h, Option.guard]
    · cases t <;> simp [h, Option.guard]
  · rfl

/-- When `WHERE` succeeds, it keeps some of its input rows. -/
theorem mem_of_filterRows_eq_ok {p : Expr n} {rs rs' : List (Row n)}
    (h : p.filterRows rs = .ok rs') {r : Row n} (hr : r ∈ rs') : r ∈ rs := by
  have h' := congrArg Except.toOption h
  rw [toOption_filterRows] at h'
  split_ifs at h'
  · simp only [Except.toOption_ok, Option.some.injEq] at h'
    exact (List.mem_filter.mp (h' ▸ hr)).1
  · simp at h'

/-- When `WHERE` fails, the predicate fails with that error on one of the rows. -/
theorem exists_evalTruth_eq_error_of_filterRows_eq_error {p : Expr n} {rs : List (Row n)}
    {e : EvalError} (h : p.filterRows rs = .error e) : ∃ r ∈ rs, p.evalTruth r = .error e := by
  obtain ⟨r, hr, he⟩ := Except.exists_mem_eq_error_of_filterMapM_eq_error h
  refine ⟨r, hr, ?_⟩
  rcases ht : p.evalTruth r with e' | t
  · simpa [ht] using he
  · simp [ht, pure, Except.pure] at he

/-- Type soundness for predicates: on a conforming row, a boolean predicate either has a truth
value or divides by zero, which requires a division that is not `divSafe`. -/
theorem evalTruth_ok_or_divisionByZero {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {p : Expr n} (hp : p.typeOf Γ = some .bool) :
    (∃ t, p.evalTruth r = .ok t) ∨
      (p.evalTruth r = .error .divisionByZero ∧ p.divSafe = false) := by
  rcases eval_ok_or_divisionByZero hr hp with ⟨d, hd, hdτ⟩ | ⟨hd, hs⟩
  · obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hdτ
    exact .inl ⟨t, by simp [evalTruth, hd, ht]⟩
  · exact .inr ⟨by simp [evalTruth, hd], hs⟩

/-- On rows conforming to `Γ`, `WHERE` with a boolean predicate keeps some of the rows, or divides
by zero. -/
theorem filterRows_ok_or_divisionByZero {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {p : Expr n} (hp : p.typeOf Γ = some .bool) :
    (∃ rs', p.filterRows rs = .ok rs' ∧ ∀ r ∈ rs', r ∈ rs) ∨
      (p.filterRows rs = .error .divisionByZero ∧ p.divSafe = false) := by
  rcases h : p.filterRows rs with e | rs'
  · obtain ⟨r, hr, he⟩ := exists_evalTruth_eq_error_of_filterRows_eq_error h
    rcases evalTruth_ok_or_divisionByZero (hrs r hr) hp with ⟨t, ht⟩ | ⟨ht, hs⟩
    · simp [ht] at he
    · rw [he, Except.error.injEq] at ht
      exact .inr ⟨by rw [ht], hs⟩
  · exact .inl ⟨rs', rfl, fun _ => mem_of_filterRows_eq_ok h⟩

/-- Type soundness for `SELECT` lists: on a conforming row, well-typed expressions give a row of
their types, or one of them divides by zero. -/
theorem evalRow_ok_or_divisionByZero {Γ : Fin n → SqlType} {Δ : Fin k → SqlType}
    {r : Row n} (hr : r.Conforms Γ) {es : Fin k → Expr n}
    (hes : ∀ i, (es i).typeOf Γ = some (Δ i)) :
    (∃ d, evalRow es r = .ok d ∧ d.Conforms Δ) ∨
      (evalRow es r = .error .divisionByZero ∧ ∃ i, (es i).divSafe = false) := by
  rcases h : evalRow es r with e | d
  · obtain ⟨i, hi⟩ := exists_eval_eq_error_of_evalRow_eq_error h
    rcases eval_ok_or_divisionByZero hr (hes i) with ⟨d, hd, -⟩ | ⟨hd, hs⟩
    · simp [hd] at hi
    · rw [hi, Except.error.injEq] at hd
      exact .inr ⟨by rw [hd], i, hs⟩
  · exact .inl ⟨d, rfl, fun i => hasType_of_eval_eq_ok hr (hes i) (evalRow_eq_ok_iff.mp h i)⟩

/-! ### Equijoin predicates -/

/-- The equijoin predicate `q₁.i = q₂.j` over the joined row of an `n`-column left input and an
`m`-column right input: column `i` of the left input (`Fin.castAdd m i`) equals column `j` of the
right input (`Fin.natAdd n j`). -/
def eqCols (i : Fin n) (j : Fin m) : Expr (n + m) :=
  binary (.cmp .eq) (col (Fin.castAdd m i)) (col (Fin.natAdd n j))

/-- The equijoin predicate on a joined row is the three-valued comparison of the two keys. -/
theorem evalTruth_eqCols (i : Fin n) (j : Fin m) (r : Row n) (s : Row m) :
    (eqCols i j).evalTruth (Fin.append r s) = CmpOp.eq.eval (r i) (s j) := by
  simp only [evalTruth, eqCols, eval_binary, eval_col, Fin.append_left, Fin.append_right,
    Except.ok_bind, evalBinOp]
  rcases CmpOp.eq.eval (r i) (s j) with e | t
  · rfl
  · exact Datum.toTruth_toDatum t

/-- Over keys of a common type, the equijoin predicate keeps a pair of rows exactly when both keys
are the same non-null value. (Across numeric types it also keeps `1` with `1.0`.) -/
theorem evalTruth_eqCols_eq_ok_true_iff {i : Fin n} {j : Fin m} {r : Row n} {s : Row m}
    {τ : SqlType} (hr : (r i).HasType τ) (hs : (s j).HasType τ) :
    (eqCols i j).evalTruth (Fin.append r s) = .ok .true ↔ ∃ v, r i = some v ∧ s j = some v := by
  rw [evalTruth_eqCols, CmpOp.eval_eq_ok_true_iff hr hs]
  generalize r i = a at hr ⊢
  generalize s j = b at hs ⊢
  cases a <;> cases b <;> simp [eq_comm]

/-- The equijoin predicate is a safe predicate on the joined rows exactly when the two key
columns have comparable types (the same type, or two numeric types). -/
theorem isSafePredicate_eqCols_iff {Γ : Fin n → SqlType} {Δ : Fin m → SqlType} {i : Fin n}
    {j : Fin m} : (eqCols i j).IsSafePredicate (Fin.append Γ Δ) ↔ (Γ i).Comparable (Δ j) := by
  simp only [IsSafePredicate, eqCols, typeOf, Fin.append_left, Fin.append_right, BinOp.typeOf,
    divSafe, BinOp.isDivision, Bool.not_false, Bool.true_or, Bool.and_self, and_true,
    Option.bind_eq_bind, Option.bind_some]
  split_ifs with h <;> simp [h]

end Expr

/-! ### Grouping (phase 8a, #313) -/

namespace Row

variable {g : ℕ}

/-- Add a row to the group of its key, or open a new group at the end. -/
def insertGroup (k : Row g) (r : Row n) :
    List (Row g × List (Row n)) → List (Row g × List (Row n))
  | [] => [(k, [r])]
  | (k', rs) :: gs => if k' = k then (k', rs ++ [r]) :: gs else (k', rs) :: insertGroup k r gs

def groupAux (acc : List (Row g × List (Row n))) : List (Row g × Row n) → List (Row g × List (Row n))
  | [] => acc
  | (k, r) :: l => groupAux (insertGroup k r acc) l

/-- The groups of keyed rows, in order of first appearance. With no key columns there is exactly
one group, even for no rows, as an aggregate query without `GROUP BY` returns one row. -/
def groups (keyed : List (Row g × Row n)) : List (Row g × List (Row n)) :=
  if g = 0 then [(fun _ => none, keyed.map Prod.snd)] else groupAux [] keyed

/-- Every group is nonempty, and pairs its key with rows keyed by it in `src`. -/
def GroupsOf (src : List (Row g × Row n)) (gs : List (Row g × List (Row n))) : Prop :=
  ∀ grp ∈ gs, grp.2 ≠ [] ∧ ∀ r ∈ grp.2, (grp.1, r) ∈ src

theorem groupsOf_insertGroup {src : List (Row g × Row n)} {k : Row g} {r : Row n}
    (hkr : (k, r) ∈ src) : ∀ {gs}, GroupsOf src gs → GroupsOf src (insertGroup k r gs)
  | [], _ => by
    intro grp hgrp
    simp only [insertGroup, List.mem_singleton] at hgrp
    subst hgrp
    exact ⟨by simp, by simpa using hkr⟩
  | (k', rs) :: gs, h => by
    intro grp hgrp
    unfold insertGroup at hgrp
    split_ifs at hgrp with hk
    · subst hk
      rcases List.mem_cons.mp hgrp with rfl | hgrp
      · refine ⟨by simp, fun r' hr' => ?_⟩
        rcases List.mem_append.mp hr' with hr' | hr'
        · exact (h (k', rs) (by simp)).2 r' hr'
        · simp only [List.mem_singleton] at hr'
          exact hr' ▸ hkr
      · exact h grp (List.mem_cons_of_mem _ hgrp)
    · rcases List.mem_cons.mp hgrp with rfl | hgrp
      · exact h _ (by simp)
      · exact groupsOf_insertGroup hkr (fun grp' hg' => h grp' (List.mem_cons_of_mem _ hg')) grp hgrp

theorem groupsOf_groupAux {src : List (Row g × Row n)} :
    ∀ {acc l}, GroupsOf src acc → (∀ x ∈ l, x ∈ src) → GroupsOf src (groupAux acc l)
  | _, [], h, _ => h
  | _, (k, r) :: l, h, hl => by
    unfold groupAux
    exact groupsOf_groupAux (groupsOf_insertGroup (hl _ (by simp)) h)
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))

/-- The rows of a group come from the input, and its key is the key of an input row (or there are
no key columns). -/
theorem mem_groups {keyed : List (Row g × Row n)} {grp : Row g × List (Row n)}
    (h : grp ∈ groups keyed) :
    (∀ r ∈ grp.2, ∃ k, (k, r) ∈ keyed) ∧ (g = 0 ∨ ∃ r, (grp.1, r) ∈ keyed) := by
  unfold groups at h
  split_ifs at h with hg
  · simp only [List.mem_singleton] at h
    subst h
    refine ⟨fun r hr => ?_, .inl hg⟩
    obtain ⟨⟨k, r'⟩, hkr, rfl⟩ := List.mem_map.mp hr
    exact ⟨k, hkr⟩
  · obtain ⟨hne, hall⟩ := groupsOf_groupAux (src := keyed) (fun _ h => absurd h List.not_mem_nil)
      (fun _ hx => hx) grp h
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨fun r hr => ⟨grp.1, hall r hr⟩, .inr ⟨r, hall r hr⟩⟩

end Row

/-! ### Queries -/

/-- A query over the schema `S` whose result rows have `n` columns. -/
inductive Query (S : DbSchema) : ℕ → Type where
  /-- The rows of a table, in the instance's list order. -/
  | table (t : S.Table) : Query S (S.arity t)
  /-- `SELECT * FROM q WHERE p`: the rows of `q` on which `p` is `TRUE`. -/
  | select {n : ℕ} (p : Expr n) (q : Query S n) : Query S n
  /-- `SELECT es₀, …, esₖ₋₁ FROM q`: one row of results per row of `q`; duplicates are kept. -/
  | project {n k : ℕ} (es : Fin k → Expr n) (q : Query S n) : Query S k
  /-- `q₁ JOIN q₂ ON θ`: the joined rows `Fin.append r s` of the pairs on which `θ` is `TRUE`.
  The left columns come first; a cross join is `ON TRUE`. -/
  | join {n m : ℕ} (θ : Expr (n + m)) (q₁ : Query S n) (q₂ : Query S m) : Query S (n + m)
  /-- `q₁ UNION ALL q₂`: the rows of both, with duplicates. -/
  | unionAll {n : ℕ} (q₁ q₂ : Query S n) : Query S n
  /-- `SELECT DISTINCT * FROM q`: one copy of each row of `q`. Rows with `NULL` in the same places
  and equal values elsewhere are duplicates. -/
  | distinct {n : ℕ} (q : Query S n) : Query S n
  /-- `SELECT keys, aggs FROM q GROUP BY keys` (phase 8a, #313): one row per group of the rows of
  `q` with equal key values (`NULL` keys group together), in order of first appearance, made of
  the key values followed by the aggregates over the group. With no keys there is one group,
  even for no rows. -/
  | aggregate {n g a : ℕ} (keys : Fin g → Expr n) (aggs : Fin a → AggCall n) (q : Query S n) :
      Query S (g + a)

namespace Query

variable {S : DbSchema}

/-- Evaluate a query on a database instance: the bag of result rows as a list, or the first error.
Every predicate and projection is evaluated on every row of its input. -/
def eval (D : Database S) : {n : ℕ} → Query S n → Except EvalError (List (Row n))
  | _, table t => .ok (D t)
  | _, select p q => do p.filterRows (← q.eval D)
  | _, project es q => do (← q.eval D).mapM (Expr.evalRow es)
  | _, join θ q₁ q₂ => do
    let rs ← q₁.eval D
    let ss ← q₂.eval D
    θ.filterRows (Row.product rs ss)
  | _, unionAll q₁ q₂ => do
    let rs ← q₁.eval D
    let ss ← q₂.eval D
    return rs ++ ss
  | _, distinct q => do return (← q.eval D).dedup
  | _, aggregate keys aggs q => do
    let rs ← q.eval D
    let keyed ← rs.mapM fun r => do return (← Expr.evalRow keys r, r)
    (Row.groups keyed).mapM fun kg => do return Fin.append kg.1 (← AggCall.evalAll aggs kg.2)

section Eval

variable (D : Database S)

@[simp] theorem eval_table (t : S.Table) : (table t).eval D = .ok (D t) := rfl

theorem eval_select (p : Expr n) (q : Query S n) :
    (select p q).eval D = (do p.filterRows (← q.eval D)) := rfl

theorem eval_project (es : Fin k → Expr n) (q : Query S n) :
    (project es q).eval D = (do (← q.eval D).mapM (Expr.evalRow es)) := rfl

theorem eval_join (θ : Expr (n + m)) (q₁ : Query S n) (q₂ : Query S m) :
    (join θ q₁ q₂).eval D =
      (do let rs ← q₁.eval D; let ss ← q₂.eval D; θ.filterRows (Row.product rs ss)) := rfl

theorem eval_unionAll (q₁ q₂ : Query S n) :
    (unionAll q₁ q₂).eval D = (do let rs ← q₁.eval D; let ss ← q₂.eval D; return rs ++ ss) :=
  rfl

theorem eval_distinct (q : Query S n) :
    (distinct q).eval D = (do return (← q.eval D).dedup) := rfl

theorem eval_aggregate {g a : ℕ} (keys : Fin g → Expr n) (aggs : Fin a → AggCall n) (q : Query S n) :
    (aggregate keys aggs q).eval D = (do
      let rs ← q.eval D
      let keyed ← rs.mapM fun r => do return (← Expr.evalRow keys r, r)
      (Row.groups keyed).mapM fun kg => do return Fin.append kg.1 (← AggCall.evalAll aggs kg.2)) :=
  rfl

end Eval

/-- When the join predicate `θ` succeeds on every pair of input rows, the join succeeds and
returns the joined rows of the pairs on which `θ` is `TRUE`, in the order of `rs ×ˢ ss`. -/
theorem eval_join_eq_ok_of_forall {D : Database S} {θ : Expr (n + m)} {q₁ : Query S n}
    {q₂ : Query S m} {rs : List (Row n)} {ss : List (Row m)} (h₁ : q₁.eval D = .ok rs)
    (h₂ : q₂.eval D = .ok ss)
    (hθ : ∀ r ∈ rs, ∀ s ∈ ss, ∃ t, θ.evalTruth (Fin.append r s) = .ok t) :
    (join θ q₁ q₂).eval D =
      .ok (((rs ×ˢ ss).filter fun (r, s) => (θ.evalTruth (Fin.append r s)).toOption = some .true)
        |>.map fun (r, s) => Fin.append r s) := by
  have hall : ∀ t ∈ Row.product rs ss, (θ.evalTruth t).toOption.isSome := by
    intro t ht
    obtain ⟨r, hr, s, hs, rfl⟩ := Row.mem_product.mp ht
    obtain ⟨u, hu⟩ := hθ r hr s hs
    simp [hu]
  rw [eval_join, h₁, h₂, Except.ok_bind, Except.ok_bind, ← Except.toOption_eq_some_iff,
    Expr.toOption_filterRows, ite_eq_left hall, Row.product, List.filter_map]
  rfl

/-! ### Typing and safety -/

/-- The typing context of the query's result rows, if the query is well-typed: `WHERE` and `ON`
predicates are boolean over their input, the expressions of a `SELECT` list are well-typed, and
the inputs of `UNION ALL` have the same types. -/
def typeOf : {n : ℕ} → Query S n → Option (Fin n → SqlType)
  | _, table t => some (S.ctx t)
  | _, select p q => do
    let Γ ← q.typeOf
    if p.typeOf Γ = some .bool then some Γ else none
  | _, project es q => do
    let Γ ← q.typeOf
    if h : ∀ i, ((es i).typeOf Γ).isSome then some fun i => ((es i).typeOf Γ).get (h i)
    else none
  | _, join θ q₁ q₂ => do
    let Γ ← q₁.typeOf
    let Δ ← q₂.typeOf
    if θ.typeOf (Fin.append Γ Δ) = some .bool then some (Fin.append Γ Δ) else none
  | _, unionAll q₁ q₂ => do
    let Γ ← q₁.typeOf
    if q₂.typeOf = some Γ then some Γ else none
  | _, distinct q => q.typeOf
  | _, aggregate keys aggs q => do
    let Γ ← q.typeOf
    if h₁ : ∀ i, ((keys i).typeOf Γ).isSome then
      if h₂ : ∀ j, ((aggs j).typeOf Γ).isSome then
        some (Fin.append (fun i => ((keys i).typeOf Γ).get (h₁ i))
          (fun j => ((aggs j).typeOf Γ).get (h₂ j)))
      else none
    else none

@[simp] theorem typeOf_table (t : S.Table) : (table t).typeOf = some (S.ctx t) := rfl

theorem typeOf_select_eq_some {p : Expr n} {q : Query S n} {Γ : Fin n → SqlType} :
    (select p q).typeOf = some Γ ↔ q.typeOf = some Γ ∧ p.typeOf Γ = some .bool := by
  simp only [typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h, hp, rfl⟩
    exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨Γ, h, hp, rfl⟩

theorem typeOf_project_eq_some {es : Fin k → Expr n} {q : Query S n} {Δ : Fin k → SqlType} :
    (project es q).typeOf = some Δ ↔
      ∃ Γ, q.typeOf = some Γ ∧ ∀ i, (es i).typeOf Γ = some (Δ i) := by
  simp only [typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff]
  refine exists_congr fun Γ => and_congr_right fun _ => ?_
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl i
      simp
    · intro hΔ
      funext i
      simp [hΔ i]
  · simp only [false_iff, not_forall]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact ⟨i, fun h' => hi (by simp [h'])⟩

theorem typeOf_join_eq_some {θ : Expr (n + m)} {q₁ : Query S n} {q₂ : Query S m}
    {Γ' : Fin (n + m) → SqlType} :
    (join θ q₁ q₂).typeOf = some Γ' ↔
      ∃ Γ Δ, q₁.typeOf = some Γ ∧ q₂.typeOf = some Δ ∧
        θ.typeOf (Fin.append Γ Δ) = some .bool ∧ Fin.append Γ Δ = Γ' := by
  simp only [typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ, h₁, Δ, h₂, hθ, rfl⟩
    exact ⟨Γ, Δ, h₁, h₂, hθ, rfl⟩
  · rintro ⟨Γ, Δ, h₁, h₂, hθ, rfl⟩
    exact ⟨Γ, h₁, Δ, h₂, hθ, rfl⟩

theorem typeOf_unionAll_eq_some {q₁ q₂ : Query S n} {Γ : Fin n → SqlType} :
    (unionAll q₁ q₂).typeOf = some Γ ↔ q₁.typeOf = some Γ ∧ q₂.typeOf = some Γ := by
  simp only [typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h₁, h₂, rfl⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Γ, h₁, h₂, rfl⟩

@[simp] theorem typeOf_distinct (q : Query S n) : (distinct q).typeOf = q.typeOf := rfl

theorem typeOf_aggregate_eq_some {g a : ℕ} {keys : Fin g → Expr n} {aggs : Fin a → AggCall n}
    {q : Query S n} {Γ' : Fin (g + a) → SqlType} (h : (aggregate keys aggs q).typeOf = some Γ') :
    ∃ Γ Δk Δa, q.typeOf = some Γ ∧ (∀ i, (keys i).typeOf Γ = some (Δk i)) ∧
      (∀ j, (aggs j).typeOf Γ = some (Δa j)) ∧ Fin.append Δk Δa = Γ' := by
  simp only [typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨Γ, hq, h⟩ := h
  split_ifs at h with h₁ h₂
  cases h
  exact ⟨Γ, _, _, hq, fun i => by simp, fun j => by simp, rfl⟩

/-- Every division in the query's predicates and projections is by a nonzero numeric literal. -/
def divSafe : {n : ℕ} → Query S n → Bool
  | _, table _ => true
  | _, select p q => p.divSafe && q.divSafe
  | _, project es q => decide (∀ i, (es i).divSafe) && q.divSafe
  | _, join θ q₁ q₂ => θ.divSafe && q₁.divSafe && q₂.divSafe
  | _, unionAll q₁ q₂ => q₁.divSafe && q₂.divSafe
  | _, distinct q => q.divSafe
  | _, aggregate keys aggs q =>
    decide (∀ i, (keys i).divSafe) && decide (∀ j, (aggs j).divSafe) && q.divSafe

/-- The query is well-typed and every division in it is by a nonzero literal; then it succeeds
on every conforming instance (`Query.IsSafe.exists_eval_eq_ok`). -/
def IsSafe (q : Query S n) : Prop := q.typeOf.isSome ∧ q.divSafe

instance (q : Query S n) : Decidable q.IsSafe :=
  inferInstanceAs (Decidable (q.typeOf.isSome ∧ q.divSafe))

/-- The keyed rows of an aggregate's input: a key row per input row. -/
private theorem keyed_ok_or_divisionByZero {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {g : ℕ} {keys : Fin g → Expr n} {Δ : Fin g → SqlType}
    (hks : ∀ i, (keys i).typeOf Γ = some (Δ i)) :
    (∃ keyed, (rs.mapM fun r => do return (← Expr.evalRow keys r, r)) = .ok keyed ∧
        ∀ x ∈ keyed, x.2 ∈ rs ∧ x.1.Conforms Δ) ∨
      ((rs.mapM fun r => do return (← Expr.evalRow keys r, r)) =
          (.error .divisionByZero : Except EvalError (List (Row g × Row n))) ∧
        ∃ i, (keys i).divSafe = false) := by
  rcases h : rs.mapM (fun r => do return (← Expr.evalRow keys r, r) :
      Row n → Except EvalError (Row g × Row n)) with e | keyed
  · obtain ⟨r, hr, he⟩ := Except.exists_mem_eq_error_of_mapM_eq_error h
    rcases Expr.evalRow_ok_or_divisionByZero (hrs r hr) hks with ⟨d, hd, -⟩ | ⟨hd, i, hi⟩
    · simp [hd, pure, Except.pure] at he
    · simp only [hd, error_bind, _root_.Except.error.injEq] at he
      exact .inr ⟨by rw [← he], i, hi⟩
  · refine .inl ⟨keyed, rfl, fun x hx => ?_⟩
    obtain ⟨r, hr, hrx⟩ := Except.exists_mem_eq_ok_of_mapM_eq_ok h hx
    rcases hd : Expr.evalRow keys r with e | d
    · simp [hd] at hrx
    · simp only [hd, ok_bind, pure, Except.pure, _root_.Except.ok.injEq] at hrx
      subst hrx
      rcases Expr.evalRow_ok_or_divisionByZero (hrs r hr) hks with ⟨d', hd', hconf⟩ | ⟨hd', -⟩
      · rw [hd, _root_.Except.ok.injEq] at hd'
        exact ⟨hr, hd' ▸ hconf⟩
      · simp [hd] at hd'

/-- Type soundness: on a conforming instance, a well-typed query returns rows of its type, or
divides by zero, which requires a division that is not `divSafe`. -/
theorem eval_ok_or_divisionByZero {D : Database S} (hD : D.Conforms) {q : Query S n}
    {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ) :
    (∃ rs, q.eval D = .ok rs ∧ ∀ r ∈ rs, r.Conforms Γ) ∨
      (q.eval D = .error .divisionByZero ∧ q.divSafe = false) := by
  induction q with
  | table t =>
    cases hq
    exact .inl ⟨D t, rfl, hD t⟩
  | select p q ih =>
    obtain ⟨hq, hp⟩ := typeOf_select_eq_some.mp hq
    rcases ih hq with ⟨rs, hrs, hconf⟩ | ⟨he, hs⟩
    · rcases Expr.filterRows_ok_or_divisionByZero hconf hp with ⟨rs', h, hsub⟩ | ⟨h, hs⟩
      · exact .inl ⟨rs', by simp [eval_select, hrs, h], fun r hr => hconf r (hsub r hr)⟩
      · exact .inr ⟨by simp [eval_select, hrs, h], by simp [divSafe, hs]⟩
    · exact .inr ⟨by simp [eval_select, he], by simp [divSafe, hs]⟩
  | project es q ih =>
    obtain ⟨Γ₀, hq, hes⟩ := typeOf_project_eq_some.mp hq
    rcases ih hq with ⟨rs, hrs, hconf⟩ | ⟨he, hs⟩
    · rcases h : rs.mapM (Expr.evalRow es) with e | ds
      · obtain ⟨r, hr, he⟩ := Except.exists_mem_eq_error_of_mapM_eq_error h
        rcases Expr.evalRow_ok_or_divisionByZero (hconf r hr) hes with ⟨d, hd, -⟩ | ⟨hd, i, hi⟩
        · simp [hd] at he
        · rw [he, Except.error.injEq] at hd
          refine .inr ⟨by simp [eval_project, hrs, h, hd], ?_⟩
          simp only [divSafe, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_forall]
          exact .inl ⟨i, by simp [hi]⟩
      · refine .inl ⟨ds, by simp [eval_project, hrs, h], fun d hd i => ?_⟩
        obtain ⟨r, hr, hrd⟩ := Except.exists_mem_eq_ok_of_mapM_eq_ok h hd
        exact Expr.hasType_of_eval_eq_ok (hconf r hr) (hes i) (Expr.evalRow_eq_ok_iff.mp hrd i)
    · exact .inr ⟨by simp [eval_project, he], by simp [divSafe, hs]⟩
  | join θ q₁ q₂ ih₁ ih₂ =>
    obtain ⟨Γ₁, Γ₂, h₁, h₂, hθ, rfl⟩ := typeOf_join_eq_some.mp hq
    rcases ih₁ h₁ with ⟨rs, hrs, hconf₁⟩ | ⟨he, hs⟩
    · rcases ih₂ h₂ with ⟨ss, hss, hconf₂⟩ | ⟨he, hs⟩
      · have hconf : ∀ t ∈ Row.product rs ss, t.Conforms (Fin.append Γ₁ Γ₂) :=
          fun _ => Row.conforms_of_mem_product hconf₁ hconf₂
        rcases Expr.filterRows_ok_or_divisionByZero hconf hθ with ⟨ts, h, hsub⟩ | ⟨h, hs⟩
        · exact .inl ⟨ts, by simp [eval_join, hrs, hss, h], fun t ht => hconf t (hsub t ht)⟩
        · exact .inr ⟨by simp [eval_join, hrs, hss, h], by simp [divSafe, hs]⟩
      · exact .inr ⟨by simp [eval_join, hrs, he], by simp [divSafe, hs]⟩
    · exact .inr ⟨by simp [eval_join, he], by simp [divSafe, hs]⟩
  | unionAll q₁ q₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := typeOf_unionAll_eq_some.mp hq
    rcases ih₁ h₁ with ⟨rs, hrs, hconf₁⟩ | ⟨he, hs⟩
    · rcases ih₂ h₂ with ⟨ss, hss, hconf₂⟩ | ⟨he, hs⟩
      · refine .inl ⟨rs ++ ss, by simp [eval_unionAll, hrs, hss, pure, Except.pure], ?_⟩
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hconf₁ r hr
        · exact hconf₂ r hr
      · exact .inr ⟨by simp [eval_unionAll, hrs, he], by simp [divSafe, hs]⟩
    · exact .inr ⟨by simp [eval_unionAll, he], by simp [divSafe, hs]⟩
  | distinct q ih =>
    rcases ih hq with ⟨rs, hrs, hconf⟩ | ⟨he, hs⟩
    · exact .inl ⟨rs.dedup, by simp [eval_distinct, hrs, pure, Except.pure],
        fun r hr => hconf r (List.mem_dedup.mp hr)⟩
    · exact .inr ⟨by simp [eval_distinct, he], by simp [divSafe, hs]⟩
  | aggregate keys aggs q ih =>
    obtain ⟨Γ₀, Δk, Δa, hq₀, hks, has, rfl⟩ := typeOf_aggregate_eq_some hq
    rcases ih hq₀ with ⟨rs, hrs, hconf⟩ | ⟨he, hs⟩
    · rcases keyed_ok_or_divisionByZero hconf hks with ⟨keyed, hk, hkeyed⟩ | ⟨hk, i, hi⟩
      · have hconfg : ∀ kg ∈ Row.groups keyed, ∀ r ∈ kg.2, r.Conforms Γ₀ := fun kg hkg r hr => by
          obtain ⟨k, hkr⟩ := (Row.mem_groups hkg).1 r hr
          exact hconf r (hkeyed _ hkr).1
        rcases hout : (Row.groups keyed).mapM (fun kg => do
            return Fin.append kg.1 (← AggCall.evalAll aggs kg.2)) with e | outs
        · obtain ⟨kg, hkg, he⟩ := Except.exists_mem_eq_error_of_mapM_eq_error hout
          rcases AggCall.evalAll_ok_or_divisionByZero (hconfg kg hkg) has with
            ⟨d, hd, -⟩ | ⟨hd, j, hj⟩
          · simp [hd, pure, Except.pure] at he
          · simp only [hd, error_bind, _root_.Except.error.injEq] at he
            subst he
            refine .inr ⟨by simp only [eval_aggregate, hrs, ok_bind, hk, hout], ?_⟩
            simp only [divSafe, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_forall]
            exact .inl (.inr ⟨j, by simp [hj]⟩)
        · refine .inl ⟨outs, by simp only [eval_aggregate, hrs, ok_bind, hk, hout], fun t ht => ?_⟩
          obtain ⟨kg, hkg, htk⟩ := Except.exists_mem_eq_ok_of_mapM_eq_ok hout ht
          rcases hd : AggCall.evalAll aggs kg.2 with e | d
          · simp [hd] at htk
          · simp only [hd, ok_bind, pure, Except.pure, _root_.Except.ok.injEq] at htk
            subst htk
            rcases AggCall.evalAll_ok_or_divisionByZero (hconfg kg hkg) has with
              ⟨d', hd', hdc⟩ | ⟨hd', -⟩
            · rw [hd, _root_.Except.ok.injEq] at hd'
              subst hd'
              have hkc : kg.1.Conforms Δk := by
                rcases (Row.mem_groups hkg).2 with hg | ⟨r, hr⟩
                · exact fun i => absurd i.isLt (by omega)
                · exact (hkeyed _ hr).2
              exact Row.conforms_append_iff.mpr ⟨hkc, hdc⟩
            · simp [hd] at hd'
      · refine .inr ⟨by simp only [eval_aggregate, hrs, ok_bind, hk, error_bind], ?_⟩
        simp only [divSafe, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_forall]
        exact .inl (.inl ⟨i, by simp [hi]⟩)
    · exact .inr ⟨by simp only [eval_aggregate, he, error_bind], by simp [divSafe, hs]⟩

/-- A well-typed query never raises a type error on a conforming instance. -/
theorem eval_ne_typeMismatch {D : Database S} (hD : D.Conforms) {q : Query S n}
    {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ) : q.eval D ≠ .error .typeMismatch := by
  rcases eval_ok_or_divisionByZero hD hq with ⟨rs, h, -⟩ | ⟨h, -⟩ <;> simp [h]

/-- The rows of a well-typed query on a conforming instance conform to its type. -/
theorem conforms_of_eval_eq_ok {D : Database S} (hD : D.Conforms) {q : Query S n}
    {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ) {rs : List (Row n)} (h : q.eval D = .ok rs) :
    ∀ r ∈ rs, r.Conforms Γ := by
  rcases eval_ok_or_divisionByZero hD hq with ⟨rs', h', hconf⟩ | ⟨h', -⟩
  · rw [h, Except.ok.injEq] at h'
    exact h' ▸ hconf
  · simp [h] at h'

/-- A safe query succeeds on every conforming instance. -/
theorem IsSafe.exists_eval_eq_ok {q : Query S n} (hs : q.IsSafe) {D : Database S}
    (hD : D.Conforms) : ∃ rs, q.eval D = .ok rs := by
  obtain ⟨Γ, hΓ⟩ := Option.isSome_iff_exists.mp hs.1
  rcases eval_ok_or_divisionByZero hD hΓ with ⟨rs, h, -⟩ | ⟨-, h⟩
  · exact ⟨rs, h⟩
  · simp [hs.2] at h

end Query

end SqlCore
