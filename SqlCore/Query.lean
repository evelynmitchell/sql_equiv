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
public import Mathlib.Data.List.Sort
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
inputs of the same types. Type soundness (`Query.eval_ok_or_runtimeError`): on a conforming
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
* `SqlCore.Query.eval_ok_or_runtimeError`: type soundness.
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

/-- Type soundness for predicates: on a conforming row, a boolean predicate has a truth value, or
divides by zero, which requires a division that is not `divSafe`. -/
theorem evalTruth_spec {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ) {p : Expr n}
    (hp : p.typeOf Γ = some .bool) :
    Except.Spec (p.evalTruth r) (fun _ => True)
      fun err => err = .divisionByZero ∧ p.divSafe = false :=
  (eval_spec hr hp).bind fun d _ hd => by
    obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hd
    simp [ht]

/-- On rows conforming to `Γ`, `WHERE` with a boolean predicate keeps some of the rows, or divides
by zero. -/
theorem filterRows_spec {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {p : Expr n} (hp : p.typeOf Γ = some .bool) :
    Except.Spec (p.filterRows rs) (fun rs' => ∀ r ∈ rs', r ∈ rs)
      fun err => err = .divisionByZero ∧ p.divSafe = false :=
  (Except.Spec.filterMapM (R := fun r r' => r' = r) fun r hr =>
    (evalTruth_spec (hrs r hr) hp).bind fun t _ _ => by split <;> simp).mono
    (fun _ h r' hr' => by obtain ⟨r, hr, rfl⟩ := h r' hr'; exact hr) fun _ => id

/-- Type soundness for `SELECT` lists: on a conforming row, well-typed expressions give a row of
their types, or one of them divides by zero. -/
theorem evalRow_spec {Γ : Fin n → SqlType} {Δ : Fin k → SqlType} {r : Row n}
    (hr : r.Conforms Γ) {es : Fin k → Expr n} (hes : ∀ i, (es i).typeOf Γ = some (Δ i)) :
    Except.Spec (evalRow es r) (·.Conforms Δ)
      fun err => err = .divisionByZero ∧ ∃ i, (es i).divSafe = false := by
  rcases h : evalRow es r with e | d
  · obtain ⟨i, hi⟩ := exists_eval_eq_error_of_evalRow_eq_error h
    have hi' := (eval_spec hr (hes i)).of_eq_error hi
    exact ⟨hi'.1, i, hi'.2⟩
  · exact fun i => (eval_spec hr (hes i)).of_eq_ok (evalRow_eq_ok_iff.mp h i)

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

/-! ### Sorting (phase 8b, ORDER BY) -/

/-- An `ORDER BY` key: an expression, a direction, and where `NULL` sorts (absolute, independent
of the direction; the parser resolves the dialect's default, registry row 1). -/
structure SortKey (n : ℕ) where
  e : Expr n
  desc : Bool
  nullsFirst : Bool
  deriving DecidableEq, Repr

/-- Compare two key datums under a key's direction and `NULL` placement. Values of one type
compare by `Value.cmp`; incomparable values (excluded by typing) count as equal. -/
def SortKey.cmpDatum {n : ℕ} (k : SortKey n) : Datum → Datum → Ordering
  | none, none => .eq
  | none, some _ => if k.nullsFirst then .lt else .gt
  | some _, none => if k.nullsFirst then .gt else .lt
  | some a, some b =>
    let o := ((Value.cmp a b).toOption).getD .eq
    if k.desc then o.swap else o

/-- Lexicographic comparison of key rows. -/
def cmpKeyRows {n k : ℕ} (keys : Fin k → SortKey n) (a b : Row k) : Ordering :=
  (List.finRange k).foldr (fun i acc => (keys i |>.cmpDatum (a i) (b i)).then acc) .eq

/-- Sort keyed rows by their keys, stably: rows with equal keys keep their input order
(registry row 2). Insertion sort is structural, so the kernel evaluates it. -/
def sortKeyed {n k : ℕ} (keys : Fin k → SortKey n) (rs : List (Row k × Row n)) :
    List (Row k × Row n) :=
  rs.insertionSort fun x y => cmpKeyRows keys x.1 y.1 ≠ .gt

/-! ### Queries -/

/-- `INTERSECT` (`keep = true`) and `EXCEPT` (`keep = false`) of two lists of rows: the rows of
`rs` that occur (or do not occur) in `ss`, one copy each (phase 8c). Rows are compared as wholes, so
`NULL`s in the same places are equal, as in `DISTINCT`. -/
def Row.setOp {n : ℕ} (keep : Bool) (rs ss : List (Row n)) : List (Row n) :=
  (rs.filter fun r => decide (r ∈ ss) == keep).dedup

theorem Row.mem_setOp {n : ℕ} {keep : Bool} {rs ss : List (Row n)} {r : Row n} :
    r ∈ Row.setOp keep rs ss ↔ r ∈ rs ∧ (r ∈ ss ↔ keep = true) := by
  cases keep <;> simp [Row.setOp, List.mem_dedup, List.mem_filter]

/-- How an uncorrelated subquery contributes a column to each row of the outer query (phase 8f,
#329): its value (`scalar`), or the truth of `e [NOT] IN (subquery)` (`inSub`). With `firstRow`, a
scalar subquery with several rows gives its first row's value (sqlite); otherwise it is a
`cardinality` error (the standard, Postgres and DuckDB). -/
inductive SubKind (n : ℕ) where
  | scalar (firstRow : Bool)
  | inSub (neg : Bool) (e : Expr n)
  deriving DecidableEq, Repr

/-- The value of a scalar subquery with values `vals`: `NULL` for none, the value for one, and for
several the first one (`firstRow`) or a `cardinality` error. -/
def scalarOf (firstRow : Bool) : List Datum → Except EvalError Datum
  | [] => .ok none
  | [v] => .ok v
  | v :: _ :: _ => if firstRow then .ok v else .error .cardinality

/-- The extra column's expression, given the subquery's values. -/
def SubKind.extra {n : ℕ} : SubKind n → List Datum → Except EvalError (Expr n)
  | .scalar firstRow, vals => Expr.ofDatum .int <$> scalarOf firstRow vals
  | .inSub neg e, vals =>
    .ok (if neg then .unary .not (.inList e vals) else .inList e vals)

/-- The kind cannot fail at evaluation: a scalar subquery that takes its first row, or `IN` with a
`divSafe` probe. -/
def SubKind.divSafe {n : ℕ} : SubKind n → Bool
  | .scalar firstRow => firstRow
  | .inSub _ e => e.divSafe

/-- A window function (phase 9.5, #463). -/
inductive WinFn (n : ℕ) where
  /-- `ROW_NUMBER()`: the row's position in its sorted partition (ties in input order). -/
  | rowNumber
  /-- `RANK()`: one more than the number of rows of the partition sorted before it. -/
  | rank
  /-- `DENSE_RANK()`: one more than the number of distinct sort keys before it. -/
  | denseRank
  /-- An aggregate over the window frame. -/
  | agg (a : AggCall n)
  deriving DecidableEq, Repr

/-- `fn OVER (PARTITION BY part ORDER BY order)` (phase 9.5, #463), with SQL's default frame:
the whole partition without `ORDER BY`; with it, the rows sorted up to the current one and its
peers (rows with equal sort keys). -/
structure WinCall (n : ℕ) where
  part : List (Expr n)
  order : List (SortKey n)
  fn : WinFn n
  deriving DecidableEq, Repr

/-- Lexicographic comparison of two lists of sort-key values. -/
def cmpKeyList {n : ℕ} : List (SortKey n) → List Datum → List Datum → Ordering
  | k :: ks, a :: as, b :: bs => (k.cmpDatum a b).then (cmpKeyList ks as bs)
  | _, _, _ => .eq

/-- A row of a window's input with its partition key values, its sort key values and its
position. -/
abbrev WinRow (n : ℕ) := List Datum × List Datum × Row n × ℕ

namespace WinCall

variable {n : ℕ}

/-- The window function's value at row `x`, among the input rows `all`. -/
def value (c : WinCall n) (all : List (WinRow n)) (x : WinRow n) : Except EvalError Datum :=
  let P := all.filter fun y => decide (y.1 = x.1)
  let cmp (y : WinRow n) := cmpKeyList c.order y.2.1 x.2.1
  match c.fn with
  | .rowNumber => .ok (some (.int (1 + (P.filter fun y =>
      cmp y == .lt || (cmp y == .eq && decide (y.2.2.2 < x.2.2.2))).length)))
  | .rank => .ok (some (.int (1 + (P.filter fun y => cmp y == .lt).length)))
  | .denseRank => .ok (some (.int (1 + ((P.filter fun y => cmp y == .lt).map (·.2.1)).dedup.length)))
  | .agg a => a.eval ((P.filter fun y => cmp y != .gt).map (·.2.2.1))

/-- The result type of the window function over input rows of type `Γ`. -/
def typeOf (c : WinCall n) (Γ : Fin n → SqlType) : Option SqlType :=
  if c.part.all (fun e => (e.typeOf Γ).isSome) && c.order.all (fun k => (k.e.typeOf Γ).isSome) then
    match c.fn with
    | .agg a => a.typeOf Γ
    | _ => some .int
  else none

/-- Every division in the call's keys and argument is by a nonzero literal. -/
def divSafe (c : WinCall n) : Bool :=
  c.part.all (·.divSafe) && c.order.all (·.e.divSafe) &&
    (match c.fn with | .agg a => a.divSafe | _ => true)

end WinCall

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
  /-- `q ORDER BY keys` (phase 8b): the rows of `q`, stably sorted by the keys. -/
  | orderBy {n k : ℕ} (keys : Fin k → SortKey n) (q : Query S n) : Query S n
  /-- `q LIMIT count OFFSET offset` (phase 8b): skip `offset` rows, then keep at most `count`. -/
  | limit {n : ℕ} (count : Option ℕ) (offset : ℕ) (q : Query S n) : Query S n
  /-- `q₁ INTERSECT q₂` (phase 8c): one copy of each row of `q₁` that is also a row of `q₂`. -/
  | intersect {n : ℕ} (q₁ q₂ : Query S n) : Query S n
  /-- `q₁ EXCEPT q₂` (phase 8c): one copy of each row of `q₁` that is not a row of `q₂`. -/
  | difference {n : ℕ} (q₁ q₂ : Query S n) : Query S n
  /-- An uncorrelated subquery `sub` of one column, attached to `q` as an extra last column
  (phase 8f, #329): its value or the truth of `e [NOT] IN sub` on each row. `sub` is evaluated
  once, first. -/
  | attach {n : ℕ} (kind : SubKind n) (sub : Query S 1) (q : Query S n) : Query S (n + 1)
  /-- The source of a `SELECT` without `FROM` (phase 9.1a, #459): one row with no columns. A
  projection over it gives `SELECT 1`'s one row. -/
  | one : Query S 0
  /-- The outer row of a correlated body (phase 9.4b, #462, decision D6), with its column types. Outside a
  `lateral` body it is ill-typed. -/
  | outer {n : ℕ} (Γ : Fin n → SqlType) : Query S n
  /-- `q CROSS JOIN LATERAL body` (phase 9.4b, #462, decision D6): for each row `r` of `q`, the rows of
  `body` evaluated with `r` as its outer row, each appended to `r`. -/
  | lateral {n k : ℕ} (body : Query S k) (q : Query S n) : Query S (n + k)
  /-- `q` with a window function's value appended to each row (phase 9.5, #463), the rows in
  their input order. -/
  | window {n : ℕ} (c : WinCall n) (q : Query S n) : Query S (n + 1)
  /-- `WITH RECURSIVE r AS (base UNION [ALL] step)` with linear recursion (phase 9.6, #464): the
  rows of `base`, then rounds in which `step` is evaluated once per row of the previous round's new
  rows (the working table), that row being its outer row (`outer`), until a round adds no row. With
  `distinct` (`UNION`), duplicates are removed, against every row so far. After `rounds` rounds
  that still add rows the evaluation fails with `recursionLimit`. -/
  | recurse {n : ℕ} (distinct : Bool) (rounds : ℕ) (base step : Query S n) : Query S n

namespace Query

variable {S : DbSchema}

/-- The rounds of `WITH RECURSIVE` (`Query.recurse`): `f` evaluates the step on one row of the
working table; `acc` holds every row so far and `work` the previous round's new rows. A round's
new rows are the step's rows on every working row (with `distinct`, without duplicates and without
rows already in `acc`); the iteration stops when there are none, and fails with `recursionLimit`
when the round budget is spent first. -/
def recurseRounds {n : ℕ} (f : Row n → Except EvalError (List (Row n))) (distinct : Bool) :
    ℕ → List (Row n) → List (Row n) → Except EvalError (List (Row n))
  | _, acc, [] => .ok acc
  | 0, _, _ :: _ => .error .recursionLimit
  | k + 1, acc, w :: ws => do
    let out := (← (w :: ws).mapM f).flatten
    let new := if distinct then out.dedup.filter (· ∉ acc) else out
    recurseRounds f distinct k (acc ++ new) new

/-- Evaluate a query on a database instance: the bag of result rows as a list, or the first error.
Every predicate and projection is evaluated on every row of its input. -/
def evalIn (D : Database S) (env : Option ((m : ℕ) × Row m)) :
    {n : ℕ} → Query S n → Except EvalError (List (Row n))
  | _, table t => .ok (D t)
  | _, select p q => do p.filterRows (← q.evalIn D env)
  | _, project es q => do (← q.evalIn D env).mapM (Expr.evalRow es)
  | _, join θ q₁ q₂ => do
    let rs ← q₁.evalIn D env
    let ss ← q₂.evalIn D env
    θ.filterRows (Row.product rs ss)
  | _, unionAll q₁ q₂ => do
    let rs ← q₁.evalIn D env
    let ss ← q₂.evalIn D env
    return rs ++ ss
  | _, distinct q => do return (← q.evalIn D env).dedup
  | _, aggregate keys aggs q => do
    let rs ← q.evalIn D env
    let keyed ← rs.mapM fun r => do return (← Expr.evalRow keys r, r)
    (Row.groups keyed).mapM fun kg => do return Fin.append kg.1 (← AggCall.evalAll aggs kg.2)
  | _, orderBy keys q => do
    let rs ← q.evalIn D env
    let keyed ← rs.mapM fun r => do return (← Expr.evalRow (fun i => (keys i).e) r, r)
    return (sortKeyed keys keyed).map Prod.snd
  | _, limit count offset q => do
    let rs ← q.evalIn D env
    return match count with
      | some c => (rs.drop offset).take c
      | none => rs.drop offset
  | _, intersect q₁ q₂ => do return Row.setOp true (← q₁.evalIn D env) (← q₂.evalIn D env)
  | _, difference q₁ q₂ => do return Row.setOp false (← q₁.evalIn D env) (← q₂.evalIn D env)
  | _, attach kind sub q => do
    let ss ← sub.evalIn D env
    let x ← kind.extra (ss.map (· 0))
    (← q.evalIn D env).mapM (Expr.evalRow (Fin.append (fun i => Expr.col i) ![x]))
  | _, one => .ok [![]]
  | n, outer _ => match env with
    | some ⟨m, r⟩ => if h : m = n then .ok [h ▸ r] else .error .typeMismatch
    | none => .error .typeMismatch
  | _, lateral body q => do
    let rs ← q.evalIn D env
    let parts ← rs.mapM fun r => do
      return (← body.evalIn D (some ⟨_, r⟩)).map (Fin.append r)
    return parts.flatten
  | _, window c q => do
    let rs ← q.evalIn D env
    let keyed ← rs.zipIdx.mapM fun (r, i) => do
      return ((← c.part.mapM (·.eval r)), (← c.order.mapM (·.e.eval r)), r, i)
    keyed.mapM fun x => do return Fin.append x.2.2.1 ![← c.value keyed x]
  | n, recurse dist rounds base step => do
    let rs ← base.evalIn D env
    let rs := if dist then rs.dedup else rs
    recurseRounds (fun w => step.evalIn D (some ⟨n, w⟩)) dist rounds rs rs

/-- Evaluate a query on a database instance, with no outer row. -/
def eval (D : Database S) {n : ℕ} (q : Query S n) : Except EvalError (List (Row n)) :=
  q.evalIn D none

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

theorem eval_orderBy {k : ℕ} (keys : Fin k → SortKey n) (q : Query S n) :
    (orderBy keys q).eval D = (do
      let rs ← q.eval D
      let keyed ← rs.mapM fun r => do return (← Expr.evalRow (fun i => (keys i).e) r, r)
      return (sortKeyed keys keyed).map Prod.snd) := rfl

theorem eval_limit (count : Option ℕ) (offset : ℕ) (q : Query S n) :
    (limit count offset q).eval D = (do
      let rs ← q.eval D
      return match count with
        | some c => (rs.drop offset).take c
        | none => rs.drop offset) := rfl

theorem eval_intersect (q₁ q₂ : Query S n) :
    (intersect q₁ q₂).eval D =
      (do let rs ← q₁.eval D; let ss ← q₂.eval D; return Row.setOp true rs ss) := rfl

theorem eval_difference (q₁ q₂ : Query S n) :
    (difference q₁ q₂).eval D =
      (do let rs ← q₁.eval D; let ss ← q₂.eval D; return Row.setOp false rs ss) := rfl

theorem eval_attach (kind : SubKind n) (sub : Query S 1) (q : Query S n) :
    (attach kind sub q).eval D = (do
      let ss ← sub.eval D
      let x ← kind.extra (ss.map (· 0))
      (← q.eval D).mapM (Expr.evalRow (Fin.append (fun i => Expr.col i) ![x]))) := rfl

@[simp] theorem eval_one : (one : Query S 0).eval D = .ok [![]] := rfl

end Eval

section EvalIn

variable (D : Database S) (env : Option ((m : ℕ) × Row m))

@[simp] theorem evalIn_table (t : S.Table) : (table t).evalIn D env = .ok (D t) := rfl

theorem evalIn_select (p : Expr n) (q : Query S n) :
    (select p q).evalIn D env = (do p.filterRows (← q.evalIn D env)) := rfl

theorem evalIn_project (es : Fin k → Expr n) (q : Query S n) :
    (project es q).evalIn D env = (do (← q.evalIn D env).mapM (Expr.evalRow es)) := rfl

theorem evalIn_join (θ : Expr (n + m)) (q₁ : Query S n) (q₂ : Query S m) :
    (join θ q₁ q₂).evalIn D env =
      (do let rs ← q₁.evalIn D env; let ss ← q₂.evalIn D env; θ.filterRows (Row.product rs ss)) := rfl

theorem evalIn_unionAll (q₁ q₂ : Query S n) :
    (unionAll q₁ q₂).evalIn D env = (do let rs ← q₁.evalIn D env; let ss ← q₂.evalIn D env; return rs ++ ss) :=
  rfl

theorem evalIn_distinct (q : Query S n) :
    (distinct q).evalIn D env = (do return (← q.evalIn D env).dedup) := rfl

theorem evalIn_aggregate {g a : ℕ} (keys : Fin g → Expr n) (aggs : Fin a → AggCall n) (q : Query S n) :
    (aggregate keys aggs q).evalIn D env = (do
      let rs ← q.evalIn D env
      let keyed ← rs.mapM fun r => do return (← Expr.evalRow keys r, r)
      (Row.groups keyed).mapM fun kg => do return Fin.append kg.1 (← AggCall.evalAll aggs kg.2)) :=
  rfl

theorem evalIn_orderBy {k : ℕ} (keys : Fin k → SortKey n) (q : Query S n) :
    (orderBy keys q).evalIn D env = (do
      let rs ← q.evalIn D env
      let keyed ← rs.mapM fun r => do return (← Expr.evalRow (fun i => (keys i).e) r, r)
      return (sortKeyed keys keyed).map Prod.snd) := rfl

theorem evalIn_limit (count : Option ℕ) (offset : ℕ) (q : Query S n) :
    (limit count offset q).evalIn D env = (do
      let rs ← q.evalIn D env
      return match count with
        | some c => (rs.drop offset).take c
        | none => rs.drop offset) := rfl

theorem evalIn_intersect (q₁ q₂ : Query S n) :
    (intersect q₁ q₂).evalIn D env =
      (do let rs ← q₁.evalIn D env; let ss ← q₂.evalIn D env; return Row.setOp true rs ss) := rfl

theorem evalIn_difference (q₁ q₂ : Query S n) :
    (difference q₁ q₂).evalIn D env =
      (do let rs ← q₁.evalIn D env; let ss ← q₂.evalIn D env; return Row.setOp false rs ss) := rfl

theorem evalIn_attach (kind : SubKind n) (sub : Query S 1) (q : Query S n) :
    (attach kind sub q).evalIn D env = (do
      let ss ← sub.evalIn D env
      let x ← kind.extra (ss.map (· 0))
      (← q.evalIn D env).mapM (Expr.evalRow (Fin.append (fun i => Expr.col i) ![x]))) := rfl

@[simp] theorem evalIn_one : (one : Query S 0).evalIn D env = .ok [![]] := rfl

end EvalIn

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
def typeOfIn (Γo : Option ((m : ℕ) × (Fin m → SqlType))) :
    {n : ℕ} → Query S n → Option (Fin n → SqlType)
  | _, table t => some (S.ctx t)
  | _, select p q => do
    let Γ ← q.typeOfIn Γo
    if p.typeOf Γ = some .bool then some Γ else none
  | _, project es q => do
    let Γ ← q.typeOfIn Γo
    if h : ∀ i, ((es i).typeOf Γ).isSome then some fun i => ((es i).typeOf Γ).get (h i)
    else none
  | _, join θ q₁ q₂ => do
    let Γ ← q₁.typeOfIn Γo
    let Δ ← q₂.typeOfIn Γo
    if θ.typeOf (Fin.append Γ Δ) = some .bool then some (Fin.append Γ Δ) else none
  | _, unionAll q₁ q₂ => do
    let Γ ← q₁.typeOfIn Γo
    if q₂.typeOfIn Γo = some Γ then some Γ else none
  | _, distinct q => q.typeOfIn Γo
  | _, aggregate keys aggs q => do
    let Γ ← q.typeOfIn Γo
    if h₁ : ∀ i, ((keys i).typeOf Γ).isSome then
      if h₂ : ∀ j, ((aggs j).typeOf Γ).isSome then
        some (Fin.append (fun i => ((keys i).typeOf Γ).get (h₁ i))
          (fun j => ((aggs j).typeOf Γ).get (h₂ j)))
      else none
    else none
  | _, orderBy keys q => do
    let Γ ← q.typeOfIn Γo
    if ∀ i, ((keys i).e.typeOf Γ).isSome then some Γ else none
  | _, limit _ _ q => q.typeOfIn Γo
  | _, intersect q₁ q₂ => do
    let Γ ← q₁.typeOfIn Γo
    if q₂.typeOfIn Γo = some Γ then some Γ else none
  | _, difference q₁ q₂ => do
    let Γ ← q₁.typeOfIn Γo
    if q₂.typeOfIn Γo = some Γ then some Γ else none
  | _, attach kind sub q => do
    let Δ ← sub.typeOfIn Γo
    let Γ ← q.typeOfIn Γo
    match kind with
    | .scalar _ => some (Fin.append Γ ![Δ 0])
    | .inSub _ e =>
      if (e.typeOf Γ).any (fun τ => decide (τ.Comparable (Δ 0))) then some (Fin.append Γ ![.bool])
      else none
  | _, one => some ![]
  | n, outer Γ => match Γo with
    | some ⟨m, Δ⟩ => if h : m = n then (if h ▸ Δ = Γ then some Γ else none) else none
    | none => none
  | _, lateral body q => do
    let Γ ← q.typeOfIn Γo
    let Δ ← body.typeOfIn (some ⟨_, Γ⟩)
    some (Fin.append Γ Δ)
  | _, window c q => do
    let Γ ← q.typeOfIn Γo
    let τ ← c.typeOf Γ
    some (Fin.append Γ ![τ])
  | n, recurse _ _ base step => do
    let Γ ← base.typeOfIn Γo
    if step.typeOfIn (some ⟨n, Γ⟩) = some Γ then some Γ else none

/-- The typing context of the query's result rows, with no outer row. -/
def typeOf {n : ℕ} (q : Query S n) : Option (Fin n → SqlType) := q.typeOfIn none

@[simp] theorem typeOf_table (t : S.Table) : (table t).typeOf = some (S.ctx t) := rfl

theorem typeOf_select_eq_some {p : Expr n} {q : Query S n} {Γ : Fin n → SqlType} :
    (select p q).typeOf = some Γ ↔ q.typeOf = some Γ ∧ p.typeOf Γ = some .bool := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h, hp, rfl⟩
    exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨Γ, h, hp, rfl⟩

theorem typeOf_project_eq_some {es : Fin k → Expr n} {q : Query S n} {Δ : Fin k → SqlType} :
    (project es q).typeOf = some Δ ↔
      ∃ Γ, q.typeOf = some Γ ∧ ∀ i, (es i).typeOf Γ = some (Δ i) := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff]
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
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ, h₁, Δ, h₂, hθ, rfl⟩
    exact ⟨Γ, Δ, h₁, h₂, hθ, rfl⟩
  · rintro ⟨Γ, Δ, h₁, h₂, hθ, rfl⟩
    exact ⟨Γ, h₁, Δ, h₂, hθ, rfl⟩

theorem typeOf_unionAll_eq_some {q₁ q₂ : Query S n} {Γ : Fin n → SqlType} :
    (unionAll q₁ q₂).typeOf = some Γ ↔ q₁.typeOf = some Γ ∧ q₂.typeOf = some Γ := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h₁, h₂, rfl⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Γ, h₁, h₂, rfl⟩

@[simp] theorem typeOf_distinct (q : Query S n) : (distinct q).typeOf = q.typeOf := rfl

theorem typeOf_intersect_eq_some {q₁ q₂ : Query S n} {Γ : Fin n → SqlType} :
    (intersect q₁ q₂).typeOf = some Γ ↔ q₁.typeOf = some Γ ∧ q₂.typeOf = some Γ := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h₁, h₂, rfl⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Γ, h₁, h₂, rfl⟩

theorem typeOf_difference_eq_some {q₁ q₂ : Query S n} {Γ : Fin n → SqlType} :
    (difference q₁ q₂).typeOf = some Γ ↔ q₁.typeOf = some Γ ∧ q₂.typeOf = some Γ := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h₁, h₂, rfl⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Γ, h₁, h₂, rfl⟩

theorem typeOf_orderBy_eq_some {k : ℕ} {keys : Fin k → SortKey n} {q : Query S n}
    {Γ : Fin n → SqlType} (h : (orderBy keys q).typeOf = some Γ) :
    q.typeOf = some Γ ∧ ∃ Δ : Fin k → SqlType, ∀ i, (keys i).e.typeOf Γ = some (Δ i) := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨Γ', hq, h⟩ := h
  split_ifs at h with hk
  cases h
  exact ⟨hq, fun i => ((keys i).e.typeOf Γ).get (hk i), fun i => by simp⟩

@[simp] theorem typeOf_limit (count : Option ℕ) (offset : ℕ) (q : Query S n) :
    (limit count offset q).typeOf = q.typeOf := rfl

theorem typeOf_aggregate_eq_some {g a : ℕ} {keys : Fin g → Expr n} {aggs : Fin a → AggCall n}
    {q : Query S n} {Γ' : Fin (g + a) → SqlType} (h : (aggregate keys aggs q).typeOf = some Γ') :
    ∃ Γ Δk Δa, q.typeOf = some Γ ∧ (∀ i, (keys i).typeOf Γ = some (Δk i)) ∧
      (∀ j, (aggs j).typeOf Γ = some (Δa j)) ∧ Fin.append Δk Δa = Γ' := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨Γ, hq, h⟩ := h
  split_ifs at h with h₁ h₂
  cases h
  exact ⟨Γ, _, _, hq, fun i => by simp, fun j => by simp, rfl⟩

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
@[simp] theorem typeOfIn_table (t : S.Table) : (table t).typeOfIn Γo = some (S.ctx t) := rfl

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
theorem typeOfIn_select_eq_some {p : Expr n} {q : Query S n} {Γ : Fin n → SqlType} :
    (select p q).typeOfIn Γo = some Γ ↔ q.typeOfIn Γo = some Γ ∧ p.typeOf Γ = some .bool := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h, hp, rfl⟩
    exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨Γ, h, hp, rfl⟩

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
theorem typeOfIn_project_eq_some {es : Fin k → Expr n} {q : Query S n} {Δ : Fin k → SqlType} :
    (project es q).typeOfIn Γo = some Δ ↔
      ∃ Γ, q.typeOfIn Γo = some Γ ∧ ∀ i, (es i).typeOf Γ = some (Δ i) := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff]
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

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
theorem typeOfIn_join_eq_some {θ : Expr (n + m)} {q₁ : Query S n} {q₂ : Query S m}
    {Γ' : Fin (n + m) → SqlType} :
    (join θ q₁ q₂).typeOfIn Γo = some Γ' ↔
      ∃ Γ Δ, q₁.typeOfIn Γo = some Γ ∧ q₂.typeOfIn Γo = some Δ ∧
        θ.typeOf (Fin.append Γ Δ) = some .bool ∧ Fin.append Γ Δ = Γ' := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ, h₁, Δ, h₂, hθ, rfl⟩
    exact ⟨Γ, Δ, h₁, h₂, hθ, rfl⟩
  · rintro ⟨Γ, Δ, h₁, h₂, hθ, rfl⟩
    exact ⟨Γ, h₁, Δ, h₂, hθ, rfl⟩

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
theorem typeOfIn_unionAll_eq_some {q₁ q₂ : Query S n} {Γ : Fin n → SqlType} :
    (unionAll q₁ q₂).typeOfIn Γo = some Γ ↔ q₁.typeOfIn Γo = some Γ ∧ q₂.typeOfIn Γo = some Γ := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h₁, h₂, rfl⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Γ, h₁, h₂, rfl⟩

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
@[simp] theorem typeOfIn_distinct (q : Query S n) : (distinct q).typeOfIn Γo = q.typeOfIn Γo := rfl

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
theorem typeOfIn_intersect_eq_some {q₁ q₂ : Query S n} {Γ : Fin n → SqlType} :
    (intersect q₁ q₂).typeOfIn Γo = some Γ ↔ q₁.typeOfIn Γo = some Γ ∧ q₂.typeOfIn Γo = some Γ := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h₁, h₂, rfl⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Γ, h₁, h₂, rfl⟩

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
theorem typeOfIn_difference_eq_some {q₁ q₂ : Query S n} {Γ : Fin n → SqlType} :
    (difference q₁ q₂).typeOfIn Γo = some Γ ↔ q₁.typeOfIn Γo = some Γ ∧ q₂.typeOfIn Γo = some Γ := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨Γ', h₁, h₂, rfl⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Γ, h₁, h₂, rfl⟩

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
theorem typeOfIn_orderBy_eq_some {k : ℕ} {keys : Fin k → SortKey n} {q : Query S n}
    {Γ : Fin n → SqlType} (h : (orderBy keys q).typeOfIn Γo = some Γ) :
    q.typeOfIn Γo = some Γ ∧ ∃ Δ : Fin k → SqlType, ∀ i, (keys i).e.typeOf Γ = some (Δ i) := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨Γ', hq, h⟩ := h
  split_ifs at h with hk
  cases h
  exact ⟨hq, fun i => ((keys i).e.typeOf Γ).get (hk i), fun i => by simp⟩

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
@[simp] theorem typeOfIn_limit (count : Option ℕ) (offset : ℕ) (q : Query S n) :
    (limit count offset q).typeOfIn Γo = q.typeOfIn Γo := rfl

variable {Γo : Option ((m : ℕ) × (Fin m → SqlType))} in
theorem typeOfIn_aggregate_eq_some {g a : ℕ} {keys : Fin g → Expr n} {aggs : Fin a → AggCall n}
    {q : Query S n} {Γ' : Fin (g + a) → SqlType} (h : (aggregate keys aggs q).typeOfIn Γo = some Γ') :
    ∃ Γ Δk Δa, q.typeOfIn Γo = some Γ ∧ (∀ i, (keys i).typeOf Γ = some (Δk i)) ∧
      (∀ j, (aggs j).typeOf Γ = some (Δa j)) ∧ Fin.append Δk Δa = Γ' := by
  simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
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
  | _, orderBy keys q => decide (∀ i, (keys i).e.divSafe) && q.divSafe
  | _, limit _ _ q => q.divSafe
  | _, intersect q₁ q₂ => q₁.divSafe && q₂.divSafe
  | _, difference q₁ q₂ => q₁.divSafe && q₂.divSafe
  | _, attach kind sub q => kind.divSafe && sub.divSafe && q.divSafe
  | _, one => true
  | _, outer _ => true
  | _, lateral body q => body.divSafe && q.divSafe
  | _, window c q => c.divSafe && q.divSafe
  -- the round limit can always be reached
  | _, recurse _ _ _ _ => false

/-- The query is well-typed and every division in it is by a nonzero literal; then it succeeds
on every conforming instance (`Query.IsSafe.exists_eval_eq_ok`). -/
def IsSafe (q : Query S n) : Prop := q.typeOf.isSome ∧ q.divSafe

instance (q : Query S n) : Decidable q.IsSafe :=
  inferInstanceAs (Decidable (q.typeOf.isSome ∧ q.divSafe))

/-- The keyed rows of an aggregate's input: a key row per input row. -/
private theorem keyed_spec {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {g : ℕ} {keys : Fin g → Expr n} {Δ : Fin g → SqlType}
    (hks : ∀ i, (keys i).typeOf Γ = some (Δ i)) :
    Except.Spec (rs.mapM fun r => do return (← Expr.evalRow keys r, r))
      (fun keyed => ∀ x ∈ keyed, x.2 ∈ rs ∧ x.1.Conforms Δ)
      fun err => err = .divisionByZero ∧ ∃ i, (keys i).divSafe = false :=
  (Except.Spec.mapM (R := fun r (x : Row g × Row n) => x.2 = r ∧ x.1.Conforms Δ) fun r hr =>
    (Expr.evalRow_spec (hrs r hr) hks).bind fun d _ hd => Except.spec_ok.mpr ⟨rfl, hd⟩).mono
    (fun _ h x hx => by obtain ⟨r, hr, rfl, hc⟩ := h x hx; exact ⟨hr, hc⟩) fun _ => id

/-- Appending a computed column `x` to every row: the rows conform to `Fin.append Γ ![σ]`, or `x`
divides by zero on some row (and then `P` holds). -/
theorem mapM_evalRow_append {rs : List (Row n)} {Γ : Fin n → SqlType} (hrs : ∀ r ∈ rs, r.Conforms Γ)
    {x : Expr n} {σ : SqlType} {P : Prop}
    (hx : ∀ r : Row n, r.Conforms Γ →
      (∃ d, x.eval r = .ok d ∧ d.HasType σ) ∨ (x.eval r = .error .divisionByZero ∧ P)) :
    (∃ ts, rs.mapM (Expr.evalRow (Fin.append (fun i => Expr.col i) ![x])) = .ok ts ∧
        ∀ t ∈ ts, t.Conforms (Fin.append Γ ![σ])) ∨
      (rs.mapM (Expr.evalRow (Fin.append (fun i => Expr.col i) ![x])) = .error .divisionByZero ∧
        P) := by
  have hrow : ∀ r : Row n, r.Conforms Γ →
      (∃ t, Expr.evalRow (Fin.append (fun i => Expr.col i) ![x]) r = .ok t ∧
        t.Conforms (Fin.append Γ ![σ])) ∨
      (Expr.evalRow (Fin.append (fun i => Expr.col i) ![x]) r = .error .divisionByZero ∧ P) := by
    intro r hr
    rcases hx r hr with ⟨d, hd, hdσ⟩ | ⟨hd, hP⟩
    · refine .inl ⟨Fin.append r ![d], Expr.evalRow_eq_ok_iff.mpr fun i => ?_,
        Row.conforms_append_iff.mpr ⟨hr, fun j => ?_⟩⟩
      · induction i using Fin.addCases with
        | left j => simp
        | right j =>
          obtain rfl : j = 0 := Subsingleton.elim _ _
          simpa using hd
      · obtain rfl : j = 0 := Subsingleton.elim _ _
        simpa using hdσ
    · refine .inr ⟨?_, hP⟩
      rcases h : Expr.evalRow (Fin.append (fun i => Expr.col i) ![x]) r with e | t
      · obtain ⟨i, hi⟩ := Expr.exists_eval_eq_error_of_evalRow_eq_error h
        induction i using Fin.addCases with
        | left j => simp at hi
        | right j =>
          obtain rfl : j = 0 := Subsingleton.elim _ _
          simp only [Fin.append_right] at hi
          simp only [Fin.isValue, Matrix.cons_val_fin_one] at hi
          rw [hd] at hi
          simp only [_root_.Except.error.injEq] at hi
          rw [← hi]
      · have := Expr.evalRow_eq_ok_iff.mp h (Fin.natAdd n 0)
        simp [hd] at this
  induction rs with
  | nil => exact .inl ⟨[], rfl, by simp⟩
  | cons r rs ih =>
    have hr := hrs r (by simp)
    have hrs' : ∀ r' ∈ rs, r'.Conforms Γ := fun r' h => hrs r' (by simp [h])
    rcases hrow r hr with ⟨t, ht, htc⟩ | ⟨ht, hP⟩
    · rcases ih hrs' with ⟨ts, hts, htsc⟩ | ⟨hts, hP⟩
      · refine .inl ⟨t :: ts, by simp [List.mapM_cons, ht, hts, pure, Except.pure], ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        exacts [htc, htsc u hu]
      · exact .inr ⟨by simp [List.mapM_cons, ht, hts], hP⟩
    · exact .inr ⟨by simp [List.mapM_cons, ht], hP⟩

/-! ### Window functions: soundness (phase 9.5, #463) -/

theorem mem_of_mem_zipIdx {α : Type} : ∀ {l : List α} {k : ℕ} {x : α} {i : ℕ},
    (x, i) ∈ l.zipIdx k → x ∈ l
  | [], _, _, _, h => by simp at h
  | a :: l, k, x, i, h => by
    simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, -⟩ | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mem_zipIdx h)

/-- A list of well-typed expressions fails on a conforming row only by dividing by zero, at an
expression that is not `divSafe`. -/
theorem mapM_eval_spec {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {l : List (Expr n)} (hl : ∀ e ∈ l, (e.typeOf Γ).isSome) :
    Except.Spec (l.mapM (·.eval r)) (fun _ => True)
      fun err => err = .divisionByZero ∧ ∃ e ∈ l, e.divSafe = false :=
  (Except.Spec.mapM (R := fun _ _ => True) fun e he => by
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp (hl e he)
    exact (Expr.eval_spec hr hτ).mono (fun _ _ => trivial) fun _ h => ⟨h.1, e, he, h.2⟩).mono
    (fun _ _ => trivial) fun _ h => h

/-- A window function's value has its type, over conforming rows. -/
theorem winValue_spec (c : WinCall n) {Γ : Fin n → SqlType} {all : List (WinRow n)}
    (hall : ∀ y ∈ all, y.2.2.1.Conforms Γ) (x : WinRow n) {τ : SqlType}
    (hτ : c.typeOf Γ = some τ) :
    Except.Spec (c.value all x) (·.HasType τ)
      fun err => err = .divisionByZero ∧ c.divSafe = false := by
  obtain ⟨part, order, fn⟩ := c
  simp only [WinCall.typeOf] at hτ
  split_ifs at hτ
  cases fn with
  | rowNumber => cases hτ; exact rfl
  | rank => cases hτ; exact rfl
  | denseRank => cases hτ; exact rfl
  | agg a =>
    refine (AggCall.eval_spec (fun r hr => ?_) hτ).mono (fun _ h => h) fun _ h =>
      ⟨h.1, by simp [WinCall.divSafe, h.2]⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    exact hall y (List.mem_of_mem_filter (List.mem_of_mem_filter hy))

/-- The rounds of `WITH RECURSIVE` keep rows of the step's type: if the step maps a row of type
`Γ` to rows of type `Γ`, or fails with an error in `E`, so do the rounds, which may also fail with
`recursionLimit` (in `E`). -/
theorem recurseRounds_spec {Γ : Fin n → SqlType} {f : Row n → Except EvalError (List (Row n))}
    {E : EvalError → Prop} (hE : E .recursionLimit)
    (hf : ∀ w : Row n, w.Conforms Γ → Except.Spec (f w) (fun rs => ∀ r ∈ rs, r.Conforms Γ) E)
    (dist : Bool) : ∀ (k : ℕ) (acc work : List (Row n)), (∀ r ∈ acc, r.Conforms Γ) →
      (∀ r ∈ work, r.Conforms Γ) →
      Except.Spec (recurseRounds f dist k acc work) (fun rs => ∀ r ∈ rs, r.Conforms Γ) E
  | _, acc, [], hacc, _ => by simpa [recurseRounds] using hacc
  | 0, _, _ :: _, _, _ => by simpa [recurseRounds] using hE
  | k + 1, acc, w :: ws, hacc, hwork => by
    simp only [recurseRounds]
    refine (Except.Spec.mapM (R := fun _ (ts : List (Row n)) => ∀ t ∈ ts, t.Conforms Γ)
      fun x hx => hf x (hwork x hx)).bind fun parts _ hparts => ?_
    have hout : ∀ r ∈ parts.flatten, r.Conforms Γ := by
      intro r hr
      obtain ⟨ts, hts, hr⟩ := List.mem_flatten.mp hr
      obtain ⟨_, _, h⟩ := hparts ts hts
      exact h r hr
    have hnew : ∀ r ∈ (if dist then parts.flatten.dedup.filter (· ∉ acc) else parts.flatten),
        r.Conforms Γ := by
      split
      · intro r hr
        exact hout r (List.mem_dedup.mp (List.mem_of_mem_filter hr))
      · exact hout
    exact recurseRounds_spec hE hf dist k _ _ (fun r hr => by
      rcases List.mem_append.mp hr with h | h
      · exact hacc r h
      · exact hnew r h) hnew

/-- The outer row conforms to the outer typing context (phase 9.4b, #462, decision D6). -/
def EnvOk (env : Option ((m : ℕ) × Row m)) (Γo : Option ((m : ℕ) × (Fin m → SqlType))) : Prop :=
  ∀ m Γ, Γo = some ⟨m, Γ⟩ → ∃ r : Row m, env = some ⟨m, r⟩ ∧ r.Conforms Γ

/-- Type soundness as a postcondition: on a conforming instance, a well-typed query returns rows
of its type, or fails with a runtime error (`EvalError.IsRuntime`: division by zero, or a scalar
subquery with several rows), which requires a part that is not `divSafe`. -/
theorem evalIn_spec {D : Database S} (hD : D.Conforms) {q : Query S n} :
    ∀ {env : Option ((m : ℕ) × Row m)} {Γo : Option ((m : ℕ) × (Fin m → SqlType))}
      {Γ : Fin n → SqlType}, EnvOk env Γo → q.typeOfIn Γo = some Γ →
    Except.Spec (q.evalIn D env) (fun rs => ∀ r ∈ rs, r.Conforms Γ)
      fun e => e.IsRuntime ∧ q.divSafe = false := by
  induction q with
  | table t =>
    intro env Γo Γ henv hq
    cases hq; exact hD t
  | select p q ih =>
    intro env Γo Γ henv hq
    obtain ⟨hq, hp⟩ := typeOfIn_select_eq_some.mp hq
    exact ((ih henv hq).imp_right fun hs => by simp [divSafe, hs]).bind fun rs _ hrs =>
      (Expr.filterRows_spec hrs hp).mono (fun _ h r hr => hrs r (h r hr))
        fun _ h => ⟨.inl h.1, by simp [divSafe, h.2]⟩
  | project es q ih =>
    intro env Γo Γ henv hq
    obtain ⟨Γ₀, hq, hes⟩ := typeOfIn_project_eq_some.mp hq
    refine ((ih henv hq).imp_right fun hs => by simp [divSafe, hs]).bind fun rs _ hrs =>
      (Except.Spec.mapM fun r hr => Expr.evalRow_spec (hrs r hr) hes).mono
        (fun _ h d hd => by obtain ⟨_, _, h⟩ := h d hd; exact h) ?_
    rintro _ ⟨rfl, i, hi⟩
    refine ⟨.inl rfl, ?_⟩
    simp only [divSafe, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_forall]
    exact .inl ⟨i, by simp [hi]⟩
  | join θ q₁ q₂ ih₁ ih₂ =>
    intro env Γo Γ henv hq
    obtain ⟨Γ₁, Γ₂, h₁, h₂, hθ, rfl⟩ := typeOfIn_join_eq_some.mp hq
    exact ((ih₁ henv h₁).imp_right fun hs => by simp [divSafe, hs]).bind fun rs _ hrs =>
      ((ih₂ henv h₂).imp_right fun hs => by simp [divSafe, hs]).bind fun ss _ hss =>
      (Expr.filterRows_spec (fun _ => Row.conforms_of_mem_product hrs hss) hθ).mono
        (fun _ h t ht => Row.conforms_of_mem_product hrs hss (h t ht))
        fun _ h => ⟨.inl h.1, by simp [divSafe, h.2]⟩
  | unionAll q₁ q₂ ih₁ ih₂ =>
    intro env Γo Γ henv hq
    obtain ⟨h₁, h₂⟩ := typeOfIn_unionAll_eq_some.mp hq
    exact ((ih₁ henv h₁).imp_right fun hs => by simp [divSafe, hs]).bind fun rs _ hrs =>
      ((ih₂ henv h₂).imp_right fun hs => by simp [divSafe, hs]).bind fun ss _ hss r hr =>
      (List.mem_append.mp hr).elim (hrs r) (hss r)
  | distinct q ih =>
    intro env Γo Γ henv hq
    exact (ih henv hq).bind fun rs _ hrs r hr => hrs r (List.mem_dedup.mp hr)
  | aggregate keys aggs q ih =>
    intro env Γo Γ henv hq
    obtain ⟨Γ₀, Δk, Δa, hq₀, hks, has, rfl⟩ := typeOfIn_aggregate_eq_some hq
    refine ((ih henv hq₀).imp_right fun hs => by simp [divSafe, hs]).bind ?_
    intro rs _ hconf
    have hk : Except.Spec (rs.mapM fun r => do return (← Expr.evalRow keys r, r))
        (fun keyed => ∀ x ∈ keyed, x.2 ∈ rs ∧ x.1.Conforms Δk)
        fun e => e.IsRuntime ∧ (aggregate keys aggs q).divSafe = false := by
      refine (keyed_spec hconf hks).mono (fun _ => id) ?_
      rintro _ ⟨rfl, i, hi⟩
      refine ⟨.inl rfl, ?_⟩
      simp only [divSafe, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_forall]
      exact .inl (.inl ⟨i, by simp [hi]⟩)
    refine hk.bind ?_
    intro keyed _ hkeyed
    have hconfg : ∀ kg ∈ Row.groups keyed, ∀ r ∈ kg.2, r.Conforms Γ₀ := fun kg hkg r hr => by
      obtain ⟨k, hkr⟩ := (Row.mem_groups hkg).1 r hr
      exact hconf r (hkeyed _ hkr).1
    refine (Except.Spec.mapM
      (R := fun kg (t : Row _) => ∃ d : Row _, t = Fin.append kg.1 d ∧ d.Conforms Δa)
      fun kg hkg => (AggCall.evalAll_spec (hconfg kg hkg) has).bind
        fun d _ hd => Except.spec_ok.mpr ⟨d, rfl, hd⟩).mono ?_ ?_
    · intro _ h t ht
      obtain ⟨kg, hkg, d, rfl, hdc⟩ := h t ht
      have hkc : kg.1.Conforms Δk := by
        rcases (Row.mem_groups hkg).2 with hg | ⟨r, hr⟩
        · exact fun i => absurd i.isLt (by omega)
        · exact (hkeyed _ hr).2
      exact Row.conforms_append_iff.mpr ⟨hkc, hdc⟩
    · rintro _ ⟨rfl, j, hj⟩
      refine ⟨.inl rfl, ?_⟩
      simp only [divSafe, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_forall]
      exact .inl (.inr ⟨j, by simp [hj]⟩)
  | orderBy keys q ih =>
    intro env Γo Γ henv hq
    obtain ⟨hq₀, Δ, hks⟩ := typeOfIn_orderBy_eq_some hq
    refine ((ih henv hq₀).imp_right fun hs => by simp [divSafe, hs]).bind ?_
    intro rs _ hconf
    have hk : Except.Spec (rs.mapM fun r => do
          return (← Expr.evalRow (fun i => (keys i).e) r, r))
        (fun keyed => ∀ x ∈ keyed, x.2 ∈ rs ∧ x.1.Conforms Δ)
        fun e => e.IsRuntime ∧ (orderBy keys q).divSafe = false := by
      refine (keyed_spec hconf hks).mono (fun _ => id) ?_
      rintro _ ⟨rfl, i, hi⟩
      refine ⟨.inl rfl, ?_⟩
      simp only [divSafe, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_forall]
      exact .inl ⟨i, by simp [hi]⟩
    refine hk.bind ?_
    intro keyed _ hkeyed r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact hconf _ (hkeyed x ((List.perm_insertionSort _ keyed).subset hx)).1
  | limit count offset q ih =>
    intro env Γo Γ henv hq
    refine (ih henv hq).bind fun rs _ hconf r hr => ?_
    cases count with
    | none => exact hconf r (List.mem_of_mem_drop hr)
    | some c => exact hconf r (List.mem_of_mem_drop (List.mem_of_mem_take hr))
  | intersect q₁ q₂ ih₁ ih₂ =>
    intro env Γo Γ henv hq
    obtain ⟨h₁, h₂⟩ := typeOfIn_intersect_eq_some.mp hq
    exact ((ih₁ henv h₁).imp_right fun hs => by simp [divSafe, hs]).bind fun rs _ hrs =>
      ((ih₂ henv h₂).mono (fun _ _ => trivial) fun _ h => ⟨h.1, by simp [divSafe, h.2]⟩).bind
      fun ss _ _ r hr => hrs r (Row.mem_setOp.mp hr).1
  | difference q₁ q₂ ih₁ ih₂ =>
    intro env Γo Γ henv hq
    obtain ⟨h₁, h₂⟩ := typeOfIn_difference_eq_some.mp hq
    exact ((ih₁ henv h₁).imp_right fun hs => by simp [divSafe, hs]).bind fun rs _ hrs =>
      ((ih₂ henv h₂).mono (fun _ _ => trivial) fun _ h => ⟨h.1, by simp [divSafe, h.2]⟩).bind
      fun ss _ _ r hr => hrs r (Row.mem_setOp.mp hr).1
  | attach kind sub q ihs ihq =>
    intro env Γo Γ henv hq
    simp only [typeOf, typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff] at hq
    obtain ⟨Δ, hs₀, Γ₀, hq₀, hk⟩ := hq
    refine Except.Spec.of_ok_or_error ?_
    rcases (ihs henv hs₀).ok_or_error with ⟨ss, hss, hconfs⟩ | ⟨ee, he, hre, hs⟩
    · have hvals : ∀ v ∈ ss.map (· 0), v.HasType (Δ 0) := by
        intro v hv
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
        exact hconfs r hr 0
      cases kind with
      | scalar firstRow =>
        cases hk
        rcases hsc : scalarOf firstRow (ss.map (· 0)) with err | v
        · have hcard : err = .cardinality ∧ firstRow = false := by
            unfold scalarOf at hsc
            split at hsc
            · cases hsc
            · cases hsc
            · split_ifs at hsc with hf
              cases hsc
              exact ⟨rfl, by simpa using hf⟩
          obtain ⟨rfl, hf⟩ := hcard
          refine .inr ⟨_, by simp [evalIn_attach, hss, SubKind.extra, hsc], .inr (.inl rfl), ?_⟩
          simp [divSafe, SubKind.divSafe, hf]
        · have hv : v.HasType (Δ 0) := by
            rcases hm : ss.map (· 0) with _ | ⟨v₁, _ | ⟨v₂, rest⟩⟩ <;> rw [hm] at hsc hvals <;>
              simp only [scalarOf] at hsc
            · cases hsc; trivial
            · cases hsc; exact hvals _ (by simp)
            · split_ifs at hsc
              cases hsc
              exact hvals _ (by simp)
          rcases (ihq henv hq₀).ok_or_error with ⟨rs, hrs, hconf⟩ | ⟨ee, he, hre, hs⟩
          · rcases mapM_evalRow_append hconf (x := Expr.ofDatum .int v) (σ := Δ 0) (P := False)
                (fun _ _ => .inl ⟨v, by simp, hv⟩) with ⟨ts, hts, htc⟩ | ⟨_, hF⟩
            · exact .inl ⟨ts, by simp [evalIn_attach, hss, SubKind.extra, hsc, hrs, hts], htc⟩
            · exact hF.elim
          · exact .inr ⟨ee, by simp [evalIn_attach, hss, SubKind.extra, hsc, he], hre,
              by simp [divSafe, hs]⟩
      | inSub neg e =>
        dsimp only at hk
        split_ifs at hk with hc
        cases hk
        obtain ⟨τ₀, he₀, hcmp⟩ : ∃ τ₀, e.typeOf Γ₀ = some τ₀ ∧ τ₀.Comparable (Δ 0) := by
          revert hc
          cases e.typeOf Γ₀ <;> simp
        have hall : (ss.map (· 0)).all (fun v => v.comparableWith τ₀) = true := by
          rw [List.all_eq_true]
          intro v hv
          rcases v with _ | w
          · rfl
          · have hw : w.type = Δ 0 := by simpa using hvals _ hv
            simpa [Datum.comparableWith, hw] using hcmp
        have hx : (if neg then Expr.unary .not (Expr.inList e (ss.map (· 0)))
            else Expr.inList e (ss.map (· 0))).typeOf Γ₀ = some .bool := by
          have hall' : ∀ x ∈ ss, Datum.comparableWith τ₀ (x 0) = true := by
            simpa [List.all_eq_true] using hall
          split_ifs <;> simp only [Expr.typeOf, he₀, Option.bind_eq_bind, Option.bind_some] <;>
            split_ifs with H <;> first | rfl | exact absurd (by simpa using hall') H
        rcases (ihq henv hq₀).ok_or_error with ⟨rs, hrs, hconf⟩ | ⟨ee, he', hre, hs⟩
        · rcases mapM_evalRow_append hconf (σ := .bool) (fun r hr => Expr.eval_ok_or_divisionByZero hr hx)
            with ⟨ts, hts, htc⟩ | ⟨hts, hP⟩
          · exact .inl ⟨ts, by simp [evalIn_attach, hss, SubKind.extra, hrs, hts], htc⟩
          · refine .inr ⟨_, by simp [evalIn_attach, hss, SubKind.extra, hrs, hts], .inl rfl, ?_⟩
            split_ifs at hP <;> simp_all [divSafe, SubKind.divSafe, Expr.divSafe]
        · exact .inr ⟨ee, by simp [evalIn_attach, hss, SubKind.extra, he'], hre, by simp [divSafe, hs]⟩
    · exact .inr ⟨ee, by simp [evalIn_attach, he], hre, by simp [divSafe, hs]⟩
  | one =>
    intro env Γo Γ henv hq
    cases hq
    exact fun _ _ i => i.elim0
  | outer Γ' =>
    intro env Γo Γ henv hq
    rcases Γo with _ | ⟨m, Δ⟩
    · cases hq
    · simp only [typeOfIn] at hq
      split_ifs at hq with h h'
      subst h; subst h'; cases hq
      obtain ⟨r, rfl, hr⟩ := henv _ _ rfl
      simp only [evalIn, dite_true, Except.spec_ok, List.mem_singleton, forall_eq]
      exact hr
  | window c q ih =>
    intro env Γo Γ henv hq
    simp only [typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hq
    obtain ⟨Γq, hq₀, τ, hτ, rfl⟩ := hq
    have hkeys : c.part.all (fun e => (e.typeOf Γq).isSome) = true ∧
        c.order.all (fun k => (k.e.typeOf Γq).isSome) = true := by
      simp only [WinCall.typeOf] at hτ
      split_ifs at hτ with h
      · simpa using h
    refine ((ih henv hq₀).imp_right fun hs => by simp [divSafe, hs]).bind fun rs _ hrs => ?_
    have hkey : Except.Spec (rs.zipIdx.mapM fun (r, i) => do
          return ((← c.part.mapM (·.eval r)), (← c.order.mapM (·.e.eval r)), r, i))
        (fun keyed : List (WinRow _) => ∀ y ∈ keyed, y.2.2.1.Conforms Γq)
        fun e => e.IsRuntime ∧ (window c q).divSafe = false := by
      refine (Except.Spec.mapM (R := fun (ri : Row _ × ℕ) (y : WinRow _) => y.2.2.1 = ri.1)
        fun ri hri => ?_).mono (fun ys h y hy => ?_) (fun _ h => h)
      · obtain ⟨r, i⟩ := ri
        have hr := hrs r (mem_of_mem_zipIdx hri)
        have hpd : ∀ err : EvalError, (err = .divisionByZero ∧ ∃ e ∈ c.part, e.divSafe = false) →
            err.IsRuntime ∧ (window c q).divSafe = false := by
          rintro _ ⟨rfl, e, he, hd⟩
          have : c.part.all (·.divSafe) = false := by
            rw [List.all_eq_false]; exact ⟨e, he, by simp [hd]⟩
          exact ⟨.inl rfl, by simp [divSafe, WinCall.divSafe, this]⟩
        have hod : ∀ err : EvalError, (err = .divisionByZero ∧ ∃ e ∈ c.order.map (·.e), e.divSafe = false) →
            err.IsRuntime ∧ (window c q).divSafe = false := by
          rintro _ ⟨rfl, e, he, hd⟩
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
          have : c.order.all (·.e.divSafe) = false := by
            rw [List.all_eq_false]; exact ⟨k, hk, by simp [hd]⟩
          exact ⟨.inl rfl, by simp [divSafe, WinCall.divSafe, this]⟩
        have hp := (mapM_eval_spec hr (l := c.part) (by simpa using hkeys.1)).mono
          (fun _ _ => trivial) hpd
        have ho := (mapM_eval_spec hr (l := c.order.map (·.e)) (by simpa using hkeys.2)).mono
          (fun _ _ => trivial) hod
        rw [List.mapM_map] at ho
        refine hp.bind fun ps _ _ => ho.bind fun os _ _ => Except.spec_ok.mpr rfl
      · obtain ⟨ri, hri, hy'⟩ := h y hy
        rw [hy']
        exact hrs _ (mem_of_mem_zipIdx (show (ri.1, ri.2) ∈ _ from hri))
    refine hkey.bind fun keyed _ hkeyed => ?_
    refine (Except.Spec.mapM (R := fun _ (t : Row _) => t.Conforms (Fin.append Γq ![τ]))
      fun y hy => ?_).mono (fun ts h t ht => ?_) (fun _ h => h)
    · refine ((winValue_spec c hkeyed y hτ).mono (fun _ h => h) fun _ h =>
        ⟨.inl h.1, by simp [divSafe, h.2]⟩).bind fun d _ hd => Except.spec_ok.mpr ?_
      exact Row.conforms_append_iff.mpr ⟨hkeyed y hy, fun i => by
        refine Fin.cases ?_ (fun j => j.elim0) i
        simpa using hd⟩
    · obtain ⟨_, _, h⟩ := h t ht
      exact h
  | lateral body q ihb ihq =>
    intro env Γo Γ henv hq
    simp only [typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hq
    obtain ⟨Γq, hq₀, Δ, hb, rfl⟩ := hq
    refine ((ihq henv hq₀).imp_right fun hs => by simp [divSafe, hs]).bind fun rs _ hrs => ?_
    refine ((Except.Spec.mapM
      (R := fun r (ts : List (Row _)) => ∀ t ∈ ts, t.Conforms (Fin.append Γq Δ))
      fun r hr => ((ihb (env := some ⟨_, r⟩) (fun _ _ h => by cases h; exact ⟨r, rfl, hrs r hr⟩)
        hb).imp_right fun hs => by simp [divSafe, hs]).bind fun ss _ hss =>
          Except.spec_ok.mpr fun t ht => by
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
            exact Row.conforms_append_iff.mpr ⟨hrs r hr, hss s hs⟩).bind
      fun parts _ hparts => Except.spec_ok.mpr fun t ht => ?_)
    obtain ⟨ts, hts, ht⟩ := List.mem_flatten.mp ht
    obtain ⟨r, _, hr⟩ := hparts ts hts
    exact hr t ht
  | recurse dist k base step ihb ihs =>
    intro env Γo Γ henv hq
    simp only [typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff] at hq
    obtain ⟨Γb, hb, hq⟩ := hq
    split_ifs at hq with hs
    cases hq
    refine ((ihb henv hb).imp_right fun _ => by simp [divSafe]).bind fun rs _ hrs => ?_
    have hrs' : ∀ r ∈ (if dist then rs.dedup else rs), r.Conforms Γ := by
      split
      · intro r hr
        exact hrs r (List.mem_dedup.mp hr)
      · exact hrs
    exact recurseRounds_spec (E := fun e => e.IsRuntime ∧ (recurse dist k base step).divSafe = false)
      ⟨.inr (.inr rfl), by simp [divSafe]⟩
      (fun w hw => (ihs (env := some ⟨_, w⟩) (Γo := some ⟨_, Γ⟩)
        (fun _ _ h => by cases h; exact ⟨w, rfl, hw⟩) hs).imp_right fun _ => by simp [divSafe])
      dist k _ _ hrs' hrs'

/-- Type soundness as a postcondition: on a conforming instance, a well-typed query returns rows
of its type, or fails with a runtime error (`EvalError.IsRuntime`: division by zero, or a scalar
subquery with several rows), which requires a part that is not `divSafe`. -/
theorem eval_spec {D : Database S} (hD : D.Conforms) {q : Query S n} {Γ : Fin n → SqlType}
    (hq : q.typeOf = some Γ) :
    Except.Spec (q.eval D) (fun rs => ∀ r ∈ rs, r.Conforms Γ)
      fun e => e.IsRuntime ∧ q.divSafe = false :=
  evalIn_spec hD (env := none) (Γo := none) (fun _ _ h => by cases h) hq

/-- Type soundness: on a conforming instance, a well-typed query returns rows of its type, or fails
with a runtime error (`EvalError.IsRuntime`: division by zero, or a scalar subquery with several
rows), which requires a part that is not `divSafe`. -/
theorem eval_ok_or_runtimeError {D : Database S} (hD : D.Conforms) {q : Query S n}
    {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ) :
    (∃ rs, q.eval D = .ok rs ∧ ∀ r ∈ rs, r.Conforms Γ) ∨
      (∃ e, q.eval D = .error e ∧ e.IsRuntime ∧ q.divSafe = false) :=
  (eval_spec hD hq).ok_or_error

/-- A well-typed query never raises a type error on a conforming instance. -/
theorem eval_ne_typeMismatch {D : Database S} (hD : D.Conforms) {q : Query S n}
    {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ) : q.eval D ≠ .error .typeMismatch :=
  (eval_spec hD hq).ne_error fun h => by rcases h.1 with h | h | h <;> cases h

/-- The rows of a well-typed query on a conforming instance conform to its type. -/
theorem conforms_of_eval_eq_ok {D : Database S} (hD : D.Conforms) {q : Query S n}
    {Γ : Fin n → SqlType} (hq : q.typeOf = some Γ) {rs : List (Row n)} (h : q.eval D = .ok rs) :
    ∀ r ∈ rs, r.Conforms Γ :=
  (eval_spec hD hq).of_eq_ok h

/-- A safe query succeeds on every conforming instance. -/
theorem IsSafe.exists_eval_eq_ok {q : Query S n} (hs : q.IsSafe) {D : Database S}
    (hD : D.Conforms) : ∃ rs, q.eval D = .ok rs := by
  obtain ⟨Γ, hΓ⟩ := Option.isSome_iff_exists.mp hs.1
  obtain ⟨rs, h, -⟩ := (eval_spec hD hΓ).exists_eq_ok fun e h => by simp [hs.2] at h
  exact ⟨rs, h⟩

/-! ### Outer rows (phase 9.4b, #462, decision D6) -/

/-- The query reads no outer row: it has no `outer` leaf outside the body of a `lateral` (whose
leaves read the `lateral`'s own row). -/
def closed : {n : ℕ} → Query S n → Bool
  | _, table _ => true
  | _, select _ q => q.closed
  | _, project _ q => q.closed
  | _, join _ q₁ q₂ => q₁.closed && q₂.closed
  | _, unionAll q₁ q₂ => q₁.closed && q₂.closed
  | _, distinct q => q.closed
  | _, aggregate _ _ q => q.closed
  | _, orderBy _ q => q.closed
  | _, limit _ _ q => q.closed
  | _, intersect q₁ q₂ => q₁.closed && q₂.closed
  | _, difference q₁ q₂ => q₁.closed && q₂.closed
  | _, attach _ sub q => sub.closed && q.closed
  | _, one => true
  | _, outer _ => false
  | _, lateral _ q => q.closed
  | _, window _ q => q.closed
  -- the step reads its own outer row, the working row
  | _, recurse _ _ base _ => base.closed

/-- A closed query does not depend on the outer row. -/
theorem evalIn_of_closed (D : Database S) {q : Query S n} (h : q.closed = true)
    (env : Option ((m : ℕ) × Row m)) : q.evalIn D env = q.eval D := by
  induction q with
  | table t => rfl
  | select p q ih => simp only [closed] at h; simp only [eval, evalIn, ih h]
  | project es q ih => simp only [closed] at h; simp only [eval, evalIn, ih h]
  | join θ q₁ q₂ ih₁ ih₂ =>
    simp only [closed, Bool.and_eq_true] at h; simp only [eval, evalIn, ih₁ h.1, ih₂ h.2]
  | unionAll q₁ q₂ ih₁ ih₂ =>
    simp only [closed, Bool.and_eq_true] at h; simp only [eval, evalIn, ih₁ h.1, ih₂ h.2]
  | distinct q ih => simp only [closed] at h; simp only [eval, evalIn, ih h]
  | aggregate keys aggs q ih => simp only [closed] at h; simp only [eval, evalIn, ih h]
  | orderBy keys q ih => simp only [closed] at h; simp only [eval, evalIn, ih h]
  | limit c o q ih => simp only [closed] at h; simp only [eval, evalIn, ih h]
  | intersect q₁ q₂ ih₁ ih₂ =>
    simp only [closed, Bool.and_eq_true] at h; simp only [eval, evalIn, ih₁ h.1, ih₂ h.2]
  | difference q₁ q₂ ih₁ ih₂ =>
    simp only [closed, Bool.and_eq_true] at h; simp only [eval, evalIn, ih₁ h.1, ih₂ h.2]
  | attach kind sub q ihs ihq =>
    simp only [closed, Bool.and_eq_true] at h; simp only [eval, evalIn, ihs h.1, ihq h.2]
  | one => rfl
  | outer Γ => simp [closed] at h
  | lateral body q _ ihq => simp only [closed] at h; simp only [eval, evalIn, ihq h]
  | window c q ih => simp only [closed] at h; simp only [eval, evalIn, ih h]
  | recurse dist k base step ihb _ => simp only [closed] at h; simp only [eval, evalIn, ihb h]

theorem eval_lateral (D : Database S) (body : Query S k) (q : Query S n) :
    (lateral body q).eval D = (do
      let rs ← q.eval D
      let parts ← rs.mapM fun r => do
        return (← body.evalIn D (some ⟨_, r⟩)).map (Fin.append r)
      return parts.flatten) := rfl

end Query

end SqlCore
