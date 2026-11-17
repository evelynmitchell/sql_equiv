/-
Copyright (c) 2026 Evelyn Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell
-/
module

public import SqlCore.Typing
public import SqlCore.Except

/-!
# Aggregate calls (typed core phase 8a, #313)

An aggregate call (`AggCall n`) is evaluated over a group of rows (`AggCall.eval`):
`COUNT(*)`, `COUNT([DISTINCT] e)`, `SUM([DISTINCT] e)`, `MIN(e)` and `MAX(e)`. The argument is
evaluated on every row of the group, strictly, and `NULL` arguments are ignored. `SUM`, `MIN`
and `MAX` over no non-null value give `NULL`, and `COUNT` gives `0`. These are the semantics of
Postgres and DuckDB (#313).

Typing (`AggCall.typeOf`): `COUNT` is `int`. `SUM` takes an `int` or `decimal` argument and keeps
its type. `MIN` and `MAX` take `int`, `decimal` or `text`; booleans are ill-typed, because
Postgres rejects them and DuckDB accepts them (registry row 14). `AVG` takes an `int` or `decimal`
argument and is the exact mean, a `decimal` (phase 8d, #326; registry T10).

Soundness (`AggCall.eval_ok_or_divisionByZero`): on rows conforming to `Γ`, a well-typed call
returns a datum of its type, or its argument divides by zero.
-/

@[expose] public section

namespace SqlCore

/-- The aggregate functions. -/
inductive AggFn where
  | count | sum | min | max
  /-- `AVG`: the exact mean as a decimal (phase 8d; registry T10). -/
  | avg
  deriving DecidableEq, Repr

/-- An aggregate call over rows of `n` columns. -/
inductive AggCall (n : ℕ) where
  /-- `COUNT(*)`. -/
  | countStar
  /-- `fn([DISTINCT] e)`. -/
  | call (fn : AggFn) (distinct : Bool) (e : Expr n)
  /-- The value of `e` on the first row of the group, `NULL` included (DuckDB's `first`). It has
  no SQL syntax here: the bridge uses it for the sort key of `SELECT DISTINCT … ORDER BY` a key
  that is not selected (registry row 5, `firstRow`). Like every aggregate, it evaluates `e` on
  every row, so a failure on any row fails the group. -/
  | first (e : Expr n)
  deriving DecidableEq, Repr

namespace Value

/-- Add two numbers, promoting an integer when the other is a decimal; any other value is a
type error. -/
def add : Value → Value → Except EvalError Value
  | int a, int b => .ok (int (a + b))
  | decimal p, decimal q => .ok (decimal (p + q))
  | int a, decimal q => .ok (decimal (a + q))
  | decimal p, int b => .ok (decimal (p + b))
  | _, _ => .error .typeMismatch

end Value

/-- The sum of a nonempty list of values, from the left. -/
def sumFrom (acc : Value) : List Value → Except EvalError Value
  | [] => .ok acc
  | v :: vs => do sumFrom (← acc.add v) vs

/-- The least (`pick = .lt`) or greatest (`pick = .gt`) of a list of values, from the left. -/
def extremeFrom (pick : Ordering) (acc : Value) : List Value → Except EvalError Value
  | [] => .ok acc
  | v :: vs => do
    let o ← Value.cmp v acc
    extremeFrom pick (if o = pick then v else acc) vs

/-- The mean of a sum over `k` values, exact, as a decimal (an integer sum is promoted). -/
def meanOf (s : Value) (k : ℕ) : Except EvalError Value :=
  match s with
  | .int z => .ok (.decimal ((z : ℚ) / k))
  | .decimal q => .ok (.decimal (q / k))
  | _ => .error .typeMismatch

/-- An aggregate function over the non-null values of a group. -/
def AggFn.apply : AggFn → List Value → Except EvalError Datum
  | .count, vs => .ok (some (.int vs.length))
  | _, [] => .ok none
  | .sum, v :: vs => some <$> sumFrom v vs
  | .min, v :: vs => some <$> extremeFrom .lt v vs
  | .max, v :: vs => some <$> extremeFrom .gt v vs
  | .avg, v :: vs => do return some (← meanOf (← sumFrom v vs) (vs.length + 1))

namespace AggCall

variable {n : ℕ}

/-- Evaluate an aggregate call over a group of rows. -/
def eval : AggCall n → List (Row n) → Except EvalError Datum
  | countStar, rs => .ok (some (.int rs.length))
  | call fn distinct e, rs => do
    let ds ← rs.mapM e.eval
    let vs := ds.filterMap id
    fn.apply (if distinct then vs.dedup else vs)
  | first e, rs => do
    let ds ← rs.mapM e.eval
    return ds.head?.getD none

/-- The result type of an aggregate call, if it is well-typed. -/
def typeOf (Γ : Fin n → SqlType) : AggCall n → Option SqlType
  | countStar => some .int
  | call .count _ e => (e.typeOf Γ).map fun _ => .int
  | call .sum _ e =>
    match e.typeOf Γ with
    | some .int => some .int
    | some .decimal => some .decimal
    | _ => none
  | call .avg _ e =>
    match e.typeOf Γ with
    | some .int => some .decimal
    | some .decimal => some .decimal
    | _ => none
  | call .min _ e | call .max _ e =>
    match e.typeOf Γ with
    | some .int => some .int
    | some .decimal => some .decimal
    | some .text => some .text
    | _ => none
  | first e => e.typeOf Γ

/-- Every division in the argument is by a nonzero numeric literal. -/
def divSafe : AggCall n → Bool
  | countStar => true
  | call _ _ e => e.divSafe
  | first e => e.divSafe

/-! ### Soundness -/

/-- The result type `σ` of `fn` over an argument of type `τ`. -/
def _root_.SqlCore.AggFn.ResultType (fn : AggFn) (τ σ : SqlType) : Prop :=
  match fn with
  | .count => σ = .int
  | .sum => (τ = .int ∨ τ = .decimal) ∧ σ = τ
  | .min | .max => σ = τ
  | .avg => (τ = .int ∨ τ = .decimal) ∧ σ = .decimal

private theorem sumFrom_type {τ : SqlType} (hτ : τ = .int ∨ τ = .decimal) :
    ∀ (acc : Value) (vs : List Value), acc.type = τ → (∀ v ∈ vs, v.type = τ) →
      ∃ w, sumFrom acc vs = .ok w ∧ w.type = τ
  | acc, [], hacc, _ => ⟨acc, rfl, hacc⟩
  | acc, v :: vs, hacc, hvs => by
    have hv := hvs v (by simp)
    obtain ⟨s, hs, hsτ⟩ : ∃ s, acc.add v = .ok s ∧ s.type = τ := by
      rcases hτ with rfl | rfl <;> cases acc <;> cases v <;> simp_all [Value.add]
    obtain ⟨w, hw, hwτ⟩ := sumFrom_type hτ s vs hsτ fun u hu => hvs u (by simp [hu])
    exact ⟨w, by simp [sumFrom, hs, hw], hwτ⟩

private theorem extremeFrom_type {τ : SqlType} (pick : Ordering) :
    ∀ (acc : Value) (vs : List Value), acc.type = τ → (∀ v ∈ vs, v.type = τ) →
      ∃ w, extremeFrom pick acc vs = .ok w ∧ w.type = τ
  | acc, [], hacc, _ => ⟨acc, rfl, hacc⟩
  | acc, v :: vs, hacc, hvs => by
    have hv := hvs v (by simp)
    obtain ⟨o, ho⟩ := Value.exists_cmp_eq_ok_iff.mpr (.inl (hv.trans hacc.symm) : v.type.Comparable acc.type)
    have hnext : (if o = pick then v else acc).type = τ := by split_ifs <;> assumption
    obtain ⟨w, hw, hwτ⟩ := extremeFrom_type pick _ vs hnext fun u hu => hvs u (by simp [hu])
    exact ⟨w, by simp [extremeFrom, ho, hw], hwτ⟩

private theorem apply_type {fn : AggFn} {τ σ : SqlType} {vs : List Value}
    (hvs : ∀ v ∈ vs, v.type = τ) (h : fn.ResultType τ σ) :
    ∃ d, fn.apply vs = .ok d ∧ d.HasType σ := by
  cases fn <;> simp only [AggFn.ResultType] at h
  case count => subst h; exact ⟨_, rfl, rfl⟩
  case sum =>
    obtain ⟨hτ, rfl⟩ := h
    rcases vs with _ | ⟨v, vs⟩
    · exact ⟨none, rfl, trivial⟩
    · obtain ⟨w, hw, hwτ⟩ := sumFrom_type hτ v vs (hvs v (by simp)) fun u hu => hvs u (by simp [hu])
      exact ⟨some w, by simp [AggFn.apply, hw], hwτ⟩
  case min =>
    subst h
    rcases vs with _ | ⟨v, vs⟩
    · exact ⟨none, rfl, trivial⟩
    · obtain ⟨w, hw, hwτ⟩ := extremeFrom_type .lt v vs (hvs v (by simp)) fun u hu => hvs u (by simp [hu])
      exact ⟨some w, by simp [AggFn.apply, hw], hwτ⟩
  case max =>
    subst h
    rcases vs with _ | ⟨v, vs⟩
    · exact ⟨none, rfl, trivial⟩
    · obtain ⟨w, hw, hwτ⟩ := extremeFrom_type .gt v vs (hvs v (by simp)) fun u hu => hvs u (by simp [hu])
      exact ⟨some w, by simp [AggFn.apply, hw], hwτ⟩
  case avg =>
    obtain ⟨hτ, rfl⟩ := h
    rcases vs with _ | ⟨v, vs⟩
    · exact ⟨none, rfl, trivial⟩
    · obtain ⟨w, hw, hwτ⟩ := sumFrom_type hτ v vs (hvs v (by simp)) fun u hu => hvs u (by simp [hu])
      rcases hτ with rfl | rfl <;> cases w <;> simp at hwτ
      case inl.int z =>
        exact ⟨some (.decimal ((z : ℚ) / (vs.length + 1 : ℕ))),
          by simp [AggFn.apply, hw, meanOf, pure, Except.pure], rfl⟩
      case inr.decimal q =>
        exact ⟨some (.decimal (q / (vs.length + 1 : ℕ))),
          by simp [AggFn.apply, hw, meanOf, pure, Except.pure], rfl⟩

/-- The argument of an aggregate over conforming rows: all values of its type, or a division by
zero. -/
private theorem mapM_eval_ok_or_divisionByZero {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {e : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ) :
    (∃ ds, rs.mapM e.eval = .ok ds ∧ ∀ d ∈ ds, d.HasType τ) ∨
      (rs.mapM e.eval = .error .divisionByZero ∧ e.divSafe = false) := by
  rcases h : rs.mapM e.eval with err | ds
  · obtain ⟨r, hr, herr⟩ := Except.exists_mem_eq_error_of_mapM_eq_error h
    rcases Expr.eval_ok_or_divisionByZero (hrs r hr) he with ⟨d, hd, -⟩ | ⟨hd, hs⟩
    · simp [hd] at herr
    · rw [herr, _root_.Except.error.injEq] at hd
      exact .inr ⟨by rw [hd], hs⟩
  · refine .inl ⟨ds, rfl, fun d hd => ?_⟩
    obtain ⟨r, hr, hrd⟩ := Except.exists_mem_eq_ok_of_mapM_eq_ok h hd
    exact Expr.hasType_of_eval_eq_ok (hrs r hr) he hrd

/-- Type soundness: over rows conforming to `Γ`, a well-typed aggregate call returns a datum of its
type, or its argument divides by zero. -/
theorem eval_ok_or_divisionByZero {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {a : AggCall n} {σ : SqlType} (ha : a.typeOf Γ = some σ) :
    (∃ d, a.eval rs = .ok d ∧ d.HasType σ) ∨
      (a.eval rs = .error .divisionByZero ∧ a.divSafe = false) := by
  cases a with
  | countStar => cases ha; exact .inl ⟨_, rfl, rfl⟩
  | call fn dist e =>
    obtain ⟨τ, he, hfn⟩ : ∃ τ, e.typeOf Γ = some τ ∧ fn.ResultType τ σ := by
      cases fn <;> simp only [typeOf] at ha
      · obtain ⟨τ, hτ, rfl⟩ := Option.map_eq_some_iff.mp ha
        exact ⟨τ, hτ, rfl⟩
      all_goals
        split at ha
        all_goals first
          | (cases ha; exact ⟨_, ‹_›, by simp [AggFn.ResultType]⟩)
          | exact absurd ha (by simp)
    rcases mapM_eval_ok_or_divisionByZero hrs he with ⟨ds, hds, hdτ⟩ | ⟨hds, hs⟩
    · have hvs : ∀ v ∈ (if dist then (ds.filterMap id).dedup else ds.filterMap id), v.type = τ := by
        intro v hv
        have hv' : v ∈ ds.filterMap id := by split_ifs at hv <;> simp_all [List.mem_dedup]
        obtain ⟨d, hd, rfl⟩ := List.mem_filterMap.mp hv'
        exact hdτ (some v) (by simpa using hd)
      obtain ⟨d, hd, hdσ⟩ := apply_type hvs hfn
      exact .inl ⟨d, by simpa [eval, hds] using hd, hdσ⟩
    · exact .inr ⟨by simp [eval, hds], hs⟩
  | first e =>
    rcases mapM_eval_ok_or_divisionByZero hrs ha with ⟨ds, hds, hdτ⟩ | ⟨hds, hs⟩
    · refine .inl ⟨ds.head?.getD none, by simp [eval, hds, pure, Except.pure], ?_⟩
      rcases ds with _ | ⟨d, ds⟩
      · trivial
      · exact hdτ d (by simp)
    · exact .inr ⟨by simp [eval, hds], hs⟩

/-- Evaluate a list of aggregate calls over a group: the row of results, or the first error. -/
def evalAll : {a : ℕ} → (Fin a → AggCall n) → List (Row n) → Except EvalError (Row a)
  | 0, _, _ => .ok ![]
  | _ + 1, as, rs => do
    let d ← (as 0).eval rs
    let ds ← evalAll (fun i => as i.succ) rs
    return Matrix.vecCons d ds

/-- Type soundness for a list of aggregate calls. -/
theorem evalAll_ok_or_divisionByZero {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) : ∀ {a : ℕ} {as : Fin a → AggCall n} {Δ : Fin a → SqlType},
    (∀ j, (as j).typeOf Γ = some (Δ j)) →
    (∃ d, evalAll as rs = .ok d ∧ d.Conforms Δ) ∨
      (evalAll as rs = .error .divisionByZero ∧ ∃ j, (as j).divSafe = false)
  | 0, _, _, _ => .inl ⟨![], rfl, fun i => i.elim0⟩
  | a + 1, as, Δ, has => by
    rcases eval_ok_or_divisionByZero hrs (has 0) with ⟨d, hd, hdτ⟩ | ⟨hd, hs⟩
    · rcases evalAll_ok_or_divisionByZero hrs (as := fun i => as i.succ) (Δ := fun i => Δ i.succ)
          (fun j => has j.succ) with ⟨ds, hds, hdsτ⟩ | ⟨hds, j, hs⟩
      · refine .inl ⟨Matrix.vecCons d ds, by simp [evalAll, hd, hds, pure, Except.pure], ?_⟩
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hdτ
        · simpa using hdsτ j
      · exact .inr ⟨by simp [evalAll, hd, hds], j.succ, hs⟩
    · exact .inr ⟨by simp [evalAll, hd], 0, hs⟩

end AggCall

end SqlCore
