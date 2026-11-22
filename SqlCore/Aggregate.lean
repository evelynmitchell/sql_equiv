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
  /-- The value of `e` on the first row of the group whose `key` is least (`pick = .lt`) or greatest
  (`pick = .gt`), `NULL` keys skipped; on the last row if every key is `NULL`. It has no SQL syntax:
  it is sqlite's value of a bare column next to one `MIN(key)` or `MAX(key)` (registry T9, the
  sqlite dialect). Both expressions are evaluated on every row. -/
  | atExtreme (pick : Ordering) (key e : Expr n)
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

/-- The pair with the least (`pick = .lt`) or greatest (`pick = .gt`) non-`NULL` key, the first one
on ties, starting from `best`. -/
def bestAt (pick : Ordering) :
    Option (Value × Datum) → List (Datum × Datum) → Except EvalError (Option (Value × Datum))
  | best, [] => .ok best
  | best, (none, _) :: ps => bestAt pick best ps
  | none, (some k, v) :: ps => bestAt pick (some (k, v)) ps
  | some (b, w), (some k, v) :: ps => do
    let o ← Value.cmp k b
    bestAt pick (if o = pick then some (k, v) else some (b, w)) ps

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
  | atExtreme pick key e, rs => do
    let ks ← rs.mapM key.eval
    let vs ← rs.mapM e.eval
    let best ← bestAt pick none (ks.zip vs)
    return match best with
      | some (_, v) => v
      | none => vs.getLast?.getD none

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
  | atExtreme _ key e =>
    match key.typeOf Γ with
    | some .int | some .decimal | some .text => e.typeOf Γ
    | _ => none

/-- Every division in the argument is by a nonzero numeric literal. -/
def divSafe : AggCall n → Bool
  | countStar => true
  | call _ _ e => e.divSafe
  | first e => e.divSafe
  | atExtreme _ key e => key.divSafe && e.divSafe

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

private theorem bestAt_type {pick : Ordering} {κ σ : SqlType} :
    ∀ (ps : List (Datum × Datum)) (best : Option (Value × Datum)),
      (∀ p ∈ ps, p.1.HasType κ ∧ p.2.HasType σ) →
      (∀ b w, best = some (b, w) → b.type = κ ∧ w.HasType σ) →
      ∃ r, bestAt pick best ps = .ok r ∧ ∀ b w, r = some (b, w) → b.type = κ ∧ w.HasType σ
  | [], best, _, hb => ⟨best, rfl, hb⟩
  | (none, v) :: ps, best, hps, hb => by
    obtain ⟨r, hr, hrt⟩ := bestAt_type (pick := pick) ps best (fun p hp => hps p (by simp [hp])) hb
    exact ⟨r, by simpa [bestAt] using hr, hrt⟩
  | (some k, v) :: ps, none, hps, _ => by
    have ⟨hk, hv⟩ := hps (some k, v) (by simp)
    have hk' : k.type = κ := by simpa using hk
    obtain ⟨r, hr, hrt⟩ := bestAt_type (pick := pick) ps (some (k, v)) (fun p hp => hps p (by simp [hp]))
      (fun b w h => by cases h; exact ⟨hk', hv⟩)
    exact ⟨r, by simpa [bestAt] using hr, hrt⟩
  | (some k, v) :: ps, some (b, w), hps, hb => by
    have ⟨hk, hv⟩ := hps (some k, v) (by simp)
    have hk' : k.type = κ := by simpa using hk
    obtain ⟨hbt, hw⟩ := hb b w rfl
    obtain ⟨o, ho⟩ := Value.exists_cmp_eq_ok_iff.mpr
      (.inl (hk'.trans hbt.symm) : k.type.Comparable b.type)
    obtain ⟨r, hr, hrt⟩ := bestAt_type (pick := pick) ps (if o = pick then some (k, v) else some (b, w))
      (fun p hp => hps p (by simp [hp]))
      (fun b' w' h => by
        split_ifs at h <;> cases h
        · exact ⟨hk', hv⟩
        · exact ⟨hbt, hw⟩)
    exact ⟨r, by simp [bestAt, ho, hr], hrt⟩

/-- The argument of an aggregate over conforming rows: all values of its type, or a division by
zero. -/
private theorem mapM_eval_spec {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {e : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ) :
    Except.Spec (rs.mapM e.eval) (fun ds => ∀ d ∈ ds, d.HasType τ)
      fun err => err = .divisionByZero ∧ e.divSafe = false :=
  (Except.Spec.mapM fun r hr => Expr.eval_spec (hrs r hr) he).mono
    (fun _ h d hd => by obtain ⟨_, _, h⟩ := h d hd; exact h) fun _ => id

/-- Type soundness as a postcondition: over rows conforming to `Γ`, a well-typed aggregate call
returns a datum of its type, or its argument divides by zero. -/
theorem eval_spec {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {a : AggCall n} {σ : SqlType} (ha : a.typeOf Γ = some σ) :
    Except.Spec (a.eval rs) (·.HasType σ)
      fun err => err = .divisionByZero ∧ a.divSafe = false := by
  cases a with
  | countStar => cases ha; rfl
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
    refine (mapM_eval_spec hrs he).bind fun ds _ hdτ => ?_
    have hvs : ∀ v ∈ (if dist then (ds.filterMap id).dedup else ds.filterMap id), v.type = τ := by
      intro v hv
      have hv' : v ∈ ds.filterMap id := by split_ifs at hv <;> simp_all [List.mem_dedup]
      obtain ⟨d, hd, rfl⟩ := List.mem_filterMap.mp hv'
      exact hdτ (some v) (by simpa using hd)
    obtain ⟨d, hd, hdσ⟩ := apply_type hvs hfn
    show Except.Spec (fn.apply (if dist then (ds.filterMap id).dedup else ds.filterMap id)) _ _
    rw [hd]
    exact hdσ
  | first e =>
    refine (mapM_eval_spec hrs ha).bind fun ds _ hdτ => ?_
    rcases ds with _ | ⟨d, ds⟩
    · trivial
    · exact hdτ d (by simp)
  | atExtreme pick key e =>
    obtain ⟨κ, hk⟩ : ∃ κ, key.typeOf Γ = some κ := by
      simp only [typeOf] at ha
      split at ha <;> first | exact ⟨_, ‹_›⟩ | exact absurd ha (by simp)
    have he : e.typeOf Γ = some σ := by
      simp only [typeOf, hk] at ha
      split at ha <;> first | exact ha | exact absurd ha (by simp)
    refine ((mapM_eval_spec hrs hk).imp_error fun hs => by simp [divSafe, hs]).bind
      fun ks _ hkτ => ((mapM_eval_spec hrs he).imp_error fun hs => by simp [divSafe, hs]).bind
      fun vs _ hvτ => ?_
    obtain ⟨r, hr, hrt⟩ := bestAt_type (pick := pick) (ks.zip vs) none
      (fun p hp => ⟨hkτ _ (List.of_mem_zip hp).1, hvτ _ (List.of_mem_zip hp).2⟩)
      (fun _ _ h => by cases h)
    rw [hr, Except.ok_bind]
    rcases r with _ | ⟨b, w⟩
    · rcases hl : vs.getLast? with _ | d
      · simp
      · simpa [hl] using hvτ d (List.mem_of_getLast? hl)
    · exact (hrt b w rfl).2

/-- Type soundness: over rows conforming to `Γ`, a well-typed aggregate call returns a datum of its
type, or its argument divides by zero. -/
theorem eval_ok_or_divisionByZero {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {a : AggCall n} {σ : SqlType} (ha : a.typeOf Γ = some σ) :
    (∃ d, a.eval rs = .ok d ∧ d.HasType σ) ∨
      (a.eval rs = .error .divisionByZero ∧ a.divSafe = false) :=
  (eval_spec hrs ha).eq_ok_or_eq_error

/-- Evaluate a list of aggregate calls over a group: the row of results, or the first error. -/
def evalAll : {a : ℕ} → (Fin a → AggCall n) → List (Row n) → Except EvalError (Row a)
  | 0, _, _ => .ok ![]
  | _ + 1, as, rs => do
    let d ← (as 0).eval rs
    let ds ← evalAll (fun i => as i.succ) rs
    return Matrix.vecCons d ds

/-- Type soundness for a list of aggregate calls, as a postcondition. -/
theorem evalAll_spec {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) : ∀ {a : ℕ} {as : Fin a → AggCall n} {Δ : Fin a → SqlType},
    (∀ j, (as j).typeOf Γ = some (Δ j)) →
    Except.Spec (evalAll as rs) (·.Conforms Δ)
      fun err => err = .divisionByZero ∧ ∃ j, (as j).divSafe = false
  | 0, _, _, _ => fun i => i.elim0
  | a + 1, as, Δ, has => by
    refine ((eval_spec hrs (has 0)).mono (fun _ => id) fun _ h => ⟨h.1, 0, h.2⟩).bind
      fun d _ hdτ => ((evalAll_spec hrs (as := fun i => as i.succ) (Δ := fun i => Δ i.succ)
        (fun j => has j.succ)).mono (fun _ => id) fun _ h =>
          ⟨h.1, let ⟨j, hj⟩ := h.2; ⟨j.succ, hj⟩⟩).bind
      fun ds _ hdsτ i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hdτ
    · simpa using hdsτ j

/-- Type soundness for a list of aggregate calls. -/
theorem evalAll_ok_or_divisionByZero {Γ : Fin n → SqlType} {rs : List (Row n)}
    (hrs : ∀ r ∈ rs, r.Conforms Γ) {a : ℕ} {as : Fin a → AggCall n} {Δ : Fin a → SqlType}
    (has : ∀ j, (as j).typeOf Γ = some (Δ j)) :
    (∃ d, evalAll as rs = .ok d ∧ d.Conforms Δ) ∨
      (evalAll as rs = .error .divisionByZero ∧ ∃ j, (as j).divSafe = false) :=
  (evalAll_spec hrs has).eq_ok_or_eq_error

end AggCall

end SqlCore
