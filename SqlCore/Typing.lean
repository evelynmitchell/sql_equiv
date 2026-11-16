/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module

public import SqlCore.Expr

/-!
# Typing and safety of SQL expressions

`UnOp.typeOf` and `BinOp.typeOf` give the result type of an operator on operands of given types,
and `Expr.typeOf Γ e` the type of an expression over a typing context `Γ : Fin n → SqlType`: a
literal has its value's type, `NULL` its declared type, `col i` the type `Γ i`, `e IN vs` is
boolean when every list element is comparable with `e`'s type, and `CASE` needs a boolean
condition and branches of one type. Arithmetic with a decimal operand has type `decimal`, and
comparison needs comparable types (decisions 4 and 6). Decimal `/` is ill-typed: its result scale
is implementation-defined, and `evalBinOp` reports it as `unsupported`.

Type soundness (`Expr.eval_ok_or_divisionByZero`): on a row conforming to `Γ`, a well-typed
expression of type `τ` never raises `typeMismatch`; it either returns `NULL` or a value of type
`τ`, or divides by zero. Division by zero is excluded syntactically by `Expr.divSafe`: `/` and `%`
only by a nonzero integer or decimal literal. An expression is *safe* (`Expr.IsSafe`, decidable) when it is
well-typed and `divSafe`, and a safe expression succeeds on every conforming row
(`Expr.IsSafe.exists_eval_eq_ok`). A safe predicate (`Expr.IsSafePredicate`, also boolean-typed)
never makes a `WHERE` or `ON` clause fail. Laws that move, duplicate or drop the evaluation of an
expression use safety as their side condition. A divisor that is a column or a computed expression
is not safe even when it is never zero on the data: safety is a syntactic check.

Typing and safety are preserved by renaming and by substitution of safe expressions of the right
types (`Expr.typeOf_rename`, `Expr.typeOf_subst`, `Expr.IsSafe.rename`,
`Expr.IsSafePredicate.rename`, `Expr.IsSafe.subst`).

Typed core phase 3 (#292), re-derived from cslib-frontier's `Languages/SQL/Typing.lean` (pinned
`e78796a1`) and extended to decimals. `SqlEquiv` checks types on the data at evaluation time; here
typing is static, relative to a typing context.

## Main definitions

* `SqlCore.UnOp.typeOf`, `SqlCore.BinOp.typeOf`: result types of the operators.
* `SqlCore.Expr.typeOf`: the type of an expression in a typing context.
* `SqlCore.Expr.divSafe`: every division or remainder is by a nonzero numeric literal.
* `SqlCore.Expr.IsSafe`, `SqlCore.Expr.IsSafePredicate`: the decidable safety checks.

## Main results

* `SqlCore.evalUnOp_ok_of_typeOf`, `SqlCore.evalBinOp_ok_or_divisionByZero`: operator
  soundness.
* `SqlCore.Expr.eval_ok_or_divisionByZero`: type soundness of expressions.
* `SqlCore.Expr.eval_ne_typeMismatch`: a well-typed expression never raises a type error.
* `SqlCore.Expr.IsSafe.exists_eval_eq_ok`: a safe expression succeeds on conforming rows.
* `SqlCore.Expr.IsSafePredicate.exists_evalTruth_eq_ok`: a safe predicate never fails.
-/

@[expose] public section

namespace SqlCore

/-! ### Operators -/

/-- The result type of a unary operator on an operand of type `τ`, if the application is
well-typed. -/
def UnOp.typeOf : UnOp → SqlType → Option SqlType
  | .not, .bool => some .bool
  | .neg, .int => some .int
  | .neg, .decimal => some .decimal
  | .isNull, _ => some .bool
  | .isNotNull, _ => some .bool
  | _, _ => none

/-- The result type of an arithmetic operator: integers stay integers, a decimal operand makes the
result a decimal, and decimal `/` is ill-typed. -/
def ArithOp.typeOf (op : ArithOp) : SqlType → SqlType → Option SqlType
  | .int, .int => some .int
  | .int, .decimal | .decimal, .int | .decimal, .decimal =>
    if op = .div then none else some .decimal
  | _, _ => none

/-- The result type of a binary operator on operands of types `τ₁` and `τ₂`, if the application is
well-typed: comparisons need comparable types. -/
def BinOp.typeOf : BinOp → SqlType → SqlType → Option SqlType
  | .arith op, τ₁, τ₂ => op.typeOf τ₁ τ₂
  | .cmp _, τ₁, τ₂ => if τ₁.Comparable τ₂ then some .bool else none
  | .and, .bool, .bool => some .bool
  | .or, .bool, .bool => some .bool
  | .concat, .text, .text => some .text
  | _, _, _ => none

/-- Whether the operator fails on a zero divisor: `/` and `%`. -/
def BinOp.isDivision : BinOp → Bool
  | .arith op => op.isDivision
  | _ => false

/-- The datum is the number zero, integer or decimal. -/
def Datum.isZero : Datum → Bool
  | some (.int z) => z == 0
  | some (.decimal q) => q == 0
  | _ => false

private theorem hasType_int_cases {d : Datum} (h : d.HasType .int) :
    d = none ∨ ∃ z, d = some (.int z) := by
  rcases d with _ | (z | _ | _ | _) <;> simp_all

private theorem hasType_decimal_cases {d : Datum} (h : d.HasType .decimal) :
    d = none ∨ ∃ q, d = some (.decimal q) := by
  rcases d with _ | (_ | _ | _ | q) <;> simp_all

/-- A well-typed unary operator succeeds, with a result of its type. -/
theorem evalUnOp_ok_of_typeOf {op : UnOp} {τ τ' : SqlType} (h : op.typeOf τ = some τ')
    {d : Datum} (hd : d.HasType τ) : ∃ d', evalUnOp op d = .ok d' ∧ d'.HasType τ' := by
  match op, τ, h with
  | .not, .bool, h =>
    cases h
    obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hd
    exact ⟨t.not.toDatum, by simp [evalUnOp, ht], Truth.toDatum_hasType _⟩
  | .neg, .int, h =>
    cases h
    rcases hasType_int_cases hd with rfl | ⟨z, rfl⟩
    · exact ⟨none, rfl, trivial⟩
    · exact ⟨some (.int (negInt z)), rfl, rfl⟩
  | .neg, .decimal, h =>
    cases h
    rcases hasType_decimal_cases hd with rfl | ⟨q, rfl⟩
    · exact ⟨none, rfl, trivial⟩
    · exact ⟨some (.decimal (negDec q)), rfl, rfl⟩
  | .isNull, _, h => cases h; exact ⟨_, rfl, rfl⟩
  | .isNotNull, _, h => cases h; exact ⟨_, rfl, rfl⟩

private theorem hasType_numeric_cases {d : Datum} {τ : SqlType} (hτ : τ.isNumeric)
    (h : d.HasType τ) : d = none ∨ (∃ z, d = some (.int z)) ∨ ∃ q, d = some (.decimal q) := by
  cases τ <;> simp [SqlType.isNumeric] at hτ
  · rcases hasType_int_cases h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · rcases hasType_decimal_cases h with h | h
    · exact .inl h
    · exact .inr (.inr h)

private theorem ArithOp.typeOf_isNumeric {op : ArithOp} {τ₁ τ₂ τ : SqlType}
    (h : op.typeOf τ₁ τ₂ = some τ) : τ₁.isNumeric ∧ τ₂.isNumeric := by
  cases τ₁ <;> cases τ₂ <;> simp [ArithOp.typeOf, SqlType.isNumeric] at h ⊢

/-- An arithmetic operator on numeric operands of the right types: the integer case. -/
private theorem arith_int_int (op : ArithOp) (x y : ℤ) :
    (∃ z, evalBinOp (.arith op) (some (.int x)) (some (.int y)) = .ok (some (.int z))) ∨
      (evalBinOp (.arith op) (some (.int x)) (some (.int y)) = .error .divisionByZero ∧
        op.isDivision ∧ y = 0) := by
  rcases hz : op.eval x y with e | z
  · obtain ⟨rfl, hd, rfl⟩ := ArithOp.eval_eq_error hz
    exact .inr ⟨by simp [evalBinOp, Datum.asNum, ArithOp.evalNum, hz], hd, rfl⟩
  · exact .inl ⟨z, by simp [evalBinOp, Datum.asNum, ArithOp.evalNum, hz]⟩

/-- The decimal case: away from `/`, the operator succeeds unless `%` divides by zero. -/
private theorem evalDec_ok_or_zero {op : ArithOp} (hop : op ≠ .div) (p q : ℚ) :
    (∃ r, op.evalDec p q = .ok r) ∨ (op.evalDec p q = .error .divisionByZero ∧ op = .mod ∧ q = 0) := by
  cases op <;> simp only [ArithOp.evalDec, modDec] at hop ⊢
  · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact absurd rfl hop
  · by_cases hq : q = 0
    · exact .inr ⟨by simp [hq], by simp, hq⟩
    · exact .inl ⟨p - q * truncRat (p / q), by simp [hq]⟩

/-- A well-typed binary operator succeeds with a result of its type, unless it divides by zero,
in which case the divisor is the number zero. -/
theorem evalBinOp_ok_or_divisionByZero {op : BinOp} {τ₁ τ₂ τ : SqlType}
    (h : op.typeOf τ₁ τ₂ = some τ) {a b : Datum} (ha : a.HasType τ₁) (hb : b.HasType τ₂) :
    (∃ d, evalBinOp op a b = .ok d ∧ d.HasType τ) ∨
      (evalBinOp op a b = .error .divisionByZero ∧ op.isDivision ∧ b.isZero) := by
  match op, h with
  | .arith op, h =>
    simp only [BinOp.typeOf] at h
    obtain ⟨hn₁, hn₂⟩ := ArithOp.typeOf_isNumeric h
    rcases hasType_numeric_cases hn₁ ha with rfl | ⟨x, rfl⟩ | ⟨p, rfl⟩
    · refine .inl ⟨none, ?_, trivial⟩
      rcases hasType_numeric_cases hn₂ hb with rfl | ⟨y, rfl⟩ | ⟨q, rfl⟩ <;> rfl
    all_goals rcases hasType_numeric_cases hn₂ hb with rfl | ⟨y, rfl⟩ | ⟨q, rfl⟩
    · refine .inl ⟨none, ?_, trivial⟩
      cases op <;> rfl
    · -- int, int
      simp only [Datum.hasType_some, Value.type_int] at ha hb
      subst ha hb
      simp only [ArithOp.typeOf, Option.some.injEq] at h
      subst h
      rcases arith_int_int op x y with ⟨z, hz⟩ | ⟨hz, hd, rfl⟩
      · exact .inl ⟨_, hz, rfl⟩
      · exact .inr ⟨hz, hd, rfl⟩
    all_goals try (refine .inl ⟨none, ?_, trivial⟩; cases op <;> rfl)
    all_goals
      simp only [Datum.hasType_some, Value.type_int, Value.type_decimal] at ha hb
      subst ha hb
      simp only [ArithOp.typeOf, Option.ite_none_left_eq_some, Option.some.injEq] at h
      obtain ⟨hop, rfl⟩ := h
    · rcases evalDec_ok_or_zero hop x q with ⟨r, hr⟩ | ⟨hr, rfl, rfl⟩
      · exact .inl ⟨some (.decimal r), by simp [evalBinOp, Datum.asNum, ArithOp.evalNum, hr], rfl⟩
      · exact .inr ⟨by simp [evalBinOp, Datum.asNum, ArithOp.evalNum, hr], rfl, by simp [Datum.isZero]⟩
    · rcases evalDec_ok_or_zero hop p y with ⟨r, hr⟩ | ⟨hr, rfl, hy⟩
      · exact .inl ⟨some (.decimal r), by simp [evalBinOp, Datum.asNum, ArithOp.evalNum, hr], rfl⟩
      · refine .inr ⟨by simp [evalBinOp, Datum.asNum, ArithOp.evalNum, hr], rfl, ?_⟩
        simp only [Datum.isZero, beq_iff_eq]
        exact_mod_cast hy
    · rcases evalDec_ok_or_zero hop p q with ⟨r, hr⟩ | ⟨hr, rfl, rfl⟩
      · exact .inl ⟨some (.decimal r), by simp [evalBinOp, Datum.asNum, ArithOp.evalNum, hr], rfl⟩
      · exact .inr ⟨by simp [evalBinOp, Datum.asNum, ArithOp.evalNum, hr], rfl, by simp [Datum.isZero]⟩
  | .cmp op, h =>
    simp only [BinOp.typeOf, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨hc, rfl⟩ := h
    obtain ⟨t, ht⟩ := CmpOp.exists_eval_eq_ok_iff (op := op).mpr ⟨τ₁, τ₂, hc, ha, hb⟩
    exact .inl ⟨t.toDatum, by simp [evalBinOp, ht], Truth.toDatum_hasType _⟩
  | .and, h =>
    match τ₁, τ₂, h with
    | .bool, .bool, h =>
    cases h
    obtain ⟨s, hs⟩ := Datum.exists_toTruth_eq_ok_iff.mpr ha
    obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hb
    exact .inl ⟨(s ⊓ t).toDatum, by simp [evalBinOp, hs, ht], Truth.toDatum_hasType _⟩
  | .or, h =>
    match τ₁, τ₂, h with
    | .bool, .bool, h =>
    cases h
    obtain ⟨s, hs⟩ := Datum.exists_toTruth_eq_ok_iff.mpr ha
    obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hb
    exact .inl ⟨(s ⊔ t).toDatum, by simp [evalBinOp, hs, ht], Truth.toDatum_hasType _⟩
  | .concat, h =>
    match τ₁, τ₂, h with
    | .text, .text, h =>
    cases h
    obtain ⟨x, hx⟩ := Datum.exists_asText_eq_ok_iff.mpr ha
    obtain ⟨y, hy⟩ := Datum.exists_asText_eq_ok_iff.mpr hb
    rcases x with _ | x <;> rcases y with _ | y
    case some.some =>
      refine .inl ⟨some (.text (concatText x y)), ?_, rfl⟩
      simp [evalBinOp, hx, hy, pure, Except.pure]
    all_goals exact .inl ⟨none, by simp [evalBinOp, hx, hy, pure, Except.pure], trivial⟩

namespace Expr

variable {n m : ℕ}

/-! ### Expressions -/

/-- The datum can be compared with a value of type `τ`: it is `NULL` or of a comparable type. -/
def _root_.SqlCore.Datum.comparableWith (τ : SqlType) : Datum → Bool
  | none => true
  | some v => decide (τ.Comparable v.type)

/-- The type of an expression over the typing context `Γ`, if it is well-typed. -/
def typeOf (Γ : Fin n → SqlType) : Expr n → Option SqlType
  | lit v => some v.type
  | null τ => some τ
  | col i => some (Γ i)
  | unary op e => do op.typeOf (← e.typeOf Γ)
  | binary op e₁ e₂ => do op.typeOf (← e₁.typeOf Γ) (← e₂.typeOf Γ)
  | inList e vs => do
    let τ ← e.typeOf Γ
    if vs.all fun v => v.comparableWith τ then some .bool else none
  | caseWhen c a b => do
    let τ ← a.typeOf Γ
    if c.typeOf Γ = some .bool ∧ b.typeOf Γ = some τ then some τ else none

/-- The expression is a numeric literal other than `0`. -/
def isNonzeroIntLit : Expr n → Bool
  | lit (.int z) => z != 0
  | lit (.decimal q) => q != 0
  | _ => false

/-- Every division and remainder in the expression is by a nonzero numeric literal. -/
def divSafe : Expr n → Bool
  | lit _ => true
  | null _ => true
  | col _ => true
  | unary _ e => e.divSafe
  | binary op e₁ e₂ => (!op.isDivision || e₂.isNonzeroIntLit) && e₁.divSafe && e₂.divSafe
  | inList e _ => e.divSafe
  | caseWhen c a b => c.divSafe && a.divSafe && b.divSafe

/-- The expression is well-typed in `Γ` and every division is by a nonzero literal; then it
succeeds on every row conforming to `Γ` (`Expr.IsSafe.exists_eval_eq_ok`). -/
def IsSafe (Γ : Fin n → SqlType) (e : Expr n) : Prop :=
  (e.typeOf Γ).isSome ∧ e.divSafe

instance (Γ : Fin n → SqlType) (e : Expr n) : Decidable (e.IsSafe Γ) :=
  inferInstanceAs (Decidable ((e.typeOf Γ).isSome ∧ e.divSafe))

/-- The expression is a safe boolean predicate in `Γ`; then a `WHERE` or `ON` clause using it
never fails on a row conforming to `Γ` (`Expr.IsSafePredicate.exists_evalTruth_eq_ok`). -/
def IsSafePredicate (Γ : Fin n → SqlType) (e : Expr n) : Prop :=
  e.typeOf Γ = some .bool ∧ e.divSafe

instance (Γ : Fin n → SqlType) (e : Expr n) : Decidable (e.IsSafePredicate Γ) :=
  inferInstanceAs (Decidable (e.typeOf Γ = some .bool ∧ e.divSafe))

private theorem isZero_of_eval_of_isNonzeroIntLit {e : Expr n} (he : e.isNonzeroIntLit)
    (r : Row n) {b : Datum} (hb : e.eval r = .ok b) : b.isZero = false := by
  match e, he with
  | lit (.int z), he =>
    cases hb
    simpa [isNonzeroIntLit, Datum.isZero] using he
  | lit (.decimal q), he =>
    cases hb
    simpa [isNonzeroIntLit, Datum.isZero] using he

/-- Type soundness: on a row conforming to `Γ`, an expression of type `τ` returns `NULL` or a
value of type `τ`, or divides by zero, which requires a division that is not `divSafe`. -/
theorem eval_ok_or_divisionByZero {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {e : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ) :
    (∃ d, e.eval r = .ok d ∧ d.HasType τ) ∨
      (e.eval r = .error .divisionByZero ∧ e.divSafe = false) := by
  induction e generalizing τ with
  | lit v => cases he; exact .inl ⟨_, rfl, rfl⟩
  | null σ => cases he; exact .inl ⟨_, rfl, trivial⟩
  | col i => cases he; exact .inl ⟨_, rfl, hr i⟩
  | unary op e ih =>
    obtain ⟨τ₀, h₀, hop⟩ := Option.bind_eq_some_iff.mp he
    rcases ih h₀ with ⟨d, hd, hdτ⟩ | ⟨hd, hs⟩
    · obtain ⟨d', hd', hd'τ⟩ := evalUnOp_ok_of_typeOf hop hdτ
      exact .inl ⟨d', by simp [eval_unary, hd, hd'], hd'τ⟩
    · exact .inr ⟨by simp [eval_unary, hd], by simp [divSafe, hs]⟩
  | binary op e₁ e₂ ih₁ ih₂ =>
    obtain ⟨τ₁, h₁, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨τ₂, h₂, hop⟩ := Option.bind_eq_some_iff.mp he
    rcases ih₁ h₁ with ⟨a, ha, haτ⟩ | ⟨ha, hs⟩
    · rcases ih₂ h₂ with ⟨b, hb, hbτ⟩ | ⟨hb, hs⟩
      · rcases evalBinOp_ok_or_divisionByZero hop haτ hbτ with ⟨d, hd, hdτ⟩ | ⟨hd, hdiv, hzero⟩
        · exact .inl ⟨d, by simp [eval_binary, ha, hb, hd], hdτ⟩
        · refine .inr ⟨by simp [eval_binary, ha, hb, hd], ?_⟩
          have hlit : e₂.isNonzeroIntLit = false := by
            by_contra hlit
            have := isZero_of_eval_of_isNonzeroIntLit (Bool.eq_true_of_not_eq_false hlit) r hb
            simp [this] at hzero
          simp [divSafe, hdiv, hlit]
      · exact .inr ⟨by simp [eval_binary, ha, hb], by simp [divSafe, hs]⟩
    · exact .inr ⟨by simp [eval_binary, ha], by simp [divSafe, hs]⟩
  | inList e vs ih =>
    obtain ⟨τ₀, h₀, hvs⟩ := Option.bind_eq_some_iff.mp he
    split_ifs at hvs with hall
    cases hvs
    rcases ih h₀ with ⟨d, hd, hdτ⟩ | ⟨hd, hs⟩
    · have hall : ∀ v ∈ vs, v.comparableWith τ₀ := by simpa using hall
      obtain ⟨t, ht⟩ : ∃ t, d.inList vs = .ok t := by
        refine Datum.exists_inList_eq_ok_iff.mpr fun v hv => CmpOp.exists_eval_eq_ok_iff.mpr ?_
        have hc := hall v hv
        match v, hc with
        | none, _ => exact ⟨τ₀, τ₀, .refl _, hdτ, trivial⟩
        | some w, hc => exact ⟨τ₀, w.type, by simpa [Datum.comparableWith] using hc, hdτ, rfl⟩
      exact .inl ⟨_, by simp [eval_inList, hd, ht], Truth.toDatum_hasType t⟩
    · exact .inr ⟨by simp [eval_inList, hd], by simp [divSafe, hs]⟩
  | caseWhen c a b ihc iha ihb =>
    obtain ⟨τ₀, ha, hcb⟩ := Option.bind_eq_some_iff.mp he
    split_ifs at hcb with hcond
    cases hcb
    obtain ⟨hc, hb⟩ := hcond
    rcases ihc hc with ⟨d, hd, hdτ⟩ | ⟨hd, hs⟩
    · obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hdτ
      have hct : c.evalTruth r = .ok t := by simp [evalTruth, hd, ht]
      by_cases htt : t = .true
      · rw [eval_caseWhen_of_true r (htt ▸ hct)]
        rcases iha ha with h | ⟨hd', hs⟩
        · exact .inl h
        · exact .inr ⟨hd', by simp [divSafe, hs]⟩
      · rw [eval_caseWhen_of_ne_true r hct htt]
        rcases ihb hb with h | ⟨hd', hs⟩
        · exact .inl h
        · exact .inr ⟨hd', by simp [divSafe, hs]⟩
    · exact .inr ⟨by simp [eval_caseWhen, hd], by simp [divSafe, hs]⟩

/-- A well-typed expression never raises a type error on a conforming row. -/
theorem eval_ne_typeMismatch {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {e : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ) : e.eval r ≠ .error .typeMismatch := by
  rcases eval_ok_or_divisionByZero hr he with ⟨d, hd, -⟩ | ⟨hd, -⟩ <;> simp [hd]

/-- The result of a well-typed expression on a conforming row has the expression's type. -/
theorem hasType_of_eval_eq_ok {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {e : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ) {d : Datum} (h : e.eval r = .ok d) :
    d.HasType τ := by
  rcases eval_ok_or_divisionByZero hr he with ⟨d', hd', hd'τ⟩ | ⟨hd', -⟩
  · rw [h, Except.ok.injEq] at hd'
    exact hd' ▸ hd'τ
  · simp [h] at hd'

/-- A well-typed `divSafe` expression succeeds on a conforming row, with a result of its type. -/
theorem exists_eval_eq_ok_of_divSafe {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {e : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ) (hs : e.divSafe) :
    ∃ d, e.eval r = .ok d ∧ d.HasType τ := by
  rcases eval_ok_or_divisionByZero hr he with h | ⟨-, h⟩
  · exact h
  · simp [hs] at h

/-- A safe expression succeeds on every conforming row. -/
theorem IsSafe.exists_eval_eq_ok {Γ : Fin n → SqlType} {e : Expr n} (hs : e.IsSafe Γ)
    {r : Row n} (hr : r.Conforms Γ) : ∃ d, e.eval r = .ok d := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs.1
  obtain ⟨d, hd, -⟩ := exists_eval_eq_ok_of_divSafe hr hτ hs.2
  exact ⟨d, hd⟩

theorem IsSafePredicate.isSafe {Γ : Fin n → SqlType} {e : Expr n} (h : e.IsSafePredicate Γ) :
    e.IsSafe Γ :=
  ⟨by simp [h.1], h.2⟩

/-- A safe predicate never fails on a conforming row, so a `WHERE` or `ON` clause using it is
total. -/
theorem IsSafePredicate.exists_evalTruth_eq_ok {Γ : Fin n → SqlType} {e : Expr n}
    (h : e.IsSafePredicate Γ) {r : Row n} (hr : r.Conforms Γ) : ∃ t, e.evalTruth r = .ok t := by
  obtain ⟨d, hd, hdτ⟩ := exists_eval_eq_ok_of_divSafe hr h.1 h.2
  obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hdτ
  exact ⟨t, by simp [evalTruth, hd, ht]⟩

/-! ### Renaming and substitution -/

theorem typeOf_rename (ρ : Fin n → Fin m) (Γ : Fin m → SqlType) (e : Expr n) :
    (e.rename ρ).typeOf Γ = e.typeOf (Γ ∘ ρ) := by
  induction e <;> simp_all [rename, typeOf]

/-- Substituting expressions of the column types preserves the type. -/
theorem typeOf_subst {σ : Fin n → Expr m} {Γ : Fin n → SqlType} {Δ : Fin m → SqlType}
    (hσ : ∀ i, (σ i).typeOf Δ = some (Γ i)) (e : Expr n) : (e.subst σ).typeOf Δ = e.typeOf Γ := by
  induction e <;> simp_all [subst, typeOf]

@[simp] theorem divSafe_rename (ρ : Fin n → Fin m) (e : Expr n) :
    (e.rename ρ).divSafe = e.divSafe := by
  have hlit : ∀ e : Expr n, (e.rename ρ).isNonzeroIntLit = e.isNonzeroIntLit := by
    intro e
    cases e with
    | lit v => cases v <;> rfl
    | _ => rfl
  induction e <;> simp_all [rename, divSafe]

/-- Substituting `divSafe` expressions into a `divSafe` expression keeps it `divSafe`. -/
theorem divSafe_subst {σ : Fin n → Expr m} (hσ : ∀ i, (σ i).divSafe) {e : Expr n}
    (he : e.divSafe) : (e.subst σ).divSafe := by
  have hlit : ∀ e : Expr n, e.isNonzeroIntLit → (e.subst σ).isNonzeroIntLit := by
    intro e h
    match e, h with
    | lit (.int _), h => exact h
    | lit (.decimal _), h => exact h
  induction e with
  | lit | null | col => simp_all [subst, divSafe]
  | unary op e ih => simp_all [subst, divSafe]
  | binary op e₁ e₂ ih₁ ih₂ =>
    simp only [divSafe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at he
    obtain ⟨⟨hdiv, h₁⟩, h₂⟩ := he
    simp only [subst, divSafe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, ih₁ h₁, ih₂ h₂, and_true]
    exact hdiv.imp_right (hlit e₂)
  | inList e vs ih => simp_all [subst, divSafe]
  | caseWhen c a b ihc iha ihb => simp_all [subst, divSafe]

theorem IsSafe.rename {Γ : Fin m → SqlType} {e : Expr n} (ρ : Fin n → Fin m)
    (h : e.IsSafe (Γ ∘ ρ)) : (e.rename ρ).IsSafe Γ := by
  simpa [IsSafe, typeOf_rename] using h

theorem IsSafePredicate.rename {Γ : Fin m → SqlType} {e : Expr n} (ρ : Fin n → Fin m)
    (h : e.IsSafePredicate (Γ ∘ ρ)) : (e.rename ρ).IsSafePredicate Γ := by
  simpa [IsSafePredicate, typeOf_rename] using h

/-- Substituting safe expressions of the column types into a safe expression keeps it safe. -/
theorem IsSafe.subst {σ : Fin n → Expr m} {Γ : Fin n → SqlType} {Δ : Fin m → SqlType}
    (hσ : ∀ i, (σ i).typeOf Δ = some (Γ i)) (hσs : ∀ i, (σ i).divSafe) {e : Expr n}
    (h : e.IsSafe Γ) : (e.subst σ).IsSafe Δ :=
  ⟨by rw [typeOf_subst hσ]; exact h.1, divSafe_subst hσs h.2⟩

end Expr

end SqlCore
