/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/
module

public import Mathlib.Algebra.Order.Ring.Rat

/-!
# Values and `NULL` (typed core, phase 1, #290)

A `Value` is a non-null SQL value of one column type (`SqlType`). A table cell holds a `Datum`,
which is `Option Value`: `none` is `NULL`, and `NULL` has every type (`Datum.HasType`).

Re-derived from cslib-frontier's `Languages/SQL/Value.lean` (pinned `e78796a1`, by Evelyn
Mitchell and Samuel Schlesinger), which redesigned `SqlEquiv.Value`. The differences from
`SqlEquiv` are:

* `NULL` is not a value constructor. In `SqlEquiv`, `Value.null` carries an optional type and
  `none : Option Value` means an evaluation error; here `none` is `NULL`, and errors are a
  separate type (`SqlCore.EvalError`, in `SqlCore.Scalar`).
* Integers are unbounded `ℤ`, and text is a Lean `String`, as in `SqlEquiv`.
* An exact decimal is a rational `ℚ` (decision 4, #290 part 2). `SqlEquiv` stores a canonical
  scaled integer (`Value.mkDecimal`); with `ℚ`, `2.50` and `2.5` are equal by construction and
  the order is Mathlib's. Values built from SQL literals by `+ - * %` are decimal fractions; a
  `decimal` whose denominator is not a power-of-ten divisor is representable but never produced.
* `int` and `decimal` are the numeric types (`SqlType.isNumeric`); comparisons and arithmetic
  promote `int` to `decimal` (decision 6), so two types can be `SqlType.Comparable` without being
  equal.
-/

@[expose] public section

namespace SqlCore

/-- The column types. -/
inductive SqlType where
  /-- Unbounded integers. -/
  | int
  /-- Character strings, compared by code point. -/
  | text
  /-- Booleans. -/
  | bool
  /-- Exact decimals. -/
  | decimal
  deriving DecidableEq, Repr, Inhabited

namespace SqlType

/-- The numeric types, between which comparison and arithmetic promote. -/
def isNumeric : SqlType → Bool
  | int | decimal => true
  | text | bool => false

/-- Two types whose values can be compared: the same type, or two numeric types. -/
def Comparable (τ σ : SqlType) : Prop := τ = σ ∨ (τ.isNumeric ∧ σ.isNumeric)

instance (τ σ : SqlType) : Decidable (Comparable τ σ) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem Comparable.refl (τ : SqlType) : Comparable τ τ := .inl rfl

theorem Comparable.symm {τ σ : SqlType} (h : Comparable τ σ) : Comparable σ τ :=
  h.imp Eq.symm And.symm

end SqlType

/-- A non-null SQL value. -/
inductive Value where
  /-- An integer. -/
  | int (z : ℤ)
  /-- A character string. -/
  | text (s : String)
  /-- A boolean. -/
  | bool (b : Bool)
  /-- An exact decimal. -/
  | decimal (q : ℚ)
  deriving DecidableEq, Repr, Inhabited

namespace Value

/-- The type of a value. -/
def type : Value → SqlType
  | int _ => .int
  | text _ => .text
  | bool _ => .bool
  | decimal _ => .decimal

@[simp] theorem type_int (z : ℤ) : (int z).type = .int := rfl
@[simp] theorem type_text (s : String) : (text s).type = .text := rfl
@[simp] theorem type_bool (b : Bool) : (bool b).type = .bool := rfl
@[simp] theorem type_decimal (q : ℚ) : (decimal q).type = .decimal := rfl

theorem type_eq_int_iff {v : Value} : v.type = .int ↔ ∃ z, v = int z := by
  cases v <;> simp [type]

theorem type_eq_text_iff {v : Value} : v.type = .text ↔ ∃ s, v = text s := by
  cases v <;> simp [type]

theorem type_eq_bool_iff {v : Value} : v.type = .bool ↔ ∃ b, v = bool b := by
  cases v <;> simp [type]

theorem type_eq_decimal_iff {v : Value} : v.type = .decimal ↔ ∃ q, v = decimal q := by
  cases v <;> simp [type]

end Value

/-- A cell: a value, or `none` for `NULL`. An `abbrev`, so `Option`'s instances and lemmas apply
directly. Evaluation returns `Except EvalError Datum`, keeping a `NULL` result apart from a
failure. -/
abbrev Datum := Option Value

namespace Datum

/-- `d.HasType τ`: `d` is `NULL` or a value of type `τ`. -/
def HasType : Datum → SqlType → Prop
  | none, _ => True
  | some v, τ => v.type = τ

instance decidableHasType : ∀ (d : Datum) (τ : SqlType), Decidable (d.HasType τ)
  | none, _ => isTrue trivial
  | some v, τ => inferInstanceAs (Decidable (v.type = τ))

@[simp] theorem hasType_none (τ : SqlType) : HasType none τ := trivial

@[simp] theorem hasType_some {v : Value} {τ : SqlType} : HasType (some v) τ ↔ v.type = τ :=
  Iff.rfl

/-- `NULL` aside, a datum has one type. -/
theorem HasType.unique {d : Datum} {τ τ' : SqlType} (h : d.HasType τ) (h' : d.HasType τ')
    (hd : d ≠ none) : τ = τ' := by
  cases d with
  | none => exact absurd rfl hd
  | some v => exact h.symm.trans h'

end Datum

end SqlCore
