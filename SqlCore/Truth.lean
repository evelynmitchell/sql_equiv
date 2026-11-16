/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/
module

public import Mathlib.Order.Hom.Basic

/-!
# Three-valued logic (typed core, phase 1, #290)

SQL's truth values are ordered `false < unknown < true`. With that order `AND` is `⊓`, `OR` is `⊔`,
and `NOT` (`Truth.not`) reverses the order and fixes `unknown`: Kleene's strong three-valued logic.
A `WHERE` or `ON` clause keeps a row exactly when its predicate is `true` (`Truth.isTrue`).

`Truth` is a `LinearOrder` (transported from `ℕ` along `rank`) and a `BoundedOrder`, so Mathlib's
lattice lemmas (`inf_comm`, `sup_assoc`, `inf_sup_left`, …) apply to `AND` and `OR` as they are.
`min` and `max` are truth tables, so `decide` evaluates them in the kernel.

`NOT` is deliberately not a `Compl` instance: excluded middle fails (`unknown_sup_not_unknown`), and
the Heyting complement of this chain sends `unknown` to `false`, which is not SQL's `NOT`.

Re-derived from cslib-frontier's `Languages/SQL/Truth.lean` (pinned `e78796a1`). It replaces
`SqlEquiv.Trilean`, whose connectives are separate truth tables.
-/

@[expose] public section

namespace SqlCore

/-- SQL's truth values; `unknown` is the value of a comparison with `NULL`. -/
inductive Truth where
  | false
  | unknown
  | true
  deriving DecidableEq, Repr, Inhabited

namespace Truth

/-- Position in the chain `false < unknown < true`. -/
def rank : Truth → ℕ
  | false => 0
  | unknown => 1
  | true => 2

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- `AND`: the minimum. -/
instance : Min Truth where
  min
    | false, _ => false
    | _, false => false
    | unknown, _ => unknown
    | _, unknown => unknown
    | true, true => true

/-- `OR`: the maximum. -/
instance : Max Truth where
  max
    | true, _ => true
    | _, true => true
    | unknown, _ => unknown
    | _, unknown => unknown
    | false, false => false

instance : LinearOrder Truth :=
  LinearOrder.lift rank rank_injective
    (fun a b => by cases a <;> cases b <;> rfl) (fun a b => by cases a <;> cases b <;> rfl)

instance : BoundedOrder Truth where
  top := true
  le_top a := by cases a <;> decide
  bot := false
  bot_le a := by cases a <;> decide

@[simp] theorem top_eq : (⊤ : Truth) = true := rfl
@[simp] theorem bot_eq : (⊥ : Truth) = false := rfl

theorem le_iff_rank_le {a b : Truth} : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

@[simp] theorem sup_false (a : Truth) : a ⊔ false = a := sup_bot_eq a
@[simp] theorem false_sup (a : Truth) : false ⊔ a = a := bot_sup_eq a
@[simp] theorem sup_true (a : Truth) : a ⊔ true = true := sup_top_eq a
@[simp] theorem true_sup (a : Truth) : true ⊔ a = true := top_sup_eq a
@[simp] theorem inf_true (a : Truth) : a ⊓ true = a := inf_top_eq a
@[simp] theorem true_inf (a : Truth) : true ⊓ a = a := top_inf_eq a
@[simp] theorem inf_false (a : Truth) : a ⊓ false = false := inf_bot_eq a
@[simp] theorem false_inf (a : Truth) : false ⊓ a = false := bot_inf_eq a

theorem sup_eq_true_iff {a b : Truth} : a ⊔ b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem sup_eq_false_iff {a b : Truth} : a ⊔ b = false ↔ a = false ∧ b = false := by
  cases a <;> cases b <;> decide

theorem inf_eq_true_iff {a b : Truth} : a ⊓ b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem inf_eq_false_iff {a b : Truth} : a ⊓ b = false ↔ a = false ∨ b = false := by
  cases a <;> cases b <;> decide

/-- `NOT`: swaps `false` and `true`, fixes `unknown`. -/
def not : Truth → Truth
  | false => true
  | unknown => unknown
  | true => false

@[simp] theorem not_false : not false = true := rfl
@[simp] theorem not_unknown : not unknown = unknown := rfl
@[simp] theorem not_true : not true = false := rfl

@[simp] theorem not_not (a : Truth) : not (not a) = a := by cases a <;> rfl

theorem not_injective : Function.Injective not := Function.LeftInverse.injective not_not

@[simp] theorem not_le_not {a b : Truth} : not a ≤ not b ↔ b ≤ a := by
  cases a <;> cases b <;> decide

/-- `NOT` is an order isomorphism onto the dual order. -/
def notOrderIso : Truth ≃o Truthᵒᵈ where
  toFun a := OrderDual.toDual (not a)
  invFun a := not (OrderDual.ofDual a)
  left_inv := not_not
  right_inv := not_not
  map_rel_iff' := not_le_not

theorem not_antitone : Antitone not := fun _ _ h => not_le_not.mpr h

/-- De Morgan. -/
@[simp] theorem not_inf (a b : Truth) : not (a ⊓ b) = not a ⊔ not b := by
  cases a <;> cases b <;> rfl

/-- De Morgan. -/
@[simp] theorem not_sup (a b : Truth) : not (a ⊔ b) = not a ⊓ not b := by
  cases a <;> cases b <;> rfl

/-- Kleene's law. -/
theorem inf_not_le_sup_not (a b : Truth) : a ⊓ not a ≤ b ⊔ not b := by
  cases a <;> cases b <;> decide

/-- Excluded middle fails. -/
theorem unknown_sup_not_unknown : unknown ⊔ not unknown = unknown := rfl

/-- Non-contradiction fails. -/
theorem unknown_inf_not_unknown : unknown ⊓ not unknown = unknown := rfl

/-- A known Boolean as a truth value. -/
def ofBool : Bool → Truth
  | .false => false
  | .true => true

@[simp] theorem ofBool_true : ofBool .true = true := rfl
@[simp] theorem ofBool_false : ofBool .false = false := rfl

@[simp] theorem ofBool_ne_unknown (b : Bool) : ofBool b ≠ unknown := by cases b <;> decide

theorem ofBool_injective : Function.Injective ofBool := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[simp] theorem ofBool_inj {a b : Bool} : ofBool a = ofBool b ↔ a = b := ofBool_injective.eq_iff

@[simp] theorem ofBool_and (a b : Bool) : ofBool (a && b) = ofBool a ⊓ ofBool b := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBool_or (a b : Bool) : ofBool (a || b) = ofBool a ⊔ ofBool b := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBool_not (a : Bool) : ofBool (!a) = not (ofBool a) := by cases a <;> rfl

/-- The `WHERE` test: only `true` keeps a row. -/
def isTrue : Truth → Bool
  | true => .true
  | _ => .false

@[simp] theorem isTrue_iff {a : Truth} : a.isTrue = .true ↔ a = true := by
  cases a <;> simp [isTrue]

@[simp] theorem isTrue_ofBool (b : Bool) : (ofBool b).isTrue = b := by cases b <;> rfl

@[simp] theorem isTrue_inf (a b : Truth) : (a ⊓ b).isTrue = (a.isTrue && b.isTrue) := by
  cases a <;> cases b <;> rfl

@[simp] theorem isTrue_sup (a b : Truth) : (a ⊔ b).isTrue = (a.isTrue || b.isTrue) := by
  cases a <;> cases b <;> rfl

/-- `NOT a` holds exactly when `a` is `false`: an `unknown` predicate and its negation both drop
the row. -/
@[simp] theorem not_eq_true_iff {a : Truth} : not a = true ↔ a = false := by cases a <;> decide

@[simp] theorem not_eq_false_iff {a : Truth} : not a = false ↔ a = true := by cases a <;> decide

end Truth

end SqlCore
