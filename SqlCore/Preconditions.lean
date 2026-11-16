/-
Copyright (c) 2026 Evelyn Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell
-/
module

public import SqlCore.Typing

/-!
# Typed counterparts of `SqlEquiv`'s rewrite preconditions (#292)

`SqlEquiv/Equiv/Defs.lean` states the side conditions of its rewrite laws semantically: over all
databases and rows, the expression evaluates to a value of some shape. In the typed core the
quantification is over rows conforming to a typing context `Γ`, and most conditions become
decidable checks:

| `SqlEquiv` | Typed counterpart | Decidable |
|---|---|---|
| `Expr.evaluable` (never an error) | `Expr.IsSafe Γ` | yes |
| `Expr.isStringOrNull` (text or NULL, never an error) | `Expr.IsSafeText Γ` | yes |
| `Expr.isStringOrNullValued`, `isStringOrUntypedNullValued` (text, NULL or an error) | `Expr.IsText Γ` | yes |
| `Expr.isBoolValued` (a boolean, never NULL) | `Expr.IsTwoValued Γ` | no: nullability is not typed |

The untyped-NULL distinction of `isStringOrUntypedNullValued` disappears: `NULL` carries no type.
`IsTwoValued` stays semantic because the typing does not track nullability. In Kleene logic most
boolean laws (`NOT NOT`, `AND TRUE`, De Morgan) already hold for `unknown`, so they need only
`IsSafePredicate`; only laws such as excluded middle need `IsTwoValued`.

The laws using these conditions come in phase 5 (#294).
-/

@[expose] public section

namespace SqlCore.Expr

variable {n : ℕ}

/-- The expression is text-typed (`isStringOrNullValued`): on a conforming row it returns text,
`NULL`, or an error. -/
def IsText (Γ : Fin n → SqlType) (e : Expr n) : Prop := e.typeOf Γ = some .text

instance (Γ : Fin n → SqlType) (e : Expr n) : Decidable (e.IsText Γ) :=
  inferInstanceAs (Decidable (_ = _))

/-- The expression is a safe text expression (`isStringOrNull`): on a conforming row it returns
text or `NULL`, never an error. -/
def IsSafeText (Γ : Fin n → SqlType) (e : Expr n) : Prop := e.IsText Γ ∧ e.divSafe

instance (Γ : Fin n → SqlType) (e : Expr n) : Decidable (e.IsSafeText Γ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The expression is two-valued (`isBoolValued`): on every conforming row it returns `TRUE` or
`FALSE`, never `NULL` or an error. -/
def IsTwoValued (Γ : Fin n → SqlType) (e : Expr n) : Prop :=
  ∀ r : Row n, r.Conforms Γ → ∃ b : Bool, e.eval r = .ok (some (.bool b))

private theorem text_cases {d : Datum} (h : d.HasType .text) : d = none ∨ ∃ s, d = some (.text s) := by
  rcases d with _ | (_ | s | _ | _) <;> simp_all

/-- A text-typed expression returns text or `NULL` when it succeeds. -/
theorem IsText.eval_eq_ok {Γ : Fin n → SqlType} {e : Expr n} (h : e.IsText Γ) {r : Row n}
    (hr : r.Conforms Γ) {d : Datum} (hd : e.eval r = .ok d) : d = none ∨ ∃ s, d = some (.text s) :=
  text_cases (hasType_of_eval_eq_ok hr h hd)

/-- A safe text expression succeeds, with text or `NULL`. -/
theorem IsSafeText.exists_eval_eq_ok {Γ : Fin n → SqlType} {e : Expr n} (h : e.IsSafeText Γ)
    {r : Row n} (hr : r.Conforms Γ) :
    ∃ d, e.eval r = .ok d ∧ (d = none ∨ ∃ s, d = some (.text s)) := by
  obtain ⟨d, hd, hdτ⟩ := exists_eval_eq_ok_of_divSafe hr h.1 h.2
  exact ⟨d, hd, text_cases hdτ⟩

theorem IsSafeText.isSafe {Γ : Fin n → SqlType} {e : Expr n} (h : e.IsSafeText Γ) :
    e.IsSafe Γ := ⟨by rw [(h.1 : e.typeOf Γ = some .text)]; rfl, h.2⟩

/-- A two-valued expression's truth value is never `unknown`. -/
theorem IsTwoValued.evalTruth {Γ : Fin n → SqlType} {e : Expr n} (h : e.IsTwoValued Γ)
    {r : Row n} (hr : r.Conforms Γ) : ∃ b : Bool, e.evalTruth r = .ok (Truth.ofBool b) := by
  obtain ⟨b, hb⟩ := h r hr
  exact ⟨b, by simp [Expr.evalTruth, hb, Datum.toTruth]⟩

/-- A boolean literal is two-valued. -/
theorem isTwoValued_lit_bool (Γ : Fin n → SqlType) (b : Bool) :
    (lit (.bool b) : Expr n).IsTwoValued Γ := fun _ _ => ⟨b, rfl⟩

end SqlCore.Expr
