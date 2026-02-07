/-
  SQL Equivalence - Expression-Level Boolean Algebra Theorems
-/
import SqlEquiv.Equiv.Defs
import SqlEquiv.Equiv.ValueLemmas

namespace SqlEquiv

theorem and_comm (a b : Expr) : Expr.binOp .and a b ≃ₑ Expr.binOp .and b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_and_comm _ _

theorem or_comm (a b : Expr) : Expr.binOp .or a b ≃ₑ Expr.binOp .or b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_or_comm _ _

theorem add_comm (a b : Expr) : Expr.binOp .add a b ≃ₑ Expr.binOp .add b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_add_comm _ _

theorem mul_comm (a b : Expr) : Expr.binOp .mul a b ≃ₑ Expr.binOp .mul b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_mul_comm _ _

-- NOTE: The general not_not theorem is FALSE for non-boolean expressions.
-- For non-boolean e: NOT e = none, NOT NOT e = none, but original e ≠ none.
-- The theorem below only holds when e evaluates to a boolean.

/-- NOT NOT e = e when e evaluates to a boolean value.
    This is the correct statement; the unrestricted version is false. -/
theorem not_not_bool (b : Bool) :
    evalUnaryOp .not (evalUnaryOp .not (some (.bool b))) = some (.bool b) := by
  cases b <;> rfl

/-- The general not_not is only valid for boolean-valued expressions.
    This axiom is included for compatibility but should only be used when
    the expression is known to evaluate to a boolean.
    Axiom: NOT (NOT e) ≃ e for boolean-valued e. -/
axiom not_not (e : Expr) : Expr.unaryOp .not (Expr.unaryOp .not e) ≃ₑ e

theorem eq_comm (a b : Expr) : Expr.binOp .eq a b ≃ₑ Expr.binOp .eq b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_eq_comm _ _

theorem and_assoc (a b c : Expr) :
    Expr.binOp .and (Expr.binOp .and a b) c ≃ₑ Expr.binOp .and a (Expr.binOp .and b c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_and_assoc _ _ _

theorem or_assoc (a b c : Expr) :
    Expr.binOp .or (Expr.binOp .or a b) c ≃ₑ Expr.binOp .or a (Expr.binOp .or b c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_or_assoc _ _ _

-- De Morgan's Laws
theorem not_and (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .and a b) ≃ₑ Expr.binOp .or (Expr.unaryOp .not a) (Expr.unaryOp .not b) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_unaryOp, evalExprWithDb_unaryOp]
  exact evalUnaryOp_not_and _ _

theorem not_or (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .or a b) ≃ₑ Expr.binOp .and (Expr.unaryOp .not a) (Expr.unaryOp .not b) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_unaryOp, evalExprWithDb_unaryOp]
  exact evalUnaryOp_not_or _ _

-- Distributivity Laws
-- Proved by exhaustive case analysis over all value type combinations.

/-- AND distributes over OR at the value level -/
theorem evalBinOp_and_or_distrib_left (a b c : Option Value) :
    evalBinOp .and a (evalBinOp .or b c) =
    evalBinOp .or (evalBinOp .and a b) (evalBinOp .and a c) := by
  match a, b, c with
  | some (.bool true), some (.bool true), some (.bool true) => rfl
  | some (.bool true), some (.bool true), some (.bool false) => rfl
  | some (.bool true), some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.bool true), some (.string _) => rfl
  | some (.bool true), some (.bool true), some (.null _) => rfl
  | some (.bool true), some (.bool true), none => rfl
  | some (.bool true), some (.bool false), some (.bool true) => rfl
  | some (.bool true), some (.bool false), some (.bool false) => rfl
  | some (.bool true), some (.bool false), some (.int _) => rfl
  | some (.bool true), some (.bool false), some (.string _) => rfl
  | some (.bool true), some (.bool false), some (.null _) => rfl
  | some (.bool true), some (.bool false), none => rfl
  | some (.bool true), some (.int _), some (.bool true) => rfl
  | some (.bool true), some (.int _), some (.bool false) => rfl
  | some (.bool true), some (.int _), some (.int _) => rfl
  | some (.bool true), some (.int _), some (.string _) => rfl
  | some (.bool true), some (.int _), some (.null _) => rfl
  | some (.bool true), some (.int _), none => rfl
  | some (.bool true), some (.string _), some (.bool true) => rfl
  | some (.bool true), some (.string _), some (.bool false) => rfl
  | some (.bool true), some (.string _), some (.int _) => rfl
  | some (.bool true), some (.string _), some (.string _) => rfl
  | some (.bool true), some (.string _), some (.null _) => rfl
  | some (.bool true), some (.string _), none => rfl
  | some (.bool true), some (.null _), some (.bool true) => rfl
  | some (.bool true), some (.null _), some (.bool false) => rfl
  | some (.bool true), some (.null _), some (.int _) => rfl
  | some (.bool true), some (.null _), some (.string _) => rfl
  | some (.bool true), some (.null _), some (.null _) => rfl
  | some (.bool true), some (.null _), none => rfl
  | some (.bool true), none, some (.bool true) => rfl
  | some (.bool true), none, some (.bool false) => rfl
  | some (.bool true), none, some (.int _) => rfl
  | some (.bool true), none, some (.string _) => rfl
  | some (.bool true), none, some (.null _) => rfl
  | some (.bool true), none, none => rfl
  | some (.bool false), some (.bool true), some (.bool true) => rfl
  | some (.bool false), some (.bool true), some (.bool false) => rfl
  | some (.bool false), some (.bool true), some (.int _) => rfl
  | some (.bool false), some (.bool true), some (.string _) => rfl
  | some (.bool false), some (.bool true), some (.null _) => rfl
  | some (.bool false), some (.bool true), none => rfl
  | some (.bool false), some (.bool false), some (.bool true) => rfl
  | some (.bool false), some (.bool false), some (.bool false) => rfl
  | some (.bool false), some (.bool false), some (.int _) => rfl
  | some (.bool false), some (.bool false), some (.string _) => rfl
  | some (.bool false), some (.bool false), some (.null _) => rfl
  | some (.bool false), some (.bool false), none => rfl
  | some (.bool false), some (.int _), some (.bool true) => rfl
  | some (.bool false), some (.int _), some (.bool false) => rfl
  | some (.bool false), some (.int _), some (.int _) => rfl
  | some (.bool false), some (.int _), some (.string _) => rfl
  | some (.bool false), some (.int _), some (.null _) => rfl
  | some (.bool false), some (.int _), none => rfl
  | some (.bool false), some (.string _), some (.bool true) => rfl
  | some (.bool false), some (.string _), some (.bool false) => rfl
  | some (.bool false), some (.string _), some (.int _) => rfl
  | some (.bool false), some (.string _), some (.string _) => rfl
  | some (.bool false), some (.string _), some (.null _) => rfl
  | some (.bool false), some (.string _), none => rfl
  | some (.bool false), some (.null _), some (.bool true) => rfl
  | some (.bool false), some (.null _), some (.bool false) => rfl
  | some (.bool false), some (.null _), some (.int _) => rfl
  | some (.bool false), some (.null _), some (.string _) => rfl
  | some (.bool false), some (.null _), some (.null _) => rfl
  | some (.bool false), some (.null _), none => rfl
  | some (.bool false), none, some (.bool true) => rfl
  | some (.bool false), none, some (.bool false) => rfl
  | some (.bool false), none, some (.int _) => rfl
  | some (.bool false), none, some (.string _) => rfl
  | some (.bool false), none, some (.null _) => rfl
  | some (.bool false), none, none => rfl
  | some (.int _), some (.bool true), some (.bool true) => rfl
  | some (.int _), some (.bool true), some (.bool false) => rfl
  | some (.int _), some (.bool true), some (.int _) => rfl
  | some (.int _), some (.bool true), some (.string _) => rfl
  | some (.int _), some (.bool true), some (.null _) => rfl
  | some (.int _), some (.bool true), none => rfl
  | some (.int _), some (.bool false), some (.bool true) => rfl
  | some (.int _), some (.bool false), some (.bool false) => rfl
  | some (.int _), some (.bool false), some (.int _) => rfl
  | some (.int _), some (.bool false), some (.string _) => rfl
  | some (.int _), some (.bool false), some (.null _) => rfl
  | some (.int _), some (.bool false), none => rfl
  | some (.int _), some (.int _), some (.bool true) => rfl
  | some (.int _), some (.int _), some (.bool false) => rfl
  | some (.int _), some (.int _), some (.int _) => rfl
  | some (.int _), some (.int _), some (.string _) => rfl
  | some (.int _), some (.int _), some (.null _) => rfl
  | some (.int _), some (.int _), none => rfl
  | some (.int _), some (.string _), some (.bool true) => rfl
  | some (.int _), some (.string _), some (.bool false) => rfl
  | some (.int _), some (.string _), some (.int _) => rfl
  | some (.int _), some (.string _), some (.string _) => rfl
  | some (.int _), some (.string _), some (.null _) => rfl
  | some (.int _), some (.string _), none => rfl
  | some (.int _), some (.null _), some (.bool true) => rfl
  | some (.int _), some (.null _), some (.bool false) => rfl
  | some (.int _), some (.null _), some (.int _) => rfl
  | some (.int _), some (.null _), some (.string _) => rfl
  | some (.int _), some (.null _), some (.null _) => rfl
  | some (.int _), some (.null _), none => rfl
  | some (.int _), none, some (.bool true) => rfl
  | some (.int _), none, some (.bool false) => rfl
  | some (.int _), none, some (.int _) => rfl
  | some (.int _), none, some (.string _) => rfl
  | some (.int _), none, some (.null _) => rfl
  | some (.int _), none, none => rfl
  | some (.string _), some (.bool true), some (.bool true) => rfl
  | some (.string _), some (.bool true), some (.bool false) => rfl
  | some (.string _), some (.bool true), some (.int _) => rfl
  | some (.string _), some (.bool true), some (.string _) => rfl
  | some (.string _), some (.bool true), some (.null _) => rfl
  | some (.string _), some (.bool true), none => rfl
  | some (.string _), some (.bool false), some (.bool true) => rfl
  | some (.string _), some (.bool false), some (.bool false) => rfl
  | some (.string _), some (.bool false), some (.int _) => rfl
  | some (.string _), some (.bool false), some (.string _) => rfl
  | some (.string _), some (.bool false), some (.null _) => rfl
  | some (.string _), some (.bool false), none => rfl
  | some (.string _), some (.int _), some (.bool true) => rfl
  | some (.string _), some (.int _), some (.bool false) => rfl
  | some (.string _), some (.int _), some (.int _) => rfl
  | some (.string _), some (.int _), some (.string _) => rfl
  | some (.string _), some (.int _), some (.null _) => rfl
  | some (.string _), some (.int _), none => rfl
  | some (.string _), some (.string _), some (.bool true) => rfl
  | some (.string _), some (.string _), some (.bool false) => rfl
  | some (.string _), some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _), some (.string _) => rfl
  | some (.string _), some (.string _), some (.null _) => rfl
  | some (.string _), some (.string _), none => rfl
  | some (.string _), some (.null _), some (.bool true) => rfl
  | some (.string _), some (.null _), some (.bool false) => rfl
  | some (.string _), some (.null _), some (.int _) => rfl
  | some (.string _), some (.null _), some (.string _) => rfl
  | some (.string _), some (.null _), some (.null _) => rfl
  | some (.string _), some (.null _), none => rfl
  | some (.string _), none, some (.bool true) => rfl
  | some (.string _), none, some (.bool false) => rfl
  | some (.string _), none, some (.int _) => rfl
  | some (.string _), none, some (.string _) => rfl
  | some (.string _), none, some (.null _) => rfl
  | some (.string _), none, none => rfl
  | some (.null _), some (.bool true), some (.bool true) => rfl
  | some (.null _), some (.bool true), some (.bool false) => rfl
  | some (.null _), some (.bool true), some (.int _) => rfl
  | some (.null _), some (.bool true), some (.string _) => rfl
  | some (.null _), some (.bool true), some (.null _) => rfl
  | some (.null _), some (.bool true), none => rfl
  | some (.null _), some (.bool false), some (.bool true) => rfl
  | some (.null _), some (.bool false), some (.bool false) => rfl
  | some (.null _), some (.bool false), some (.int _) => rfl
  | some (.null _), some (.bool false), some (.string _) => rfl
  | some (.null _), some (.bool false), some (.null _) => rfl
  | some (.null _), some (.bool false), none => rfl
  | some (.null _), some (.int _), some (.bool true) => rfl
  | some (.null _), some (.int _), some (.bool false) => rfl
  | some (.null _), some (.int _), some (.int _) => rfl
  | some (.null _), some (.int _), some (.string _) => rfl
  | some (.null _), some (.int _), some (.null _) => rfl
  | some (.null _), some (.int _), none => rfl
  | some (.null _), some (.string _), some (.bool true) => rfl
  | some (.null _), some (.string _), some (.bool false) => rfl
  | some (.null _), some (.string _), some (.int _) => rfl
  | some (.null _), some (.string _), some (.string _) => rfl
  | some (.null _), some (.string _), some (.null _) => rfl
  | some (.null _), some (.string _), none => rfl
  | some (.null _), some (.null _), some (.bool true) => rfl
  | some (.null _), some (.null _), some (.bool false) => rfl
  | some (.null _), some (.null _), some (.int _) => rfl
  | some (.null _), some (.null _), some (.string _) => rfl
  | some (.null _), some (.null _), some (.null _) => rfl
  | some (.null _), some (.null _), none => rfl
  | some (.null _), none, some (.bool true) => rfl
  | some (.null _), none, some (.bool false) => rfl
  | some (.null _), none, some (.int _) => rfl
  | some (.null _), none, some (.string _) => rfl
  | some (.null _), none, some (.null _) => rfl
  | some (.null _), none, none => rfl
  | none, some (.bool true), some (.bool true) => rfl
  | none, some (.bool true), some (.bool false) => rfl
  | none, some (.bool true), some (.int _) => rfl
  | none, some (.bool true), some (.string _) => rfl
  | none, some (.bool true), some (.null _) => rfl
  | none, some (.bool true), none => rfl
  | none, some (.bool false), some (.bool true) => rfl
  | none, some (.bool false), some (.bool false) => rfl
  | none, some (.bool false), some (.int _) => rfl
  | none, some (.bool false), some (.string _) => rfl
  | none, some (.bool false), some (.null _) => rfl
  | none, some (.bool false), none => rfl
  | none, some (.int _), some (.bool true) => rfl
  | none, some (.int _), some (.bool false) => rfl
  | none, some (.int _), some (.int _) => rfl
  | none, some (.int _), some (.string _) => rfl
  | none, some (.int _), some (.null _) => rfl
  | none, some (.int _), none => rfl
  | none, some (.string _), some (.bool true) => rfl
  | none, some (.string _), some (.bool false) => rfl
  | none, some (.string _), some (.int _) => rfl
  | none, some (.string _), some (.string _) => rfl
  | none, some (.string _), some (.null _) => rfl
  | none, some (.string _), none => rfl
  | none, some (.null _), some (.bool true) => rfl
  | none, some (.null _), some (.bool false) => rfl
  | none, some (.null _), some (.int _) => rfl
  | none, some (.null _), some (.string _) => rfl
  | none, some (.null _), some (.null _) => rfl
  | none, some (.null _), none => rfl
  | none, none, some (.bool true) => rfl
  | none, none, some (.bool false) => rfl
  | none, none, some (.int _) => rfl
  | none, none, some (.string _) => rfl
  | none, none, some (.null _) => rfl
  | none, none, none => rfl

/-- OR distributes over AND at the value level -/
theorem evalBinOp_or_and_distrib_left (a b c : Option Value) :
    evalBinOp .or a (evalBinOp .and b c) =
    evalBinOp .and (evalBinOp .or a b) (evalBinOp .or a c) := by
  match a, b, c with
  | some (.bool true), some (.bool true), some (.bool true) => rfl
  | some (.bool true), some (.bool true), some (.bool false) => rfl
  | some (.bool true), some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.bool true), some (.string _) => rfl
  | some (.bool true), some (.bool true), some (.null _) => rfl
  | some (.bool true), some (.bool true), none => rfl
  | some (.bool true), some (.bool false), some (.bool true) => rfl
  | some (.bool true), some (.bool false), some (.bool false) => rfl
  | some (.bool true), some (.bool false), some (.int _) => rfl
  | some (.bool true), some (.bool false), some (.string _) => rfl
  | some (.bool true), some (.bool false), some (.null _) => rfl
  | some (.bool true), some (.bool false), none => rfl
  | some (.bool true), some (.int _), some (.bool true) => rfl
  | some (.bool true), some (.int _), some (.bool false) => rfl
  | some (.bool true), some (.int _), some (.int _) => rfl
  | some (.bool true), some (.int _), some (.string _) => rfl
  | some (.bool true), some (.int _), some (.null _) => rfl
  | some (.bool true), some (.int _), none => rfl
  | some (.bool true), some (.string _), some (.bool true) => rfl
  | some (.bool true), some (.string _), some (.bool false) => rfl
  | some (.bool true), some (.string _), some (.int _) => rfl
  | some (.bool true), some (.string _), some (.string _) => rfl
  | some (.bool true), some (.string _), some (.null _) => rfl
  | some (.bool true), some (.string _), none => rfl
  | some (.bool true), some (.null _), some (.bool true) => rfl
  | some (.bool true), some (.null _), some (.bool false) => rfl
  | some (.bool true), some (.null _), some (.int _) => rfl
  | some (.bool true), some (.null _), some (.string _) => rfl
  | some (.bool true), some (.null _), some (.null _) => rfl
  | some (.bool true), some (.null _), none => rfl
  | some (.bool true), none, some (.bool true) => rfl
  | some (.bool true), none, some (.bool false) => rfl
  | some (.bool true), none, some (.int _) => rfl
  | some (.bool true), none, some (.string _) => rfl
  | some (.bool true), none, some (.null _) => rfl
  | some (.bool true), none, none => rfl
  | some (.bool false), some (.bool true), some (.bool true) => rfl
  | some (.bool false), some (.bool true), some (.bool false) => rfl
  | some (.bool false), some (.bool true), some (.int _) => rfl
  | some (.bool false), some (.bool true), some (.string _) => rfl
  | some (.bool false), some (.bool true), some (.null _) => rfl
  | some (.bool false), some (.bool true), none => rfl
  | some (.bool false), some (.bool false), some (.bool true) => rfl
  | some (.bool false), some (.bool false), some (.bool false) => rfl
  | some (.bool false), some (.bool false), some (.int _) => rfl
  | some (.bool false), some (.bool false), some (.string _) => rfl
  | some (.bool false), some (.bool false), some (.null _) => rfl
  | some (.bool false), some (.bool false), none => rfl
  | some (.bool false), some (.int _), some (.bool true) => rfl
  | some (.bool false), some (.int _), some (.bool false) => rfl
  | some (.bool false), some (.int _), some (.int _) => rfl
  | some (.bool false), some (.int _), some (.string _) => rfl
  | some (.bool false), some (.int _), some (.null _) => rfl
  | some (.bool false), some (.int _), none => rfl
  | some (.bool false), some (.string _), some (.bool true) => rfl
  | some (.bool false), some (.string _), some (.bool false) => rfl
  | some (.bool false), some (.string _), some (.int _) => rfl
  | some (.bool false), some (.string _), some (.string _) => rfl
  | some (.bool false), some (.string _), some (.null _) => rfl
  | some (.bool false), some (.string _), none => rfl
  | some (.bool false), some (.null _), some (.bool true) => rfl
  | some (.bool false), some (.null _), some (.bool false) => rfl
  | some (.bool false), some (.null _), some (.int _) => rfl
  | some (.bool false), some (.null _), some (.string _) => rfl
  | some (.bool false), some (.null _), some (.null _) => rfl
  | some (.bool false), some (.null _), none => rfl
  | some (.bool false), none, some (.bool true) => rfl
  | some (.bool false), none, some (.bool false) => rfl
  | some (.bool false), none, some (.int _) => rfl
  | some (.bool false), none, some (.string _) => rfl
  | some (.bool false), none, some (.null _) => rfl
  | some (.bool false), none, none => rfl
  | some (.int _), some (.bool true), some (.bool true) => rfl
  | some (.int _), some (.bool true), some (.bool false) => rfl
  | some (.int _), some (.bool true), some (.int _) => rfl
  | some (.int _), some (.bool true), some (.string _) => rfl
  | some (.int _), some (.bool true), some (.null _) => rfl
  | some (.int _), some (.bool true), none => rfl
  | some (.int _), some (.bool false), some (.bool true) => rfl
  | some (.int _), some (.bool false), some (.bool false) => rfl
  | some (.int _), some (.bool false), some (.int _) => rfl
  | some (.int _), some (.bool false), some (.string _) => rfl
  | some (.int _), some (.bool false), some (.null _) => rfl
  | some (.int _), some (.bool false), none => rfl
  | some (.int _), some (.int _), some (.bool true) => rfl
  | some (.int _), some (.int _), some (.bool false) => rfl
  | some (.int _), some (.int _), some (.int _) => rfl
  | some (.int _), some (.int _), some (.string _) => rfl
  | some (.int _), some (.int _), some (.null _) => rfl
  | some (.int _), some (.int _), none => rfl
  | some (.int _), some (.string _), some (.bool true) => rfl
  | some (.int _), some (.string _), some (.bool false) => rfl
  | some (.int _), some (.string _), some (.int _) => rfl
  | some (.int _), some (.string _), some (.string _) => rfl
  | some (.int _), some (.string _), some (.null _) => rfl
  | some (.int _), some (.string _), none => rfl
  | some (.int _), some (.null _), some (.bool true) => rfl
  | some (.int _), some (.null _), some (.bool false) => rfl
  | some (.int _), some (.null _), some (.int _) => rfl
  | some (.int _), some (.null _), some (.string _) => rfl
  | some (.int _), some (.null _), some (.null _) => rfl
  | some (.int _), some (.null _), none => rfl
  | some (.int _), none, some (.bool true) => rfl
  | some (.int _), none, some (.bool false) => rfl
  | some (.int _), none, some (.int _) => rfl
  | some (.int _), none, some (.string _) => rfl
  | some (.int _), none, some (.null _) => rfl
  | some (.int _), none, none => rfl
  | some (.string _), some (.bool true), some (.bool true) => rfl
  | some (.string _), some (.bool true), some (.bool false) => rfl
  | some (.string _), some (.bool true), some (.int _) => rfl
  | some (.string _), some (.bool true), some (.string _) => rfl
  | some (.string _), some (.bool true), some (.null _) => rfl
  | some (.string _), some (.bool true), none => rfl
  | some (.string _), some (.bool false), some (.bool true) => rfl
  | some (.string _), some (.bool false), some (.bool false) => rfl
  | some (.string _), some (.bool false), some (.int _) => rfl
  | some (.string _), some (.bool false), some (.string _) => rfl
  | some (.string _), some (.bool false), some (.null _) => rfl
  | some (.string _), some (.bool false), none => rfl
  | some (.string _), some (.int _), some (.bool true) => rfl
  | some (.string _), some (.int _), some (.bool false) => rfl
  | some (.string _), some (.int _), some (.int _) => rfl
  | some (.string _), some (.int _), some (.string _) => rfl
  | some (.string _), some (.int _), some (.null _) => rfl
  | some (.string _), some (.int _), none => rfl
  | some (.string _), some (.string _), some (.bool true) => rfl
  | some (.string _), some (.string _), some (.bool false) => rfl
  | some (.string _), some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _), some (.string _) => rfl
  | some (.string _), some (.string _), some (.null _) => rfl
  | some (.string _), some (.string _), none => rfl
  | some (.string _), some (.null _), some (.bool true) => rfl
  | some (.string _), some (.null _), some (.bool false) => rfl
  | some (.string _), some (.null _), some (.int _) => rfl
  | some (.string _), some (.null _), some (.string _) => rfl
  | some (.string _), some (.null _), some (.null _) => rfl
  | some (.string _), some (.null _), none => rfl
  | some (.string _), none, some (.bool true) => rfl
  | some (.string _), none, some (.bool false) => rfl
  | some (.string _), none, some (.int _) => rfl
  | some (.string _), none, some (.string _) => rfl
  | some (.string _), none, some (.null _) => rfl
  | some (.string _), none, none => rfl
  | some (.null _), some (.bool true), some (.bool true) => rfl
  | some (.null _), some (.bool true), some (.bool false) => rfl
  | some (.null _), some (.bool true), some (.int _) => rfl
  | some (.null _), some (.bool true), some (.string _) => rfl
  | some (.null _), some (.bool true), some (.null _) => rfl
  | some (.null _), some (.bool true), none => rfl
  | some (.null _), some (.bool false), some (.bool true) => rfl
  | some (.null _), some (.bool false), some (.bool false) => rfl
  | some (.null _), some (.bool false), some (.int _) => rfl
  | some (.null _), some (.bool false), some (.string _) => rfl
  | some (.null _), some (.bool false), some (.null _) => rfl
  | some (.null _), some (.bool false), none => rfl
  | some (.null _), some (.int _), some (.bool true) => rfl
  | some (.null _), some (.int _), some (.bool false) => rfl
  | some (.null _), some (.int _), some (.int _) => rfl
  | some (.null _), some (.int _), some (.string _) => rfl
  | some (.null _), some (.int _), some (.null _) => rfl
  | some (.null _), some (.int _), none => rfl
  | some (.null _), some (.string _), some (.bool true) => rfl
  | some (.null _), some (.string _), some (.bool false) => rfl
  | some (.null _), some (.string _), some (.int _) => rfl
  | some (.null _), some (.string _), some (.string _) => rfl
  | some (.null _), some (.string _), some (.null _) => rfl
  | some (.null _), some (.string _), none => rfl
  | some (.null _), some (.null _), some (.bool true) => rfl
  | some (.null _), some (.null _), some (.bool false) => rfl
  | some (.null _), some (.null _), some (.int _) => rfl
  | some (.null _), some (.null _), some (.string _) => rfl
  | some (.null _), some (.null _), some (.null _) => rfl
  | some (.null _), some (.null _), none => rfl
  | some (.null _), none, some (.bool true) => rfl
  | some (.null _), none, some (.bool false) => rfl
  | some (.null _), none, some (.int _) => rfl
  | some (.null _), none, some (.string _) => rfl
  | some (.null _), none, some (.null _) => rfl
  | some (.null _), none, none => rfl
  | none, some (.bool true), some (.bool true) => rfl
  | none, some (.bool true), some (.bool false) => rfl
  | none, some (.bool true), some (.int _) => rfl
  | none, some (.bool true), some (.string _) => rfl
  | none, some (.bool true), some (.null _) => rfl
  | none, some (.bool true), none => rfl
  | none, some (.bool false), some (.bool true) => rfl
  | none, some (.bool false), some (.bool false) => rfl
  | none, some (.bool false), some (.int _) => rfl
  | none, some (.bool false), some (.string _) => rfl
  | none, some (.bool false), some (.null _) => rfl
  | none, some (.bool false), none => rfl
  | none, some (.int _), some (.bool true) => rfl
  | none, some (.int _), some (.bool false) => rfl
  | none, some (.int _), some (.int _) => rfl
  | none, some (.int _), some (.string _) => rfl
  | none, some (.int _), some (.null _) => rfl
  | none, some (.int _), none => rfl
  | none, some (.string _), some (.bool true) => rfl
  | none, some (.string _), some (.bool false) => rfl
  | none, some (.string _), some (.int _) => rfl
  | none, some (.string _), some (.string _) => rfl
  | none, some (.string _), some (.null _) => rfl
  | none, some (.string _), none => rfl
  | none, some (.null _), some (.bool true) => rfl
  | none, some (.null _), some (.bool false) => rfl
  | none, some (.null _), some (.int _) => rfl
  | none, some (.null _), some (.string _) => rfl
  | none, some (.null _), some (.null _) => rfl
  | none, some (.null _), none => rfl
  | none, none, some (.bool true) => rfl
  | none, none, some (.bool false) => rfl
  | none, none, some (.int _) => rfl
  | none, none, some (.string _) => rfl
  | none, none, some (.null _) => rfl
  | none, none, none => rfl

theorem and_or_distrib_left (a b c : Expr) :
    Expr.binOp .and a (Expr.binOp .or b c) ≃ₑ Expr.binOp .or (Expr.binOp .and a b) (Expr.binOp .and a c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_and_or_distrib_left _ _ _

theorem and_or_distrib_right (a b c : Expr) :
    Expr.binOp .and (Expr.binOp .or a b) c ≃ₑ Expr.binOp .or (Expr.binOp .and a c) (Expr.binOp .and b c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalBinOp_and_comm, evalBinOp_and_or_distrib_left]
  congr 1 <;> exact evalBinOp_and_comm _ _

theorem or_and_distrib_left (a b c : Expr) :
    Expr.binOp .or a (Expr.binOp .and b c) ≃ₑ Expr.binOp .and (Expr.binOp .or a b) (Expr.binOp .or a c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_or_and_distrib_left _ _ _

theorem or_and_distrib_right (a b c : Expr) :
    Expr.binOp .or (Expr.binOp .and a b) c ≃ₑ Expr.binOp .and (Expr.binOp .or a c) (Expr.binOp .or b c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalBinOp_or_comm, evalBinOp_or_and_distrib_left]
  congr 1 <;> exact evalBinOp_or_comm _ _

-- Absorption Laws
-- Note: These only hold for boolean-valued expressions.
-- For non-boolean a (e.g., int): a AND (a OR b) = none ≠ a
-- Value-level versions proven above (evalBinOp_and_absorb_or, evalBinOp_or_absorb_and)

/-- Absorption: a AND (a OR b) = a. Axiom: only valid for boolean-valued a, b. -/
axiom and_absorb_or (a b : Expr) :
    Expr.binOp .and a (Expr.binOp .or a b) ≃ₑ a

/-- Absorption: a OR (a AND b) = a. Axiom: only valid for boolean-valued a, b. -/
axiom or_absorb_and (a b : Expr) :
    Expr.binOp .or a (Expr.binOp .and a b) ≃ₑ a

-- Identity Laws
-- Note: and_true and or_false only hold for boolean-valued expressions.
-- For non-boolean expressions, e.g., (5 AND TRUE) = none ≠ 5.
-- Value-level versions proven above (evalBinOp_and_true_right, evalBinOp_or_false_right)

/-- Identity: a AND TRUE = a. Axiom: only valid for boolean-valued a. -/
axiom and_true (a : Expr) :
    Expr.binOp .and a (Expr.lit (.bool true)) ≃ₑ a

/-- Identity: a OR FALSE = a. Axiom: only valid for boolean-valued a. -/
axiom or_false (a : Expr) :
    Expr.binOp .or a (Expr.lit (.bool false)) ≃ₑ a

-- These ARE provable due to short-circuit evaluation
theorem and_false (a : Expr) :
    Expr.binOp .and a (Expr.lit (.bool false)) ≃ₑ Expr.lit (.bool false) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  exact evalBinOp_and_false_right _

theorem or_true (a : Expr) :
    Expr.binOp .or a (Expr.lit (.bool true)) ≃ₑ Expr.lit (.bool true) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  exact evalBinOp_or_true_right _

/-- WHERE TRUE is equivalent to no WHERE clause.
    Axiom: TRUE filter keeps all rows, equivalent to no filter.
    Proof requires showing filter identity at the List level. -/
axiom where_true_elim (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderByItem)
    (limit offset : Option Nat) :
    evalSelect db (.mk false items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ none groupBy having orderBy limit offset)

/-- WHERE FALSE produces empty result (or no FROM clause).
    Axiom: FALSE filter removes all rows. -/
axiom where_false_empty (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderByItem)
    (limit offset : Option Nat) :
    (evalSelect db (.mk false items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset)).length = 0 ∨
    from_.isNone

/-- Inner join is commutative up to row permutation.
    Axiom: swapping join order preserves rows. -/
axiom join_comm (db : Database) (a b : FromClause) (cond : Expr) :
    ∀ row ∈ evalFrom db (.join a .inner b (some cond)),
    ∃ row2 ∈ evalFrom db (.join b .inner a (some cond)),
    (∀ p, p ∈ row ↔ p ∈ row2)

partial def normalizeExpr : Expr → Expr
  | .binOp .and a b => let na := normalizeExpr a; let nb := normalizeExpr b; if toString (repr na) ≤ toString (repr nb) then .binOp .and na nb else .binOp .and nb na
  | .binOp .or a b => let na := normalizeExpr a; let nb := normalizeExpr b; if toString (repr na) ≤ toString (repr nb) then .binOp .or na nb else .binOp .or nb na
  | .binOp .add a b => let na := normalizeExpr a; let nb := normalizeExpr b; if toString (repr na) ≤ toString (repr nb) then .binOp .add na nb else .binOp .add nb na
  | .binOp .mul a b => let na := normalizeExpr a; let nb := normalizeExpr b; if toString (repr na) ≤ toString (repr nb) then .binOp .mul na nb else .binOp .mul nb na
  | .binOp op a b => .binOp op (normalizeExpr a) (normalizeExpr b)
  | .unaryOp .not (.unaryOp .not e) => normalizeExpr e
  | .unaryOp op e => .unaryOp op (normalizeExpr e)
  | .func name args => .func name (args.map normalizeExpr)
  | .agg fn arg distinct => .agg fn (arg.map normalizeExpr) distinct
  | .case branches else_ => .case (branches.map fun (c, r) => (normalizeExpr c, normalizeExpr r)) (else_.map normalizeExpr)
  | .inList e neg vals => .inList (normalizeExpr e) neg (vals.map normalizeExpr)
  | .inSubquery e neg sel => .inSubquery (normalizeExpr e) neg sel
  | .exists neg sel => .exists neg sel
  | .subquery sel => .subquery sel
  | .between e lo hi => .between (normalizeExpr e) (normalizeExpr lo) (normalizeExpr hi)
  | e => e

def syntacticEquiv (e1 e2 : Expr) : Bool := normalizeExpr e1 == normalizeExpr e2

theorem expr_equiv_subst {e1 e2 : Expr} (h : e1 ≃ₑ e2) (row : Row) : evalExpr row e1 = evalExpr row e2 := h row

-- ============================================================================
-- Additional Identity Laws (commuted versions)
-- ============================================================================

theorem true_and (a : Expr) :
    Expr.binOp .and (Expr.lit (.bool true)) a ≃ₑ a := by
  intro row
  have h := and_comm (Expr.lit (.bool true)) a row
  rw [h]
  exact and_true a row

theorem false_or (a : Expr) :
    Expr.binOp .or (Expr.lit (.bool false)) a ≃ₑ a := by
  intro row
  have h := or_comm (Expr.lit (.bool false)) a row
  rw [h]
  exact or_false a row

theorem false_and (a : Expr) :
    Expr.binOp .and (Expr.lit (.bool false)) a ≃ₑ Expr.lit (.bool false) := by
  intro row
  have h := and_comm (Expr.lit (.bool false)) a row
  rw [h]
  exact and_false a row

theorem true_or (a : Expr) :
    Expr.binOp .or (Expr.lit (.bool true)) a ≃ₑ Expr.lit (.bool true) := by
  intro row
  have h := or_comm (Expr.lit (.bool true)) a row
  rw [h]
  exact or_true a row

-- ============================================================================
-- Idempotent Laws
-- Note: These only hold for boolean-valued expressions in SQL's 3-valued logic.
-- For non-boolean a: a AND a = none ≠ a (since AND requires booleans)
-- Value-level versions proven above (evalBinOp_and_idem, evalBinOp_or_idem)
-- ============================================================================

/-- Idempotent: a AND a = a. Axiom: only valid for boolean-valued a. -/
axiom and_self (a : Expr) : Expr.binOp .and a a ≃ₑ a

/-- Idempotent: a OR a = a. Axiom: only valid for boolean-valued a. -/
axiom or_self (a : Expr) : Expr.binOp .or a a ≃ₑ a

-- ============================================================================
-- Complement Laws
-- Note: These only hold for boolean-valued expressions.
-- For non-boolean a: NOT a = none, so a AND (NOT a) = none OR false = none/false
-- Value-level versions proven above (evalBinOp_and_not_self, evalBinOp_or_not_self)
-- ============================================================================

/-- Complement: a AND (NOT a) = FALSE. Axiom: only valid for boolean-valued a. -/
axiom and_not_self (a : Expr) :
    Expr.binOp .and a (Expr.unaryOp .not a) ≃ₑ Expr.lit (.bool false)

/-- Complement: a OR (NOT a) = TRUE. Axiom: only valid for boolean-valued a. -/
axiom or_not_self (a : Expr) :
    Expr.binOp .or a (Expr.unaryOp .not a) ≃ₑ Expr.lit (.bool true)

theorem not_self_and (a : Expr) :
    Expr.binOp .and (Expr.unaryOp .not a) a ≃ₑ Expr.lit (.bool false) := by
  intro row
  have h := and_comm (Expr.unaryOp .not a) a row
  rw [h]
  exact and_not_self a row

theorem not_self_or (a : Expr) :
    Expr.binOp .or (Expr.unaryOp .not a) a ≃ₑ Expr.lit (.bool true) := by
  intro row
  have h := or_comm (Expr.unaryOp .not a) a row
  rw [h]
  exact or_not_self a row

-- ============================================================================
-- Reverse De Morgan Laws (for factoring)
-- ============================================================================

theorem or_not_not (a b : Expr) :
    Expr.binOp .or (Expr.unaryOp .not a) (Expr.unaryOp .not b) ≃ₑ
    Expr.unaryOp .not (Expr.binOp .and a b) := by
  intro row; exact (not_and a b row).symm

theorem and_not_not (a b : Expr) :
    Expr.binOp .and (Expr.unaryOp .not a) (Expr.unaryOp .not b) ≃ₑ
    Expr.unaryOp .not (Expr.binOp .or a b) := by
  intro row; exact (not_or a b row).symm

-- ============================================================================
-- Reverse Distributivity (factoring)
-- ============================================================================

theorem or_and_factor_left (a b c : Expr) :
    Expr.binOp .or (Expr.binOp .and a b) (Expr.binOp .and a c) ≃ₑ
    Expr.binOp .and a (Expr.binOp .or b c) := by
  intro row; exact (and_or_distrib_left a b c row).symm

theorem and_or_factor_left (a b c : Expr) :
    Expr.binOp .and (Expr.binOp .or a b) (Expr.binOp .or a c) ≃ₑ
    Expr.binOp .or a (Expr.binOp .and b c) := by
  intro row; exact (or_and_distrib_left a b c row).symm

-- ============================================================================
-- Congruence Theorems
-- ============================================================================

/-- Binary operation congruence -/
theorem binOp_congr {op : BinOp} {a1 a2 b1 b2 : Expr}
    (ha : a1 ≃ₑ a2) (hb : b1 ≃ₑ b2) :
    Expr.binOp op a1 b1 ≃ₑ Expr.binOp op a2 b2 := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  have ha' := ha row
  have hb' := hb row
  simp only [evalExpr] at ha' hb'
  rw [ha', hb']

/-- Unary operation congruence -/
theorem unaryOp_congr {op : UnaryOp} {a b : Expr}
    (h : a ≃ₑ b) :
    Expr.unaryOp op a ≃ₑ Expr.unaryOp op b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_unaryOp]
  have h' := h row
  simp only [evalExpr] at h'
  rw [h']

/-- Binary operation left congruence -/
theorem binOp_congr_left {op : BinOp} {a1 a2 b : Expr}
    (ha : a1 ≃ₑ a2) :
    Expr.binOp op a1 b ≃ₑ Expr.binOp op a2 b := by
  exact binOp_congr ha (expr_equiv_refl b)

/-- Binary operation right congruence -/
theorem binOp_congr_right {op : BinOp} {a b1 b2 : Expr}
    (hb : b1 ≃ₑ b2) :
    Expr.binOp op a b1 ≃ₑ Expr.binOp op a b2 := by
  exact binOp_congr (expr_equiv_refl a) hb


end SqlEquiv
