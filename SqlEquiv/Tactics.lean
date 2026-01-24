/-
  SQL Equivalence Tactics

  Custom tactics for proving SQL equivalence properties:
  - sql_equiv: Automated equivalence proving
  - sql_simp: SQL-specific simplification
  - sql_normalize: Normalize expressions to canonical form
-/
import SqlEquiv.Ast
import SqlEquiv.Semantics
import SqlEquiv.Equiv
import Lean

namespace SqlEquiv

open Lean Elab Tactic Meta

-- ============================================================================
-- sql_simp Tactic
-- ============================================================================

/-- sql_simp tactic: Apply SQL-specific rewrites by unfolding equivalence definitions -/
syntax "sql_simp" : tactic

macro_rules
  | `(tactic| sql_simp) =>
    `(tactic| simp only [ExprEquiv, SelectEquiv, QueryEquiv, StmtEquiv])

-- ============================================================================
-- sql_normalize Tactic
-- ============================================================================

/-- sql_normalize tactic: Normalize SQL expressions to canonical form -/
syntax "sql_normalize" : tactic

macro_rules
  | `(tactic| sql_normalize) =>
    `(tactic| simp only [ExprEquiv, SelectEquiv, QueryEquiv, StmtEquiv,
               normalizeExpr, syntacticEquiv])

-- ============================================================================
-- sql_equiv Tactic
-- ============================================================================

/-- sql_equiv tactic: Automated SQL equivalence proving -/
syntax "sql_equiv" : tactic

/-- Main sql_equiv implementation -/
elab "sql_equiv" : tactic => do
  -- Step 1: Try reflexivity lemmas
  let tryRefl : TacticM Unit := do
    evalTactic (← `(tactic| first
      | exact expr_equiv_refl _
      | exact select_equiv_refl _
      | exact query_equiv_refl _
      | exact stmt_equiv_refl _))
  if ← tryTactic tryRefl then return

  -- Step 2: Try commutativity lemmas directly
  let tryComm : TacticM Unit := do
    evalTactic (← `(tactic| first
      | exact and_comm _ _
      | exact or_comm _ _
      | exact add_comm _ _
      | exact mul_comm _ _
      | exact not_not _
      | exact eq_comm _ _))
  if ← tryTactic tryComm then return

  -- Step 3: Unfold equivalence definitions and try to close
  evalTactic (← `(tactic| unfold ExprEquiv SelectEquiv QueryEquiv StmtEquiv))

  -- Step 4: Introduce the universal quantifier if present
  let tryIntro : TacticM Unit := evalTactic (← `(tactic| intro _))
  discard <| tryTactic tryIntro

  -- Step 5: Try reflexivity
  let tryRfl : TacticM Unit := evalTactic (← `(tactic| rfl))
  discard <| tryTactic tryRfl

-- ============================================================================
-- Helper Tactics
-- ============================================================================

/-- sql_refl tactic: Reflexivity for SQL equivalence -/
syntax "sql_refl" : tactic

macro_rules
  | `(tactic| sql_refl) =>
    `(tactic| first
      | exact expr_equiv_refl _
      | exact select_equiv_refl _
      | exact query_equiv_refl _
      | exact stmt_equiv_refl _
      | rfl)

/-- sql_symm tactic: Symmetry for SQL equivalence -/
syntax "sql_symm" : tactic

macro_rules
  | `(tactic| sql_symm) =>
    `(tactic| first
      | apply expr_equiv_symm
      | apply select_equiv_symm
      | apply query_equiv_symm
      | apply stmt_equiv_symm)

/-- sql_trans tactic: Transitivity for SQL equivalence -/
syntax "sql_trans" (term)? : tactic

macro_rules
  | `(tactic| sql_trans $e) =>
    `(tactic| first
      | apply expr_equiv_trans (e2 := $e)
      | apply select_equiv_trans (s2 := $e)
      | apply query_equiv_trans (q2 := $e)
      | apply stmt_equiv_trans (s2 := $e))
  | `(tactic| sql_trans) =>
    `(tactic| first
      | apply expr_equiv_trans
      | apply select_equiv_trans
      | apply query_equiv_trans
      | apply stmt_equiv_trans)

-- ============================================================================
-- Example Proofs (tests for the tactics)
-- ============================================================================

section Examples

variable (a b c : Expr)

/-- Example: AND commutativity using sql_equiv -/
example : Expr.binOp .and a b ≃ₑ Expr.binOp .and b a := by sql_equiv

/-- Example: OR commutativity using sql_equiv -/
example : Expr.binOp .or a b ≃ₑ Expr.binOp .or b a := by sql_equiv

/-- Example: Addition commutativity -/
example : Expr.binOp .add a b ≃ₑ Expr.binOp .add b a := by sql_equiv

/-- Example: Multiplication commutativity -/
example : Expr.binOp .mul a b ≃ₑ Expr.binOp .mul b a := by sql_equiv

/-- Example: Double negation elimination -/
example : Expr.unaryOp .not (Expr.unaryOp .not a) ≃ₑ a := by sql_equiv

/-- Example: Reflexivity -/
example : a ≃ₑ a := by sql_refl

/-- Example: Symmetry usage -/
example (h : a ≃ₑ b) : b ≃ₑ a := by
  sql_symm
  exact h

/-- Example: Transitivity usage -/
example (h1 : a ≃ₑ b) (h2 : b ≃ₑ c) : a ≃ₑ c := by
  sql_trans b
  · exact h1
  · exact h2

end Examples

end SqlEquiv
