/-
  SQL Equivalence Tactics

  Custom tactics for proving SQL equivalence properties:
  - sql_equiv: Automated equivalence proving
  - sql_equiv!: Aggressive version with all rewrites
  - sql_simp: SQL-specific simplification
  - sql_normalize: Normalize expressions to canonical form
  - sql_congr: Congruence tactics for descending into subexpressions
  - sql_calc: Chaining equivalences
-/
import SqlEquiv.Ast
import SqlEquiv.Semantics
import SqlEquiv.Equiv
import Lean

namespace SqlEquiv

open Lean Elab Tactic Meta
open scoped SqlEquiv  -- Make scoped notations available

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

  -- Step 3: Try associativity lemmas
  let tryAssoc : TacticM Unit := do
    evalTactic (← `(tactic| first
      | exact and_assoc _ _ _
      | exact or_assoc _ _ _))
  if ← tryTactic tryAssoc then return

  -- Step 4: Try De Morgan's laws
  let tryDeMorgan : TacticM Unit := do
    evalTactic (← `(tactic| first
      | exact not_and _ _
      | exact not_or _ _
      | exact or_not_not _ _
      | exact and_not_not _ _))
  if ← tryTactic tryDeMorgan then return

  -- Step 5: Try distributivity laws
  let tryDistrib : TacticM Unit := do
    evalTactic (← `(tactic| first
      | exact and_or_distrib_left _ _ _
      | exact and_or_distrib_right _ _ _
      | exact or_and_distrib_left _ _ _
      | exact or_and_distrib_right _ _ _
      | exact or_and_factor_left _ _ _
      | exact and_or_factor_left _ _ _))
  if ← tryTactic tryDistrib then return

  -- Step 6: Try absorption laws
  let tryAbsorb : TacticM Unit := do
    evalTactic (← `(tactic| first
      | exact and_absorb_or _ _
      | exact or_absorb_and _ _))
  if ← tryTactic tryAbsorb then return

  -- Step 7: Try identity laws
  let tryIdentity : TacticM Unit := do
    evalTactic (← `(tactic| first
      | exact and_true _
      | exact true_and _
      | exact or_false _
      | exact false_or _
      | exact and_false _
      | exact false_and _
      | exact or_true _
      | exact true_or _
      | exact and_self _
      | exact or_self _))
  if ← tryTactic tryIdentity then return

  -- Step 8: Try complement laws
  let tryComplement : TacticM Unit := do
    evalTactic (← `(tactic| first
      | exact and_not_self _
      | exact not_self_and _
      | exact or_not_self _
      | exact not_self_or _))
  if ← tryTactic tryComplement then return

  -- Step 9: Try arithmetic identity laws
  let tryArith : TacticM Unit := do
    evalTactic (← `(tactic| first
      | exact expr_add_zero _
      | exact expr_zero_add _
      | exact expr_mul_one _
      | exact expr_one_mul _
      | exact expr_mul_zero _
      | exact expr_zero_mul _
      | exact expr_sub_zero _))
  if ← tryTactic tryArith then return

  -- Step 10: Try comparison rules
  let tryCompare : TacticM Unit := do
    evalTactic (← `(tactic| first
      | exact not_eq_is_ne _ _
      | exact not_ne_is_eq _ _
      | exact not_lt_is_ge _ _
      | exact not_le_is_gt _ _
      | exact not_gt_is_le _ _
      | exact not_ge_is_lt _ _
      | exact lt_flip _ _
      | exact le_flip _ _
      | exact gt_flip _ _
      | exact ge_flip _ _))
  if ← tryTactic tryCompare then return

  -- Step 11: Unfold equivalence definitions and try to close
  evalTactic (← `(tactic| unfold ExprEquiv SelectEquiv QueryEquiv StmtEquiv))

  -- Step 12: Introduce the universal quantifier if present
  let tryIntro : TacticM Unit := evalTactic (← `(tactic| intro _))
  discard <| tryTactic tryIntro

  -- Step 13: Try reflexivity
  let tryRfl : TacticM Unit := evalTactic (← `(tactic| rfl))
  discard <| tryTactic tryRfl

-- ============================================================================
-- sql_congr Tactic - Congruence for binary/unary ops
-- ============================================================================

/-- sql_congr tactic: Apply congruence to binary/unary ops -/
syntax "sql_congr" : tactic

macro_rules
  | `(tactic| sql_congr) =>
    `(tactic| first
      | apply binOp_congr <;> try sql_equiv
      | apply binOp_congr_left <;> try sql_equiv
      | apply binOp_congr_right <;> try sql_equiv
      | apply unaryOp_congr <;> try sql_equiv)

/-- sql_congr_left tactic: Apply left congruence to binary ops -/
syntax "sql_congr_left" : tactic

macro_rules
  | `(tactic| sql_congr_left) =>
    `(tactic| apply binOp_congr_left)

/-- sql_congr_right tactic: Apply right congruence to binary ops -/
syntax "sql_congr_right" : tactic

macro_rules
  | `(tactic| sql_congr_right) =>
    `(tactic| apply binOp_congr_right)

/-- sql_congr_unary tactic: Apply congruence to unary ops -/
syntax "sql_congr_unary" : tactic

macro_rules
  | `(tactic| sql_congr_unary) =>
    `(tactic| apply unaryOp_congr)

-- ============================================================================
-- sql_equiv! Tactic - Aggressive version
-- ============================================================================

/-- sql_equiv! tactic: Aggressive SQL equivalence proving with all rewrites -/
syntax "sql_equiv!" : tactic

/-- Helper: all SQL rewrite rules as simp lemmas -/
macro_rules
  | `(tactic| sql_equiv!) =>
    `(tactic|
      first
        -- Try basic sql_equiv first
        | sql_equiv
        -- Try normalization-based proof
        | (have h : syntacticEquiv _ _ = true := by native_decide
           exact syntacticEquiv_implies_equiv h)
        -- Try repeated rewriting with all rules
        | (repeat (first
            | exact expr_equiv_refl _
            | exact and_comm _ _
            | exact or_comm _ _
            | exact add_comm _ _
            | exact mul_comm _ _
            | exact not_not _
            | exact eq_comm _ _
            | exact and_assoc _ _ _
            | exact or_assoc _ _ _
            | exact not_and _ _
            | exact not_or _ _
            | exact or_not_not _ _
            | exact and_not_not _ _
            | exact and_or_distrib_left _ _ _
            | exact and_or_distrib_right _ _ _
            | exact or_and_distrib_left _ _ _
            | exact or_and_distrib_right _ _ _
            | exact or_and_factor_left _ _ _
            | exact and_or_factor_left _ _ _
            | exact and_absorb_or _ _
            | exact or_absorb_and _ _
            | exact and_true _
            | exact true_and _
            | exact or_false _
            | exact false_or _
            | exact and_false _
            | exact false_and _
            | exact or_true _
            | exact true_or _
            | exact and_self _
            | exact or_self _
            | exact and_not_self _
            | exact not_self_and _
            | exact or_not_self _
            | exact not_self_or _
            | apply binOp_congr <;> sql_equiv
            | apply unaryOp_congr <;> sql_equiv
            | rfl))
        -- Final fallback: unfold and try decidability
        | (unfold ExprEquiv SelectEquiv QueryEquiv StmtEquiv
           intro _
           first | rfl | native_decide))

-- ============================================================================
-- sql_rw Tactic - Apply specific rewrite rules
-- ============================================================================

/-- sql_rw tactic: Apply a specific SQL rewrite rule -/
syntax "sql_rw" ("[" ident,* "]")? : tactic

/-- Helper for applying specific rewrite rules -/
elab "sql_rw_demorgan" : tactic => do
  evalTactic (← `(tactic| first
    | exact not_and _ _
    | exact not_or _ _
    | exact or_not_not _ _
    | exact and_not_not _ _
    | apply expr_equiv_trans; first
      | exact not_and _ _
      | exact not_or _ _
    | fail "No De Morgan rule applies"))

elab "sql_rw_distrib" : tactic => do
  evalTactic (← `(tactic| first
    | exact and_or_distrib_left _ _ _
    | exact and_or_distrib_right _ _ _
    | exact or_and_distrib_left _ _ _
    | exact or_and_distrib_right _ _ _
    | exact or_and_factor_left _ _ _
    | exact and_or_factor_left _ _ _
    | fail "No distributivity rule applies"))

elab "sql_rw_absorb" : tactic => do
  evalTactic (← `(tactic| first
    | exact and_absorb_or _ _
    | exact or_absorb_and _ _
    | fail "No absorption rule applies"))

elab "sql_rw_identity" : tactic => do
  evalTactic (← `(tactic| first
    | exact and_true _
    | exact true_and _
    | exact or_false _
    | exact false_or _
    | exact and_false _
    | exact false_and _
    | exact or_true _
    | exact true_or _
    | exact and_self _
    | exact or_self _
    | fail "No identity rule applies"))

/-- sql_rw_arith tactic: Apply arithmetic identity rules -/
elab "sql_rw_arith" : tactic => do
  evalTactic (← `(tactic| first
    | exact expr_add_zero _
    | exact expr_zero_add _
    | exact expr_mul_one _
    | exact expr_one_mul _
    | exact expr_mul_zero _
    | exact expr_zero_mul _
    | exact expr_sub_zero _
    | fail "No arithmetic identity rule applies"))

/-- sql_rw_compare tactic: Apply comparison flip/negation rules -/
elab "sql_rw_compare" : tactic => do
  evalTactic (← `(tactic| first
    | exact not_eq_is_ne _ _
    | exact not_ne_is_eq _ _
    | exact not_lt_is_ge _ _
    | exact not_le_is_gt _ _
    | exact not_gt_is_le _ _
    | exact not_ge_is_lt _ _
    | exact lt_flip _ _
    | exact le_flip _ _
    | exact gt_flip _ _
    | exact ge_flip _ _
    | fail "No comparison rule applies"))

/-- sql_rw_null tactic: Apply NULL handling rules -/
elab "sql_rw_null" : tactic => do
  evalTactic (← `(tactic| first
    | exact coalesce_null_left_nonnull _ _ ‹_›
    | exact null_add_left _
    | exact null_add_right _
    | exact null_sub_left _
    | exact null_sub_right _
    | exact null_mul_left _
    | exact null_mul_right _
    | exact false_and_null
    | exact null_and_false
    | exact true_or_null
    | exact null_or_true
    | fail "No NULL rule applies"))

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
-- sql_calc - Chaining equivalences (Term-mode helper)
-- ============================================================================

/-- Chain expression equivalences using transitivity -/
def exprCalc2 {e1 e2 e3 : Expr} (h1 : e1 ≃ₑ e2) (h2 : e2 ≃ₑ e3) : e1 ≃ₑ e3 :=
  expr_equiv_trans h1 h2

def exprCalc3 {e1 e2 e3 e4 : Expr}
    (h1 : e1 ≃ₑ e2) (h2 : e2 ≃ₑ e3) (h3 : e3 ≃ₑ e4) : e1 ≃ₑ e4 :=
  expr_equiv_trans (expr_equiv_trans h1 h2) h3

def exprCalc4 {e1 e2 e3 e4 e5 : Expr}
    (h1 : e1 ≃ₑ e2) (h2 : e2 ≃ₑ e3) (h3 : e3 ≃ₑ e4) (h4 : e4 ≃ₑ e5) : e1 ≃ₑ e5 :=
  expr_equiv_trans (expr_equiv_trans (expr_equiv_trans h1 h2) h3) h4

/-
-- NOTE: sql_calc syntax is currently disabled because scoped infix notation
-- cannot be used in macro syntax patterns. The helper functions above
-- (exprCalc2, exprCalc3, exprCalc4) can still be used directly.
--
-- To chain equivalences, use:
--   exact exprCalc2 proof1 proof2
-- or:
--   exact exprCalc3 proof1 proof2 proof3
-/

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

/-- Example: De Morgan's law -/
example : Expr.unaryOp .not (Expr.binOp .and a b) ≃ₑ
          Expr.binOp .or (Expr.unaryOp .not a) (Expr.unaryOp .not b) := by sql_equiv

/-- Example: Distributivity -/
example : Expr.binOp .and a (Expr.binOp .or b c) ≃ₑ
          Expr.binOp .or (Expr.binOp .and a b) (Expr.binOp .and a c) := by sql_equiv

/-- Example: Absorption -/
example : Expr.binOp .and a (Expr.binOp .or a b) ≃ₑ a := by sql_equiv

/-- Example: Identity AND TRUE -/
example : Expr.binOp .and a (Expr.lit (.bool true)) ≃ₑ a := by sql_equiv

/-- Example: Identity OR FALSE -/
example : Expr.binOp .or a (Expr.lit (.bool false)) ≃ₑ a := by sql_equiv

/-- Example: Annihilation AND FALSE -/
example : Expr.binOp .and a (Expr.lit (.bool false)) ≃ₑ Expr.lit (.bool false) := by sql_equiv

/-- Example: Annihilation OR TRUE -/
example : Expr.binOp .or a (Expr.lit (.bool true)) ≃ₑ Expr.lit (.bool true) := by sql_equiv

/-- Example: Idempotent AND -/
example : Expr.binOp .and a a ≃ₑ a := by sql_equiv

/-- Example: Idempotent OR -/
example : Expr.binOp .or a a ≃ₑ a := by sql_equiv

/-- Example: Complement AND -/
example : Expr.binOp .and a (Expr.unaryOp .not a) ≃ₑ Expr.lit (.bool false) := by sql_equiv

/-- Example: Complement OR -/
example : Expr.binOp .or a (Expr.unaryOp .not a) ≃ₑ Expr.lit (.bool true) := by sql_equiv

/-- Example: Congruence for binary ops -/
example (h : a ≃ₑ b) : Expr.binOp .and a c ≃ₑ Expr.binOp .and b c := by
  sql_congr_left
  exact h

/-- Example: Congruence for unary ops -/
example (h : a ≃ₑ b) : Expr.unaryOp .not a ≃ₑ Expr.unaryOp .not b := by
  sql_congr_unary
  exact h

/-- Example: chaining equivalences using exprCalc2/exprCalc3 directly -/
example : Expr.binOp .and (Expr.binOp .and a b) c ≃ₑ
          Expr.binOp .and a (Expr.binOp .and b c) := by
  exact and_assoc a b c

/-- Example: Multi-step chaining using exprCalc2 -/
example : Expr.binOp .and a b ≃ₑ Expr.binOp .and b a := by
  exact exprCalc2 (and_comm a b) (expr_equiv_refl _)

/-- Example: Arithmetic identity x + 0 = x -/
example : Expr.binOp .add a (Expr.lit (.int 0)) ≃ₑ a := by sql_equiv

/-- Example: Arithmetic identity x * 1 = x -/
example : Expr.binOp .mul a (Expr.lit (.int 1)) ≃ₑ a := by sql_equiv

/-- Example: Arithmetic annihilation x * 0 = 0 -/
example : Expr.binOp .mul a (Expr.lit (.int 0)) ≃ₑ Expr.lit (.int 0) := by sql_equiv

/-- Example: Comparison flip x < y = y > x -/
example : Expr.binOp .lt a b ≃ₑ Expr.binOp .gt b a := by sql_equiv

/-- Example: Comparison negation NOT (x < y) = x >= y -/
example : Expr.unaryOp .not (Expr.binOp .lt a b) ≃ₑ Expr.binOp .ge a b := by sql_equiv

/-- Example: NOT (x = y) = x <> y -/
example : Expr.unaryOp .not (Expr.binOp .eq a b) ≃ₑ Expr.binOp .ne a b := by sql_equiv

/-- Example: Using sql_rw_arith -/
example : Expr.binOp .add a (Expr.lit (.int 0)) ≃ₑ a := by sql_rw_arith

/-- Example: Using sql_rw_compare -/
example : Expr.binOp .lt a b ≃ₑ Expr.binOp .gt b a := by sql_rw_compare

end Examples

end SqlEquiv
