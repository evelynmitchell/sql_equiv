/-
  Property-based tests for expression algebraic identities.

  Tests the evaluator (evalExpr) against the proven theorems in
  ExprAxioms.lean and Comparison.lean. If the evaluator has a bug,
  SlimCheck will find an input where the theorem's claimed equality
  does not hold semantically.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace ExprAlgebra

-- ============================================================================
-- Commutativity
-- ============================================================================

def commutativityTests (cfg : Configuration) : TestSeq :=
  -- covers: and_comm, evalBinOp_and_comm
  check (cfg := cfg) "AND commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .and a.expr b.expr) == evalExpr [] (.binOp .and b.expr a.expr)) $
  -- covers: or_comm, evalBinOp_or_comm
  check (cfg := cfg) "OR commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .or a.expr b.expr) == evalExpr [] (.binOp .or b.expr a.expr)) $
  -- covers: add_comm, evalBinOp_add_comm
  check (cfg := cfg) "ADD commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .add a.expr b.expr) == evalExpr [] (.binOp .add b.expr a.expr)) $
  -- covers: mul_comm, evalBinOp_mul_comm
  check (cfg := cfg) "MUL commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .mul a.expr b.expr) == evalExpr [] (.binOp .mul b.expr a.expr)) $
  -- covers: eq_comm, evalBinOp_eq_comm
  check (cfg := cfg) "EQ commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .eq a.expr b.expr) == evalExpr [] (.binOp .eq b.expr a.expr))

-- ============================================================================
-- Associativity
-- ============================================================================

def associativityTests (cfg : Configuration) : TestSeq :=
  -- covers: and_assoc, evalBinOp_and_assoc
  check (cfg := cfg) "AND is associative" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .and (.binOp .and a.expr b.expr) c.expr) ==
    evalExpr [] (.binOp .and a.expr (.binOp .and b.expr c.expr))) $
  -- covers: or_assoc, evalBinOp_or_assoc
  check (cfg := cfg) "OR is associative" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .or (.binOp .or a.expr b.expr) c.expr) ==
    evalExpr [] (.binOp .or a.expr (.binOp .or b.expr c.expr)))

-- ============================================================================
-- De Morgan's Laws
-- ============================================================================

-- De Morgan's laws only hold for boolean-valued inputs (after narrowing null
-- propagation from `_` to `some _`, NOT(AND(NULL, INT)) ≠ OR(NOT NULL, NOT INT)).
def deMorganTests (cfg : Configuration) : TestSeq :=
  -- covers: not_and, trilean_de_morgan_and, evalUnaryOp_not_and
  check (cfg := cfg) "NOT (a AND b) = (NOT a) OR (NOT b)" (∀ a b : BoolGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .and a.expr b.expr)) ==
    evalExpr [] (.binOp .or (.unaryOp .not a.expr) (.unaryOp .not b.expr))) $
  -- covers: not_or, trilean_de_morgan_or, evalUnaryOp_not_or
  check (cfg := cfg) "NOT (a OR b) = (NOT a) AND (NOT b)" (∀ a b : BoolGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .or a.expr b.expr)) ==
    evalExpr [] (.binOp .and (.unaryOp .not a.expr) (.unaryOp .not b.expr)))

-- ============================================================================
-- Distributivity
-- ============================================================================

def distributivityTests (cfg : Configuration) : TestSeq :=
  -- covers: and_or_distrib_left, evalBinOp_and_or_distrib
  check (cfg := cfg) "AND distributes over OR (left)" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.binOp .or b.expr c.expr)) ==
    evalExpr [] (.binOp .or (.binOp .and a.expr b.expr) (.binOp .and a.expr c.expr))) $
  -- covers: or_and_distrib_left, evalBinOp_or_and_distrib
  check (cfg := cfg) "OR distributes over AND (left)" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.binOp .and b.expr c.expr)) ==
    evalExpr [] (.binOp .and (.binOp .or a.expr b.expr) (.binOp .or a.expr c.expr)))

-- ============================================================================
-- Identity and Annihilation
-- ============================================================================

def identityTests (cfg : Configuration) : TestSeq :=
  -- covers: and_true, evalBinOp_and_true_right
  check (cfg := cfg) "a AND TRUE = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.lit (.bool true))) == evalExpr [] a.expr) $
  -- covers: true_and, evalBinOp_and_true_left
  check (cfg := cfg) "TRUE AND a = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and (.lit (.bool true)) a.expr) == evalExpr [] a.expr) $
  -- covers: or_false, evalBinOp_or_false_right
  check (cfg := cfg) "a OR FALSE = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.lit (.bool false))) == evalExpr [] a.expr) $
  -- covers: false_or, evalBinOp_or_false_left
  check (cfg := cfg) "FALSE OR a = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or (.lit (.bool false)) a.expr) == evalExpr [] a.expr) $
  -- covers: and_false, evalBinOp_and_false_right
  check (cfg := cfg) "a AND FALSE = FALSE" (∀ a : BoundedGroundExpr,
    evalExpr [] (.binOp .and a.expr (.lit (.bool false))) == evalExpr [] (.lit (.bool false))) $
  -- covers: or_true, evalBinOp_or_true_right
  check (cfg := cfg) "a OR TRUE = TRUE" (∀ a : BoundedGroundExpr,
    evalExpr [] (.binOp .or a.expr (.lit (.bool true))) == evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- Idempotence and Complement
-- ============================================================================

def idempotenceTests (cfg : Configuration) : TestSeq :=
  -- covers: and_self, evalBinOp_and_idem
  check (cfg := cfg) "a AND a = a" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr a.expr) == evalExpr [] a.expr) $
  -- covers: or_self, evalBinOp_or_idem
  check (cfg := cfg) "a OR a = a" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr a.expr) == evalExpr [] a.expr)

def complementTests (cfg : Configuration) : TestSeq :=
  -- covers: and_not_self, evalBinOp_and_not_self
  check (cfg := cfg) "a AND (NOT a) = FALSE" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.unaryOp .not a.expr)) ==
    evalExpr [] (.lit (.bool false))) $
  -- covers: or_not_self, evalBinOp_or_not_self
  check (cfg := cfg) "a OR (NOT a) = TRUE" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.unaryOp .not a.expr)) ==
    evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- Absorption
-- ============================================================================

def absorptionTests (cfg : Configuration) : TestSeq :=
  -- covers: and_absorb_or, evalBinOp_and_absorb_or
  check (cfg := cfg) "a AND (a OR b) = a" (∀ a b : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.binOp .or a.expr b.expr)) == evalExpr [] a.expr) $
  -- covers: or_absorb_and, evalBinOp_or_absorb_and
  check (cfg := cfg) "a OR (a AND b) = a" (∀ a b : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.binOp .and a.expr b.expr)) == evalExpr [] a.expr)

-- ============================================================================
-- Arithmetic Identities (using IntGroundExpr)
-- ============================================================================

def arithmeticTests (cfg : Configuration) : TestSeq :=
  -- covers: expr_add_zero
  check (cfg := cfg) "x + 0 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .add e.expr (.lit (.int 0))) == evalExpr [] e.expr) $
  -- covers: expr_zero_add
  check (cfg := cfg) "0 + x = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .add (.lit (.int 0)) e.expr) == evalExpr [] e.expr) $
  -- covers: expr_mul_one
  check (cfg := cfg) "x * 1 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul e.expr (.lit (.int 1))) == evalExpr [] e.expr) $
  -- covers: expr_one_mul
  check (cfg := cfg) "1 * x = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul (.lit (.int 1)) e.expr) == evalExpr [] e.expr) $
  -- covers: expr_mul_zero, expr_zero_mul
  check (cfg := cfg) "x * 0 = 0" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul e.expr (.lit (.int 0))) == evalExpr [] (.lit (.int 0))) $
  -- covers: expr_sub_zero
  check (cfg := cfg) "x - 0 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .sub e.expr (.lit (.int 0))) == evalExpr [] e.expr)

-- ============================================================================
-- Comparison Flips
-- ============================================================================

def comparisonFlipTests (cfg : Configuration) : TestSeq :=
  -- covers: not_eq_is_ne
  check (cfg := cfg) "NOT (a = b) = (a <> b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .eq a.expr b.expr)) ==
    evalExpr [] (.binOp .ne a.expr b.expr)) $
  -- covers: not_ne_is_eq
  check (cfg := cfg) "NOT (a <> b) = (a = b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .ne a.expr b.expr)) ==
    evalExpr [] (.binOp .eq a.expr b.expr)) $
  -- covers: lt_flip
  check (cfg := cfg) "a < b = b > a" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .lt a.expr b.expr) ==
    evalExpr [] (.binOp .gt b.expr a.expr)) $
  -- covers: le_flip
  check (cfg := cfg) "a <= b = b >= a" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .le a.expr b.expr) ==
    evalExpr [] (.binOp .ge b.expr a.expr)) $
  -- covers: not_lt_is_ge
  check (cfg := cfg) "NOT (a < b) = (a >= b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .lt a.expr b.expr)) ==
    evalExpr [] (.binOp .ge a.expr b.expr)) $
  -- covers: not_gt_is_le
  check (cfg := cfg) "NOT (a > b) = (a <= b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .gt a.expr b.expr)) ==
    evalExpr [] (.binOp .le a.expr b.expr))

-- ============================================================================
-- Double Negation
-- ============================================================================

def doubleNegTests (cfg : Configuration) : TestSeq :=
  -- covers: not_not_bool, evalUnaryOp_not_bool, trilean_not_not
  check (cfg := cfg) "NOT (NOT a) = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.unaryOp .not (.unaryOp .not a.expr)) == evalExpr [] a.expr)

-- ============================================================================
-- All expression algebra tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Commutativity" (commutativityTests cfg) $
  group "Associativity" (associativityTests cfg) $
  group "De Morgan" (deMorganTests cfg) $
  group "Distributivity" (distributivityTests cfg) $
  group "Identity/Annihilation" (identityTests cfg) $
  group "Idempotence" (idempotenceTests cfg) $
  group "Complement" (complementTests cfg) $
  group "Absorption" (absorptionTests cfg) $
  group "Arithmetic" (arithmeticTests cfg) $
  group "Comparison Flips" (comparisonFlipTests cfg) $
  group "Double Negation" (doubleNegTests cfg)

end ExprAlgebra
