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

def commutativityTests : TestSeq :=
  check (cfg := slimCfg) "AND commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .and a.expr b.expr) == evalExpr [] (.binOp .and b.expr a.expr)) $
  check (cfg := slimCfg) "OR commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .or a.expr b.expr) == evalExpr [] (.binOp .or b.expr a.expr)) $
  check (cfg := slimCfg) "ADD commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .add a.expr b.expr) == evalExpr [] (.binOp .add b.expr a.expr)) $
  check (cfg := slimCfg) "MUL commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .mul a.expr b.expr) == evalExpr [] (.binOp .mul b.expr a.expr)) $
  check (cfg := slimCfg) "EQ commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .eq a.expr b.expr) == evalExpr [] (.binOp .eq b.expr a.expr))

-- ============================================================================
-- Associativity
-- ============================================================================

def associativityTests : TestSeq :=
  check (cfg := slimCfg) "AND is associative" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .and (.binOp .and a.expr b.expr) c.expr) ==
    evalExpr [] (.binOp .and a.expr (.binOp .and b.expr c.expr))) $
  check (cfg := slimCfg) "OR is associative" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .or (.binOp .or a.expr b.expr) c.expr) ==
    evalExpr [] (.binOp .or a.expr (.binOp .or b.expr c.expr)))

-- ============================================================================
-- De Morgan's Laws
-- ============================================================================

-- De Morgan's laws only hold for boolean-valued inputs (after narrowing null
-- propagation from `_` to `some _`, NOT(AND(NULL, INT)) ≠ OR(NOT NULL, NOT INT)).
def deMorganTests : TestSeq :=
  check (cfg := slimCfg) "NOT (a AND b) = (NOT a) OR (NOT b)" (∀ a b : BoolGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .and a.expr b.expr)) ==
    evalExpr [] (.binOp .or (.unaryOp .not a.expr) (.unaryOp .not b.expr))) $
  check (cfg := slimCfg) "NOT (a OR b) = (NOT a) AND (NOT b)" (∀ a b : BoolGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .or a.expr b.expr)) ==
    evalExpr [] (.binOp .and (.unaryOp .not a.expr) (.unaryOp .not b.expr)))

-- ============================================================================
-- Distributivity
-- ============================================================================

def distributivityTests : TestSeq :=
  check (cfg := slimCfg) "AND distributes over OR (left)" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.binOp .or b.expr c.expr)) ==
    evalExpr [] (.binOp .or (.binOp .and a.expr b.expr) (.binOp .and a.expr c.expr))) $
  check (cfg := slimCfg) "OR distributes over AND (left)" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.binOp .and b.expr c.expr)) ==
    evalExpr [] (.binOp .and (.binOp .or a.expr b.expr) (.binOp .or a.expr c.expr)))

-- ============================================================================
-- Identity and Annihilation
-- ============================================================================

def identityTests : TestSeq :=
  check (cfg := slimCfg) "a AND TRUE = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.lit (.bool true))) == evalExpr [] a.expr) $
  check (cfg := slimCfg) "TRUE AND a = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and (.lit (.bool true)) a.expr) == evalExpr [] a.expr) $
  check (cfg := slimCfg) "a OR FALSE = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.lit (.bool false))) == evalExpr [] a.expr) $
  check (cfg := slimCfg) "FALSE OR a = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or (.lit (.bool false)) a.expr) == evalExpr [] a.expr) $
  check (cfg := slimCfg) "a AND FALSE = FALSE" (∀ a : BoundedGroundExpr,
    evalExpr [] (.binOp .and a.expr (.lit (.bool false))) == evalExpr [] (.lit (.bool false))) $
  check (cfg := slimCfg) "a OR TRUE = TRUE" (∀ a : BoundedGroundExpr,
    evalExpr [] (.binOp .or a.expr (.lit (.bool true))) == evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- Idempotence and Complement
-- ============================================================================

def idempotenceTests : TestSeq :=
  check (cfg := slimCfg) "a AND a = a" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr a.expr) == evalExpr [] a.expr) $
  check (cfg := slimCfg) "a OR a = a" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr a.expr) == evalExpr [] a.expr)

def complementTests : TestSeq :=
  check (cfg := slimCfg) "a AND (NOT a) = FALSE" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.unaryOp .not a.expr)) ==
    evalExpr [] (.lit (.bool false))) $
  check (cfg := slimCfg) "a OR (NOT a) = TRUE" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.unaryOp .not a.expr)) ==
    evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- Absorption
-- ============================================================================

def absorptionTests : TestSeq :=
  check (cfg := slimCfg) "a AND (a OR b) = a" (∀ a b : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.binOp .or a.expr b.expr)) == evalExpr [] a.expr) $
  check (cfg := slimCfg) "a OR (a AND b) = a" (∀ a b : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.binOp .and a.expr b.expr)) == evalExpr [] a.expr)

-- ============================================================================
-- Arithmetic Identities (using IntGroundExpr)
-- ============================================================================

def arithmeticTests : TestSeq :=
  check (cfg := slimCfg) "x + 0 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .add e.expr (.lit (.int 0))) == evalExpr [] e.expr) $
  check (cfg := slimCfg) "0 + x = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .add (.lit (.int 0)) e.expr) == evalExpr [] e.expr) $
  check (cfg := slimCfg) "x * 1 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul e.expr (.lit (.int 1))) == evalExpr [] e.expr) $
  check (cfg := slimCfg) "1 * x = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul (.lit (.int 1)) e.expr) == evalExpr [] e.expr) $
  check (cfg := slimCfg) "x * 0 = 0" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul e.expr (.lit (.int 0))) == evalExpr [] (.lit (.int 0))) $
  check (cfg := slimCfg) "x - 0 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .sub e.expr (.lit (.int 0))) == evalExpr [] e.expr)

-- ============================================================================
-- Comparison Flips
-- ============================================================================

def comparisonFlipTests : TestSeq :=
  check (cfg := slimCfg) "NOT (a = b) = (a <> b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .eq a.expr b.expr)) ==
    evalExpr [] (.binOp .ne a.expr b.expr)) $
  check (cfg := slimCfg) "NOT (a <> b) = (a = b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .ne a.expr b.expr)) ==
    evalExpr [] (.binOp .eq a.expr b.expr)) $
  check (cfg := slimCfg) "a < b = b > a" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .lt a.expr b.expr) ==
    evalExpr [] (.binOp .gt b.expr a.expr)) $
  check (cfg := slimCfg) "a <= b = b >= a" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .le a.expr b.expr) ==
    evalExpr [] (.binOp .ge b.expr a.expr)) $
  check (cfg := slimCfg) "NOT (a < b) = (a >= b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .lt a.expr b.expr)) ==
    evalExpr [] (.binOp .ge a.expr b.expr)) $
  check (cfg := slimCfg) "NOT (a > b) = (a <= b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .gt a.expr b.expr)) ==
    evalExpr [] (.binOp .le a.expr b.expr))

-- ============================================================================
-- Double Negation
-- ============================================================================

def doubleNegTests : TestSeq :=
  check (cfg := slimCfg) "NOT (NOT a) = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.unaryOp .not (.unaryOp .not a.expr)) == evalExpr [] a.expr)

-- ============================================================================
-- All expression algebra tests
-- ============================================================================

def allTests : TestSeq :=
  group "Commutativity" commutativityTests $
  group "Associativity" associativityTests $
  group "De Morgan" deMorganTests $
  group "Distributivity" distributivityTests $
  group "Identity/Annihilation" identityTests $
  group "Idempotence" idempotenceTests $
  group "Complement" complementTests $
  group "Absorption" absorptionTests $
  group "Arithmetic" arithmeticTests $
  group "Comparison Flips" comparisonFlipTests $
  group "Double Negation" doubleNegTests

end ExprAlgebra
