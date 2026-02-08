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
  check "AND commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .and a.expr b.expr) == evalExpr [] (.binOp .and b.expr a.expr)) $
  check "OR commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .or a.expr b.expr) == evalExpr [] (.binOp .or b.expr a.expr)) $
  check "ADD commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .add a.expr b.expr) == evalExpr [] (.binOp .add b.expr a.expr)) $
  check "MUL commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .mul a.expr b.expr) == evalExpr [] (.binOp .mul b.expr a.expr)) $
  check "EQ commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .eq a.expr b.expr) == evalExpr [] (.binOp .eq b.expr a.expr))

-- ============================================================================
-- Associativity
-- ============================================================================

def associativityTests : TestSeq :=
  check "AND is associative" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .and (.binOp .and a.expr b.expr) c.expr) ==
    evalExpr [] (.binOp .and a.expr (.binOp .and b.expr c.expr))) $
  check "OR is associative" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .or (.binOp .or a.expr b.expr) c.expr) ==
    evalExpr [] (.binOp .or a.expr (.binOp .or b.expr c.expr)))

-- ============================================================================
-- De Morgan's Laws
-- ============================================================================

def deMorganTests : TestSeq :=
  check "NOT (a AND b) = (NOT a) OR (NOT b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .and a.expr b.expr)) ==
    evalExpr [] (.binOp .or (.unaryOp .not a.expr) (.unaryOp .not b.expr))) $
  check "NOT (a OR b) = (NOT a) AND (NOT b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .or a.expr b.expr)) ==
    evalExpr [] (.binOp .and (.unaryOp .not a.expr) (.unaryOp .not b.expr)))

-- ============================================================================
-- Distributivity
-- ============================================================================

def distributivityTests : TestSeq :=
  check "AND distributes over OR (left)" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.binOp .or b.expr c.expr)) ==
    evalExpr [] (.binOp .or (.binOp .and a.expr b.expr) (.binOp .and a.expr c.expr))) $
  check "OR distributes over AND (left)" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.binOp .and b.expr c.expr)) ==
    evalExpr [] (.binOp .and (.binOp .or a.expr b.expr) (.binOp .or a.expr c.expr)))

-- ============================================================================
-- Identity and Annihilation
-- ============================================================================

def identityTests : TestSeq :=
  check "a AND TRUE = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.lit (.bool true))) == evalExpr [] a.expr) $
  check "TRUE AND a = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and (.lit (.bool true)) a.expr) == evalExpr [] a.expr) $
  check "a OR FALSE = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.lit (.bool false))) == evalExpr [] a.expr) $
  check "FALSE OR a = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or (.lit (.bool false)) a.expr) == evalExpr [] a.expr) $
  check "a AND FALSE = FALSE" (∀ a : BoundedGroundExpr,
    evalExpr [] (.binOp .and a.expr (.lit (.bool false))) == evalExpr [] (.lit (.bool false))) $
  check "a OR TRUE = TRUE" (∀ a : BoundedGroundExpr,
    evalExpr [] (.binOp .or a.expr (.lit (.bool true))) == evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- Idempotence and Complement
-- ============================================================================

def idempotenceTests : TestSeq :=
  check "a AND a = a" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr a.expr) == evalExpr [] a.expr) $
  check "a OR a = a" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr a.expr) == evalExpr [] a.expr)

def complementTests : TestSeq :=
  check "a AND (NOT a) = FALSE" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.unaryOp .not a.expr)) ==
    evalExpr [] (.lit (.bool false))) $
  check "a OR (NOT a) = TRUE" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.unaryOp .not a.expr)) ==
    evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- Absorption
-- ============================================================================

def absorptionTests : TestSeq :=
  check "a AND (a OR b) = a" (∀ a b : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.binOp .or a.expr b.expr)) == evalExpr [] a.expr) $
  check "a OR (a AND b) = a" (∀ a b : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.binOp .and a.expr b.expr)) == evalExpr [] a.expr)

-- ============================================================================
-- Arithmetic Identities (using IntGroundExpr)
-- ============================================================================

def arithmeticTests : TestSeq :=
  check "x + 0 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .add e.expr (.lit (.int 0))) == evalExpr [] e.expr) $
  check "0 + x = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .add (.lit (.int 0)) e.expr) == evalExpr [] e.expr) $
  check "x * 1 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul e.expr (.lit (.int 1))) == evalExpr [] e.expr) $
  check "1 * x = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul (.lit (.int 1)) e.expr) == evalExpr [] e.expr) $
  check "x * 0 = 0" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul e.expr (.lit (.int 0))) == evalExpr [] (.lit (.int 0))) $
  check "x - 0 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .sub e.expr (.lit (.int 0))) == evalExpr [] e.expr)

-- ============================================================================
-- Comparison Flips
-- ============================================================================

def comparisonFlipTests : TestSeq :=
  check "NOT (a = b) = (a <> b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .eq a.expr b.expr)) ==
    evalExpr [] (.binOp .ne a.expr b.expr)) $
  check "NOT (a <> b) = (a = b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .ne a.expr b.expr)) ==
    evalExpr [] (.binOp .eq a.expr b.expr)) $
  check "a < b = b > a" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .lt a.expr b.expr) ==
    evalExpr [] (.binOp .gt b.expr a.expr)) $
  check "a <= b = b >= a" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .le a.expr b.expr) ==
    evalExpr [] (.binOp .ge b.expr a.expr)) $
  check "NOT (a < b) = (a >= b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .lt a.expr b.expr)) ==
    evalExpr [] (.binOp .ge a.expr b.expr)) $
  check "NOT (a > b) = (a <= b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .gt a.expr b.expr)) ==
    evalExpr [] (.binOp .le a.expr b.expr))

-- ============================================================================
-- Double Negation
-- ============================================================================

def doubleNegTests : TestSeq :=
  check "NOT (NOT a) = a (booleans)" (∀ a : BoolGroundExpr,
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
