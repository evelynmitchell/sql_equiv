/-
  Property-based tests for optimizer correctness.

  These are the highest-value tests: optimizeExpr and normalizeExprCanonical
  are axiomatized (not proven), so SlimCheck is the primary defense against
  optimizer bugs that silently change expression semantics.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace OptimizerEquiv

-- ============================================================================
-- optimizeExpr preserves semantics
-- ============================================================================

def optimizeExprTests : TestSeq :=
  check "optimizeExpr preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (optimizeExpr e.expr) == evalExpr [] e.expr)

-- ============================================================================
-- normalizeExprCanonical preserves semantics and is idempotent
-- ============================================================================

def normalizeTests : TestSeq :=
  check "normalizeExprCanonical preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (normalizeExprCanonical e.expr) == evalExpr [] e.expr) $
  check "normalizeExprCanonical is idempotent" (∀ e : BoundedGroundExpr,
    normalizeExprCanonical (normalizeExprCanonical e.expr) ==
    normalizeExprCanonical e.expr)

-- ============================================================================
-- Regression: identity laws must not fire on non-boolean operands
-- ============================================================================

-- Non-boolean int literals
private def intAndTrue := Expr.binOp .and (.lit (.int 4)) (.lit (.bool true))
private def trueAndInt := Expr.binOp .and (.lit (.bool true)) (.lit (.int 4))
private def intOrFalse := Expr.binOp .or (.lit (.int 4)) (.lit (.bool false))
private def falseOrInt := Expr.binOp .or (.lit (.bool false)) (.lit (.int 4))
-- NULL literals
private def nullAndTrue := Expr.binOp .and (.lit (.null none)) (.lit (.bool true))
private def trueAndNull := Expr.binOp .and (.lit (.bool true)) (.lit (.null none))
private def nullOrFalse := Expr.binOp .or (.lit (.null none)) (.lit (.bool false))
private def falseOrNull := Expr.binOp .or (.lit (.bool false)) (.lit (.null none))
-- Non-literal non-boolean (arithmetic expression)
private def arithAndTrue := Expr.binOp .and (.binOp .add (.lit (.int 1)) (.lit (.int 2))) (.lit (.bool true))
private def trueAndArith := Expr.binOp .and (.lit (.bool true)) (.binOp .add (.lit (.int 1)) (.lit (.int 2)))
private def arithOrFalse := Expr.binOp .or (.binOp .add (.lit (.int 1)) (.lit (.int 2))) (.lit (.bool false))
private def falseOrArith := Expr.binOp .or (.lit (.bool false)) (.binOp .add (.lit (.int 1)) (.lit (.int 2)))

def identityLawRegressionTests : TestSeq :=
  -- Int literals
  test "int AND TRUE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws intAndTrue) == evalExpr [] intAndTrue) $
  test "TRUE AND int: identity law must not fire" (
    evalExpr [] (applyIdentityLaws trueAndInt) == evalExpr [] trueAndInt) $
  test "int OR FALSE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws intOrFalse) == evalExpr [] intOrFalse) $
  test "FALSE OR int: identity law must not fire" (
    evalExpr [] (applyIdentityLaws falseOrInt) == evalExpr [] falseOrInt) $
  -- NULL literals
  test "NULL AND TRUE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws nullAndTrue) == evalExpr [] nullAndTrue) $
  test "TRUE AND NULL: identity law must not fire" (
    evalExpr [] (applyIdentityLaws trueAndNull) == evalExpr [] trueAndNull) $
  test "NULL OR FALSE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws nullOrFalse) == evalExpr [] nullOrFalse) $
  test "FALSE OR NULL: identity law must not fire" (
    evalExpr [] (applyIdentityLaws falseOrNull) == evalExpr [] falseOrNull) $
  -- Non-literal non-boolean (arithmetic sub-expressions)
  test "(1+2) AND TRUE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws arithAndTrue) == evalExpr [] arithAndTrue) $
  test "TRUE AND (1+2): identity law must not fire" (
    evalExpr [] (applyIdentityLaws trueAndArith) == evalExpr [] trueAndArith) $
  test "(1+2) OR FALSE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws arithOrFalse) == evalExpr [] arithOrFalse) $
  test "FALSE OR (1+2): identity law must not fire" (
    evalExpr [] (applyIdentityLaws falseOrArith) == evalExpr [] falseOrArith)

-- ============================================================================
-- Regression: simplifyArithmetic null propagation / type mismatch / div-by-zero
-- ============================================================================

-- Null propagation: NULL * 0 must stay NULL, not become 0
private def nullMulZero := Expr.binOp .mul (.lit (.null none)) (.lit (.int 0))
private def zeroMulNull := Expr.binOp .mul (.lit (.int 0)) (.lit (.null none))
private def zeroDivNull := Expr.binOp .div (.lit (.int 0)) (.lit (.null none))
-- Division by zero: 0 / 0 must not become 0
private def zeroDivZero := Expr.binOp .div (.lit (.int 0)) (.lit (.int 0))
-- Type mismatches on identity arms
private def stringAddZero := Expr.binOp .add (.lit (.string "hi")) (.lit (.int 0))
private def zeroAddString := Expr.binOp .add (.lit (.int 0)) (.lit (.string "hi"))
private def boolSubZero := Expr.binOp .sub (.lit (.bool true)) (.lit (.int 0))
private def nullMulOne := Expr.binOp .mul (.lit (.null none)) (.lit (.int 1))
private def oneMulBool := Expr.binOp .mul (.lit (.int 1)) (.lit (.bool false))
private def stringDivOne := Expr.binOp .div (.lit (.string "x")) (.lit (.int 1))

def arithmeticSoundnessTests : TestSeq :=
  -- Null propagation
  test "NULL*0: annihilation must not fire" (
    evalExpr [] (simplifyArithmetic nullMulZero) == evalExpr [] nullMulZero) $
  test "0*NULL: annihilation must not fire" (
    evalExpr [] (simplifyArithmetic zeroMulNull) == evalExpr [] zeroMulNull) $
  test "0/NULL: must preserve null propagation" (
    evalExpr [] (optimizeExpr zeroDivNull) == evalExpr [] zeroDivNull) $
  -- Division by zero
  test "0/0: must not rewrite to 0" (
    evalExpr [] (optimizeExpr zeroDivZero) == evalExpr [] zeroDivZero) $
  -- Type mismatches on identity arms
  test "string+0: identity must not fire" (
    evalExpr [] (simplifyArithmetic stringAddZero) == evalExpr [] stringAddZero) $
  test "0+string: identity must not fire" (
    evalExpr [] (simplifyArithmetic zeroAddString) == evalExpr [] zeroAddString) $
  test "bool-0: identity must not fire" (
    evalExpr [] (simplifyArithmetic boolSubZero) == evalExpr [] boolSubZero) $
  test "NULL*1: identity must not fire" (
    evalExpr [] (simplifyArithmetic nullMulOne) == evalExpr [] nullMulOne) $
  test "1*bool: identity must not fire" (
    evalExpr [] (simplifyArithmetic oneMulBool) == evalExpr [] oneMulBool) $
  test "string/1: identity must not fire" (
    evalExpr [] (simplifyArithmetic stringDivOne) == evalExpr [] stringDivOne)

-- ============================================================================
-- Individual optimizer passes
-- ============================================================================

def optimizerPassTests : TestSeq :=
  check "applyIdentityLaws preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (applyIdentityLaws e.expr) == evalExpr [] e.expr) $
  check "eliminateDoubleNegation preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (eliminateDoubleNegation e.expr) == evalExpr [] e.expr) $
  check "applyDeMorgan preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (applyDeMorgan e.expr) == evalExpr [] e.expr)

-- ============================================================================
-- All optimizer tests
-- ============================================================================

def allTests : TestSeq :=
  group "optimizeExpr" optimizeExprTests $
  group "normalizeExprCanonical" normalizeTests $
  group "Identity Law Regression" identityLawRegressionTests $
  group "Arithmetic Soundness" arithmeticSoundnessTests $
  group "Individual Passes" optimizerPassTests

end OptimizerEquiv
