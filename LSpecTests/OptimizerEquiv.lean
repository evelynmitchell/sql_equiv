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

private def intAndTrue := Expr.binOp .and (.lit (.int 4)) (.lit (.bool true))
private def trueAndInt := Expr.binOp .and (.lit (.bool true)) (.lit (.int 4))
private def intOrFalse := Expr.binOp .or (.lit (.int 4)) (.lit (.bool false))
private def falseOrInt := Expr.binOp .or (.lit (.bool false)) (.lit (.int 4))

def identityLawRegressionTests : TestSeq :=
  test "int AND TRUE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws intAndTrue) == evalExpr [] intAndTrue) $
  test "TRUE AND int: identity law must not fire" (
    evalExpr [] (applyIdentityLaws trueAndInt) == evalExpr [] trueAndInt) $
  test "int OR FALSE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws intOrFalse) == evalExpr [] intOrFalse) $
  test "FALSE OR int: identity law must not fire" (
    evalExpr [] (applyIdentityLaws falseOrInt) == evalExpr [] falseOrInt)

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
  group "Individual Passes" optimizerPassTests

end OptimizerEquiv
