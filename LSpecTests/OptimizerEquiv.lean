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
  group "Individual Passes" optimizerPassTests
