/-
  Property-based tests for expression ordering laws.

  Tests that exprCompare and valueCompare form total orders
  (reflexive, antisymmetric, transitive), and that exprLt is consistent
  with exprCompare.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace ExprOrdering

-- ============================================================================
-- Helper functions (avoid match inside check — Checkable can't synthesize)
-- ============================================================================

private def orderingConsistent (fwd bwd : Ordering) : Bool :=
  (fwd == .lt && bwd == .gt) || (fwd == .gt && bwd == .lt) || (fwd == .eq && bwd == .eq)

-- ============================================================================
-- exprCompare ordering laws
-- ============================================================================

def exprCompareTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "exprCompare is reflexive" (∀ e : BoundedGroundExpr,
    exprCompare e.expr e.expr == .eq) $
  check (cfg := cfg) "exprCompare is antisymmetric" (∀ a b : BoundedGroundExpr,
    orderingConsistent (exprCompare a.expr b.expr) (exprCompare b.expr a.expr)) $
  check (cfg := cfg) "exprCompare is transitive" (∀ a b c : BoundedGroundExpr,
    !(exprCompare a.expr b.expr != .gt && exprCompare b.expr c.expr != .gt) ||
    (exprCompare a.expr c.expr != .gt)) $
  check (cfg := cfg) "exprLt consistent with exprCompare" (∀ a b : BoundedGroundExpr,
    exprLt a.expr b.expr == (exprCompare a.expr b.expr == .lt))

-- ============================================================================
-- valueCompare ordering laws
-- ============================================================================

def valueCompareTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "valueCompare is reflexive" (∀ v : Value,
    valueCompare v v == .eq) $
  check (cfg := cfg) "valueCompare is antisymmetric" (∀ a b : Value,
    orderingConsistent (valueCompare a b) (valueCompare b a)) $
  check (cfg := cfg) "valueCompare is transitive" (∀ a b c : Value,
    !(valueCompare a b != .gt && valueCompare b c != .gt) ||
    (valueCompare a c != .gt))

-- ============================================================================
-- exprWeight monotonicity
-- ============================================================================

def exprWeightTests : TestSeq :=
  test "lit weight = 0" (exprWeight (.lit (.int 1)) == 0) $
  test "col weight = 1" (exprWeight (.col ⟨none, "x"⟩) == 1) $
  test "binOp weight = 2" (exprWeight (.binOp .add (.lit (.int 1)) (.lit (.int 2))) == 2) $
  test "unaryOp weight = 2" (exprWeight (.unaryOp .not (.lit (.bool true))) == 2) $
  test "lit < col" (exprWeight (.lit (.int 1)) < exprWeight (.col ⟨none, "x"⟩)) $
  test "col < binOp" (exprWeight (.col ⟨none, "x"⟩) < exprWeight (.binOp .add (.lit (.int 1)) (.lit (.int 2))))

-- ============================================================================
-- All ordering tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "exprCompare" (exprCompareTests cfg) $
  group "valueCompare" (valueCompareTests cfg) $
  group "exprWeight" exprWeightTests

end ExprOrdering
