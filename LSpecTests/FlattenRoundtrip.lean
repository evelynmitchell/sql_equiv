/-
  Property-based tests for flatten/unflatten roundtrip correctness.

  Tests that flattenAnd/flattenOr always produce nonempty lists, and that
  unflattenAnd/unflattenOr reconstruct semantically equivalent expressions.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace FlattenRoundtrip

-- ============================================================================
-- Helper functions (avoid match inside check — Checkable can't synthesize)
-- ============================================================================

private def andRoundtripOk (e : Expr) : Bool :=
  match unflattenAnd (flattenAnd e) with
  | some e' => evalExpr [] e' == evalExpr [] e
  | none => false

private def orRoundtripOk (e : Expr) : Bool :=
  match unflattenOr (flattenOr e) with
  | some e' => evalExpr [] e' == evalExpr [] e
  | none => false

-- ============================================================================
-- Nonemptiness
-- ============================================================================

def nonemptyTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "flattenAnd is nonempty" (∀ e : BoundedGroundExpr,
    (flattenAnd e.expr).length > 0) $
  check (cfg := cfg) "flattenOr is nonempty" (∀ e : BoundedGroundExpr,
    (flattenOr e.expr).length > 0)

-- ============================================================================
-- Roundtrip preserves semantics
-- ============================================================================

def roundtripTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "unflattenAnd (flattenAnd e) preserves semantics"
    (∀ e : BoundedGroundExpr, andRoundtripOk e.expr) $
  check (cfg := cfg) "unflattenOr (flattenOr e) preserves semantics"
    (∀ e : BoundedGroundExpr, orRoundtripOk e.expr)

-- ============================================================================
-- Stability: literals flatten to singleton
-- ============================================================================

def stabilityTests : TestSeq :=
  test "flattenAnd on literal is singleton" (
    (flattenAnd (.lit (.int 42))).length == 1) $
  test "flattenOr on literal is singleton" (
    (flattenOr (.lit (.bool true))).length == 1)

-- ============================================================================
-- All flatten roundtrip tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Nonemptiness" (nonemptyTests cfg) $
  group "Roundtrip Semantics" (roundtripTests cfg) $
  group "Stability" stabilityTests

end FlattenRoundtrip
