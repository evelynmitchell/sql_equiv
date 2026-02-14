/-
  Property-based tests for constant folding correctness.

  Tests that constantFoldBinOp, constantFoldUnaryOp, and simplifyExprOnce
  preserve expression semantics, and that the fold helper functions agree
  with evalBinOp on literal inputs.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace ConstantFolding

-- ============================================================================
-- Helper functions (avoid match inside check — Checkable can't synthesize)
-- ============================================================================

private def foldArithAgrees (op : BinOp) (l r : Value) : Bool :=
  match foldArithmetic op l r with
  | some v => evalBinOp op (some l) (some r) == some v
  | none => true

private def foldCompAgrees (op : BinOp) (l r : Value) : Bool :=
  match foldComparison op l r with
  | some v => evalBinOp op (some l) (some r) == some v
  | none => true

private def foldLogAgrees (op : BinOp) (l r : Value) : Bool :=
  match foldLogical op l r with
  | some v => evalBinOp op (some l) (some r) == some v
  | none => true

-- ============================================================================
-- Constant fold preserves semantics
-- ============================================================================

def constantFoldTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "constantFoldBinOp preserves semantics" (∀ op : BinOp, ∀ l r : BoundedGroundExpr,
    evalExpr [] (constantFoldBinOp op l.expr r.expr) ==
    evalExpr [] (.binOp op l.expr r.expr)) $
  check (cfg := cfg) "constantFoldUnaryOp preserves semantics" (∀ op : UnaryOp, ∀ e : BoundedGroundExpr,
    evalExpr [] (constantFoldUnaryOp op e.expr) ==
    evalExpr [] (.unaryOp op e.expr)) $
  check (cfg := cfg) "simplifyExprOnce preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (simplifyExprOnce e.expr) == evalExpr [] e.expr)

-- ============================================================================
-- Fold helpers agree with evalBinOp
-- ============================================================================

def foldAgreementTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "foldArithmetic agrees with evalBinOp"
    (∀ op : BinOp, ∀ l r : Value, foldArithAgrees op l r) $
  check (cfg := cfg) "foldComparison agrees with evalBinOp"
    (∀ op : BinOp, ∀ l r : Value, foldCompAgrees op l r) $
  check (cfg := cfg) "foldLogical agrees with evalBinOp"
    (∀ op : BinOp, ∀ l r : Value, foldLogAgrees op l r)

-- ============================================================================
-- Idempotence and isConstant/getLitValue agreement
-- ============================================================================

def idempotenceTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "simplifyExprOnce is idempotent" (∀ e : BoundedGroundExpr,
    simplifyExprOnce (simplifyExprOnce e.expr) == simplifyExprOnce e.expr) $
  check (cfg := cfg) "isConstant iff getLitValue.isSome" (∀ e : BoundedGroundExpr,
    isConstant e.expr == (getLitValue e.expr).isSome)

-- ============================================================================
-- All constant folding tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Constant Fold Semantics" (constantFoldTests cfg) $
  group "Fold Agreement" (foldAgreementTests cfg) $
  group "Idempotence" (idempotenceTests cfg)

end ConstantFolding
