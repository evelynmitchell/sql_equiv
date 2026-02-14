/-
  Property-based and exhaustive tests for constant folding correctness.

  Tests that constantFoldBinOp, constantFoldUnaryOp, and simplifyExprOnce
  preserve expression semantics, and that the fold helper functions agree
  with evalBinOp on literal inputs. Exhaustive tests cover all BinOp × Value
  and UnaryOp × Value combinations for guaranteed full combinatorial coverage.
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
-- Constant fold preserves semantics (random)
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
-- Fold helpers are sound w.r.t. evalBinOp (random)
-- (soundness-only: `none` means the fold doesn't handle that op/type combo,
-- so we only check that when a fold *does* produce a value, it matches eval)
-- ============================================================================

def foldAgreementTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "foldArithmetic sound w.r.t. evalBinOp (none = not handled)"
    (∀ op : BinOp, ∀ l r : Value, foldArithAgrees op l r) $
  check (cfg := cfg) "foldComparison sound w.r.t. evalBinOp (none = not handled)"
    (∀ op : BinOp, ∀ l r : Value, foldCompAgrees op l r) $
  check (cfg := cfg) "foldLogical sound w.r.t. evalBinOp (none = not handled)"
    (∀ op : BinOp, ∀ l r : Value, foldLogAgrees op l r)

-- ============================================================================
-- Exhaustive fold tests: all BinOp × representative Value combinations
-- ============================================================================

/-- Representative values covering every Value constructor and edge cases. -/
private def reprValues : List Value :=
  [.null none, .bool true, .bool false,
   .int 0, .int 1, .int (-1), .int 42,
   .string "", .string "hello"]

private def allBinOps : List BinOp :=
  [.add, .sub, .mul, .div, .mod, .eq, .ne, .lt, .le, .gt, .ge, .and, .or, .concat, .like]

private def allUnaryOps : List UnaryOp :=
  [.not, .neg, .isNull, .isNotNull]

/-- Test that constantFoldBinOp preserves semantics for a single (op, l, r) triple. -/
private def binOpFoldOk (op : BinOp) (l r : Value) : Bool :=
  evalExpr [] (constantFoldBinOp op (.lit l) (.lit r)) ==
  evalExpr [] (.binOp op (.lit l) (.lit r))

/-- Test that constantFoldUnaryOp preserves semantics for a single (op, v) pair. -/
private def unaryOpFoldOk (op : UnaryOp) (v : Value) : Bool :=
  evalExpr [] (constantFoldUnaryOp op (.lit v)) ==
  evalExpr [] (.unaryOp op (.lit v))

/-- Run one test per (op, l, r) triple. 15 ops × 9 values × 9 values = 1,215 tests. -/
private def exhaustiveBinOpFoldTests : TestSeq :=
  allBinOps.foldl (fun acc op =>
    reprValues.foldl (fun acc l =>
      reprValues.foldl (fun acc r =>
        test s!"constantFold {repr op} ({repr l}, {repr r})" (binOpFoldOk op l r) acc
      ) acc
    ) acc
  ) .done

/-- Run one test per (op, v) pair. 4 ops × 9 values = 36 tests. -/
private def exhaustiveUnaryOpFoldTests : TestSeq :=
  allUnaryOps.foldl (fun acc op =>
    reprValues.foldl (fun acc v =>
      test s!"constantFoldUnary {repr op} ({repr v})" (unaryOpFoldOk op v) acc
    ) acc
  ) .done

/-- Check all three fold helpers agree with evalBinOp for a single triple. -/
private def allFoldsAgree (op : BinOp) (l r : Value) : Bool :=
  foldArithAgrees op l r && foldCompAgrees op l r && foldLogAgrees op l r

/-- Run one test per (op, l, r) checking all fold helpers. 15 × 9 × 9 = 1,215 tests. -/
private def exhaustiveFoldAgreementTests : TestSeq :=
  allBinOps.foldl (fun acc op =>
    reprValues.foldl (fun acc l =>
      reprValues.foldl (fun acc r =>
        test s!"folds agree {repr op} ({repr l}, {repr r})" (allFoldsAgree op l r) acc
      ) acc
    ) acc
  ) .done

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
  group "Fold Agreement (random)" (foldAgreementTests cfg) $
  group "Idempotence" (idempotenceTests cfg) $
  group "Exhaustive BinOp Fold" exhaustiveBinOpFoldTests $
  group "Exhaustive UnaryOp Fold" exhaustiveUnaryOpFoldTests $
  group "Exhaustive Fold Agreement" exhaustiveFoldAgreementTests

end ConstantFolding
