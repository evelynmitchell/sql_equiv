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
-- Per-op stratified helpers (avoid match inside check — Checkable can't synth)
-- ============================================================================

private def constantFoldBinOpOk (op : BinOp) (l r : BoundedGroundExpr) : Bool :=
  evalExpr [] (constantFoldBinOp op l.expr r.expr) ==
  evalExpr [] (.binOp op l.expr r.expr)

private def constantFoldUnaryOpOk (op : UnaryOp) (e : BoundedGroundExpr) : Bool :=
  evalExpr [] (constantFoldUnaryOp op e.expr) ==
  evalExpr [] (.unaryOp op e.expr)

-- ============================================================================
-- Per-op constantFoldBinOp: each op gets full sample budget on Expr × Expr
-- ============================================================================

def constantFoldBinOpTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "constantFoldBinOp .add" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .add l r) $
  check (cfg := cfg) "constantFoldBinOp .sub" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .sub l r) $
  check (cfg := cfg) "constantFoldBinOp .mul" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .mul l r) $
  check (cfg := cfg) "constantFoldBinOp .div" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .div l r) $
  check (cfg := cfg) "constantFoldBinOp .mod" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .mod l r) $
  check (cfg := cfg) "constantFoldBinOp .eq" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .eq l r) $
  check (cfg := cfg) "constantFoldBinOp .ne" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .ne l r) $
  check (cfg := cfg) "constantFoldBinOp .lt" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .lt l r) $
  check (cfg := cfg) "constantFoldBinOp .le" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .le l r) $
  check (cfg := cfg) "constantFoldBinOp .gt" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .gt l r) $
  check (cfg := cfg) "constantFoldBinOp .ge" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .ge l r) $
  check (cfg := cfg) "constantFoldBinOp .and" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .and l r) $
  check (cfg := cfg) "constantFoldBinOp .or" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .or l r) $
  check (cfg := cfg) "constantFoldBinOp .concat" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .concat l r) $
  check (cfg := cfg) "constantFoldBinOp .like" (∀ l r : BoundedGroundExpr, constantFoldBinOpOk .like l r)

-- ============================================================================
-- Per-op constantFoldUnaryOp: each op gets full sample budget
-- ============================================================================

def constantFoldUnaryOpTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "constantFoldUnaryOp .not" (∀ e : BoundedGroundExpr, constantFoldUnaryOpOk .not e) $
  check (cfg := cfg) "constantFoldUnaryOp .neg" (∀ e : BoundedGroundExpr, constantFoldUnaryOpOk .neg e) $
  check (cfg := cfg) "constantFoldUnaryOp .isNull" (∀ e : BoundedGroundExpr, constantFoldUnaryOpOk .isNull e) $
  check (cfg := cfg) "constantFoldUnaryOp .isNotNull" (∀ e : BoundedGroundExpr, constantFoldUnaryOpOk .isNotNull e)

-- ============================================================================
-- simplifyExprOnce (no op parameter — already gets full budget)
-- ============================================================================

def simplifyExprOnceTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "simplifyExprOnce preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (simplifyExprOnce e.expr) == evalExpr [] e.expr)

-- ============================================================================
-- Per-op fold agreement: only test relevant ops per fold function
-- (soundness-only: `none` means the fold doesn't handle that op/type combo,
-- so we only check that when a fold *does* produce a value, it matches eval)
-- ============================================================================

def foldAgreementTests (cfg : Configuration) : TestSeq :=
  -- foldArithmetic: handles .add, .sub, .mul, .div, .mod, .concat
  check (cfg := cfg) "foldArithmetic .add sound" (∀ l r : Value, foldArithAgrees .add l r) $
  check (cfg := cfg) "foldArithmetic .sub sound" (∀ l r : Value, foldArithAgrees .sub l r) $
  check (cfg := cfg) "foldArithmetic .mul sound" (∀ l r : Value, foldArithAgrees .mul l r) $
  check (cfg := cfg) "foldArithmetic .div sound" (∀ l r : Value, foldArithAgrees .div l r) $
  check (cfg := cfg) "foldArithmetic .mod sound" (∀ l r : Value, foldArithAgrees .mod l r) $
  check (cfg := cfg) "foldArithmetic .concat sound" (∀ l r : Value, foldArithAgrees .concat l r) $
  -- foldComparison: handles .eq, .ne, .lt, .le, .gt, .ge
  check (cfg := cfg) "foldComparison .eq sound" (∀ l r : Value, foldCompAgrees .eq l r) $
  check (cfg := cfg) "foldComparison .ne sound" (∀ l r : Value, foldCompAgrees .ne l r) $
  check (cfg := cfg) "foldComparison .lt sound" (∀ l r : Value, foldCompAgrees .lt l r) $
  check (cfg := cfg) "foldComparison .le sound" (∀ l r : Value, foldCompAgrees .le l r) $
  check (cfg := cfg) "foldComparison .gt sound" (∀ l r : Value, foldCompAgrees .gt l r) $
  check (cfg := cfg) "foldComparison .ge sound" (∀ l r : Value, foldCompAgrees .ge l r) $
  -- foldLogical: handles .and, .or
  check (cfg := cfg) "foldLogical .and sound" (∀ l r : Value, foldLogAgrees .and l r) $
  check (cfg := cfg) "foldLogical .or sound" (∀ l r : Value, foldLogAgrees .or l r)

-- ============================================================================
-- Exhaustive fold tests: all BinOp × representative Value combinations
-- ============================================================================

/-- Representative values covering every Value constructor, typed NULLs, and edge cases. -/
private def reprValues : List Value :=
  [.null none, .null (some .int), .null (some .string), .null (some .bool),
   .bool true, .bool false,
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
  group "Per-Op constantFoldBinOp" (constantFoldBinOpTests cfg) $
  group "Per-Op constantFoldUnaryOp" (constantFoldUnaryOpTests cfg) $
  group "simplifyExprOnce" (simplifyExprOnceTests cfg) $
  group "Per-Op Fold Agreement" (foldAgreementTests cfg) $
  group "Idempotence" (idempotenceTests cfg) $
  group "Exhaustive BinOp Fold" exhaustiveBinOpFoldTests $
  group "Exhaustive UnaryOp Fold" exhaustiveUnaryOpFoldTests $
  group "Exhaustive Fold Agreement" exhaustiveFoldAgreementTests

end ConstantFolding
