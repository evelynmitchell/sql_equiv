/-
  Property-based and unit tests for predicate pushdown correctness.

  Tests canPushLeftThroughJoin, canPushRightThroughJoin, canPushPastProjection,
  pushPredicateDown, getReferencedColumns, and transformColumnRefs.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace PredicatePushdown

-- ============================================================================
-- canPushLeftThroughJoin / canPushRightThroughJoin
-- ============================================================================

def joinPushabilityTests : TestSeq :=
  -- Left pushability
  test "canPushLeft: inner = true" (canPushLeftThroughJoin .inner == true) $
  test "canPushLeft: cross = true" (canPushLeftThroughJoin .cross == true) $
  test "canPushLeft: left = true" (canPushLeftThroughJoin .left == true) $
  test "canPushLeft: right = false" (canPushLeftThroughJoin .right == false) $
  test "canPushLeft: full = false" (canPushLeftThroughJoin .full == false) $
  -- Right pushability
  test "canPushRight: inner = true" (canPushRightThroughJoin .inner == true) $
  test "canPushRight: cross = true" (canPushRightThroughJoin .cross == true) $
  test "canPushRight: right = true" (canPushRightThroughJoin .right == true) $
  test "canPushRight: left = false" (canPushRightThroughJoin .left == false) $
  test "canPushRight: full = false" (canPushRightThroughJoin .full == false)

-- ============================================================================
-- getReferencedColumns
-- ============================================================================

def getReferencedColumnsTests : TestSeq :=
  test "col ref returns that column" (
    getReferencedColumns (.col ⟨none, "x"⟩) == [⟨none, "x"⟩]) $
  test "literal returns empty" (
    getReferencedColumns (.lit (.int 42)) == []) $
  test "binOp includes both sides" (
    let cols := getReferencedColumns (.binOp .eq (.col ⟨none, "x"⟩) (.col ⟨none, "y"⟩))
    cols.length == 2 &&
    cols.any (· == ⟨none, "x"⟩) &&
    cols.any (· == ⟨none, "y"⟩)) $
  test "unaryOp preserves inner columns" (
    getReferencedColumns (.unaryOp .not (.col ⟨some "t", "z"⟩)) == [⟨some "t", "z"⟩])

-- ============================================================================
-- canPushPastProjection
-- ============================================================================

def canPushPastProjectionTests : TestSeq :=
  test "push past projection with matching column" (
    let pred := Expr.col ⟨none, "x"⟩
    let items := [SelectItem.exprItem (.col ⟨none, "x"⟩) (some "x")]
    canPushPastProjection pred items == true) $
  test "star projection does not expose columns for pushdown" (
    let pred := Expr.col ⟨none, "x"⟩
    let items := [SelectItem.star none]
    canPushPastProjection pred items == false) $
  test "cannot push with missing column" (
    let pred := Expr.col ⟨none, "x"⟩
    let items := [SelectItem.exprItem (.col ⟨none, "y"⟩) (some "y")]
    canPushPastProjection pred items == false) $
  test "push literal (no columns referenced)" (
    let pred := Expr.lit (.bool true)
    let items := [SelectItem.exprItem (.col ⟨none, "x"⟩) (some "x")]
    canPushPastProjection pred items == true)

-- ============================================================================
-- transformColumnRefs
-- ============================================================================

def transformColumnRefsTests : TestSeq :=
  test "transforms qualified column to inner expr" (
    let expr := Expr.col ⟨some "sub", "id"⟩
    let items := [SelectItem.exprItem (.col ⟨some "t", "id"⟩) (some "id")]
    transformColumnRefs expr "sub" items == Expr.col ⟨some "t", "id"⟩) $
  test "leaves unqualified column unchanged" (
    let expr := Expr.col ⟨none, "id"⟩
    let items := [SelectItem.exprItem (.col ⟨some "t", "id"⟩) (some "id")]
    transformColumnRefs expr "sub" items == Expr.col ⟨none, "id"⟩) $
  test "leaves differently-qualified column unchanged" (
    let expr := Expr.col ⟨some "other", "id"⟩
    let items := [SelectItem.exprItem (.col ⟨some "t", "id"⟩) (some "id")]
    transformColumnRefs expr "sub" items == Expr.col ⟨some "other", "id"⟩)

-- ============================================================================
-- pushPredicateDown on single table
-- ============================================================================

def pushPredicateDownTests : TestSeq :=
  test "pushdown on single table keeps predicate in remaining" (
    let tref : TableRef := ⟨"t", some "t"⟩
    let from_ := FromClause.table tref
    let pred := Expr.binOp .eq (.col ⟨some "t", "x"⟩) (.lit (.int 1))
    let result := pushPredicateDown pred from_
    result.remaining.isSome) $
  test "pushdown on single table preserves from clause" (
    let tref : TableRef := ⟨"t", some "t"⟩
    let from_ := FromClause.table tref
    let pred := Expr.binOp .eq (.col ⟨some "t", "x"⟩) (.lit (.int 1))
    let result := pushPredicateDown pred from_
    result.pushedFrom == from_)

-- ============================================================================
-- Property tests using ColumnGroundExpr
-- ============================================================================

private def colRefsSubset (outer inner : List ColumnRef) : Bool :=
  inner.all fun c => outer.any (· == c)

private def colRefsFromSubexprs (e : Expr) : Bool :=
  let cols := getReferencedColumns e
  match e with
  | .binOp _ l r =>
    colRefsSubset cols (getReferencedColumns l) &&
    colRefsSubset cols (getReferencedColumns r)
  | .unaryOp _ inner => colRefsSubset cols (getReferencedColumns inner)
  | _ => true

def columnExprPropertyTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "getReferencedColumns includes col refs from subexprs"
    (∀ e : ColumnGroundExpr, colRefsFromSubexprs e.expr)

-- ============================================================================
-- All predicate pushdown tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Join Pushability" joinPushabilityTests $
  group "getReferencedColumns" getReferencedColumnsTests $
  group "canPushPastProjection" canPushPastProjectionTests $
  group "transformColumnRefs" transformColumnRefsTests $
  group "pushPredicateDown" pushPredicateDownTests $
  group "Column Expr Properties" (columnExprPropertyTests cfg)

end PredicatePushdown
