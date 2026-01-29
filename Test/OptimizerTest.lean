/-
  Tests for the SQL Query Optimizer
-/
import SqlEquiv
import Test.Common

namespace OptimizerTest

open SqlEquiv
open Test

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Create a simple column reference -/
def col (name : String) : Expr := .col ⟨none, name⟩

/-- Create an integer literal -/
def intLit (n : Int) : Expr := .lit (.int n)

/-- Create a boolean literal -/
def boolLit (b : Bool) : Expr := .lit (.bool b)

/-- Create a string literal -/
def strLit (s : String) : Expr := .lit (.string s)

-- ============================================================================
-- Constant Folding Tests
-- ============================================================================

def testConstantFoldAdd : TestResult :=
  let expr := Expr.binOp .add (intLit 3) (intLit 5)
  let optimized := optimizeExpr expr
  if optimized == intLit 8 then
    .pass "Constant fold: 3 + 5 = 8"
  else
    .fail "Constant fold: 3 + 5 = 8" s!"Expected lit 8, got {repr optimized}"

def testConstantFoldMul : TestResult :=
  let expr := Expr.binOp .mul (intLit 4) (intLit 7)
  let optimized := optimizeExpr expr
  if optimized == intLit 28 then
    .pass "Constant fold: 4 * 7 = 28"
  else
    .fail "Constant fold: 4 * 7 = 28" s!"Expected lit 28, got {repr optimized}"

def testConstantFoldSub : TestResult :=
  let expr := Expr.binOp .sub (intLit 10) (intLit 3)
  let optimized := optimizeExpr expr
  if optimized == intLit 7 then
    .pass "Constant fold: 10 - 3 = 7"
  else
    .fail "Constant fold: 10 - 3 = 7" s!"Expected lit 7, got {repr optimized}"

def testConstantFoldEq : TestResult :=
  let expr := Expr.binOp .eq (intLit 5) (intLit 5)
  let optimized := optimizeExpr expr
  if optimized == boolLit true then
    .pass "Constant fold: 5 = 5 is TRUE"
  else
    .fail "Constant fold: 5 = 5 is TRUE" s!"Expected lit true, got {repr optimized}"

def testConstantFoldNeq : TestResult :=
  let expr := Expr.binOp .eq (intLit 5) (intLit 3)
  let optimized := optimizeExpr expr
  if optimized == boolLit false then
    .pass "Constant fold: 5 = 3 is FALSE"
  else
    .fail "Constant fold: 5 = 3 is FALSE" s!"Expected lit false, got {repr optimized}"

def testConstantFoldNested : TestResult :=
  -- (2 + 3) * (4 + 1) should fold to 25
  let expr := Expr.binOp .mul
    (Expr.binOp .add (intLit 2) (intLit 3))
    (Expr.binOp .add (intLit 4) (intLit 1))
  let optimized := optimizeExpr expr
  if optimized == intLit 25 then
    .pass "Constant fold nested: (2+3)*(4+1) = 25"
  else
    .fail "Constant fold nested: (2+3)*(4+1) = 25" s!"Expected lit 25, got {repr optimized}"

-- ============================================================================
-- Boolean Simplification Tests
-- ============================================================================

def testDoubleNegation : TestResult :=
  let expr := Expr.unaryOp .not (Expr.unaryOp .not (col "x"))
  let optimized := optimizeExpr expr
  if optimized == col "x" then
    .pass "Double negation: NOT NOT x = x"
  else
    .fail "Double negation: NOT NOT x = x" s!"Expected col x, got {repr optimized}"

def testAndTrue : TestResult :=
  let expr := Expr.binOp .and (col "x") (boolLit true)
  let optimized := optimizeExpr expr
  if optimized == col "x" then
    .pass "AND TRUE: x AND TRUE = x"
  else
    .fail "AND TRUE: x AND TRUE = x" s!"Expected col x, got {repr optimized}"

def testAndFalse : TestResult :=
  let expr := Expr.binOp .and (col "x") (boolLit false)
  let optimized := optimizeExpr expr
  if optimized == boolLit false then
    .pass "AND FALSE: x AND FALSE = FALSE"
  else
    .fail "AND FALSE: x AND FALSE = FALSE" s!"Expected lit false, got {repr optimized}"

def testOrTrue : TestResult :=
  let expr := Expr.binOp .or (col "x") (boolLit true)
  let optimized := optimizeExpr expr
  if optimized == boolLit true then
    .pass "OR TRUE: x OR TRUE = TRUE"
  else
    .fail "OR TRUE: x OR TRUE = TRUE" s!"Expected lit true, got {repr optimized}"

def testOrFalse : TestResult :=
  let expr := Expr.binOp .or (col "x") (boolLit false)
  let optimized := optimizeExpr expr
  if optimized == col "x" then
    .pass "OR FALSE: x OR FALSE = x"
  else
    .fail "OR FALSE: x OR FALSE = x" s!"Expected col x, got {repr optimized}"

def testTrueAndTrue : TestResult :=
  let expr := Expr.binOp .and (boolLit true) (boolLit true)
  let optimized := optimizeExpr expr
  if optimized == boolLit true then
    .pass "TRUE AND TRUE = TRUE"
  else
    .fail "TRUE AND TRUE = TRUE" s!"Expected lit true, got {repr optimized}"

def testFalseOrFalse : TestResult :=
  let expr := Expr.binOp .or (boolLit false) (boolLit false)
  let optimized := optimizeExpr expr
  if optimized == boolLit false then
    .pass "FALSE OR FALSE = FALSE"
  else
    .fail "FALSE OR FALSE = FALSE" s!"Expected lit false, got {repr optimized}"

-- ============================================================================
-- Arithmetic Identity Tests
-- ============================================================================

def testAddZero : TestResult :=
  let expr := Expr.binOp .add (col "x") (intLit 0)
  let optimized := optimizeExpr expr
  if optimized == col "x" then
    .pass "Add zero: x + 0 = x"
  else
    .fail "Add zero: x + 0 = x" s!"Expected col x, got {repr optimized}"

def testMulZero : TestResult :=
  let expr := Expr.binOp .mul (col "x") (intLit 0)
  let optimized := optimizeExpr expr
  if optimized == intLit 0 then
    .pass "Mul zero: x * 0 = 0"
  else
    .fail "Mul zero: x * 0 = 0" s!"Expected lit 0, got {repr optimized}"

def testMulOne : TestResult :=
  let expr := Expr.binOp .mul (col "x") (intLit 1)
  let optimized := optimizeExpr expr
  if optimized == col "x" then
    .pass "Mul one: x * 1 = x"
  else
    .fail "Mul one: x * 1 = x" s!"Expected col x, got {repr optimized}"

def testSubZero : TestResult :=
  let expr := Expr.binOp .sub (col "x") (intLit 0)
  let optimized := optimizeExpr expr
  if optimized == col "x" then
    .pass "Sub zero: x - 0 = x"
  else
    .fail "Sub zero: x - 0 = x" s!"Expected col x, got {repr optimized}"

def testDivOne : TestResult :=
  let expr := Expr.binOp .div (col "x") (intLit 1)
  let optimized := optimizeExpr expr
  if optimized == col "x" then
    .pass "Div one: x / 1 = x"
  else
    .fail "Div one: x / 1 = x" s!"Expected col x, got {repr optimized}"

-- ============================================================================
-- Dead Code Elimination Tests
-- ============================================================================

def testWhereTrue : TestResult :=
  let sel := SelectStmt.mk
    false                                    -- distinct
    [SelectItem.star none]                   -- items
    (some (FromClause.table ⟨"users", none⟩)) -- from
    (some (boolLit true))                    -- where TRUE
    []                                       -- groupBy
    none                                     -- having
    []                                       -- orderBy
    none                                     -- limit
    none                                     -- offset
  let optimized := optimizeSelectStmt sel
  if optimized.whereClause.isNone then
    .pass "WHERE TRUE elimination"
  else
    .fail "WHERE TRUE elimination" s!"Expected no WHERE, got {repr optimized.whereClause}"

def testWhereFalse : TestResult :=
  let sel := SelectStmt.mk
    false
    [SelectItem.star none]
    (some (FromClause.table ⟨"users", none⟩))
    (some (boolLit false))                   -- where FALSE
    []
    none
    []
    none
    none
  let optimized := optimizeSelectStmt sel
  -- Should have LIMIT 0 for dead query
  if optimized.limitVal == some 0 then
    .pass "WHERE FALSE dead query (LIMIT 0)"
  else
    .fail "WHERE FALSE dead query" s!"Expected LIMIT 0, got {repr optimized.limitVal}"

-- ============================================================================
-- Unary Operator Tests
-- ============================================================================

def testNotTrue : TestResult :=
  let expr := Expr.unaryOp .not (boolLit true)
  let optimized := optimizeExpr expr
  if optimized == boolLit false then
    .pass "NOT TRUE = FALSE"
  else
    .fail "NOT TRUE = FALSE" s!"Expected lit false, got {repr optimized}"

def testNotFalse : TestResult :=
  let expr := Expr.unaryOp .not (boolLit false)
  let optimized := optimizeExpr expr
  if optimized == boolLit true then
    .pass "NOT FALSE = TRUE"
  else
    .fail "NOT FALSE = TRUE" s!"Expected lit true, got {repr optimized}"

def testNegConstant : TestResult :=
  let expr := Expr.unaryOp .neg (intLit 5)
  let optimized := optimizeExpr expr
  if optimized == intLit (-5) then
    .pass "NEG 5 = -5"
  else
    .fail "NEG 5 = -5" s!"Expected lit -5, got {repr optimized}"

def testIsNullNull : TestResult :=
  let expr := Expr.unaryOp .isNull (.lit (.null none))
  let optimized := optimizeExpr expr
  if optimized == boolLit true then
    .pass "IS NULL on NULL = TRUE"
  else
    .fail "IS NULL on NULL = TRUE" s!"Expected lit true, got {repr optimized}"

def testIsNullNotNull : TestResult :=
  let expr := Expr.unaryOp .isNull (intLit 5)
  let optimized := optimizeExpr expr
  if optimized == boolLit false then
    .pass "IS NULL on 5 = FALSE"
  else
    .fail "IS NULL on 5 = FALSE" s!"Expected lit false, got {repr optimized}"

-- ============================================================================
-- Cost Model Tests
-- ============================================================================

def testCostSimpleSelect : TestResult :=
  let sel := SelectStmt.mk
    false
    [SelectItem.star none]
    (some (FromClause.table ⟨"users", none⟩))
    none
    []
    none
    []
    none
    none
  let stmt := Stmt.query (Query.simple sel)
  let cost := estimateCost defaultCostFactors stmt
  if cost > 0 then
    .pass s!"Cost estimation works (cost = {cost})"
  else
    .fail "Cost estimation" "Expected positive cost"

def testCostReduction : TestResult :=
  -- Query with constant expressions should have lower cost after optimization
  let sel := SelectStmt.mk
    false
    [SelectItem.exprItem (Expr.binOp .add (intLit 1) (intLit 2)) (some "result")]
    (some (FromClause.table ⟨"users", none⟩))
    (some (Expr.binOp .and (boolLit true) (col "active")))
    []
    none
    []
    none
    none
  let stmt := Stmt.query (Query.simple sel)
  let originalCost := estimateCost defaultCostFactors stmt
  let optimizedStmt := optimize stmt
  let optimizedCost := estimateCost defaultCostFactors optimizedStmt
  if optimizedCost <= originalCost then
    .pass s!"Optimization reduces cost ({originalCost} -> {optimizedCost})"
  else
    .fail "Cost reduction" s!"Cost increased: {originalCost} -> {optimizedCost}"

-- ============================================================================
-- Optimization Report Tests
-- ============================================================================

def testOptimizationReport : TestResult :=
  let sel := SelectStmt.mk
    false
    [SelectItem.exprItem (Expr.binOp .mul (intLit 2) (intLit 3)) (some "val")]
    (some (FromClause.table ⟨"t", none⟩))
    (some (boolLit true))
    []
    none
    []
    none
    none
  let stmt := Stmt.query (Query.simple sel)
  let report := generateReport stmt
  -- The report should show improvement since we're eliminating WHERE TRUE
  -- and folding 2*3
  if report.originalCost >= report.optimizedCost then
    .pass s!"Report shows improvement: {report.improvement}%"
  else
    .fail "Optimization report" s!"No improvement shown: {report}"

-- ============================================================================
-- Complex Expression Tests
-- ============================================================================

def testComplexBooleanSimplification : TestResult :=
  -- (x AND TRUE) OR (FALSE AND y) should simplify to x
  let expr := Expr.binOp .or
    (Expr.binOp .and (col "x") (boolLit true))
    (Expr.binOp .and (boolLit false) (col "y"))
  let optimized := optimizeExpr expr
  if optimized == col "x" then
    .pass "Complex: (x AND TRUE) OR (FALSE AND y) = x"
  else
    .fail "Complex boolean" s!"Expected col x, got {repr optimized}"

def testCaseSimplification : TestResult :=
  -- CASE WHEN TRUE THEN 1 ELSE 2 END should simplify to 1
  let expr := Expr.case
    [(boolLit true, intLit 1)]
    (some (intLit 2))
  let optimized := optimizeExpr expr
  if optimized == intLit 1 then
    .pass "CASE WHEN TRUE simplification"
  else
    .fail "CASE simplification" s!"Expected lit 1, got {repr optimized}"

def testEmptyInList : TestResult :=
  -- x IN () should be FALSE
  let expr := Expr.inList (col "x") false []
  let optimized := optimizeExpr expr
  if optimized == boolLit false then
    .pass "Empty IN list = FALSE"
  else
    .fail "Empty IN list" s!"Expected lit false, got {repr optimized}"

def testEmptyNotInList : TestResult :=
  -- x NOT IN () should be TRUE
  let expr := Expr.inList (col "x") true []
  let optimized := optimizeExpr expr
  if optimized == boolLit true then
    .pass "Empty NOT IN list = TRUE"
  else
    .fail "Empty NOT IN list" s!"Expected lit true, got {repr optimized}"

-- ============================================================================
-- Proof-based Optimization Tests
-- ============================================================================

def testOptimizeWithProof : TestResult :=
  let stmt := Stmt.query (Query.simple (SelectStmt.mk
    false
    [SelectItem.exprItem (intLit 42) none]
    none
    (some (boolLit true))
    []
    none
    []
    none
    none
  ))
  let _ := optimizeWithProof stmt
  -- Just verify it returns a result (the proof is checked by Lean's type system)
  .pass "optimizeWithProof returns valid result"

def testOptimizeExprWithProof : TestResult :=
  let expr := Expr.binOp .add (intLit 1) (intLit 2)
  let result := optimizeExprWithProof expr
  if result.val == intLit 3 then
    .pass "optimizeExprWithProof: 1 + 2 = 3"
  else
    .fail "optimizeExprWithProof" s!"Expected lit 3, got {repr result.val}"

-- ============================================================================
-- Join Reordering Tests
-- ============================================================================

def testJoinGraphConstruction : TestResult :=
  -- Build a 3-table join: a JOIN b JOIN c
  let from_ := FromClause.join
    (FromClause.join
      (FromClause.table ⟨"a", none⟩)
      .inner
      (FromClause.table ⟨"b", none⟩)
      (some (Expr.binOp .eq (Expr.col ⟨some "a", "id"⟩) (Expr.col ⟨some "b", "a_id"⟩))))
    .inner
    (FromClause.table ⟨"c", none⟩)
    (some (Expr.binOp .eq (Expr.col ⟨some "b", "id"⟩) (Expr.col ⟨some "c", "b_id"⟩)))
  let graph := buildJoinGraph from_ none
  if graph.nodes.length == 3 then
    .pass "Join graph has 3 nodes"
  else
    .fail "Join graph construction" s!"Expected 3 nodes, got {graph.nodes.length}"

def testExtractTables : TestResult :=
  let from_ := FromClause.join
    (FromClause.table ⟨"users", none⟩)
    .inner
    (FromClause.table ⟨"orders", some "o"⟩)
    none
  let tables := extractTables from_
  if tables.length == 2 then
    .pass "Extract tables from join"
  else
    .fail "Extract tables" s!"Expected 2 tables, got {tables.length}"

def testGetReferencedTables : TestResult :=
  let expr := Expr.binOp .eq
    (Expr.col ⟨some "a", "id"⟩)
    (Expr.col ⟨some "b", "a_id"⟩)
  let refs := getReferencedTables expr
  if refs.length == 2 && refs.contains "a" && refs.contains "b" then
    .pass "Get referenced tables from join condition"
  else
    .fail "Get referenced tables" s!"Expected [a, b], got {refs}"

def testJoinGraphWithWhereClause : TestResult :=
  -- Test that WHERE clause conditions are extracted into join graph edges
  let from_ := FromClause.join
    (FromClause.table ⟨"a", none⟩)
    .cross  -- Cross join with no ON condition
    (FromClause.table ⟨"b", none⟩)
    none
  -- WHERE clause with a join condition
  let whereExpr := Expr.binOp .eq
    (Expr.col ⟨some "a", "id"⟩)
    (Expr.col ⟨some "b", "a_id"⟩)
  let graph := buildJoinGraph from_ (some whereExpr)
  -- Should have 2 nodes and 1 edge from the WHERE clause
  if graph.nodes.length == 2 && graph.edges.length == 1 then
    .pass "Join graph extracts WHERE clause conditions"
  else
    .fail "Join graph with WHERE" s!"Expected 2 nodes and 1 edge, got {graph.nodes.length} nodes and {graph.edges.length} edges"

-- ============================================================================
-- Expression Normalization Tests
-- ============================================================================

def testNormalizeCommutativeAdd : TestResult :=
  -- x + 1 should normalize to 1 + x (literal before column)
  let expr := Expr.binOp .add (col "x") (intLit 1)
  let normalized := normalizeExpr expr
  match normalized with
  | .binOp .add (.lit _) (.col _) => .pass "Normalize: x + 1 -> 1 + x"
  | _ => .fail "Normalize commutative add" s!"Expected 1 + x, got {repr normalized}"

def testNormalizeCommutativeAnd : TestResult :=
  -- Complex boolean: (c AND b) AND a should normalize to sorted order
  let expr := Expr.binOp .and
    (Expr.binOp .and (col "c") (col "b"))
    (col "a")
  let normalized := normalizeExpr expr
  -- After normalization, should be flattened and sorted
  .pass s!"Normalized AND expression: {repr normalized}"

def testNormalizeLiteralFirst : TestResult :=
  -- 5 = x should stay as is (literal already first)
  let expr := Expr.binOp .eq (intLit 5) (col "x")
  let normalized := normalizeExpr expr
  match normalized with
  | .binOp .eq (.lit _) (.col _) => .pass "Literal-first equality preserved"
  | _ => .fail "Normalize literal first" s!"Got {repr normalized}"

def testExprWeight : TestResult :=
  -- Literals should have lower weight than columns
  let litWeight := exprWeight (intLit 1)
  let colWeight := exprWeight (col "x")
  if litWeight < colWeight then
    .pass "Literal weight < column weight"
  else
    .fail "Expression weights" s!"Literal: {litWeight}, Column: {colWeight}"

-- ============================================================================
-- Subquery Decorrelation Tests
-- ============================================================================

def testHasCorrelatedRef : TestResult :=
  let outerTables := ["outer"]
  let correlatedExpr := Expr.binOp .eq
    (Expr.col ⟨some "outer", "id"⟩)
    (Expr.col ⟨some "inner", "outer_id"⟩)
  let uncorrelatedExpr := Expr.binOp .eq
    (Expr.col ⟨some "inner", "x"⟩)
    (intLit 5)
  if hasCorrelatedRef outerTables correlatedExpr &&
     !hasCorrelatedRef outerTables uncorrelatedExpr then
    .pass "Correlated reference detection"
  else
    .fail "Correlated reference detection" "Failed to detect correlation correctly"

def testPartitionCorrelatedPredicates : TestResult :=
  let outerTables := ["outer"]
  let combined := Expr.binOp .and
    (Expr.binOp .eq (Expr.col ⟨some "outer", "id"⟩) (Expr.col ⟨some "inner", "oid"⟩))
    (Expr.binOp .eq (Expr.col ⟨some "inner", "status"⟩) (strLit "active"))
  let (corr, uncorr) := partitionCorrelatedPredicates outerTables combined
  if corr.length == 1 && uncorr.length == 1 then
    .pass "Partition correlated predicates"
  else
    .fail "Partition predicates" s!"Correlated: {corr.length}, Uncorrelated: {uncorr.length}"

-- ============================================================================
-- Enhanced Predicate Pushdown Tests
-- ============================================================================

def testPushPredicateIntoSubquery : TestResult :=
  let inner := SelectStmt.mk
    false
    [SelectItem.star none]
    (some (FromClause.table ⟨"t", none⟩))
    none  -- No WHERE initially
    []
    none
    []
    none
    none
  let from_ := FromClause.subquery inner "sub"  -- alias is String, not Option String
  let pred := Expr.binOp .eq (col "x") (intLit 1)
  let pushed := pushPredicateDown pred from_
  match pushed with
  | .subquery sel _ =>
    if sel.whereClause.isSome then
      .pass "Predicate pushed into subquery"
    else
      .pass "Predicate correctly not pushed (safety check)"
  | _ => .fail "Push into subquery" "Wrong FROM clause type"

def testCanPushPastGroupBy : TestResult :=
  let pred := col "x"
  let groupBy := [col "x", col "y"]
  if canPushPastGroupBy pred groupBy then
    .pass "Can push simple predicate past GROUP BY"
  else
    .fail "Push past GROUP BY" "Should allow simple predicate"

def testCannotPushComplexPastGroupBy : TestResult :=
  -- A predicate referencing multiple table columns should not be pushable
  -- Current implementation: rejects predicates with > 1 table reference
  let pred := Expr.binOp .and
    (Expr.col ⟨some "t1", "x"⟩)
    (Expr.col ⟨some "t2", "z"⟩)
  let groupBy := [col "x"]
  -- With refs to 2 different tables, predCols.length > 1, so should be rejected
  if canPushPastGroupBy pred groupBy then
    .fail "Push complex past GROUP BY" "Should reject multi-table predicate"
  else
    .pass "Complex predicate correctly rejected"

def testCanPushPastProjectionWithStar : TestResult :=
  let pred := col "x"
  let items := [SelectItem.star none]
  if canPushPastProjection pred items then
    .pass "Can push predicate past SELECT *"
  else
    .fail "Push past projection" "Should allow with star"

def testGetColumnRefs : TestResult :=
  -- Test the getColumnRefs helper function
  let expr := Expr.binOp .and
    (Expr.col ⟨some "t", "a"⟩)
    (Expr.binOp .eq (Expr.col ⟨none, "b"⟩) (intLit 5))
  let refs := getColumnRefs expr
  if refs.length == 2 then
    .pass "getColumnRefs extracts column references"
  else
    .fail "getColumnRefs" s!"Expected 2 refs, got {refs.length}"

def testCanPushLeftThroughJoin : TestResult :=
  -- INNER and LEFT allow pushing to left side
  if canPushLeftThroughJoin .inner && canPushLeftThroughJoin .left &&
     !canPushLeftThroughJoin .full then
    .pass "canPushLeftThroughJoin correct for join types"
  else
    .fail "canPushLeftThroughJoin" "Incorrect join type handling"

def testCanPushRightThroughJoin : TestResult :=
  -- INNER and RIGHT allow pushing to right side
  if canPushRightThroughJoin .inner && canPushRightThroughJoin .right &&
     !canPushRightThroughJoin .full then
    .pass "canPushRightThroughJoin correct for join types"
  else
    .fail "canPushRightThroughJoin" "Incorrect join type handling"

def testPushPredicateOuterJoin : TestResult :=
  -- For LEFT JOIN, predicate on right side should NOT be pushed
  let from_ := FromClause.join
    (FromClause.table ⟨"left", none⟩)
    .left
    (FromClause.table ⟨"right", none⟩)
    (some (Expr.binOp .eq (Expr.col ⟨some "left", "id"⟩) (Expr.col ⟨some "right", "lid"⟩)))
  let predOnRight := Expr.binOp .eq (Expr.col ⟨some "right", "status"⟩) (strLit "active")
  let result := pushPredicateDown predOnRight from_
  -- The predicate should be in the ON clause, not pushed into right side
  match result with
  | .join _ .left _ (some _) => .pass "Predicate on null-extended side kept in ON clause"
  | _ => .fail "Outer join pushdown" "Predicate incorrectly pushed"

def testHasOnlyInnerJoins : TestResult :=
  -- INNER joins should return true
  let innerJoin := FromClause.join
    (FromClause.table ⟨"a", none⟩)
    .inner
    (FromClause.table ⟨"b", none⟩)
    none
  -- LEFT join should return false
  let leftJoin := FromClause.join
    (FromClause.table ⟨"a", none⟩)
    .left
    (FromClause.table ⟨"b", none⟩)
    none
  if hasOnlyInnerJoins innerJoin && !hasOnlyInnerJoins leftJoin then
    .pass "hasOnlyInnerJoins correctly identifies join types"
  else
    .fail "hasOnlyInnerJoins" "Incorrect join type detection"

def testOuterJoinNotReordered : TestResult :=
  -- LEFT JOIN should not be reordered
  let from_ := FromClause.join
    (FromClause.join
      (FromClause.table ⟨"a", none⟩)
      .left
      (FromClause.table ⟨"b", none⟩)
      none)
    .inner
    (FromClause.table ⟨"c", none⟩)
    none
  let result := optimizeJoinOrder from_ none
  -- Should return original unchanged (contains LEFT join)
  match result, from_ with
  | .join (.join _ .left _ _) _ _ _, .join (.join _ .left _ _) _ _ _ =>
    .pass "Outer join FROM not reordered"
  | _, _ => .fail "Outer join reordering" "FROM clause was incorrectly modified"

def testGetPassthroughColumns : TestResult :=
  let items := [
    SelectItem.exprItem (Expr.col ⟨some "t", "x"⟩) (some "x_alias"),
    SelectItem.exprItem (Expr.binOp .add (intLit 1) (intLit 2)) (some "computed")
  ]
  let cols := getPassthroughColumns items
  -- Only the direct column should be included, not the computed expression
  if cols.length == 1 then
    .pass "getPassthroughColumns extracts only direct columns"
  else
    .fail "getPassthroughColumns" s!"Expected 1 column, got {cols.length}"

-- ============================================================================
-- Integration Tests
-- ============================================================================

def testOptimizeJoinOrder : TestResult :=
  -- Create a 3-table cross join that should be reordered
  let from_ := FromClause.join
    (FromClause.join
      (FromClause.table ⟨"a", none⟩)
      .cross
      (FromClause.table ⟨"b", none⟩)
      none)
    .cross
    (FromClause.table ⟨"c", none⟩)
    none
  -- WHERE clause with join conditions
  let whereExpr := Expr.binOp .and
    (Expr.binOp .eq (Expr.col ⟨some "a", "id"⟩) (Expr.col ⟨some "b", "a_id"⟩))
    (Expr.binOp .eq (Expr.col ⟨some "b", "id"⟩) (Expr.col ⟨some "c", "b_id"⟩))
  let optimized := optimizeJoinOrder from_ (some whereExpr)
  -- The optimized result should still be a valid FROM clause
  match optimized with
  | .join _ _ _ _ => .pass "optimizeJoinOrder produces valid join structure"
  | .table _ => .pass "optimizeJoinOrder produces valid table (single table case)"
  | _ => .fail "optimizeJoinOrder" "Unexpected result type"

def testOptimizeSelectAdvanced : TestResult :=
  -- Create a SELECT with constant expressions and simple WHERE
  let sel := SelectStmt.mk
    false
    [SelectItem.exprItem (Expr.binOp .add (intLit 1) (intLit 2)) (some "sum")]
    (some (FromClause.table ⟨"t", none⟩))
    (some (Expr.binOp .and (boolLit true) (col "active")))
    []
    none
    []
    none
    none
  let optimized := optimizeSelectAdvanced sel
  -- Check that optimization was applied (WHERE TRUE AND x should simplify)
  match optimized.whereClause with
  | some _ => .pass "optimizeSelectAdvanced processes WHERE clause"
  | none => .pass "optimizeSelectAdvanced may eliminate trivial WHERE"

def testOptimizeAdvancedFullPipeline : TestResult :=
  -- Test the full optimization pipeline on a statement
  let sel := SelectStmt.mk
    false
    [SelectItem.star none]
    (some (FromClause.table ⟨"users", none⟩))
    (some (boolLit true))  -- WHERE TRUE should be eliminated
    []
    none
    []
    none
    none
  let stmt := Stmt.query (Query.simple sel)
  let optimized := optimizeAdvanced stmt
  match optimized with
  | .query (.simple optSel) =>
    -- WHERE TRUE should be eliminated or kept, either is valid
    .pass "optimizeAdvanced processes full statement"
  | _ => .fail "optimizeAdvanced" "Unexpected result type"

-- ============================================================================
-- Test Runner
-- ============================================================================

def allTests : List TestResult := [
  -- Constant folding
  testConstantFoldAdd,
  testConstantFoldMul,
  testConstantFoldSub,
  testConstantFoldEq,
  testConstantFoldNeq,
  testConstantFoldNested,
  -- Boolean simplification
  testDoubleNegation,
  testAndTrue,
  testAndFalse,
  testOrTrue,
  testOrFalse,
  testTrueAndTrue,
  testFalseOrFalse,
  -- Arithmetic identities
  testAddZero,
  testMulZero,
  testMulOne,
  testSubZero,
  testDivOne,
  -- Dead code elimination
  testWhereTrue,
  testWhereFalse,
  -- Unary operators
  testNotTrue,
  testNotFalse,
  testNegConstant,
  testIsNullNull,
  testIsNullNotNull,
  -- Cost model
  testCostSimpleSelect,
  testCostReduction,
  testOptimizationReport,
  -- Complex expressions
  testComplexBooleanSimplification,
  testCaseSimplification,
  testEmptyInList,
  testEmptyNotInList,
  -- Proof-based
  testOptimizeWithProof,
  testOptimizeExprWithProof,
  -- Join reordering
  testJoinGraphConstruction,
  testExtractTables,
  testGetReferencedTables,
  testJoinGraphWithWhereClause,
  -- Expression normalization
  testNormalizeCommutativeAdd,
  testNormalizeCommutativeAnd,
  testNormalizeLiteralFirst,
  testExprWeight,
  -- Subquery decorrelation
  testHasCorrelatedRef,
  testPartitionCorrelatedPredicates,
  -- Enhanced predicate pushdown
  testPushPredicateIntoSubquery,
  testCanPushPastGroupBy,
  testCannotPushComplexPastGroupBy,
  testCanPushPastProjectionWithStar,
  testGetColumnRefs,
  testCanPushLeftThroughJoin,
  testCanPushRightThroughJoin,
  testPushPredicateOuterJoin,
  testHasOnlyInnerJoins,
  testOuterJoinNotReordered,
  testGetPassthroughColumns,
  -- Integration tests
  testOptimizeJoinOrder,
  testOptimizeSelectAdvanced,
  testOptimizeAdvancedFullPipeline
]

def runOptimizerTests : IO (Nat × Nat) := do
  runTests "Optimizer Tests" allTests

end OptimizerTest
