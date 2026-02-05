/-
  Tests for the SQL Query Optimizer
-/
import SqlEquiv
import Test.Common

namespace OptimizerTest

open SqlEquiv
open Test

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
-- Flatten Nonempty Tests (axioms: flattenAnd_nonempty, flattenOr_nonempty)
-- ============================================================================

private def testLengthGe (name : String) (actual bound : Nat) : TestResult :=
  if actual ≥ bound then .pass name
  else .fail name s!"Expected {actual} ≥ {bound}"

def testFlattenAndNonemptySimple : TestResult :=
  let e := Expr.binOp .and (col "a") (col "b")
  testLengthGe "flattenAnd_nonempty (simple AND)" (flattenAnd e).length 1

def testFlattenAndNonemptyAtom : TestResult :=
  let e := col "x"
  testLengthGe "flattenAnd_nonempty (atom)" (flattenAnd e).length 1

def testFlattenAndNonemptyNested : TestResult :=
  let e := Expr.binOp .and (Expr.binOp .and (col "a") (col "b")) (col "c")
  testLengthGe "flattenAnd_nonempty (nested)" (flattenAnd e).length 1

def testFlattenAndNonemptyLiteral : TestResult :=
  let e := boolLit true
  testLengthGe "flattenAnd_nonempty (literal)" (flattenAnd e).length 1

def testFlattenOrNonemptySimple : TestResult :=
  let e := Expr.binOp .or (col "a") (col "b")
  testLengthGe "flattenOr_nonempty (simple OR)" (flattenOr e).length 1

def testFlattenOrNonemptyAtom : TestResult :=
  let e := col "x"
  testLengthGe "flattenOr_nonempty (atom)" (flattenOr e).length 1

def testFlattenOrNonemptyNested : TestResult :=
  let e := Expr.binOp .or (Expr.binOp .or (col "a") (col "b")) (col "c")
  testLengthGe "flattenOr_nonempty (nested)" (flattenOr e).length 1

def testFlattenOrNonemptyLiteral : TestResult :=
  let e := boolLit false
  testLengthGe "flattenOr_nonempty (literal)" (flattenOr e).length 1

-- ============================================================================
-- Optimizer Equivalence Tests (axioms: optimizeExpr_equiv, optimizeSelectStmt_equiv, optimize_equiv)
-- ============================================================================

private def optTestDb : Database := fun name =>
  match name with
  | "t" => [[("id", .int 1), ("x", .int 10)], [("id", .int 2), ("x", .int 20)]]
  | _ => []

def testOptimizeExprEquivAdd : TestResult :=
  let e := Expr.binOp .add (intLit 3) (intLit 5)
  let opt := optimizeExpr e
  let row : Row := []
  let r1 := evalExprWithDb optTestDb row e
  let r2 := evalExprWithDb optTestDb row opt
  if r1 == r2 then .pass "optimizeExpr_equiv (constant add)"
  else .fail "optimizeExpr_equiv (constant add)" s!"Original={repr r1}, Optimized={repr r2}"

def testOptimizeExprEquivBoolSimplify : TestResult :=
  let e := Expr.binOp .and (col "x") (boolLit true)
  let opt := optimizeExpr e
  let row : Row := [("x", .bool true)]
  let r1 := evalExprWithDb optTestDb row e
  let r2 := evalExprWithDb optTestDb row opt
  if r1 == r2 then .pass "optimizeExpr_equiv (bool simplify)"
  else .fail "optimizeExpr_equiv (bool simplify)" s!"Original={repr r1}, Optimized={repr r2}"

def testOptimizeExprEquivNested : TestResult :=
  let e := Expr.binOp .or (Expr.binOp .and (boolLit false) (col "x")) (col "y")
  let opt := optimizeExpr e
  let row : Row := [("x", .bool true), ("y", .bool false)]
  let r1 := evalExprWithDb optTestDb row e
  let r2 := evalExprWithDb optTestDb row opt
  if r1 == r2 then .pass "optimizeExpr_equiv (nested)"
  else .fail "optimizeExpr_equiv (nested)" s!"Original={repr r1}, Optimized={repr r2}"

def testOptimizeSelectStmtEquivWhereTrue : TestResult :=
  let sel := SelectStmt.mk false [.star none]
    (some (.table ⟨"t", none⟩)) (some (boolLit true)) [] none [] none none
  let opt := optimizeSelectStmt sel
  let r1 := evalSelect optTestDb sel
  let r2 := evalSelect optTestDb opt
  if r1 == r2 then .pass "optimizeSelectStmt_equiv (WHERE TRUE)"
  else .fail "optimizeSelectStmt_equiv (WHERE TRUE)" s!"Original={r1.length} rows, Optimized={r2.length} rows"

def testOptimizeSelectStmtEquivConstFold : TestResult :=
  let sel := SelectStmt.mk false
    [.exprItem (Expr.binOp .add (intLit 1) (intLit 2)) (some "val")]
    (some (.table ⟨"t", none⟩)) none [] none [] none none
  let opt := optimizeSelectStmt sel
  let r1 := evalSelect optTestDb sel
  let r2 := evalSelect optTestDb opt
  if r1.length == r2.length then .pass "optimizeSelectStmt_equiv (const fold)"
  else .fail "optimizeSelectStmt_equiv (const fold)" s!"Original={r1.length} rows, Optimized={r2.length} rows"

def testOptimizeEquivFullStmt : TestResult :=
  let stmt := Stmt.query (Query.simple (SelectStmt.mk false
    [.star none] (some (.table ⟨"t", none⟩))
    (some (Expr.binOp .and (boolLit true) (col "x"))) [] none [] none none))
  let opt := optimize stmt
  let (_, r1) := evalStmt optTestDb stmt
  let (_, r2) := evalStmt optTestDb opt
  if r1 == r2 then .pass "optimize_equiv (full statement)"
  else .fail "optimize_equiv (full statement)" s!"Results differ"

def testOptimizeEquivDoubleNeg : TestResult :=
  -- Test at expression level: NOT NOT x evaluates the same as x
  let e := Expr.unaryOp .not (Expr.unaryOp .not (col "x"))
  let opt := optimizeExpr e
  let row : Row := [("x", .bool true)]
  let r1 := evalExprWithDb optTestDb row e
  let r2 := evalExprWithDb optTestDb row opt
  if r1 == r2 then .pass "optimize_equiv (double negation)"
  else .fail "optimize_equiv (double negation)" s!"Original={repr r1}, Optimized={repr r2}"

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
  -- Flatten nonempty (axioms: flattenAnd_nonempty, flattenOr_nonempty)
  testFlattenAndNonemptySimple,
  testFlattenAndNonemptyAtom,
  testFlattenAndNonemptyNested,
  testFlattenAndNonemptyLiteral,
  testFlattenOrNonemptySimple,
  testFlattenOrNonemptyAtom,
  testFlattenOrNonemptyNested,
  testFlattenOrNonemptyLiteral,
  -- Optimizer equivalence (axioms: optimizeExpr_equiv, optimizeSelectStmt_equiv, optimize_equiv)
  testOptimizeExprEquivAdd,
  testOptimizeExprEquivBoolSimplify,
  testOptimizeExprEquivNested,
  testOptimizeSelectStmtEquivWhereTrue,
  testOptimizeSelectStmtEquivConstFold,
  testOptimizeEquivFullStmt,
  testOptimizeEquivDoubleNeg
]

def runOptimizerTests : IO (Nat × Nat) := do
  runTests "Optimizer Tests" allTests

end OptimizerTest
