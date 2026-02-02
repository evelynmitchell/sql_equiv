/-
  Tests for Join Reordering (PR C)
-/
import SqlEquiv
import Test.Common

namespace JoinReorderingTest

open SqlEquiv
open Test

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Create a simple column reference -/
def col (name : String) : Expr := .col ⟨none, name⟩

/-- Create a qualified column reference -/
def qcol (table : String) (name : String) : Expr := .col ⟨some table, name⟩

/-- Create an integer literal -/
def intLit (n : Int) : Expr := .lit (.int n)

/-- Create a simple table FROM clause -/
def table (name : String) : FromClause := .table ⟨name, none⟩

/-- Create a table with alias -/
def tableAs (name : String) (alias : String) : FromClause := .table ⟨name, some alias⟩

/-- Create an inner join -/
def innerJoin (left : FromClause) (right : FromClause) (on_ : Option Expr) : FromClause :=
  .join left .inner right on_

/-- Create a cross join -/
def crossJoin (left : FromClause) (right : FromClause) : FromClause :=
  .join left .cross right none

/-- Create a left join -/
def leftJoin (left : FromClause) (right : FromClause) (on_ : Option Expr) : FromClause :=
  .join left .left right on_

-- ============================================================================
-- Safety Check Tests
-- ============================================================================

def testHasOnlyInnerJoinsSimple : TestResult :=
  let from_ := table "users"
  if hasOnlyInnerJoins from_ then
    .pass "Single table: has only inner joins"
  else
    .fail "Single table" "Should return true"

def testHasOnlyInnerJoinsInner : TestResult :=
  let from_ := innerJoin (table "users") (table "orders") none
  if hasOnlyInnerJoins from_ then
    .pass "Inner join: has only inner joins"
  else
    .fail "Inner join" "Should return true"

def testHasOnlyInnerJoinsCross : TestResult :=
  let from_ := crossJoin (table "users") (table "orders")
  if hasOnlyInnerJoins from_ then
    .pass "Cross join: has only inner joins"
  else
    .fail "Cross join" "Should return true"

def testHasOnlyInnerJoinsNested : TestResult :=
  let from_ := innerJoin
    (innerJoin (table "a") (table "b") none)
    (innerJoin (table "c") (table "d") none)
    none
  if hasOnlyInnerJoins from_ then
    .pass "Nested inner joins: has only inner joins"
  else
    .fail "Nested inner joins" "Should return true"

def testHasOnlyInnerJoinsLeftJoin : TestResult :=
  let from_ := leftJoin (table "users") (table "orders") none
  if !hasOnlyInnerJoins from_ then
    .pass "Left join: not only inner joins"
  else
    .fail "Left join" "Should return false"

def testHasOnlyInnerJoinsMixed : TestResult :=
  let from_ := innerJoin
    (table "users")
    (leftJoin (table "orders") (table "items") none)
    none
  if !hasOnlyInnerJoins from_ then
    .pass "Mixed joins: not only inner joins"
  else
    .fail "Mixed joins" "Should return false"

def testCanReorderJoins : TestResult :=
  let innerFrom := innerJoin (table "a") (table "b") none
  let leftFrom := leftJoin (table "a") (table "b") none
  if canReorderJoins innerFrom && !canReorderJoins leftFrom then
    .pass "canReorderJoins: correct results"
  else
    .fail "canReorderJoins" "Incorrect result"

def testCanReorderJoinsBlocksUnqualifiedCols : TestResult :=
  -- Unqualified column references make reordering unsafe (resolution depends on join order)
  let qualifiedPred := Expr.binOp .eq (qcol "a" "id") (qcol "b" "a_id")
  let unqualifiedPred := Expr.binOp .eq (col "id") (intLit 1)  -- Unqualified!
  let safeFrom := innerJoin (tableAs "users" "a") (tableAs "orders" "b") (some qualifiedPred)
  let unsafeFrom := innerJoin (tableAs "users" "a") (tableAs "orders" "b") (some unqualifiedPred)
  if canReorderJoins safeFrom && !canReorderJoins unsafeFrom then
    .pass "canReorderJoins: blocks unqualified column refs"
  else
    .fail "canReorderJoins unqualified" s!"safe={canReorderJoins safeFrom}, unsafe={canReorderJoins unsafeFrom}"

-- ============================================================================
-- JoinNode Tests
-- ============================================================================

def testJoinNodeLeaf : TestResult :=
  let t := TableRef.mk "users" (some "u")
  let node := JoinNode.leaf t
  if node.originalTables == ["u"] && node.estimatedRows == defaultCardinality then
    .pass "JoinNode.leaf: correct initialization"
  else
    .fail "JoinNode.leaf" s!"Got {repr node}"

def testJoinNodeCombine : TestResult :=
  let n1 := JoinNode.leaf ⟨"users", some "u"⟩
  let n2 := JoinNode.leaf ⟨"orders", some "o"⟩
  let combined := JoinNode.combine n1 n2 500
  if combined.originalTables == ["u", "o"] &&
     combined.estimatedRows == 500 &&
     combined.table.alias == some "__combined__" then
    .pass "JoinNode.combine: correct merge"
  else
    .fail "JoinNode.combine" s!"Got {repr combined}"

def testJoinNodeContainsTable : TestResult :=
  let n1 := JoinNode.leaf ⟨"users", some "u"⟩
  let n2 := JoinNode.leaf ⟨"orders", some "o"⟩
  let combined := JoinNode.combine n1 n2 500
  if combined.containsTable "u" &&
     combined.containsTable "o" &&
     !combined.containsTable "x" then
    .pass "JoinNode.containsTable: correct lookups"
  else
    .fail "JoinNode.containsTable" "Incorrect result"

-- ============================================================================
-- Edge Detection Tests
-- ============================================================================

def testExtractJoinTables : TestResult :=
  let pred := Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id")
  match extractJoinTables pred with
  | some (t1, t2) =>
    if (t1 == "u" && t2 == "o") || (t1 == "o" && t2 == "u") then
      .pass "extractJoinTables: found tables"
    else
      .fail "extractJoinTables" s!"Got ({t1}, {t2})"
  | none => .fail "extractJoinTables" "Expected Some"

def testExtractJoinTablesNonJoin : TestResult :=
  let pred := Expr.binOp .eq (qcol "u" "id") (intLit 1)
  match extractJoinTables pred with
  | none => .pass "extractJoinTables: non-join predicate returns none"
  | some _ => .fail "extractJoinTables" "Should return none for non-join"

def testMkJoinEdge : TestResult :=
  let pred := Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id")
  match mkJoinEdge pred with
  | some edge =>
    if edge.leftTable == "u" && edge.rightTable == "o" then
      .pass "mkJoinEdge: creates edge correctly"
    else
      .fail "mkJoinEdge" s!"Got {repr edge}"
  | none => .fail "mkJoinEdge" "Expected Some"

def testEdgeConnects : TestResult :=
  let n1 := JoinNode.leaf ⟨"users", some "u"⟩
  let n2 := JoinNode.leaf ⟨"orders", some "o"⟩
  let n3 := JoinNode.leaf ⟨"items", some "i"⟩
  let edge : JoinEdge := {
    leftTable := "u",
    rightTable := "o",
    predicate := Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id")
  }
  if edgeConnects edge n1 n2 &&
     edgeConnects edge n2 n1 &&  -- symmetric
     !edgeConnects edge n1 n3 then
    .pass "edgeConnects: correct matching"
  else
    .fail "edgeConnects" "Incorrect result"

-- ============================================================================
-- Extraction Tests
-- ============================================================================

def testExtractLeafTables : TestResult :=
  let from_ := innerJoin
    (tableAs "users" "u")
    (innerJoin (tableAs "orders" "o") (tableAs "items" "i") none)
    none
  let leaves := extractLeafTables from_
  if leaves.length == 3 then
    .pass "extractLeafTables: found 3 leaves"
  else
    .fail "extractLeafTables" s!"Expected 3, got {leaves.length}"

def testExtractOnPredicates : TestResult :=
  let pred1 := Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id")
  let pred2 := Expr.binOp .eq (qcol "o" "id") (qcol "i" "order_id")
  let from_ := innerJoin
    (tableAs "users" "u")
    (innerJoin (tableAs "orders" "o") (tableAs "items" "i") (some pred2))
    (some pred1)
  let preds := extractOnPredicates from_
  if preds.length == 2 then
    .pass "extractOnPredicates: found 2 predicates"
  else
    .fail "extractOnPredicates" s!"Expected 2, got {preds.length}"

-- ============================================================================
-- Reordering Tests
-- ============================================================================

def testReorderJoinsPreservesStructure : TestResult :=
  -- Simple case: two tables
  let from_ := innerJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let reordered := reorderJoins from_
  -- Should still be a join
  match reordered with
  | .join _ _ _ _ => .pass "reorderJoins: preserves join structure"
  | _ => .fail "reorderJoins" "Expected join"

def testReorderJoinsSkipsOuterJoin : TestResult :=
  let from_ := leftJoin (table "users") (table "orders") none
  let reordered := reorderJoins from_
  -- Should be unchanged (left join can't be reordered)
  if reordered == from_ then
    .pass "reorderJoins: skips outer join"
  else
    .fail "reorderJoins" "Should not modify outer join"

def testReorderJoinsMultipleTables : TestResult :=
  let from_ := innerJoin
    (innerJoin (tableAs "a" "a") (tableAs "b" "b") none)
    (tableAs "c" "c")
    none
  let reordered := reorderJoins from_
  -- Should produce some valid join structure
  -- Note: With no predicates, CROSS and INNER are semantically equivalent
  match reordered with
  | .join _ .inner _ _ => .pass "reorderJoins: produces inner join"
  | .join _ .cross _ _ => .pass "reorderJoins: produces cross join (no predicates)"
  | _ => .fail "reorderJoins" "Expected join result"

/-- Test that greedy algorithm joins smallest tables first (cost-based ordering).
    With three tables of sizes 10, 100, 1000, the greedy algorithm should:
    1. First join the two smallest (10 × 100 = 1000 result)
    2. Then join with the largest (1000 × 1000 = 1M result)
    Rather than joining largest first which would give worse intermediates. -/
def testGreedyJoinOrder : TestResult :=
  -- Create nodes with different cardinalities
  let smallTable : TableRef := ⟨"small", some "s"⟩
  let mediumTable : TableRef := ⟨"medium", some "m"⟩
  let largeTable : TableRef := ⟨"large", some "l"⟩
  let small : JoinNode := { table := smallTable, estimatedRows := 10, originalTables := ["s"], originalFrom := .table smallTable }
  let medium : JoinNode := { table := mediumTable, estimatedRows := 100, originalTables := ["m"], originalFrom := .table mediumTable }
  let large : JoinNode := { table := largeTable, estimatedRows := 1000, originalTables := ["l"], originalFrom := .table largeTable }
  let nodes := [small, medium, large]
  -- No edges = cross joins, cost is purely row count product
  match greedyReorder nodes [] with
  | none => .fail "greedyReorder" "Expected Some result"
  | some steps =>
    match steps with
    | [firstStep, _] =>
      -- First step should join the two smallest tables (s and m)
      let firstTables := firstStep.left.originalTables ++ firstStep.right.originalTables
      -- The first join should be between s and m (not involving l)
      if firstTables.contains "s" && firstTables.contains "m" && !firstTables.contains "l" then
        .pass "greedyReorder: joins smallest tables first"
      else
        .fail "greedyReorder" s!"First step should join s and m, got {firstTables}"
    | _ => .fail "greedyReorder" s!"Expected 2 steps, got {steps.length}"

/-- Test that predicates are preserved after reordering -/
def testReorderJoinsPreservesPredicates : TestResult :=
  -- Create a join with predicates
  let pred1 := Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id")
  let pred2 := Expr.binOp .eq (qcol "o" "id") (qcol "i" "order_id")
  let from_ := innerJoin
    (tableAs "users" "u")
    (innerJoin (tableAs "orders" "o") (tableAs "items" "i") (some pred2))
    (some pred1)
  let reordered := reorderJoins from_
  -- Extract all predicates from the reordered result
  let reorderedPreds := extractOnPredicates reordered
  -- Should have the same number of predicates
  if reorderedPreds.length == 2 then
    .pass "reorderJoins: preserves predicate count"
  else
    .fail "reorderJoins" s!"Expected 2 predicates, got {reorderedPreds.length}"

/-- Test that CROSS JOINs are preserved as CROSS (not converted to INNER) -/
def testReorderCrossJoinsPreservesType : TestResult :=
  -- Create a chain of CROSS JOINs (no predicates)
  let from_ := crossJoin
    (crossJoin (tableAs "a" "a") (tableAs "b" "b"))
    (tableAs "c" "c")
  let reordered := reorderJoins from_
  -- Helper to count CROSS joins specifically
  let rec countCross : FromClause → Nat
    | .table _ => 0
    | .subquery _ _ => 0
    | .join l jt r _ =>
      (if jt == .cross then 1 else 0) + countCross l + countCross r
  -- With no predicates, all joins should be CROSS
  let crossCount := countCross reordered
  if crossCount == 2 then
    .pass "reorderJoins: preserves CROSS JOIN type"
  else
    .fail "reorderJoins" s!"Expected 2 CROSS joins, got {crossCount}"

-- ============================================================================
-- Subquery Handling Tests
-- ============================================================================

/-- Helper: create a simple subquery FROM clause -/
def subqueryFrom (sel : SelectStmt) (alias : String) : FromClause := .subquery sel alias

/-- Helper: create a simple SELECT statement -/
def simpleSelect (items : List SelectItem) (from_ : Option FromClause) : SelectStmt :=
  SelectStmt.mk false items from_ none [] none [] none none

/-- Test that subqueries are treated as opaque leaf nodes and preserved during reordering -/
def testReorderJoinsWithSubquery : TestResult :=
  -- Create a subquery: (SELECT id, name FROM users) AS sub
  let innerSel := simpleSelect
    [SelectItem.exprItem (qcol "users" "id") (some "id"),
     SelectItem.exprItem (qcol "users" "name") (some "name")]
    (some (table "users"))
  let subq := subqueryFrom innerSel "sub"
  -- Join subquery with a regular table: sub INNER JOIN orders
  let from_ := innerJoin subq (tableAs "orders" "o") none
  -- hasOnlyInnerOrCrossJoins should return true (subquery is a valid leaf)
  if !hasOnlyInnerOrCrossJoins from_ then
    .fail "Subquery leaf" "hasOnlyInnerOrCrossJoins should return true"
  else
    -- Reorder should preserve the subquery
    let reordered := reorderJoins from_
    -- Check that reordered result still contains a subquery
    let rec hasSubquery : FromClause → Bool
      | .table _ => false
      | .subquery _ _ => true
      | .join l _ r _ => hasSubquery l || hasSubquery r
    if hasSubquery reordered then
      .pass "reorderJoins: preserves subquery as leaf"
    else
      .fail "Subquery preservation" "Subquery was lost during reordering"

/-- Test that extractLeafTables correctly extracts subquery as a leaf -/
def testExtractLeafTablesWithSubquery : TestResult :=
  let innerSel := simpleSelect
    [SelectItem.exprItem (qcol "t" "id") (some "id")]
    (some (table "t"))
  let subq := subqueryFrom innerSel "sub"
  let from_ := innerJoin (tableAs "users" "u") subq none
  let leaves := extractLeafTables from_
  -- Should have 2 leaves: users and the subquery
  if leaves.length != 2 then
    .fail "extractLeafTables subquery" s!"Expected 2 leaves, got {leaves.length}"
  else if leaves.any (fun n => n.originalTables == ["sub"]) then
    -- Check that one of the leaves has the subquery's alias
    .pass "extractLeafTables: includes subquery leaf"
  else
    .fail "extractLeafTables subquery" "Subquery leaf not found"

/-- Test that subquery's originalFrom is preserved (not converted to base table) -/
def testSubqueryOriginalFromPreserved : TestResult :=
  let innerSel := simpleSelect
    [SelectItem.exprItem (qcol "t" "id") (some "id")]
    (some (table "t"))
  let subq := subqueryFrom innerSel "sub"
  let leaves := extractLeafTables subq
  match leaves with
  | [node] =>
    -- The originalFrom should be the subquery, not a table
    match node.originalFrom with
    | .subquery _ _ => .pass "extractLeafTables: preserves subquery in originalFrom"
    | .table _ => .fail "Subquery originalFrom" "originalFrom should be subquery, not table"
    | _ => .fail "Subquery originalFrom" "Unexpected FromClause type"
  | _ => .fail "Subquery extraction" s!"Expected 1 leaf, got {leaves.length}"

-- ============================================================================
-- Cost Estimation Tests
-- ============================================================================

def testEstimateJoinCostNoEdges : TestResult :=
  let t1 : TableRef := ⟨"a", none⟩
  let t2 : TableRef := ⟨"b", none⟩
  let n1 : JoinNode := { table := t1, estimatedRows := 100, originalTables := ["a"], originalFrom := .table t1 }
  let n2 : JoinNode := { table := t2, estimatedRows := 200, originalTables := ["b"], originalFrom := .table t2 }
  let cost := estimateJoinCost n1 n2 []
  -- Cross join: 100 * 200 = 20000
  if cost == 20000 then
    .pass "estimateJoinCost: cross join cost correct"
  else
    .fail "estimateJoinCost" s!"Expected 20000, got {cost}"

def testEstimateJoinCostWithEdge : TestResult :=
  let t1 : TableRef := ⟨"a", none⟩
  let t2 : TableRef := ⟨"b", none⟩
  let n1 : JoinNode := { table := t1, estimatedRows := 100, originalTables := ["a"], originalFrom := .table t1 }
  let n2 : JoinNode := { table := t2, estimatedRows := 200, originalTables := ["b"], originalFrom := .table t2 }
  let edge : JoinEdge := {
    leftTable := "a",
    rightTable := "b",
    predicate := Expr.binOp .eq (qcol "a" "id") (qcol "b" "a_id"),
    selectivity := 0.1
  }
  let cost := estimateJoinCost n1 n2 [edge]
  -- With selectivity 0.1: 100 * 200 * 0.1 = 2000
  if cost == 2000 then
    .pass "estimateJoinCost: filtered join cost correct"
  else
    .fail "estimateJoinCost" s!"Expected 2000, got {cost}"

-- ============================================================================
-- Test Runner
-- ============================================================================

def allTests : List TestResult := [
  -- Safety checks
  testHasOnlyInnerJoinsSimple,
  testHasOnlyInnerJoinsInner,
  testHasOnlyInnerJoinsCross,
  testHasOnlyInnerJoinsNested,
  testHasOnlyInnerJoinsLeftJoin,
  testHasOnlyInnerJoinsMixed,
  testCanReorderJoins,
  testCanReorderJoinsBlocksUnqualifiedCols,
  -- JoinNode
  testJoinNodeLeaf,
  testJoinNodeCombine,
  testJoinNodeContainsTable,
  -- Edge detection
  testExtractJoinTables,
  testExtractJoinTablesNonJoin,
  testMkJoinEdge,
  testEdgeConnects,
  -- Extraction
  testExtractLeafTables,
  testExtractOnPredicates,
  -- Reordering
  testReorderJoinsPreservesStructure,
  testReorderJoinsSkipsOuterJoin,
  testReorderJoinsMultipleTables,
  testGreedyJoinOrder,
  testReorderJoinsPreservesPredicates,
  testReorderCrossJoinsPreservesType,
  -- Subquery handling
  testReorderJoinsWithSubquery,
  testExtractLeafTablesWithSubquery,
  testSubqueryOriginalFromPreserved,
  -- Cost estimation
  testEstimateJoinCostNoEdges,
  testEstimateJoinCostWithEdge
]

def runJoinReorderingTests : IO (Nat × Nat) := do
  runTests "Join Reordering Tests" allTests

end JoinReorderingTest
