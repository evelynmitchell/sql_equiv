/-
  Tests for Predicate Pushdown (PR B)
-/
import SqlEquiv
import Test.Common

namespace PredicatePushdownTest

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

/-- Create a boolean literal -/
def boolLit (b : Bool) : Expr := .lit (.bool b)

/-- Create a simple table FROM clause -/
def table (name : String) : FromClause := .table ⟨name, none⟩

/-- Create a table with alias -/
def tableAs (name : String) (alias : String) : FromClause := .table ⟨name, some alias⟩

/-- Create an inner join -/
def innerJoin (left : FromClause) (right : FromClause) (on_ : Option Expr) : FromClause :=
  .join left .inner right on_

/-- Create a left join -/
def leftJoin (left : FromClause) (right : FromClause) (on_ : Option Expr) : FromClause :=
  .join left .left right on_

/-- Create a right join -/
def rightJoin (left : FromClause) (right : FromClause) (on_ : Option Expr) : FromClause :=
  .join left .right right on_

-- ============================================================================
-- Basic Pushdown Tests
-- ============================================================================

def testPushdownToBaseTable : TestResult :=
  -- Pushing to a base table should leave predicate as remaining
  let from_ := table "users"
  let pred := Expr.binOp .eq (qcol "users" "id") (intLit 1)
  let result := pushPredicateDown pred from_
  match result.remaining with
  | some _ => .pass "Base table: predicate remains"
  | none => .fail "Base table pushdown" "Expected remaining predicate"

def testPushdownToInnerJoinOn : TestResult :=
  -- Predicate referencing both tables should go to ON clause
  let from_ := innerJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id")
  let result := pushPredicateDown pred from_
  match result.pushedFrom with
  | .join _ .inner _ (some _) =>
    if result.remaining.isNone then
      .pass "Inner join: predicate pushed to ON"
    else
      .fail "Inner join ON" "Predicate should not remain"
  | _ => .fail "Inner join ON" "Expected join with ON clause"

def testPushdownToLeftSide : TestResult :=
  -- Predicate referencing only left table should push to left
  let from_ := innerJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .eq (qcol "u" "active") (boolLit true)
  let result := pushPredicateDown pred from_
  -- For inner join, this should push to left or ON clause
  if result.remaining.isNone then
    .pass "Inner join: left-only predicate pushed"
  else
    .fail "Left side pushdown" "Predicate should have been pushed"

def testPushdownToRightSide : TestResult :=
  -- Predicate referencing only right table should push to right
  let from_ := innerJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .gt (qcol "o" "amount") (intLit 100)
  let result := pushPredicateDown pred from_
  -- For inner join, this should push to right or ON clause
  if result.remaining.isNone then
    .pass "Inner join: right-only predicate pushed"
  else
    .fail "Right side pushdown" "Predicate should have been pushed"

-- ============================================================================
-- Outer Join Safety Tests
-- ============================================================================

def testLeftJoinNoRightPush : TestResult :=
  -- Can't push predicate on right table through LEFT JOIN
  let from_ := leftJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .gt (qcol "o" "amount") (intLit 100)
  let result := pushPredicateDown pred from_
  -- Should remain at current level, not pushed to right
  match result.remaining with
  | some _ => .pass "Left join: right predicate not pushed through"
  | none =>
    -- Check if pushed to ON instead (which is also valid for left join)
    match result.pushedFrom with
    | .join _ .left _ (some _) => .pass "Left join: right predicate added to ON"
    | _ => .fail "Left join safety" "Predicate should remain or go to ON"

def testLeftJoinLeftPredicateBaseTable : TestResult :=
  -- For LEFT JOIN with base table on left, left predicates should remain
  -- (can't push into base table, and adding to ON would change semantics)
  let from_ := leftJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .eq (qcol "u" "active") (boolLit true)
  let result := pushPredicateDown pred from_
  -- Should remain in WHERE (not pushed to ON, as that changes LEFT JOIN semantics)
  match result.remaining with
  | some _ => .pass "Left join base table: left predicate remains in WHERE"
  | none => .fail "Left join base table" "Predicate should remain, not be added to ON"

def testRightJoinNoLeftPush : TestResult :=
  -- Can't push predicate on left table through RIGHT JOIN
  let from_ := rightJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .eq (qcol "u" "active") (boolLit true)
  let result := pushPredicateDown pred from_
  -- Should remain at current level (not pushed to ON, as that changes semantics)
  match result.remaining with
  | some _ => .pass "Right join: left predicate remains in WHERE"
  | none => .fail "Right join safety" "Predicate should remain, not be added to ON"

def testRightJoinRightPredicateBaseTable : TestResult :=
  -- For RIGHT JOIN with base table on right, right predicates should remain
  let from_ := rightJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .gt (qcol "o" "amount") (intLit 100)
  let result := pushPredicateDown pred from_
  -- Should remain in WHERE (not pushed to ON, as that changes RIGHT JOIN semantics)
  match result.remaining with
  | some _ => .pass "Right join base table: right predicate remains in WHERE"
  | none => .fail "Right join base table" "Predicate should remain, not be added to ON"

/-- Create a full outer join -/
def fullJoin (left : FromClause) (right : FromClause) (on_ : Option Expr) : FromClause :=
  .join left .full right on_

/-- Create a cross join -/
def crossJoin (left : FromClause) (right : FromClause) : FromClause :=
  .join left .cross right none

def testFullJoinNoPush : TestResult :=
  -- FULL OUTER JOIN: predicates should not be pushed to either side
  let from_ := fullJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .eq (qcol "u" "active") (boolLit true)
  let result := pushPredicateDown pred from_
  -- Should remain (can't push through FULL join)
  match result.remaining with
  | some _ => .pass "Full join: predicate remains in WHERE"
  | none => .fail "Full join safety" "Predicate should not be pushed"

def testCrossJoinPush : TestResult :=
  -- CROSS JOIN: predicates can be pushed (similar to INNER)
  let from_ := crossJoin (tableAs "users" "u") (tableAs "orders" "o")
  let pred := Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id")
  let result := pushPredicateDown pred from_
  -- Should be pushed to ON clause
  match result.pushedFrom with
  | .join _ .cross _ (some _) =>
    if result.remaining.isNone then
      .pass "Cross join: predicate pushed to ON"
    else
      .fail "Cross join" "Predicate should not remain"
  | _ => .fail "Cross join" "Expected cross join with ON clause"

def testPushToExistingOnClause : TestResult :=
  -- Pushing to a join that already has an ON clause should extend it
  let existingOn := Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id")
  let from_ := innerJoin (tableAs "users" "u") (tableAs "orders" "o") (some existingOn)
  let newPred := Expr.binOp .gt (qcol "o" "amount") (intLit 100)
  let result := pushPredicateDown newPred from_
  -- Should add to existing ON clause with AND
  match result.pushedFrom with
  | .join _ .inner _ (some (.binOp .and _ _)) =>
    if result.remaining.isNone then
      .pass "Existing ON: predicate combined with AND"
    else
      .fail "Existing ON" "Predicate should not remain"
  | _ => .fail "Existing ON" "Expected ON clause with AND"

-- ============================================================================
-- Subquery Pushdown Tests
-- ============================================================================

/-- Create a simple subquery FROM clause -/
def subquery (sel : SelectStmt) (alias : String) : FromClause := .subquery sel alias

/-- Create a simple SELECT statement -/
def simpleSelect (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) : SelectStmt :=
  SelectStmt.mk false items from_ where_ groupBy none [] none none

def testSubqueryPushdownSimple : TestResult :=
  -- Push predicate into subquery when column is in SELECT
  let innerSel := simpleSelect
    [SelectItem.exprItem (qcol "t" "id") (some "id"),
     SelectItem.exprItem (qcol "t" "name") (some "name")]
    (some (tableAs "table" "t"))
    none
    []
  let from_ := subquery innerSel "sub"
  let pred := Expr.binOp .eq (col "id") (intLit 1)
  let result := pushPredicateDown pred from_
  -- Should be pushed into subquery's WHERE
  match result.pushedFrom with
  | .subquery sel _ =>
    if sel.whereClause.isSome && result.remaining.isNone then
      .pass "Subquery: predicate pushed to WHERE"
    else
      .fail "Subquery pushdown" "Predicate should be in subquery WHERE"
  | _ => .fail "Subquery pushdown" "Expected subquery"

def testSubqueryPushdownBlockedByProjection : TestResult :=
  -- Don't push predicate if column not in SELECT
  let innerSel := simpleSelect
    [SelectItem.exprItem (qcol "t" "id") (some "id")]  -- only id, no email
    (some (tableAs "table" "t"))
    none
    []
  let from_ := subquery innerSel "sub"
  let pred := Expr.binOp .eq (col "email") (Expr.lit (.string "test"))
  let result := pushPredicateDown pred from_
  -- Should remain (email not in projection)
  match result.remaining with
  | some _ => .pass "Subquery projection: predicate blocked"
  | none => .fail "Subquery projection" "Predicate should be blocked"

def testSubqueryPushdownWithGroupBy : TestResult :=
  -- Push predicate on grouping key into subquery with GROUP BY
  let innerSel := simpleSelect
    [SelectItem.exprItem (col "category") (some "category"),
     SelectItem.exprItem (Expr.agg .count none false) (some "cnt")]
    (some (tableAs "products" "p"))
    none
    [col "category"]  -- GROUP BY category
  let from_ := subquery innerSel "sub"
  let pred := Expr.binOp .eq (col "category") (Expr.lit (.string "Electronics"))
  let result := pushPredicateDown pred from_
  -- Should be pushed (category is a grouping key)
  match result.pushedFrom with
  | .subquery sel _ =>
    if sel.whereClause.isSome && result.remaining.isNone then
      .pass "Subquery GROUP BY: grouping key predicate pushed"
    else
      .fail "Subquery GROUP BY" "Predicate on grouping key should be pushed"
  | _ => .fail "Subquery GROUP BY" "Expected subquery"

def testSubqueryPushdownBlockedByGroupBy : TestResult :=
  -- Don't push predicate on non-grouping column
  let innerSel := simpleSelect
    [SelectItem.exprItem (col "category") (some "category"),
     SelectItem.exprItem (Expr.agg .sum (some (col "price")) false) (some "total")]
    (some (tableAs "products" "p"))
    none
    [col "category"]  -- GROUP BY category only
  let from_ := subquery innerSel "sub"
  -- total is an aggregate result, not available for pushdown
  let pred := Expr.binOp .gt (col "total") (intLit 1000)
  let result := pushPredicateDown pred from_
  -- Should remain (total is aggregate, not in GROUP BY)
  match result.remaining with
  | some _ => .pass "Subquery GROUP BY: aggregate predicate blocked"
  | none => .fail "Subquery GROUP BY" "Aggregate predicate should be blocked"

def testSubqueryPushdownQualifiedPredicate : TestResult :=
  -- Push predicate using subquery alias (e.g., sub.id = 1)
  -- The column reference should be transformed to match inner columns
  let innerSel := simpleSelect
    [SelectItem.exprItem (qcol "t" "id") (some "id"),
     SelectItem.exprItem (qcol "t" "name") (some "name")]
    (some (tableAs "table" "t"))
    none
    []
  let from_ := subquery innerSel "sub"
  -- Use qualified column: sub.id (references the subquery alias)
  let pred := Expr.binOp .eq (qcol "sub" "id") (intLit 1)
  let result := pushPredicateDown pred from_
  -- Should be pushed, and column should be transformed to t.id
  match result.pushedFrom with
  | .subquery sel _ =>
    match sel.whereClause with
    | some (.binOp .eq (.col c) _) =>
      -- The column should now reference 't' (inner table), not 'sub'
      if c.table == some "t" && c.column == "id" && result.remaining.isNone then
        .pass "Subquery qualified: column transformed correctly"
      else
        .fail "Subquery qualified" s!"Expected t.id, got {repr c}"
    | _ => .fail "Subquery qualified" "Expected equality predicate in WHERE"
  | _ => .fail "Subquery qualified" "Expected subquery"

def testSubqueryPushdownBlockedByAggregate : TestResult :=
  -- Don't push predicate containing aggregate
  let innerSel := simpleSelect
    [SelectItem.exprItem (col "category") (some "category")]
    (some (tableAs "products" "p"))
    none
    [col "category"]
  let from_ := subquery innerSel "sub"
  -- Predicate uses COUNT which shouldn't be pushed past GROUP BY
  let pred := Expr.binOp .gt (Expr.agg .count none false) (intLit 5)
  let result := pushPredicateDown pred from_
  -- Should remain (predicate contains aggregate)
  match result.remaining with
  | some _ => .pass "Subquery: aggregate in predicate blocked"
  | none => .fail "Subquery aggregate" "Predicate with aggregate should be blocked"

-- ============================================================================
-- Multiple Conjunct Tests
-- ============================================================================

def testMultipleConjuncts : TestResult :=
  -- Multiple AND-ed predicates should be split and pushed independently
  let from_ := innerJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .and
    (Expr.binOp .eq (qcol "u" "active") (boolLit true))
    (Expr.binOp .gt (qcol "o" "amount") (intLit 100))
  let result := pushPredicateDown pred from_
  -- Both predicates should be pushed (inner join)
  if result.remaining.isNone then
    .pass "Multiple conjuncts: all pushed"
  else
    .fail "Multiple conjuncts" "All predicates should have been pushed"

def testNestedConjuncts : TestResult :=
  -- Nested ANDs should be flattened and pushed
  let from_ := innerJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .and
    (Expr.binOp .and
      (Expr.binOp .eq (qcol "u" "active") (boolLit true))
      (Expr.binOp .gt (qcol "o" "amount") (intLit 100)))
    (Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id"))
  let result := pushPredicateDown pred from_
  if result.remaining.isNone then
    .pass "Nested conjuncts: all flattened and pushed"
  else
    .fail "Nested conjuncts" "All predicates should have been pushed"

-- ============================================================================
-- Safety Check Tests
-- ============================================================================

def testCanPushPastProjection : TestResult :=
  -- Test the projection check helper
  let items := [
    SelectItem.exprItem (col "name") (some "user_name"),
    SelectItem.exprItem (col "id") none
  ]
  let pred1 := Expr.binOp .eq (col "user_name") (Expr.lit (.string "Alice"))
  let pred2 := Expr.binOp .eq (col "id") (intLit 1)
  let pred3 := Expr.binOp .eq (col "email") (Expr.lit (.string "test"))
  if canPushPastProjection pred1 items &&
     canPushPastProjection pred2 items &&
     !canPushPastProjection pred3 items then
    .pass "canPushPastProjection: correct results"
  else
    .fail "canPushPastProjection" "Incorrect projection check"

def testCanPushPastGroupBy : TestResult :=
  -- Test GROUP BY check helper
  let groupBy := [col "category", col "region"]
  let pred1 := Expr.binOp .eq (col "category") (Expr.lit (.string "A"))
  let pred2 := Expr.agg .sum (some (col "amount")) false  -- aggregate: can't push
  let pred3 := Expr.binOp .eq (col "price") (intLit 100)  -- non-grouping column
  if canPushPastGroupBy pred1 groupBy &&
     !canPushPastGroupBy pred2 groupBy &&
     !canPushPastGroupBy pred3 groupBy then
    .pass "canPushPastGroupBy: correct results"
  else
    .fail "canPushPastGroupBy" "Incorrect GROUP BY check"

-- ============================================================================
-- Edge Cases
-- ============================================================================

def testUnqualifiedColumn : TestResult :=
  -- Unqualified columns don't match any specific table (predReferencesOnlyTables
  -- returns false), so they can't be pushed to left or right side specifically.
  -- For INNER joins, they fall through to be added to the ON clause.
  let from_ := innerJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .eq (col "id") (intLit 1)  -- unqualified
  let result := pushPredicateDown pred from_
  -- Should be pushed to ON clause (inner join allows this)
  if result.remaining.isNone then
    .pass "Unqualified column: added to ON clause"
  else
    .fail "Unqualified column" "Should have been added to ON"

def testEmptyPredicate : TestResult :=
  -- A simple literal predicate
  let from_ := table "users"
  let pred := boolLit true
  let result := pushPredicateDown pred from_
  -- Should remain (can't push into base table)
  match result.remaining with
  | some _ => .pass "Literal predicate: remains"
  | none => .fail "Literal predicate" "Expected remaining"

-- ============================================================================
-- Test Runner
-- ============================================================================

def allTests : List TestResult := [
  -- Basic pushdown
  testPushdownToBaseTable,
  testPushdownToInnerJoinOn,
  testPushdownToLeftSide,
  testPushdownToRightSide,
  -- Outer join safety
  testLeftJoinNoRightPush,
  testLeftJoinLeftPredicateBaseTable,
  testRightJoinNoLeftPush,
  testRightJoinRightPredicateBaseTable,
  testFullJoinNoPush,
  -- Cross join and existing ON
  testCrossJoinPush,
  testPushToExistingOnClause,
  -- Subquery pushdown
  testSubqueryPushdownSimple,
  testSubqueryPushdownBlockedByProjection,
  testSubqueryPushdownWithGroupBy,
  testSubqueryPushdownBlockedByGroupBy,
  testSubqueryPushdownQualifiedPredicate,
  testSubqueryPushdownBlockedByAggregate,
  -- Multiple conjuncts
  testMultipleConjuncts,
  testNestedConjuncts,
  -- Safety checks
  testCanPushPastProjection,
  testCanPushPastGroupBy,
  -- Edge cases
  testUnqualifiedColumn,
  testEmptyPredicate
]

def runPredicatePushdownTests : IO (Nat × Nat) := do
  runTests "Predicate Pushdown Tests" allTests

end PredicatePushdownTest
