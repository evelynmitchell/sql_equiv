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

def testLeftJoinLeftPush : TestResult :=
  -- Can push predicate on left table through LEFT JOIN
  let from_ := leftJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .eq (qcol "u" "active") (boolLit true)
  let result := pushPredicateDown pred from_
  -- Should be pushed to left side
  if result.remaining.isNone then
    .pass "Left join: left predicate pushed"
  else
    .fail "Left join left push" "Left predicate should have been pushed"

def testRightJoinNoLeftPush : TestResult :=
  -- Can't push predicate on left table through RIGHT JOIN
  let from_ := rightJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .eq (qcol "u" "active") (boolLit true)
  let result := pushPredicateDown pred from_
  -- Should remain at current level
  match result.remaining with
  | some _ => .pass "Right join: left predicate not pushed through"
  | none =>
    match result.pushedFrom with
    | .join _ .right _ (some _) => .pass "Right join: left predicate added to ON"
    | _ => .fail "Right join safety" "Predicate should remain or go to ON"

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
  -- Unqualified columns should match any table
  let from_ := innerJoin (tableAs "users" "u") (tableAs "orders" "o") none
  let pred := Expr.binOp .eq (col "id") (intLit 1)  -- unqualified
  let result := pushPredicateDown pred from_
  -- Should be pushed (inner join allows pushing to ON)
  if result.remaining.isNone then
    .pass "Unqualified column: pushed to ON"
  else
    .fail "Unqualified column" "Should have been pushed"

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
  testLeftJoinLeftPush,
  testRightJoinNoLeftPush,
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
