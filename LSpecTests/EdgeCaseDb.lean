/-
  Tier 3F: Edge-case database tests.

  Tests evaluator correctness against specifically crafted databases that stress
  edge cases: NULL-heavy, single-row, duplicate-key, uniform, mixed-null, empty.
  These catch bugs that only trigger on certain data patterns which the fixed
  3-table testDb would miss.
-/
import LSpec
import SqlEquiv
import LSpecTests.QueryHelpers

open LSpec SlimCheck
open SqlEquiv
open QueryHelpers

namespace EdgeCaseDb

-- ============================================================================
-- Edge-case database definitions
-- ============================================================================

/-- All ages are NULL — tests NULL propagation in WHERE filters. -/
private def nullAgeDb : Database := fun name => match name with
  | "users" => [
    [("id", .int 1), ("name", .string "Alice"), ("age", .null none), ("department", .string "Engineering")],
    [("id", .int 2), ("name", .string "Bob"), ("age", .null none), ("department", .string "Sales")]
  ]
  | "orders" => [
    [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")]
  ]
  | _ => []

/-- Single-row tables — minimal non-empty database. -/
private def singleRowDb : Database := fun name => match name with
  | "users" => [
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")]
  ]
  | "orders" => [
    [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")]
  ]
  | _ => []

/-- Duplicate keys — multiple users with the same id. -/
private def dupKeyDb : Database := fun name => match name with
  | "users" => [
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")],
    [("id", .int 1), ("name", .string "Bob"), ("age", .int 25), ("department", .string "Sales")]
  ]
  | "orders" => [
    [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")],
    [("id", .int 2), ("user_id", .int 1), ("amount", .int 200), ("product", .string "Gadget")]
  ]
  | _ => []

/-- All identical rows — tests DISTINCT, idempotent filters. -/
private def uniformDb : Database := fun name => match name with
  | "users" => List.replicate 5
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")]
  | "orders" => List.replicate 3
    [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")]
  | _ => []

/-- Mixed NULL and non-NULL in same column — tests partial NULL propagation. -/
private def mixedNullDb : Database := fun name => match name with
  | "users" => [
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")],
    [("id", .int 2), ("name", .string "Bob"), ("age", .null none), ("department", .string "Sales")],
    [("id", .int 3), ("name", .null none), ("age", .int 25), ("department", .null none)]
  ]
  | "orders" => [
    [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")],
    [("id", .int 2), ("user_id", .int 3), ("amount", .null none), ("product", .string "Gadget")]
  ]
  | _ => []

/-- Completely empty database — every table returns []. -/
private def emptyDb : Database := fun _ => []

-- ============================================================================
-- NULL-age database tests
-- ============================================================================

private def nullAgeTests : TestSeq :=
  -- covers: where_false_empty
  test "null-age: WHERE age > 25 returns 0 rows (NULLs filtered)" (
    (evalSelect nullAgeDb (mkWhereAge .gt 25)).length == 0) $
  test "null-age: WHERE department = 'Sales' returns 1 row" (
    (evalSelect nullAgeDb
      (mkSelectWhere "users" (some (.binOp .eq (qcol "users" "department") (.lit (.string "Sales")))))).length == 1)

-- ============================================================================
-- Single-row database tests
-- ============================================================================

private def singleRowTests : TestSeq :=
  test "single-row: WHERE age > 25 returns 1 row (age=30)" (
    (evalSelect singleRowDb (mkWhereAge .gt 25)).length == 1) $
  test "single-row: WHERE age > 35 returns 0 rows" (
    (evalSelect singleRowDb (mkWhereAge .gt 35)).length == 0)

-- ============================================================================
-- Duplicate-key database tests
-- ============================================================================

private def dupKeyTests : TestSeq :=
  test "dup-key: WHERE age > 20 returns 2 rows" (
    (evalSelect dupKeyDb (mkWhereAge .gt 20)).length == 2) $
  -- covers: inner_join_cardinality_le
  test "dup-key: INNER JOIN age > 20 returns rows" (
    (evalSelect dupKeyDb (mkJoinQuery .inner 20)).length > 0)

-- ============================================================================
-- Uniform (all same) database tests
-- ============================================================================

private def uniformTests : TestSeq :=
  test "uniform: WHERE age > 25 returns all 5 rows (all age=30)" (
    (evalSelect uniformDb (mkWhereAge .gt 25)).length == 5) $
  -- covers: distinct_idempotent
  test "uniform: DISTINCT reduces to 1 row" (
    (evalSelect uniformDb (mkDistinctWhere 25)).length == 1)

-- ============================================================================
-- Mixed-NULL database tests
-- ============================================================================

private def mixedNullTests : TestSeq :=
  test "mixed-null: WHERE age > 25 returns 1 row (Alice, age=30)" (
    (evalSelect mixedNullDb (mkWhereAge .gt 25)).length == 1) $
  test "mixed-null: WHERE name = 'Alice' returns 1 row" (
    (evalSelect mixedNullDb
      (mkSelectWhere "users" (some (.binOp .eq (qcol "users" "name") (.lit (.string "Alice")))))).length == 1)

-- ============================================================================
-- Empty database tests
-- ============================================================================

private def emptyDbTests : TestSeq :=
  -- covers: inner_join_empty_left, inner_join_empty_right
  test "empty: WHERE age > 25 returns []" (
    (evalSelect emptyDb (mkWhereAge .gt 25)).length == 0) $
  -- covers: cross_join_empty_left, cross_join_empty_right
  test "empty: INNER JOIN returns []" (
    (evalSelect emptyDb (mkJoinQuery .inner 25)).length == 0) $
  test "empty: UNION ALL returns []" (
    (evalQuery emptyDb (mkUnionAll 25 30)).length == 0)

-- ============================================================================
-- All edge-case tests
-- ============================================================================

def allTests (_cfg : Configuration) : TestSeq :=
  group "NULL-Age DB" nullAgeTests $
  group "Single-Row DB" singleRowTests $
  group "Duplicate-Key DB" dupKeyTests $
  group "Uniform DB" uniformTests $
  group "Mixed-NULL DB" mixedNullTests $
  group "Empty DB" emptyDbTests

end EdgeCaseDb
