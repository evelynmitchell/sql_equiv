/-
  Tier 3E: Query-level structural properties.

  Tests properties beyond "optimizer preserves semantics":
  - E1: Optimizer idempotence (applying twice = applying once)
  - E2: Column preservation (optimizer doesn't change output schema)
  - E3: Empty database behavior (every query on empty db returns empty)
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators
import LSpecTests.QueryHelpers

open LSpec SlimCheck
open SqlEquiv
open QueryHelpers

namespace QueryProperties

-- ============================================================================
-- E1. Optimizer Idempotence
-- ============================================================================

/-- optimizeSelectStmt applied twice produces the same result as applied once. -/
private def selectIdempotent (age : AgeInt) : Bool :=
  let sel := mkWhereAge .gt age.val
  optimizeSelectStmt (optimizeSelectStmt sel) == optimizeSelectStmt sel

/-- Idempotence for JOIN queries. -/
private def joinIdempotent (jt : JoinType) (age : AgeInt) : Bool :=
  let sel := mkJoinQuery jt age.val
  optimizeSelectStmt (optimizeSelectStmt sel) == optimizeSelectStmt sel

/-- optimizeQuery applied twice produces the same result as applied once. -/
private def queryIdempotent (a1 a2 : AgeInt) : Bool :=
  let q := mkUnionAll a1.val a2.val
  optimizeQuery (optimizeQuery q) == optimizeQuery q

/-- optimize (Stmt) applied twice produces the same result as applied once. -/
private def stmtIdempotent (age : AgeInt) : Bool :=
  let stmt := Stmt.query (.simple (mkWhereAge .gt age.val))
  optimize (optimize stmt) == optimize stmt

def idempotenceTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "optimizeSelectStmt is idempotent (WHERE)" (∀ age : AgeInt, selectIdempotent age) $
  check (cfg := cfg) "optimizeSelectStmt is idempotent (JOIN)" (∀ jt : JoinType, ∀ age : AgeInt, joinIdempotent jt age) $
  check (cfg := cfg) "optimizeQuery is idempotent (UNION ALL)" (∀ a1 a2 : AgeInt, queryIdempotent a1 a2) $
  check (cfg := cfg) "optimize is idempotent (Stmt)" (∀ age : AgeInt, stmtIdempotent age) $
  -- Fixed-value idempotence tests
  test "idempotent: DISTINCT WHERE age > 25" (
    let sel := mkDistinctWhere 25
    optimizeSelectStmt (optimizeSelectStmt sel) == optimizeSelectStmt sel) $
  test "idempotent: ORDER BY LIMIT OFFSET" (
    let sel := mkOrderLimitOffset (some 3) (some 1)
    optimizeSelectStmt (optimizeSelectStmt sel) == optimizeSelectStmt sel) $
  test "idempotent: subquery" (
    let sel := mkSubqueryWhere 25
    optimizeSelectStmt (optimizeSelectStmt sel) == optimizeSelectStmt sel) $
  test "idempotent: projection" (
    let sel := mkProjection 25
    optimizeSelectStmt (optimizeSelectStmt sel) == optimizeSelectStmt sel) $
  test "idempotent: WHERE TRUE" (
    let sel := mkSelectWhere "users" (some (.lit (.bool true)))
    optimizeSelectStmt (optimizeSelectStmt sel) == optimizeSelectStmt sel) $
  test "idempotent: WHERE FALSE" (
    let sel := mkSelectWhere "users" (some (.lit (.bool false)))
    optimizeSelectStmt (optimizeSelectStmt sel) == optimizeSelectStmt sel)

-- ============================================================================
-- E2. Column Preservation
-- ============================================================================

/-- Extract column names from the first row of a table result. -/
private def columnNames (tbl : Table) : Option (List String) :=
  tbl.head?.map (·.map (·.1))

/-- Optimizer preserves output column names for simple WHERE queries.
    Only checks when the unoptimized query returns at least one row. -/
private def colNamesPreserved (age : AgeInt) : Bool :=
  let sel := mkWhereAge .gt age.val
  let base := evalSelect testDb sel
  match base.head? with
  | some _ =>
    columnNames (evalSelect testDb (optimizeSelectStmt sel)) == columnNames base
  | none => true

/-- Optimizer preserves output column names for projection queries.
    Only checks when the unoptimized query returns at least one row. -/
private def projColNamesPreserved (age : AgeInt) : Bool :=
  let sel := mkProjection age.val
  let base := evalSelect testDb sel
  match base.head? with
  | some _ =>
    columnNames (evalSelect testDb (optimizeSelectStmt sel)) == columnNames base
  | none => true

/-- Optimizer preserves output column names for JOIN queries.
    Only checks when the unoptimized query returns at least one row. -/
private def joinColNamesPreserved (jt : JoinType) (age : AgeInt) : Bool :=
  let sel := mkJoinQuery jt age.val
  let base := evalSelect testDb sel
  match base.head? with
  | some _ =>
    columnNames (evalSelect testDb (optimizeSelectStmt sel)) == columnNames base
  | none => true

def columnPreservationTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "column names preserved (WHERE)" (∀ age : AgeInt, colNamesPreserved age) $
  check (cfg := cfg) "column names preserved (projection)" (∀ age : AgeInt, projColNamesPreserved age) $
  check (cfg := cfg) "column names preserved (JOIN)" (∀ jt : JoinType, ∀ age : AgeInt, joinColNamesPreserved jt age)

-- ============================================================================
-- E3. Empty Database Behavior
-- ============================================================================

private def emptyDb : Database := fun _ => []

def emptyDbTests : TestSeq :=
  test "SELECT * FROM users on empty db = []" (
    (evalSelect emptyDb (mkSelectWhere "users" none)).length == 0) $
  test "WHERE age > 25 on empty db = []" (
    (evalSelect emptyDb (mkWhereAge .gt 25)).length == 0) $
  test "JOIN on empty db = []" (
    (evalSelect emptyDb (mkJoinQuery .inner 25)).length == 0) $
  test "LEFT JOIN on empty db = []" (
    (evalSelect emptyDb (mkJoinQuery .left 25)).length == 0) $
  test "CROSS JOIN on empty db = []" (
    (evalSelect emptyDb (mkJoinQuery .cross 25)).length == 0) $
  test "UNION ALL on empty db = []" (
    (evalQuery emptyDb (mkUnionAll 25 30)).length == 0) $
  test "DISTINCT on empty db = []" (
    (evalSelect emptyDb (mkDistinctWhere 25)).length == 0) $
  test "projection on empty db = []" (
    (evalSelect emptyDb (mkProjection 25)).length == 0) $
  test "optimizer on empty db preserves semantics (WHERE)" (
    selectOptOkDb emptyDb (mkWhereAge .gt 25)) $
  test "optimizer on empty db preserves semantics (JOIN)" (
    selectOptOkDb emptyDb (mkJoinQuery .inner 25)) $
  test "optimizer on empty db preserves semantics (DISTINCT)" (
    selectOptOkDb emptyDb (mkDistinctWhere 25))

-- ============================================================================
-- All structural property tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Idempotence" (idempotenceTests cfg) $
  group "Column Preservation" (columnPreservationTests cfg) $
  group "Empty Database" emptyDbTests

end QueryProperties
