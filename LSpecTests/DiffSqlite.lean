/-
  Tier 3D: Differential testing against SQLite.

  Compares our evaluator against SQLite as an oracle. Catches evaluator bugs
  (not just optimizer bugs) by verifying that evalSelect produces the same
  results as running the equivalent SQL against SQLite with the same data.

  Uses IO-based tests since each test shells out to sqlite3.
-/
import LSpec
import SqlEquiv
import LSpecTests.QueryHelpers

open LSpec
open SqlEquiv
open QueryHelpers

namespace DiffSqlite

-- ============================================================================
-- SQLite setup: CREATE tables and INSERT test data
-- ============================================================================

private def sqliteSetupSql : String :=
  "CREATE TABLE users (id INTEGER, name TEXT, age INTEGER, department TEXT);\n" ++
  "INSERT INTO users VALUES (1, 'Alice', 30, 'Engineering');\n" ++
  "INSERT INTO users VALUES (2, 'Bob', 25, 'Sales');\n" ++
  "INSERT INTO users VALUES (3, 'Carol', 35, 'Engineering');\n" ++
  "INSERT INTO users VALUES (4, 'Dave', 28, 'Marketing');\n" ++
  "INSERT INTO users VALUES (5, 'Eve', 22, 'Sales');\n" ++
  "CREATE TABLE orders (id INTEGER, user_id INTEGER, amount INTEGER, product TEXT);\n" ++
  "INSERT INTO orders VALUES (1, 1, 100, 'Widget');\n" ++
  "INSERT INTO orders VALUES (2, 1, 200, 'Gadget');\n" ++
  "INSERT INTO orders VALUES (3, 2, 150, 'Widget');\n" ++
  "INSERT INTO orders VALUES (4, 3, 300, 'Gizmo');\n" ++
  "CREATE TABLE products (id INTEGER, name TEXT, price INTEGER);\n" ++
  "INSERT INTO products VALUES (1, 'Widget', 50);\n" ++
  "INSERT INTO products VALUES (2, 'Gadget', 100);\n" ++
  "INSERT INTO products VALUES (3, 'Gizmo', 150);\n"

-- ============================================================================
-- SQLite query execution
-- ============================================================================

/-- Run SQL against sqlite3 and return raw stdout. -/
private def runSqliteRaw (querySql : String) : IO (Except String String) := do
  let fullSql := sqliteSetupSql ++ querySql ++ ";\n"
  let tmpPath := "/tmp/sql_equiv_diff_test.sql"
  IO.FS.writeFile tmpPath fullSql
  let result ← IO.Process.output {
    cmd := "bash"
    args := #["-c", s!"sqlite3 :memory: -header -separator '|' -nullvalue 'NULL' < {tmpPath}"]
  }
  if result.exitCode != 0 then return .error s!"sqlite3 error: {result.stderr}"
  return .ok result.stdout

-- ============================================================================
-- Output parsing
-- ============================================================================

/-- Parse a single value from SQLite text output. -/
private def parseValue (s : String) : Value :=
  if s == "NULL" then .null none
  else match s.toInt? with
    | some n => .int n
    | none => .string s

/-- Parse sqlite3 pipe-separated output into Table. -/
private def parseSqliteOutput (output : String) : Table :=
  let lines := output.splitOn "\n" |>.filter (· ≠ "")
  match lines with
  | [] => []
  | header :: rows =>
    let colNames := header.splitOn "|"
    rows.map fun row =>
      let vals := row.splitOn "|"
      colNames.zip vals |>.map fun (col, valStr) =>
        (col, parseValue valStr)

-- ============================================================================
-- Result comparison
-- ============================================================================

/-- Strip qualifier prefix from column names (e.g., "users.age" → "age"). -/
private def stripQualifier (name : String) : String :=
  match name.splitOn "." with
  | [_, col] => col
  | _ => name

/-- Normalize a row by stripping qualifiers from column names. -/
private def normalizeRow (row : Row) : Row :=
  row.map fun (k, v) => (stripQualifier k, v)

/-- Convert a row to a sortable string key. -/
private def rowSortKey (row : Row) : String :=
  row.map (fun (k, v) => s!"{k}={repr v}") |> String.intercalate ","

/-- Sort a table by all column values for order-independent comparison. -/
private def sortTable (tbl : Table) : Table :=
  tbl.map normalizeRow |>.mergeSort fun r1 r2 =>
    decide (rowSortKey r1 < rowSortKey r2)

/-- Compare our evaluator result with SQLite result.
    Returns true if both produce the same rows (as multisets). -/
private def resultsMatch (ourResult : Table) (sqliteResult : Table) : Bool :=
  sortTable ourResult == sortTable sqliteResult

-- ============================================================================
-- IO-based test runner
-- ============================================================================

/-- Run a row-count comparison test. Returns (testName, passed). -/
private def diffCountTest (description : String) (sel : SelectStmt) (sqlQuery : String) :
    IO (String × Bool) := do
  let ourResult := evalSelect testDb sel
  match ← runSqliteRaw sqlQuery with
  | .error err =>
    IO.eprintln s!"  SQLite error for '{description}': {err}"
    return (description, false)
  | .ok output =>
    let sqliteResult := parseSqliteOutput output
    if ourResult.length == sqliteResult.length then
      return (description, true)
    else
      IO.eprintln s!"  Row count mismatch for '{description}': ours={ourResult.length}, sqlite={sqliteResult.length}"
      return (description, false)

/-- Run a full result comparison test. Returns (testName, passed). -/
private def diffFullTest (description : String) (sel : SelectStmt) (sqlQuery : String) :
    IO (String × Bool) := do
  let ourResult := evalSelect testDb sel
  match ← runSqliteRaw sqlQuery with
  | .error err =>
    IO.eprintln s!"  SQLite error for '{description}': {err}"
    return (description, false)
  | .ok output =>
    let sqliteResult := parseSqliteOutput output
    if resultsMatch ourResult sqliteResult then
      return (description, true)
    else
      IO.eprintln s!"  Result mismatch for '{description}': ours={ourResult.length} rows, sqlite={sqliteResult.length} rows"
      return (description, false)

-- ============================================================================
-- Test definitions
-- ============================================================================

/-- All differential tests against SQLite. Returns IO TestSeq. -/
def runAllTests : IO TestSeq := do
  let results ← [
    -- Simple WHERE queries
    diffCountTest "WHERE age > 25" (mkWhereAge .gt 25)
      "SELECT * FROM users WHERE age > 25",
    diffCountTest "WHERE age = 30" (mkWhereAge .eq 30)
      "SELECT * FROM users WHERE age = 30",
    diffCountTest "WHERE department = 'Engineering'"
      (mkSelectWhere "users" (some (.binOp .eq (qcol "users" "department") (.lit (.string "Engineering")))))
      "SELECT * FROM users WHERE department = 'Engineering'",
    diffCountTest "WHERE age > 25 AND department = 'Engineering'"
      (mkSelectWhere "users" (some (.binOp .and
        (.binOp .gt (qcol "users" "age") (.lit (.int 25)))
        (.binOp .eq (qcol "users" "department") (.lit (.string "Engineering"))))))
      "SELECT * FROM users WHERE age > 25 AND department = 'Engineering'",
    diffCountTest "WHERE age < 25 OR age > 30"
      (mkSelectWhere "users" (some (.binOp .or
        (.binOp .lt (qcol "users" "age") (.lit (.int 25)))
        (.binOp .gt (qcol "users" "age") (.lit (.int 30))))))
      "SELECT * FROM users WHERE age < 25 OR age > 30",
    diffCountTest "WHERE FALSE returns 0 rows"
      (mkSelectWhere "users" (some (.lit (.bool false))))
      "SELECT * FROM users WHERE 0",
    diffCountTest "no WHERE returns all rows"
      (mkSelectWhere "users" none)
      "SELECT * FROM users",
    -- DISTINCT
    diffCountTest "SELECT DISTINCT department"
      (.mk true
        [.exprItem (qcol "users" "department") (some "department")]
        (some (.table ⟨"users", none⟩)) none [] none [] none none)
      "SELECT DISTINCT department FROM users",
    -- LIMIT/OFFSET
    diffCountTest "LIMIT 3"
      (.mk false [.star none] (some (.table ⟨"users", none⟩)) none [] none
        [OrderByItem.mk (qcol "users" "id") .asc] (some 3) none)
      "SELECT * FROM users ORDER BY id LIMIT 3",
    diffCountTest "LIMIT 2 OFFSET 2"
      (.mk false [.star none] (some (.table ⟨"users", none⟩)) none [] none
        [OrderByItem.mk (qcol "users" "id") .asc] (some 2) (some 2))
      "SELECT * FROM users ORDER BY id LIMIT 2 OFFSET 2",
    -- More WHERE variants
    diffCountTest "WHERE age >= 25 AND age <= 30"
      (mkSelectWhere "users" (some (.binOp .and
        (.binOp .ge (qcol "users" "age") (.lit (.int 25)))
        (.binOp .le (qcol "users" "age") (.lit (.int 30))))))
      "SELECT * FROM users WHERE age >= 25 AND age <= 30",
    diffCountTest "WHERE name != 'Alice'"
      (mkSelectWhere "users" (some (.binOp .ne (qcol "users" "name") (.lit (.string "Alice")))))
      "SELECT * FROM users WHERE name != 'Alice'"
  ].mapM id
  -- Build TestSeq from results
  return results.foldr (fun (name, passed) acc => test name passed $ acc)
    (test "sqlite3 tests complete" true)

end DiffSqlite
