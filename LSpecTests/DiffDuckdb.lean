/-
  Differential testing against DuckDB (#203).

  DuckDB complements the SQLite oracle: it has a true DECIMAL type (SQLite
  stores decimals as IEEE floats), strict typing, and standard-compliant
  NULL handling — exactly the areas the type expansion (#201) touches.

  Each test parses ONE SQL string with our parser, evaluates it against the
  Lean-side tables, runs the same string through the duckdb CLI against the
  same data, and compares normalized result tables. This exercises the
  parser, evaluator, and pretty-printing of values in one pass.
-/
import LSpec
import SqlEquiv
import LSpecTests.QueryHelpers

open LSpec
open SqlEquiv
open QueryHelpers

namespace DiffDuckdb

-- ============================================================================
-- Shared schema/data: Lean tables and the equivalent DuckDB setup SQL
-- ============================================================================

/-- Items with DECIMAL prices (canonical scaled-int form), one NULL price. -/
private def itemsTable : Table := [
  [("id", .int 1), ("name", .string "Bolt"),   ("price", .decimal 25 1)],   -- 2.5
  [("id", .int 2), ("name", .string "Nut"),    ("price", .decimal 125 2)],  -- 1.25
  [("id", .int 3), ("name", .string "Washer"), ("price", .decimal 3 0)],    -- 3
  [("id", .int 4), ("name", .string "Shim"),   ("price", .null (some .decimal))]
]

/-- QueryHelpers.testDb (users/orders/products) extended with the items table. -/
private def db : Database := fun name =>
  if name == "items" then itemsTable else testDb name

private def duckdbSetupSql : String :=
  "CREATE TABLE users (id INTEGER, name TEXT, age INTEGER, department TEXT);\n" ++
  "INSERT INTO users VALUES (1, 'Alice', 30, 'Engineering'), (2, 'Bob', 25, 'Sales'), " ++
    "(3, 'Carol', 35, 'Engineering'), (4, 'Dave', 28, 'Marketing'), (5, 'Eve', 22, 'Sales');\n" ++
  "CREATE TABLE items (id INTEGER, name TEXT, price DECIMAL(10,2));\n" ++
  "INSERT INTO items VALUES (1, 'Bolt', 2.50), (2, 'Nut', 1.25), (3, 'Washer', 3), " ++
    "(4, 'Shim', NULL);\n"

-- ============================================================================
-- DuckDB execution and output parsing
-- ============================================================================

/-- Run SQL against the duckdb CLI (pipe-separated `-list` mode). -/
private def runDuckdbRaw (querySql : String) : IO (Except String String) := do
  let fullSql := duckdbSetupSql ++ querySql ++ ";\n"
  let child ← IO.Process.spawn {
    cmd := "duckdb"
    args := #["-list", "-nullvalue", "NULL"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  child.stdin.putStr fullSql
  child.stdin.flush
  let (_stdin, child) ← child.takeStdin
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode != 0 then return .error s!"duckdb error: {stderr}"
  return .ok stdout

/-- Parse a duckdb output cell by shape: NULL, integer, decimal (digits.digits,
    canonicalized through mkDecimal so `2.50` equals our stored `decimal 25 1`),
    otherwise string. Test data avoids numeric-looking strings. -/
private def parseValue (s : String) : Value :=
  if s == "NULL" then .null none
  else match s.toInt? with
  | some n => .int n
  | none =>
    match s.splitOn "." with
    | [ip, fp] =>
      if fp.length > 0 && fp.all Char.isDigit then
        match (ip ++ fp).toInt? with
        | some u => Value.mkDecimal u fp.length
        | none => .string s
      else .string s
    | _ => .string s

/-- Parse `-list` output (header line, then pipe-separated rows). -/
private def parseDuckdbOutput (output : String) : Table :=
  let lines := output.splitOn "\n" |>.filter (· ≠ "")
  match lines with
  | [] => []
  | header :: rows =>
    let colNames := header.splitOn "|"
    rows.map fun row =>
      colNames.zip (row.splitOn "|") |>.map fun (col, v) => (col, parseValue v)

-- ============================================================================
-- Result comparison (multiset semantics, qualifier-insensitive)
-- ============================================================================

private def stripQualifier (name : String) : String :=
  (name.splitOn ".").getLastD name

private def normalizeRow (row : Row) : Row :=
  row.map fun (k, v) => (stripQualifier k, v)

private def rowSortKey (row : Row) : String :=
  row.map (fun (k, v) => s!"{k}={repr v}") |> String.intercalate ","

private def sortTable (tbl : Table) : Table :=
  tbl.map normalizeRow |>.mergeSort fun r1 r2 =>
    decide (rowSortKey r1 < rowSortKey r2)

-- ============================================================================
-- Test runner: one SQL string drives both engines
-- ============================================================================

/-- Parse the SQL with our parser, evaluate, run the same SQL through duckdb,
    compare result multisets. -/
private def diffTest (description : String) (sql : String) : IO (String × Bool) := do
  match parse sql with
  | .error e =>
    IO.eprintln s!"  Our parser failed for '{description}': {e}"
    return (description, false)
  | .ok stmt =>
    let ourResult := ((evalStmt db stmt).2).getD []
    match ← runDuckdbRaw sql with
    | .error err =>
      IO.eprintln s!"  DuckDB error for '{description}': {err}"
      return (description, false)
    | .ok output =>
      let duckResult := parseDuckdbOutput output
      if sortTable ourResult == sortTable duckResult then
        return (description, true)
      else
        IO.eprintln s!"  Mismatch for '{description}': ours={repr (sortTable ourResult)} duckdb={repr (sortTable duckResult)}"
        return (description, false)

private def duckdbAvailable : IO Bool := do
  try
    let result ← IO.Process.output { cmd := "duckdb", args := #["--version"] }
    return result.exitCode == 0
  catch _ => return false

/-- All differential tests against DuckDB. Skips (with a notice) if the duckdb
    CLI is not on PATH. -/
def runAllTests : IO TestSeq := do
  unless ← duckdbAvailable do
    IO.eprintln "  [DiffDuckdb] duckdb not found on PATH, skipping differential tests"
    return test "duckdb not available (skipped)" true
  let results ← [
    -- Decimal literals and exact arithmetic
    diffTest "decimal literal canonicalization" "SELECT 2.50 AS x",
    diffTest "exact 0.1 + 0.2" "SELECT 0.1 + 0.2 AS x",
    diffTest "scale-aligned add" "SELECT 1.5 + 2.25 AS x",
    diffTest "decimal multiplication" "SELECT 1.5 * 2.0 AS x",
    -- int↔decimal promotion
    diffTest "int + decimal promotion" "SELECT 1 + 2.5 AS x",
    diffTest "promotion in WHERE" "SELECT name FROM items WHERE price > 2",
    -- NULL semantics (the invariant: NULL propagates, never errors)
    diffTest "NULL + decimal is NULL" "SELECT NULL + 1.5 AS n",
    diffTest "IS NULL over decimal column" "SELECT name FROM items WHERE price IS NULL",
    -- Aggregates over the DECIMAL column (NULL skipped per standard)
    diffTest "SUM over decimal column" "SELECT SUM(price) AS s FROM items",
    diffTest "AVG over decimal column" "SELECT AVG(price) AS a FROM items",
    diffTest "MIN/MAX over decimal column" "SELECT MIN(price) AS lo, MAX(price) AS hi FROM items",
    -- COUNT(col) skips NULLs (regression for the bug this oracle found)
    diffTest "COUNT skips NULLs" "SELECT COUNT(price) AS c FROM items",
    -- Ports of representative SQLite differential cases
    diffTest "WHERE with AND" "SELECT * FROM users WHERE age > 25 AND department = 'Engineering'",
    diffTest "WHERE with OR" "SELECT * FROM users WHERE age < 25 OR age > 30",
    diffTest "DISTINCT" "SELECT DISTINCT department FROM users",
    diffTest "no WHERE returns all" "SELECT * FROM users"
  ].mapM id
  return results.foldr (fun (name, passed) acc => test name passed $ acc)
    (test "duckdb tests complete" true)

end DiffDuckdb
