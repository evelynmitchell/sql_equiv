/-
  Tier 3D: Differential testing against SQLite.

  Compares our evaluator against SQLite as an oracle. Catches evaluator bugs
  (not just optimizer bugs) by verifying that evalSelect produces the same
  results as running the equivalent SQL against SQLite with the same data.

  Two runners coexist:
  - the original AST-based diffCountTest/diffFullTest (kept for continuity:
    they exercise hand-built SelectStmt values without going through the
    parser), and
  - the parse-based diffTest (retrofit of the DiffDuckdb design): ONE SQL
    string is parsed with our parser, evaluated against the Lean-side tables,
    run through sqlite3, and the normalized result multisets are compared.
    This exercises parser + evaluator together.

  SQLite-specific coverage: the ON-less JOIN spelling (`A JOIN B WHERE ...`)
  is accepted by SQLite (cross product) but rejected by DuckDB, so this is
  the oracle that covers it.

  Where sqlite legitimately differs from DuckDB/Postgres (implementation-
  defined behaviour), see docs/IMPLEMENTATION_DEFINED.md for what we chose
  and how each case is tested.

  KNOWN DIVERGENCES from sqlite (registry rows; do not add cases that hit
  them, the registry records the decision and the pinning unit test):
  - Row 10, cross-type comparison (`1 = 'a'`): sqlite returns false; we
    treat it as a type error (#127, decided: matches DuckDB/Postgres).
  - Row 12, TEXT column vs number (`year >= 2014`): sqlite compares as text
    via column affinity; we treat it as a type error (#235, decided). The
    Spider harness emulates sqlite here by quoting the literal, reported as
    its own category.
  - Row 11, number vs numeric-looking string (`age = '30'`): sqlite converts
    the string; we treat it as a type error (#254, decided: keep). Pinned by
    `int_vs_numeric_string_literal_drops_row` and siblings.
  - Row 5, DISTINCT + ORDER BY on a non-selected column: accepted in the
    sqlite dialect (`DialectConfig.distinctOrderBy = .firstRow`); sqlite sorts
    by each value's first source row, but SqlEquiv's evaluator still ties the
    key (output keeps input order). Gap (#320), pinned by
    `distinct_order_by_unselected_keeps_input_order`; the typed core agrees
    with the engines (`SqlCoreTest/DuckdbDiffTest.lean`).
  - LIKE with `_` or a `%` inside the pattern (#323): SqlEquiv's `simpleLike`
    treats them as literal characters; the engines (and the typed core)
    match them as wildcards. Do not add such a case until #323 is fixed.
  - INTERSECT/EXCEPT between columns of different names, or over typed and
    untyped NULLs (#324): SqlEquiv compares rows by (name, value) pairs; the
    engines (and the typed core) compare values positionally.
  (Row 8, LIKE letter case, is per dialect: this harness parses in the
  sqlite dialect, so LIKE is ASCII case-insensitive here and has cases below.)

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
  "INSERT INTO products VALUES (3, 'Gizmo', 150);\n" ++
  -- Items with INTEGER prices (no decimals — SQLite has no true DECIMAL),
  -- one NULL price for COUNT(col)/IS NULL coverage.
  "CREATE TABLE items (id INTEGER, name TEXT, price INTEGER);\n" ++
  "INSERT INTO items VALUES (1, 'Bolt', 3);\n" ++
  "INSERT INTO items VALUES (2, 'Nut', 1);\n" ++
  "INSERT INTO items VALUES (3, 'Washer', 2);\n" ++
  "INSERT INTO items VALUES (4, 'Shim', NULL);\n" ++
  -- Duplicate-bearing tables for INTERSECT/EXCEPT set-semantics cases (#223).
  "CREATE TABLE dups (x INTEGER);\n" ++
  "INSERT INTO dups VALUES (1);\n" ++
  "INSERT INTO dups VALUES (1);\n" ++
  "INSERT INTO dups VALUES (2);\n" ++
  "INSERT INTO dups VALUES (2);\n" ++
  "INSERT INTO dups VALUES (3);\n" ++
  "CREATE TABLE other (x INTEGER);\n" ++
  "INSERT INTO other VALUES (2);\n" ++
  "INSERT INTO other VALUES (3);\n" ++
  "INSERT INTO other VALUES (3);\n" ++
  "INSERT INTO other VALUES (4);\n"

-- ============================================================================
-- Lean-side tables mirroring the SQLite setup above (for the parse-based
-- diffTest runner; the AST-based tests keep using QueryHelpers.testDb)
-- ============================================================================

/-- Items with INTEGER prices, one NULL (mirrors the items table above). -/
private def itemsTable : Table := [
  [("id", .int 1), ("name", .string "Bolt"),   ("price", .int 3)],
  [("id", .int 2), ("name", .string "Nut"),    ("price", .int 1)],
  [("id", .int 3), ("name", .string "Washer"), ("price", .int 2)],
  [("id", .int 4), ("name", .string "Shim"),   ("price", .null (some .int))]
]

/-- Duplicate-bearing table for set-op semantics (#223). -/
private def dupsTable : Table := [
  [("x", .int 1)], [("x", .int 1)], [("x", .int 2)], [("x", .int 2)], [("x", .int 3)]
]

private def otherTable : Table := [
  [("x", .int 2)], [("x", .int 3)], [("x", .int 3)], [("x", .int 4)]
]

/-- QueryHelpers.testDb (users/orders/products) extended with items/dups/other. -/
private def db : Database := fun name =>
  if name == "items" then itemsTable
  else if name == "dups" then dupsTable
  else if name == "other" then otherTable
  else testDb name

-- ============================================================================
-- SQLite query execution
-- ============================================================================

/-- Run SQL against sqlite3 via stdin and return raw stdout. -/
private def runSqliteRaw (querySql : String) : IO (Except String String) := do
  let fullSql := sqliteSetupSql ++ querySql ++ ";\n"
  let child ← IO.Process.spawn {
    cmd := "sqlite3"
    args := #[":memory:", "-header", "-separator", "|", "-nullvalue", "NULL"]
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
  if exitCode != 0 then return .error s!"sqlite3 error: {stderr}"
  return .ok stdout

-- ============================================================================
-- Output parsing
-- ============================================================================

/-- Parse a single value from SQLite text output.
    Uses SQLite column type declarations to distinguish integers from strings.
    The integer-first fallback for non-TEXT columns is safe because our test
    schema ensures INTEGER columns always contain integer values. -/
private def parseValue (s : String) (colType : String) : Value :=
  if s == "NULL" then .null none
  else if colType == "TEXT" then .string s
  else match s.toInt? with
    | some n => .int n
    | none => .string s

/-- Column type declarations for our test schema (used to disambiguate parsing). -/
private def columnTypes : List (String × String) :=
  [("id", "INTEGER"), ("name", "TEXT"), ("age", "INTEGER"), ("department", "TEXT"),
   ("user_id", "INTEGER"), ("amount", "INTEGER"), ("product", "TEXT"), ("price", "INTEGER")]

private def getColumnType (colName : String) : String :=
  (columnTypes.find? (·.1 == colName) |>.map (·.2)).getD "INTEGER"

/-- Parse sqlite3 pipe-separated output into Table.
    Note: pipe characters within values would break parsing. Our test data
    contains no pipe characters, so this is safe for the current test suite. -/
private def parseSqliteOutput (output : String) : Table :=
  let lines := output.splitOn "\n" |>.filter (· ≠ "")
  match lines with
  | [] => []
  | header :: rows =>
    let colNames := header.splitOn "|"
    rows.map fun row =>
      let vals := row.splitOn "|"
      colNames.zip vals |>.map fun (col, valStr) =>
        (col, parseValue valStr (getColumnType col))

-- ============================================================================
-- Result comparison
-- ============================================================================

/-- Strip qualifier prefix(es) from column names (e.g., "users.age" or
    "alias.users.age" → "age"). -/
private def stripQualifier (name : String) : String :=
  let parts := name.splitOn "."
  parts.getLastD name

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

/-- Parse-based runner (retrofit of the DiffDuckdb design): parse the SQL with
    our parser in the `sqlite` dialect (sqlite's implementation-defined
    choices), evaluate against the Lean-side `db`, run the same SQL through
    sqlite3, compare normalized result multisets. -/
private def diffTest (description : String) (sql : String) : IO (String × Bool) := do
  match parse sql (dialect := .sqlite) with
  | .error e =>
    IO.eprintln s!"  Our parser failed for '{description}': {e}"
    return (description, false)
  | .ok stmt =>
    let ourResult := ((evalStmt db stmt).2).getD []
    match ← runSqliteRaw sql with
    | .error err =>
      IO.eprintln s!"  SQLite error for '{description}': {err}"
      return (description, false)
    | .ok output =>
      let sqliteResult := parseSqliteOutput output
      if resultsMatch ourResult sqliteResult then
        return (description, true)
      else
        IO.eprintln s!"  Mismatch for '{description}': ours={repr (sortTable ourResult)} sqlite={repr (sortTable sqliteResult)}"
        return (description, false)

-- ============================================================================
-- Test definitions
-- ============================================================================

/-- Check if sqlite3 is available on PATH. -/
private def sqlite3Available : IO Bool := do
  try
    let result ← IO.Process.output { cmd := "sqlite3", args := #["--version"] }
    return result.exitCode == 0
  catch _ => return false

/-- All differential tests against SQLite. Returns IO TestSeq.
    Skips all tests with a message if sqlite3 is not available. -/
def runAllTests : IO TestSeq := do
  unless ← sqlite3Available do
    IO.eprintln "  [DiffSqlite] sqlite3 not found on PATH, skipping differential tests"
    return test "sqlite3 not available (skipped)" true
  let results ← [
    -- Simple WHERE queries
    diffCountTest "WHERE age > 25" (mkWhereAge .gt 25)
      "SELECT * FROM users WHERE age > 25",
    diffFullTest "WHERE age = 30" (mkWhereAge .eq 30)
      "SELECT * FROM users WHERE age = 30",
    diffFullTest "WHERE department = 'Engineering'"
      (mkSelectWhere "users" (some (.binOp .eq (qcol "users" "department") (.lit (.string "Engineering")))))
      "SELECT * FROM users WHERE department = 'Engineering'",
    -- covers: filter_and
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
    -- covers: where_false_empty
    diffCountTest "WHERE FALSE returns 0 rows"
      (mkSelectWhere "users" (some (.lit (.bool false))))
      "SELECT * FROM users WHERE 0",
    -- covers: where_true_elim
    diffFullTest "no WHERE returns all rows"
      (mkSelectWhere "users" none)
      "SELECT * FROM users",
    -- DISTINCT
    -- covers: distinct_count_le
    diffCountTest "SELECT DISTINCT department"
      (.mk true
        [.exprItem (qcol "users" "department") (some "department")]
        (some (.table ⟨"users", none⟩)) none [] none [] none none)
      "SELECT DISTINCT department FROM users",
    -- covers: limit_upper_bound
    diffCountTest "LIMIT 3"
      (.mk false [.star none] (some (.table ⟨"users", none⟩)) none [] none
        [OrderByItem.ofDir (qcol "users" "id") .asc] (some 3) none)
      "SELECT * FROM users ORDER BY id LIMIT 3",
    -- covers: limit_offset_compose
    diffCountTest "LIMIT 2 OFFSET 2"
      (.mk false [.star none] (some (.table ⟨"users", none⟩)) none [] none
        [OrderByItem.ofDir (qcol "users" "id") .asc] (some 2) (some 2))
      "SELECT * FROM users ORDER BY id LIMIT 2 OFFSET 2",
    -- More WHERE variants
    diffCountTest "WHERE age >= 25 AND age <= 30"
      (mkSelectWhere "users" (some (.binOp .and
        (.binOp .ge (qcol "users" "age") (.lit (.int 25)))
        (.binOp .le (qcol "users" "age") (.lit (.int 30))))))
      "SELECT * FROM users WHERE age >= 25 AND age <= 30",
    diffFullTest "WHERE name != 'Alice'"
      (mkSelectWhere "users" (some (.binOp .ne (qcol "users" "name") (.lit (.string "Alice")))))
      "SELECT * FROM users WHERE name != 'Alice'",
    -- ------------------------------------------------------------------
    -- Parse-based cases (one SQL string drives both engines), ported from
    -- the DiffDuckdb harness where sqlite-safe (no decimals)
    -- ------------------------------------------------------------------
    -- ORDER BY on a non-projected column; LIMIT makes the sort observable
    diffTest "ORDER BY non-projected column with LIMIT"
      "SELECT name FROM items WHERE price IS NOT NULL ORDER BY price LIMIT 1",
    diffTest "ORDER BY non-projected DESC with LIMIT"
      "SELECT name FROM users ORDER BY age DESC LIMIT 2",
    -- COUNT(col) skips NULLs (items has one NULL price)
    diffTest "COUNT skips NULLs"
      "SELECT COUNT(price) AS c FROM items",
    -- NULL ordering under sqlite's rule (NULL smallest: first on ASC, last
    -- on DESC); LIMIT 1 makes the position of the NULL price observable
    diffTest "NULL first on ASC (sqlite rule)"
      "SELECT name FROM items ORDER BY price LIMIT 1",
    diffTest "NULL last on DESC (sqlite rule)"
      "SELECT name FROM items ORDER BY price DESC LIMIT 1",
    diffTest "explicit NULLS LAST"
      "SELECT name FROM items ORDER BY price NULLS LAST LIMIT 1",
    diffTest "explicit DESC NULLS FIRST"
      "SELECT name FROM items ORDER BY price DESC NULLS FIRST LIMIT 1",
    -- Set-operation subquery (#218): UNION inside an IN subquery
    diffTest "IN with UNION subquery"
      "SELECT name FROM users WHERE id IN (SELECT user_id FROM orders WHERE amount > 150 UNION SELECT user_id FROM orders WHERE amount < 120)",
    diffTest "MIN/MAX over strings"
      "SELECT MIN(name) AS lo, MAX(name) AS hi FROM users",
    diffTest "MAX over strings per group"
      "SELECT department, MAX(name) AS m FROM users GROUP BY department",
    diffTest "MAX over strings skips NULL"
      "SELECT MAX(CASE WHEN age > 26 THEN name END) AS m FROM users",
    -- Mixed numbers and strings (registry row 13): in the sqlite dialect
    -- numbers order before strings, as in sqlite itself
    diffTest "MAX over mixed types (sqlite type-class order)"
      "SELECT MAX(CASE WHEN age > 26 THEN name ELSE age END) AS m FROM users",
    diffTest "MIN over mixed types (sqlite type-class order)"
      "SELECT MIN(CASE WHEN age > 26 THEN name ELSE age END) AS m FROM users",
    -- MIN/MAX over booleans (registry row 14): sqlite reads them as 1/0
    diffTest "MIN/MAX over booleans (sqlite: integers)"
      "SELECT MAX(age > 26) AS hi, MIN(age > 26) AS lo FROM users",
    diffTest "MAX over booleans and integers (sqlite)"
      "SELECT MAX(CASE WHEN age > 26 THEN age > 29 ELSE age END) AS m FROM users",
    -- Subquery name resolution is inner-first (#253): unqualified names bind
    -- to the subquery's own FROM, then fall through to the outer row.
    diffTest "scope: same-table scalar subquery"
      "SELECT name FROM users WHERE age > (SELECT MIN(age) FROM users)",
    diffTest "scope: same-table scalar in SELECT list"
      "SELECT name, (SELECT MAX(age) FROM users) AS m FROM users",
    diffTest "scope: shadowed id in IN subquery"
      "SELECT name FROM users WHERE id IN (SELECT id FROM orders WHERE amount > 150)",
    diffTest "scope: outer fall-through"
      "SELECT name FROM users WHERE EXISTS (SELECT 1 FROM orders WHERE amount > age * 10)",
    diffTest "scope: derived-table outer row (unqualified keys)"
      "SELECT name FROM (SELECT name, age FROM users) AS d WHERE age > (SELECT MIN(age) FROM users)",
    -- Derived-table alias qualifies its columns (#257)
    diffTest "derived: alias-qualified column"
      "SELECT x.name FROM (SELECT name, id FROM users) AS x",
    diffTest "derived: alias-qualified WHERE"
      "SELECT d.name FROM (SELECT name, age FROM users) AS d WHERE d.age > 26",
    diffTest "derived: SELECT * re-qualified"
      "SELECT x.name FROM (SELECT * FROM users) AS x WHERE x.id < 3",
    diffTest "derived: nested aliases"
      "SELECT y.name FROM (SELECT x.name FROM (SELECT name FROM users) AS x) AS y",
    -- LIKE letter case (registry row 8): ASCII case-insensitive in sqlite
    diffTest "LIKE ignores ASCII case (sqlite dialect)"
      "SELECT name FROM users WHERE name LIKE 'al%'",
    diffTest "LIKE whole-string case-insensitive"
      "SELECT name FROM users WHERE department LIKE 'SALES'",
    diffTest "LIKE suffix case-insensitive"
      "SELECT name FROM users WHERE name LIKE '%E'",
    diffTest "NOT LIKE case-insensitive"
      "SELECT name FROM users WHERE name NOT LIKE 'al%'",
    -- Integer division/modulo truncate toward zero (row 6)
    diffTest "integer division and modulo, negatives"
      "SELECT (0 - age) / 7 AS q, (0 - age) % 7 AS r FROM users",
    -- String order is by code point (row 9)
    diffTest "string order: uppercase before lowercase"
      "SELECT name FROM users WHERE name < 'a'",
    -- ON-less JOIN: SQLite accepts this spelling (cross product); DuckDB
    -- rejects it, so this oracle is the one that covers it
    diffTest "ON-less JOIN (cross product + WHERE)"
      "SELECT users.name, orders.product FROM users JOIN orders WHERE users.id = orders.user_id",
    -- DISTINCT and WHERE variants (parse-based versions)
    diffTest "DISTINCT department (parsed)"
      "SELECT DISTINCT department FROM users",
    diffTest "WHERE with AND (parsed)"
      "SELECT * FROM users WHERE age > 25 AND department = 'Engineering'",
    diffTest "WHERE with OR (parsed)"
      "SELECT * FROM users WHERE age < 25 OR age > 30",
    -- INTERSECT/EXCEPT deduplicate (#223): duplicate-bearing inputs on both
    -- sides; both engines (and now our semantics) return set results
    diffTest "INTERSECT dedups duplicate-bearing inputs"
      "SELECT x FROM dups INTERSECT SELECT x FROM other",
    diffTest "EXCEPT dedups duplicate-bearing inputs"
      "SELECT x FROM dups EXCEPT SELECT x FROM other",
    -- Window functions (#214; sqlite3 >= 3.25 supports them). Integer-valued
    -- columns only — the output parser types unknown columns as INTEGER.
    diffTest "ROW_NUMBER over ORDER BY (window)"
      "SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users",
    diffTest "SUM OVER PARTITION BY (window)"
      "SELECT name, SUM(age) OVER (PARTITION BY department) AS s FROM users"
  ].mapM id
  -- Build TestSeq from results
  return results.foldr (fun (name, passed) acc => test name passed $ acc)
    (test "sqlite3 tests complete" true)

end DiffSqlite
