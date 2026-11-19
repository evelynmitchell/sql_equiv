/-
  Differential testing against DuckDB (#203).

  DuckDB complements the SQLite oracle: it has a true DECIMAL type (SQLite
  stores decimals as IEEE floats), strict typing, and standard-compliant
  NULL handling — exactly the areas the type expansion (#201) touches.

  Each test parses ONE SQL string with our parser, evaluates it against the
  Lean-side tables, runs the same string through the duckdb CLI against the
  same data, and compares normalized result tables. This exercises the
  parser, evaluator, and pretty-printing of values in one pass.

  KNOWN DIVERGENCES (do not add cases that hit these without resolving them;
  the full registry of implementation-defined behaviour, with sqlite and
  Postgres results and our decisions, is docs/IMPLEMENTATION_DEFINED.md):
  - AVG over decimals: we truncate at the sum's scale; DuckDB returns a
    DOUBLE. Test data below is curated so the average is exact. Blocked on
    the decimal division/scale policy (#201).
  - Decimal division/modulo: ours is intentionally an error pending the
    same #201 policy decision; DuckDB computes it.
  - (resolved) ORDER BY on non-projected columns used to no-op (#206); now
    fixed and covered by the ORDER BY agreement case below.
  - (resolved by #320) DISTINCT + ORDER BY on a non-projected column
    (registry row 5): in the duckdb dialect each distinct row now sorts by
    its first source row's key, as DuckDB does. This harness compares bags,
    so the order is checked in `SqlCoreTest/DuckdbDiffTest.lean`, which runs
    SqlEquiv, the typed core and DuckDB on the same queries.
  - (resolved by #330) `x NOT IN (subquery)` where `x` or a subquery value is
    NULL used to return the row; it is now unknown and drops it, as in the
    engines. Covered by the `NOT IN null:` cases below.
  - (resolved by #323) LIKE with `_` or a `%` inside the pattern used to treat
    them as literal characters; `likeMatch` now matches them as wildcards, as
    the engines do. Covered by the `LIKE wildcard:` cases below.
  - (resolved by #324) INTERSECT/EXCEPT/UNION used to compare rows by
    (name, value) pairs and keep typed and untyped NULLs apart; rows are now
    compared by value in column order, NULL tags erased. Covered by the
    `set op:` cases below.
  - Number vs numeric-looking string (`age = '30'`, registry row 11): DuckDB
    converts the string; we treat it as a type error and drop the row (#254,
    decided: keep).
  - ON-less JOIN (`A JOIN B WHERE ...`): we follow Spider/SQLite (cross
    product); DuckDB rejects the spelling outright (requires CROSS JOIN).
    The CROSS JOIN case below covers the shared semantics.
  - (resolved by #223) INTERSECT/EXCEPT used to keep left-side duplicates
    (bag-style); applySetOp now deduplicates per the SQL standard (set
    semantics), matching DuckDB. Covered by the duplicate-bearing set-op
    cases below. The ALL variants (INTERSECT ALL/EXCEPT ALL) are still not
    parsed.
  - MIN/MAX over mixed numbers and strings (registry row 13): DuckDB and our
    `duckdb` dialect both treat it as an error, but DuckDB fails the query
    while ours yields NULL in a SELECT list (the cross-cutting "quieter
    error"), so no differential case; pinned by unit tests instead.
  - Integer `/` (registry row 6): DuckDB's `/` is float division (7 / 2 =
    3.5); ours truncates like sqlite and Postgres. DuckDB's `//` matches ours,
    but we do not parse `//`. Pinned by `int_division_*`.
  - Pipe characters or numeric-looking strings in data would break the
    `-list` output parsing (same limitation as the sqlite harness).
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

/-- Duplicate-bearing table for INTERSECT/EXCEPT set-semantics cases (#223). -/
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

private def duckdbSetupSql : String :=
  "CREATE TABLE users (id INTEGER, name TEXT, age INTEGER, department TEXT);\n" ++
  "INSERT INTO users VALUES (1, 'Alice', 30, 'Engineering'), (2, 'Bob', 25, 'Sales'), " ++
    "(3, 'Carol', 35, 'Engineering'), (4, 'Dave', 28, 'Marketing'), (5, 'Eve', 22, 'Sales');\n" ++
  "CREATE TABLE items (id INTEGER, name TEXT, price DECIMAL(10,2));\n" ++
  "INSERT INTO items VALUES (1, 'Bolt', 2.50), (2, 'Nut', 1.25), (3, 'Washer', 3), " ++
    "(4, 'Shim', NULL);\n" ++
  "CREATE TABLE dups (x INTEGER);\n" ++
  "INSERT INTO dups VALUES (1), (1), (2), (2), (3);\n" ++
  "CREATE TABLE other (x INTEGER);\n" ++
  "INSERT INTO other VALUES (2), (3), (3), (4);\n"

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

/-- Parse a duckdb output cell by shape: NULL, boolean (`true`/`false`),
    integer, decimal (digits.digits, canonicalized through mkDecimal so `2.50`
    equals our stored `decimal 25 1`), otherwise string. Test data avoids
    numeric-looking strings and the strings `true`/`false`. -/
private def parseValue (s : String) : Value :=
  if s == "NULL" then .null none
  else if s == "true" then .bool true
  else if s == "false" then .bool false
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

/-- Normalize a row: strip qualifiers from column names, and erase the type tag of a NULL,
    which an engine's printed `NULL` does not carry (#324). -/
private def normalizeRow (row : Row) : Row :=
  row.map fun (k, v) => (stripQualifier k, v.eraseNullType)

private def rowSortKey (row : Row) : String :=
  row.map (fun (k, v) => s!"{k}={repr v}") |> String.intercalate ","

private def sortTable (tbl : Table) : Table :=
  tbl.map normalizeRow |>.mergeSort fun r1 r2 =>
    decide (rowSortKey r1 < rowSortKey r2)

-- ============================================================================
-- Test runner: one SQL string drives both engines
-- ============================================================================

/-- Parse the SQL with our parser, evaluate, run the same SQL through duckdb,
    compare result multisets. Parsed in the `duckdb` dialect, so every
    implementation-defined choice is DuckDB's (e.g. NULLS LAST both ways). -/
private def diffTest (description : String) (sql : String) : IO (String × Bool) := do
  match parse sql (dialect := .duckdb) with
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
    -- NULL ordering under DuckDB's rule (NULLS LAST both ways); LIMIT 1
    -- makes the position of the NULL price observable
    diffTest "NULLs last on ASC (duckdb rule)"
      "SELECT name FROM items ORDER BY price LIMIT 1",
    diffTest "NULLs last on DESC (duckdb rule)"
      "SELECT name FROM items ORDER BY price DESC LIMIT 1",
    diffTest "explicit NULLS FIRST"
      "SELECT name FROM items ORDER BY price NULLS FIRST LIMIT 1",
    diffTest "explicit DESC NULLS FIRST"
      "SELECT name FROM items ORDER BY price DESC NULLS FIRST LIMIT 1",
    -- ORDER BY on a non-projected column (#206 fix); LIMIT makes order observable
    diffTest "ORDER BY non-projected column"
      "SELECT name FROM items WHERE price IS NOT NULL ORDER BY price LIMIT 1",
    diffTest "ORDER BY non-projected DESC with LIMIT"
      "SELECT name FROM users ORDER BY age DESC LIMIT 2",
    -- Cross-product join semantics (explicit CROSS JOIN — see known
    -- divergences for the ON-less spelling)
    diffTest "CROSS JOIN product"
      "SELECT users.name, items.name FROM users CROSS JOIN items WHERE items.price > 2",
    -- Set-operation subquery (#218): UNION inside a NOT IN subquery.
    diffTest "NOT IN with UNION subquery"
      "SELECT name FROM items WHERE name NOT IN (SELECT users.department FROM users UNION SELECT users.name FROM users)",
    diffTest "MIN/MAX over strings"
      "SELECT MIN(name) AS lo, MAX(name) AS hi FROM users",
    diffTest "MAX over strings per group"
      "SELECT department, MAX(name) AS m FROM users GROUP BY department",
    -- LIKE letter case (registry row 8): case-sensitive in the duckdb dialect
    diffTest "LIKE is case-sensitive (duckdb dialect)"
      "SELECT name FROM users WHERE name LIKE 'al%'",
    diffTest "LIKE matching case"
      "SELECT name FROM users WHERE name LIKE 'Al%'",
    diffTest "NOT LIKE"
      "SELECT name FROM users WHERE name NOT LIKE 'Al%'",
    -- NOT BETWEEN (#354), including a NULL bound
    diffTest "NOT BETWEEN"
      "SELECT name FROM users WHERE age NOT BETWEEN 25 AND 30",
    diffTest "NOT BETWEEN with a NULL bound"
      "SELECT name FROM users WHERE age NOT BETWEEN NULL AND 30",
    -- Modulo truncates toward zero (row 6; `/` differs, see KNOWN DIVERGENCES)
    diffTest "modulo of negatives"
      "SELECT (0 - age) % 7 AS r FROM users",
    -- String order is by code point (row 9)
    diffTest "string order: uppercase before lowercase"
      "SELECT name FROM users WHERE name < 'a'",
    -- MIN/MAX over booleans (registry row 14): duckdb dialect gives a boolean
    diffTest "MIN/MAX over booleans (duckdb: boolean result)"
      "SELECT MAX(age > 26) AS hi, MIN(age > 26) AS lo FROM users",
    diffTest "MAX over booleans per group"
      "SELECT department, MAX(age > 26) AS m FROM users GROUP BY department",
    -- Subquery name resolution is inner-first (#253): unqualified names bind
    -- to the subquery's own FROM, then fall through to the outer row.
    diffTest "scope: same-table scalar subquery"
      "SELECT name FROM users WHERE age > (SELECT MIN(age) FROM users)",
    diffTest "scope: shadowed id in IN subquery"
      "SELECT name FROM users WHERE id IN (SELECT id FROM items WHERE price > 2)",
    diffTest "scope: outer fall-through"
      "SELECT name FROM users WHERE EXISTS (SELECT 1 FROM items WHERE id = age - 27)",
    -- Derived-table alias qualifies its columns (#257)
    diffTest "derived: alias-qualified column"
      "SELECT x.name FROM (SELECT name, id FROM users) AS x",
    diffTest "derived: alias-qualified WHERE"
      "SELECT d.name FROM (SELECT name, age FROM users) AS d WHERE d.age > 26",
    diffTest "derived: SELECT * re-qualified"
      "SELECT x.name FROM (SELECT * FROM users) AS x WHERE x.id < 3",
    diffTest "derived: nested aliases"
      "SELECT y.name FROM (SELECT x.name FROM (SELECT name FROM users) AS x) AS y",
    -- LIKE: `_` matches one character and `%` any sequence, anywhere (#323)
    diffTest "LIKE wildcard: _"
      "SELECT name FROM users WHERE name LIKE '_ob'",
    diffTest "LIKE wildcard: interior %"
      "SELECT name FROM users WHERE name LIKE 'C%l'",
    diffTest "LIKE wildcard: NOT LIKE with _ and %"
      "SELECT name FROM users WHERE name NOT LIKE '_%e'",
    -- DISTINCT and GROUP BY: a typed and an untyped NULL are one value (#315)
    diffTest "distinct null: typed and untyped NULL are one row"
      "SELECT DISTINCT p FROM (SELECT price AS p FROM items WHERE price IS NULL UNION ALL SELECT NULL) AS t",
    diffTest "distinct null: COUNT(DISTINCT) over numbers by value"
      "SELECT COUNT(DISTINCT v) AS c FROM (SELECT 1 AS v UNION ALL SELECT 1.0) AS t",
    -- NOT IN (subquery) is three-valued (#330): a NULL in the subquery, or a NULL
    -- probe against a non-empty subquery, makes it unknown and drops the row
    diffTest "NOT IN null: NULL in the subquery"
      "SELECT name FROM items WHERE id NOT IN (SELECT price FROM items)",
    diffTest "NOT IN null: NULL probe"
      "SELECT name FROM items WHERE price NOT IN (SELECT id FROM users)",
    diffTest "NOT IN null: empty subquery keeps a NULL probe"
      "SELECT name FROM items WHERE price NOT IN (SELECT id FROM users WHERE id > 100)",
    -- Set operations match rows by position and value, NULL tags erased (#324)
    diffTest "set op: INTERSECT across column names"
      "SELECT x AS a FROM dups INTERSECT SELECT x AS b FROM other",
    diffTest "set op: EXCEPT across column names"
      "SELECT id FROM users EXCEPT SELECT x FROM dups",
    diffTest "set op: typed and untyped NULL are one row"
      "SELECT price FROM items WHERE price IS NULL UNION SELECT NULL",
    -- (an EXCEPT that empties: DuckDB types a set operation's column as the
    -- common supertype, so a surviving row would print as 1.0 where we keep 1)
    diffTest "set op: numbers compare by value"
      "SELECT id FROM users WHERE id = 1 EXCEPT SELECT 1.0",
    -- INTERSECT/EXCEPT deduplicate (#223): duplicate-bearing inputs on both
    -- sides; both engines (and now our semantics) return set results
    diffTest "INTERSECT dedups duplicate-bearing inputs"
      "SELECT x FROM dups INTERSECT SELECT x FROM other",
    diffTest "EXCEPT dedups duplicate-bearing inputs"
      "SELECT x FROM dups EXCEPT SELECT x FROM other",
    -- Window functions (#214). AVG window cases are omitted: DuckDB returns
    -- DOUBLE while we truncate (same known divergence as plain AVG).
    diffTest "ROW_NUMBER over ORDER BY"
      "SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users",
    diffTest "RANK with ties"
      "SELECT name, RANK() OVER (ORDER BY department) AS r FROM users",
    diffTest "DENSE_RANK with ties"
      "SELECT name, DENSE_RANK() OVER (ORDER BY department) AS dr FROM users",
    diffTest "SUM OVER PARTITION BY"
      "SELECT name, SUM(age) OVER (PARTITION BY department) AS s FROM users",
    diffTest "running SUM (ORDER BY default frame)"
      "SELECT name, SUM(age) OVER (ORDER BY age) AS s FROM users",
    diffTest "running SUM with peers (ties share frame)"
      "SELECT name, SUM(age) OVER (ORDER BY department) AS s FROM users",
    diffTest "ROW_NUMBER with PARTITION BY and ORDER BY"
      "SELECT name, ROW_NUMBER() OVER (PARTITION BY department ORDER BY age) AS rn FROM users",
    diffTest "SUM OVER () on decimal column skips NULL"
      "SELECT name, SUM(price) OVER () AS s FROM items",
    diffTest "COUNT(*) OVER ()"
      "SELECT name, COUNT(*) OVER () AS c FROM users",
    diffTest "no WHERE returns all" "SELECT * FROM users"
  ].mapM id
  return results.foldr (fun (name, passed) acc => test name passed $ acc)
    (test "duckdb tests complete" true)

end DiffDuckdb
