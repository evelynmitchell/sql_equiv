/-
  Differential testing against PostgreSQL (#224).

  Postgres is the standards tiebreaker of the three oracles (role split in
  docs/IMPLEMENTATION_DEFINED.md, "Engines and their roles"): sqlite is the
  Spider-fidelity target, DuckDB the DECIMAL/strict-typing cross-check, and
  Postgres the closest thing to a reference implementation of the standard.

  Each test parses ONE SQL string with our parser in the `postgres` dialect,
  evaluates it against the Lean-side tables, runs the same string through
  `psql` against the same data (temporary tables, so nothing persists), and
  compares normalized result tables. `diffRejects` cases check that both
  sides refuse a query (our parser, and Postgres with an error).

  Connection: `psql` with the libpq defaults (PGHOST/PGUSER/... if set). The
  suite is skipped, with a notice, when `psql -c 'select 1'` fails. CI starts
  the runner's preinstalled Postgres before the LSpec step (it was 18.6 when
  this landed; the dev environment has 16.15 — `pg_ctlcluster 16 main start`
  plus a superuser role and database for your user).

  Text columns are declared `COLLATE "C"`: string order is then by code point
  (registry row 9) whatever the server's default collation is.

  KNOWN DIVERGENCES (do not add cases that hit these without resolving them;
  the full registry is docs/IMPLEMENTATION_DEFINED.md):
  - LOWER/UPPER of non-ASCII letters (registry row 19): Postgres folds them
    (`lower('ÉCOLE')` is `école`); we fold ASCII letters only, as sqlite
    (`École`). Decided; pinned by `diffDiverges` below and the unit tests
    `lower_non_ascii_ascii_only`, `upper_non_ascii_ascii_only`.
  - Errors that are quieter here: an expression error in a SELECT item is
    NULL for us but fails the whole query in Postgres. So no agreement case
    for MIN/MAX over booleans (row 14), SUM/AVG over booleans (row 18),
    AVG/SUM over text (row 17), mixed-type MIN/MAX (row 13) or cross-type
    comparison (row 10); unit tests pin those. `diffRejects` covers parse-time
    rejections only.
  - Number vs numeric-looking string (`age = '30'`, row 11): Postgres
    converts the untyped literal; we treat it as a type error (#254, keep).
  - ON-less JOIN (row 4): we follow sqlite (cross product); Postgres rejects
    it. Not a `diffRejects` case because we accept it in every dialect.
  - Double-quoted text (row 3): a string literal for us, an identifier in
    Postgres.
  - Scalar subquery with several rows (T17): both error, but Postgres only
    when the value is needed (lazy), and our error is quieter (above).
  - AVG that does not terminate: Postgres prints numeric with 16 places,
    rounded as we do (row 7), but the cases below use terminating averages.
  - Decimal division/modulo: ours is an error pending #201.
  - Pipe characters, `t`/`f`, or numeric-looking strings in data would break
    the output parsing (as in the sqlite and DuckDB harnesses).
-/
import LSpec
import SqlEquiv
import LSpecTests.QueryHelpers

open LSpec
open SqlEquiv
open QueryHelpers

namespace DiffPostgres

-- ============================================================================
-- Shared schema/data: Lean tables and the equivalent Postgres setup SQL
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

/-- Non-ASCII table and column names (#370). -/
private def eteTable : Table := [
  [("Élan", .int 1), ("日本", .int 10)],
  [("Élan", .int 2), ("日本", .int 20)],
  [("Élan", .int 3), ("日本", .int 30)]
]

/-- QueryHelpers.testDb (users/orders/products) extended with items/dups/other/Été. -/
private def db : Database := fun name =>
  if name == "Été" then eteTable
  else if name == "items" then itemsTable
  else if name == "dups" then dupsTable
  else if name == "other" then otherTable
  else testDb name

private def postgresSetupSql : String :=
  "CREATE TEMP TABLE users (id INTEGER, name TEXT COLLATE \"C\", age INTEGER, " ++
    "department TEXT COLLATE \"C\");\n" ++
  "INSERT INTO users VALUES (1, 'Alice', 30, 'Engineering'), (2, 'Bob', 25, 'Sales'), " ++
    "(3, 'Carol', 35, 'Engineering'), (4, 'Dave', 28, 'Marketing'), (5, 'Eve', 22, 'Sales');\n" ++
  "CREATE TEMP TABLE items (id INTEGER, name TEXT COLLATE \"C\", price NUMERIC(10,2));\n" ++
  "INSERT INTO items VALUES (1, 'Bolt', 2.50), (2, 'Nut', 1.25), (3, 'Washer', 3), " ++
    "(4, 'Shim', NULL);\n" ++
  "CREATE TEMP TABLE dups (x INTEGER);\n" ++
  "INSERT INTO dups VALUES (1), (1), (2), (2), (3);\n" ++
  "CREATE TEMP TABLE other (x INTEGER);\n" ++
  "INSERT INTO other VALUES (2), (3), (3), (4);\n" ++
  "CREATE TEMP TABLE Été (Élan INTEGER, 日本 INTEGER);\n" ++
  "INSERT INTO Été VALUES (1, 10), (2, 20), (3, 30);\n"

-- ============================================================================
-- Postgres execution and output parsing
-- ============================================================================

/-- Run SQL through `psql` (unaligned, `|`-separated, header kept, no footer, NULL
    printed as `NULL`, stop at the first error). -/
private def runPostgresRaw (querySql : String) : IO (Except String String) := do
  let fullSql := postgresSetupSql ++ querySql ++ ";\n"
  let child ← IO.Process.spawn {
    cmd := "psql"
    args := #["-X", "-q", "-A", "-F", "|", "-P", "footer=off", "-P", "null=NULL",
              "-v", "ON_ERROR_STOP=1"]
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
  if exitCode != 0 then return .error s!"postgres error: {stderr}"
  return .ok stdout

/-- Parse a psql output cell by shape: NULL, boolean (`t`/`f`), integer, decimal
    (digits.digits, canonicalized through mkDecimal so Postgres's `2.50` and
    `1.5000000000000000` equal our `decimal 25 1` and `decimal 15 1`), otherwise
    string. Test data avoids numeric-looking strings and the strings `t`/`f`. -/
private def parseValue (s : String) : Value :=
  if s == "NULL" then .null none
  else if s == "t" then .bool true
  else if s == "f" then .bool false
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

/-- Parse unaligned output (header line, then `|`-separated rows). -/
private def parsePostgresOutput (output : String) : Table :=
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

/-- Normalize a row: strip qualifiers from column names (Postgres prints bare,
    lowercased names; every alias below is lowercase), erase NULL type tags
    (#324) and the integer/scale-0-decimal difference (Postgres prints `numeric`
    `30` like an integer, #355). The unit tests pin our types. -/
private def normalizeRow (row : Row) : Row :=
  row.map fun (k, v) => (stripQualifier k, match v.eraseNullType with
    | .decimal u 0 => .int u
    | v' => v')

private def rowSortKey (row : Row) : String :=
  row.map (fun (k, v) => s!"{k}={repr v}") |> String.intercalate ","

private def sortTable (tbl : Table) : Table :=
  tbl.map normalizeRow |>.mergeSort fun r1 r2 =>
    decide (rowSortKey r1 < rowSortKey r2)

-- ============================================================================
-- Test runners: one SQL string drives both engines
-- ============================================================================

/-- Parse the SQL in the `postgres` dialect, evaluate, run the same SQL through
    psql, compare result multisets. -/
private def diffTest (description : String) (sql : String) : IO (String × Bool) := do
  match parse sql (dialect := .postgres) with
  | .error e =>
    IO.eprintln s!"  Our parser failed for '{description}': {e}"
    return (description, false)
  | .ok stmt =>
    let ourResult := ((evalStmt db stmt).2).getD []
    match ← runPostgresRaw sql with
    | .error err =>
      IO.eprintln s!"  Postgres error for '{description}': {err}"
      return (description, false)
    | .ok output =>
      let pgResult := parsePostgresOutput output
      if sortTable ourResult == sortTable pgResult then
        return (description, true)
      else
        IO.eprintln s!"  Mismatch for '{description}': ours={repr (sortTable ourResult)} postgres={repr (sortTable pgResult)}"
        return (description, false)

/-- Both sides refuse the query: our parser (postgres dialect) and Postgres. -/
private def diffRejects (description : String) (sql : String) : IO (String × Bool) := do
  let oursRejects := match parse sql (dialect := .postgres) with
    | .error _ => true
    | .ok _ => false
  let pgRejects := match ← runPostgresRaw sql with
    | .error _ => true
    | .ok _ => false
  unless oursRejects && pgRejects do
    IO.eprintln s!"  Rejection mismatch for '{description}': ours rejects={oursRejects} postgres rejects={pgRejects}"
  return (description, oursRejects && pgRejects)

/-- A documented divergence (registry row 19 and similar): passes while ours and Postgres
    both answer and the answers DIFFER, so it fails if either side changes. -/
private def diffDiverges (description : String) (sql : String) : IO (String × Bool) := do
  match parse sql (dialect := .postgres) with
  | .error e =>
    IO.eprintln s!"  Our parser failed for '{description}': {e}"
    return (description, false)
  | .ok stmt =>
    let ourResult := ((evalStmt db stmt).2).getD []
    match ← runPostgresRaw sql with
    | .error err =>
      IO.eprintln s!"  Postgres error for '{description}': {err}"
      return (description, false)
    | .ok output =>
      let theirs := parsePostgresOutput output
      if sortTable ourResult != sortTable theirs then return (description, true)
      IO.eprintln s!"  Expected a divergence for '{description}', both gave {repr (sortTable theirs)}"
      return (description, false)

/-- `DISTINCT … LIMIT 1` without `ORDER BY` (registry T18): which distinct row comes first is the
    implementation's choice. `SqlEquiv` keeps first occurrences, as sqlite does; the typed core keeps
    last occurrences; Postgres hashes, so its row depends on the plan and the version. The test
    asserts what must hold on every engine and logs what Postgres chose:
    * without the `LIMIT`, Postgres and we return the same set of rows;
    * with it, each side returns exactly one row, and that row is one of the distinct rows.
    The order Postgres returned is printed, for the registry; it is not asserted. -/
private def distinctLimitTest (description : String) (distinctSql : String) :
    IO (String × Bool) := do
  let limitSql := distinctSql ++ " LIMIT 1"
  match parse distinctSql (dialect := .postgres), parse limitSql (dialect := .postgres) with
  | .ok full, .ok limited =>
    let oursFull := ((evalStmt db full).2).getD []
    let oursLimited := ((evalStmt db limited).2).getD []
    match ← runPostgresRaw distinctSql, ← runPostgresRaw limitSql with
    | .ok outFull, .ok outLimited =>
      let pgFull := parsePostgresOutput outFull
      let pgLimited := parsePostgresOutput outLimited
      let key (r : Row) := rowSortKey (normalizeRow r)
      IO.println s!"  [DiffPostgres] {description}: Postgres order {pgFull.map key}, LIMIT 1 {pgLimited.map key}; SqlEquiv order {oursFull.map key}, LIMIT 1 {oursLimited.map key}"
      let sameSet := sortTable oursFull == sortTable pgFull
      let member (one : Table) := one.length == 1 && one.all fun r => (pgFull.map key).contains (key r)
      if sameSet && member pgLimited && member oursLimited && pgFull.length > 1 then
        return (description, true)
      IO.eprintln s!"  DISTINCT/LIMIT check failed for '{description}': sameSet={sameSet} postgres={repr pgLimited} ours={repr oursLimited}"
      return (description, false)
    | .error err, _ | _, .error err =>
      IO.eprintln s!"  Postgres error for '{description}': {err}"
      return (description, false)
  | _, _ =>
    IO.eprintln s!"  Our parser failed for '{description}'"
    return (description, false)

private def postgresAvailable : IO Bool := do
  try
    let r ← IO.Process.output { cmd := "psql", args := #["-X", "-At", "-c", "select 1"] }
    return r.exitCode == 0 && (r.stdout.splitOn "\n").head? == some "1"
  catch _ => return false

/-- All differential tests against Postgres. Skips (with a notice) if no Postgres
    is reachable through `psql`. -/
def runAllTests : IO TestSeq := do
  unless ← postgresAvailable do
    IO.eprintln "  [DiffPostgres] no Postgres reachable via psql, skipping differential tests"
    return test "postgres not available (skipped)" true
  let results ← [
    -- Decimal literals and exact arithmetic
    diffTest "decimal literal canonicalization" "SELECT 2.50 AS x",
    diffTest "exact 0.1 + 0.2" "SELECT 0.1 + 0.2 AS x",
    diffTest "scale-aligned add" "SELECT 1.5 + 2.25 AS x",
    diffTest "decimal multiplication" "SELECT 1.5 * 2.0 AS x",
    diffTest "int + decimal promotion" "SELECT 1 + 2.5 AS x",
    diffTest "promotion in WHERE" "SELECT name FROM items WHERE price > 2",
    -- Integer division and modulo truncate toward zero (row 6; DuckDB differs on `/`)
    diffTest "integer division truncates"
      "SELECT 7 / 2 AS a, (0 - 7) / 2 AS b, (0 - 7) % 2 AS c",
    diffTest "modulo of negatives"
      "SELECT (0 - age) % 7 AS r FROM users",
    -- NULL semantics
    diffTest "NULL + decimal is NULL" "SELECT NULL + 1.5 AS n",
    diffTest "IS NULL over decimal column" "SELECT name FROM items WHERE price IS NULL",
    -- Aggregates (NULL skipped); AVG exact (row 7), a numeric in Postgres
    diffTest "SUM over decimal column" "SELECT SUM(price) AS s FROM items",
    diffTest "AVG over decimal column" "SELECT AVG(price) AS a FROM items",
    diffTest "AVG over integers" "SELECT AVG(age) AS a FROM users",
    diffTest "AVG over integers, grouped"
      "SELECT department, AVG(age) AS a FROM users GROUP BY department",
    diffTest "MIN/MAX over decimal column" "SELECT MIN(price) AS lo, MAX(price) AS hi FROM items",
    diffTest "COUNT skips NULLs" "SELECT COUNT(price) AS c FROM items",
    diffTest "HAVING on an aggregate"
      "SELECT department, COUNT(*) AS c FROM users GROUP BY department HAVING COUNT(*) BETWEEN 2 AND 3",
    -- Basic filters
    diffTest "WHERE with AND" "SELECT * FROM users WHERE age > 25 AND department = 'Engineering'",
    diffTest "WHERE with OR" "SELECT * FROM users WHERE age < 25 OR age > 30",
    diffTest "DISTINCT" "SELECT DISTINCT department FROM users",
    -- NULL ordering under Postgres's rule (row 1: NULL largest, so last on ASC
    -- and first on DESC); LIMIT 1 makes the position of the NULL price observable
    diffTest "NULL largest on ASC (postgres rule)"
      "SELECT name FROM items ORDER BY price LIMIT 1",
    diffTest "NULL largest on DESC (postgres rule)"
      "SELECT name FROM items ORDER BY price DESC LIMIT 1",
    diffTest "explicit NULLS FIRST"
      "SELECT name FROM items ORDER BY price NULLS FIRST LIMIT 1",
    diffTest "explicit DESC NULLS LAST"
      "SELECT name FROM items ORDER BY price DESC NULLS LAST LIMIT 1",
    diffTest "ORDER BY non-projected column"
      "SELECT name FROM items WHERE price IS NOT NULL ORDER BY price LIMIT 1",
    diffTest "ORDER BY non-projected DESC with LIMIT"
      "SELECT name FROM users ORDER BY age DESC LIMIT 2",
    -- Row 5: DISTINCT with a sort key that is not selected is an error in Postgres;
    -- the postgres dialect rejects it at parse time
    diffRejects "DISTINCT + ORDER BY unselected key (row 5)"
      "SELECT DISTINCT name FROM items ORDER BY price",
    diffTest "DISTINCT + ORDER BY a selected key"
      "SELECT DISTINCT department FROM users ORDER BY department LIMIT 2",
    -- T18: which distinct row a LIMIT keeps without ORDER BY is implementation-defined
    distinctLimitTest "DISTINCT order and LIMIT 1 (T18)"
      "SELECT DISTINCT department FROM users WHERE id > 1",
    -- Row 15: a compound's ORDER BY sees the first branch's names only
    diffTest "compound ORDER BY first branch's name (row 15)"
      "SELECT name AS x FROM users UNION ALL SELECT department AS y FROM users ORDER BY x LIMIT 2",
    diffRejects "compound ORDER BY a later branch's name (row 15)"
      "SELECT name AS x FROM users UNION ALL SELECT department AS y FROM users ORDER BY y",
    -- Joins
    diffTest "CROSS JOIN product"
      "SELECT users.name, items.name FROM users CROSS JOIN items WHERE items.price > 2",
    diffTest "INNER JOIN with ON"
      "SELECT u.name, i.name AS item FROM users AS u JOIN items AS i ON u.id = i.id WHERE i.price IS NOT NULL",
    diffTest "LEFT JOIN keeps unmatched rows"
      "SELECT u.name, i.price FROM users AS u LEFT JOIN items AS i ON u.id = i.id",
    -- Subqueries
    diffTest "NOT IN with UNION subquery"
      "SELECT name FROM items WHERE name NOT IN (SELECT users.department FROM users UNION SELECT users.name FROM users)",
    diffTest "scope: same-table scalar subquery"
      "SELECT name FROM users WHERE age > (SELECT MIN(age) FROM users)",
    diffTest "scope: shadowed id in IN subquery"
      "SELECT name FROM users WHERE id IN (SELECT id FROM items WHERE price > 2)",
    diffTest "scope: outer fall-through"
      "SELECT name FROM users WHERE EXISTS (SELECT 1 FROM items WHERE id = age - 27)",
    diffTest "NOT IN null: NULL in the subquery"
      "SELECT name FROM items WHERE id NOT IN (SELECT price FROM items)",
    diffTest "NOT IN null: NULL probe"
      "SELECT name FROM items WHERE price NOT IN (SELECT id FROM users)",
    diffTest "NOT IN null: empty subquery keeps a NULL probe"
      "SELECT name FROM items WHERE price NOT IN (SELECT id FROM users WHERE id > 100)",
    -- Derived tables (#257)
    diffTest "derived: alias-qualified column"
      "SELECT x.name FROM (SELECT name, id FROM users) AS x",
    diffTest "derived: alias-qualified WHERE"
      "SELECT d.name FROM (SELECT name, age FROM users) AS d WHERE d.age > 26",
    diffTest "derived: nested aliases"
      "SELECT y.name FROM (SELECT x.name FROM (SELECT name FROM users) AS x) AS y",
    -- Strings: MIN/MAX, code-point order (row 9), LIKE case-sensitive (row 8) and wildcards
    diffTest "MIN/MAX over strings"
      "SELECT MIN(name) AS lo, MAX(name) AS hi FROM users",
    diffTest "MAX over strings per group"
      "SELECT department, MAX(name) AS m FROM users GROUP BY department",
    diffTest "string order: uppercase before lowercase"
      "SELECT name FROM users WHERE name < 'a'",
    diffTest "LIKE is case-sensitive (postgres dialect)"
      "SELECT name FROM users WHERE name LIKE 'al%'",
    diffTest "LIKE matching case"
      "SELECT name FROM users WHERE name LIKE 'Al%'",
    diffTest "LIKE wildcard: _"
      "SELECT name FROM users WHERE name LIKE '_ob'",
    diffTest "LIKE wildcard: interior %"
      "SELECT name FROM users WHERE name LIKE 'C%l'",
    diffTest "LIKE wildcard: NOT LIKE with _ and %"
      "SELECT name FROM users WHERE name NOT LIKE '_%e'",
    -- ROUND/ABS on decimals (row 16): Postgres returns numeric, same values
    diffTest "ROUND of an integer column, negative places"
      "SELECT ROUND(age, -1) AS r FROM users",
    diffTest "ROUND of decimals"
      "SELECT ROUND(7.45, 1) AS a, ROUND(-2.5) AS b, ROUND(123.456, -1) AS c, ABS(-2.50) AS d FROM users WHERE id = 1",
    -- BETWEEN (#354), including a NULL bound
    diffTest "NOT BETWEEN"
      "SELECT name FROM users WHERE age NOT BETWEEN 25 AND 30",
    diffTest "NOT BETWEEN with a NULL bound"
      "SELECT name FROM users WHERE age NOT BETWEEN NULL AND 30",
    -- CASE
    diffTest "CASE over a column"
      "SELECT name, CASE WHEN age >= 30 THEN 'senior' ELSE 'junior' END AS band FROM users",
    -- Booleans as values
    diffTest "boolean result column"
      "SELECT name, age > 26 AS older FROM users",
    -- DISTINCT and GROUP BY treat typed and untyped NULLs as one value (#315)
    diffTest "distinct null: typed and untyped NULL are one row"
      "SELECT DISTINCT p FROM (SELECT price AS p FROM items WHERE price IS NULL UNION ALL SELECT NULL) AS t",
    diffTest "distinct null: COUNT(DISTINCT) over numbers by value"
      "SELECT COUNT(DISTINCT v) AS c FROM (SELECT 1 AS v UNION ALL SELECT 1.0) AS t",
    -- Set operations (#223, #324)
    diffTest "set op: INTERSECT across column names"
      "SELECT x AS a FROM dups INTERSECT SELECT x AS b FROM other",
    diffTest "set op: EXCEPT across column names"
      "SELECT id FROM users EXCEPT SELECT x FROM dups",
    diffTest "set op: typed and untyped NULL are one row"
      "SELECT price FROM items WHERE price IS NULL UNION SELECT NULL",
    diffTest "set op: numbers compare by value"
      "SELECT id FROM users WHERE id = 1 EXCEPT SELECT 1.0",
    diffTest "INTERSECT dedups duplicate-bearing inputs"
      "SELECT x FROM dups INTERSECT SELECT x FROM other",
    diffTest "EXCEPT dedups duplicate-bearing inputs"
      "SELECT x FROM dups EXCEPT SELECT x FROM other",
    diffTest "UNION ALL keeps duplicates"
      "SELECT x FROM dups UNION ALL SELECT x FROM other",
    -- Window functions (#214)
    diffTest "AVG over PARTITION BY"
      "SELECT name, AVG(age) OVER (PARTITION BY department) AS a FROM users",
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
    -- LOWER/UPPER (registry row 19): agree on ASCII letters; on non-ASCII letters this engine
    -- folds them and we do not (decided: ASCII, as sqlite)
    diffTest "LOWER/UPPER of ASCII letters"
      "SELECT LOWER(name) AS lo, UPPER(name) AS up FROM users",
    diffDiverges "LOWER/UPPER of non-ASCII letters (row 19 divergence)"
      "SELECT LOWER('ÉCOLE') AS lo, UPPER('école') AS up",
    -- Non-ASCII identifiers (#370): every engine accepts them unquoted
    diffTest "non-ASCII table, column and alias names"
      "SELECT Élan, 日本 AS a€b FROM Été WHERE Élan > 1",
    diffTest "non-ASCII table alias as qualifier"
      "SELECT é.Élan FROM Été AS é WHERE é.日本 < 25",
    diffTest "no WHERE returns all" "SELECT * FROM users"
  ].mapM id
  return results.foldr (fun (name, passed) acc => test name passed $ acc)
    (test "postgres tests complete" true)

end DiffPostgres
