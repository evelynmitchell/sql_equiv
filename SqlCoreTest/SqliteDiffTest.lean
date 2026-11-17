/-
  Typed core phases 8e and 8f: bare columns (registry T9) and scalar
  subqueries with several rows (T17) through `SqlBridge` + `SqlCore`, against
  sqlite.

  Only sqlite accepts a column that is neither grouped nor aggregated next to
  aggregates; the standard, Postgres and DuckDB reject it. In the sqlite
  dialect (`DialectConfig.bareColumns = .sqlite`) the bridge reads such a
  column from the row of the query's one `MIN`/`MAX` (`AggCall.atExtreme`),
  or from the group's first row (`AggCall.first`). Each query is parsed in
  the sqlite dialect, elaborated, evaluated by `SqlCore` and by the `sqlite3`
  CLI on the same tables (`DuckdbDiff.setupSql`), and the results compared as
  bags of rows (as lists under `ORDER BY`).

  The corpus reads only `users`, `orders` and `museum`: sqlite's
  `CAST(… AS DECIMAL)` is an integer, so the generated `items` prices are
  not exact there. Without a `sqlite3` binary the test is skipped.
-/
import SqlCoreTest.DuckdbDiffTest

namespace SqlCoreTest.SqliteDiff
open SqlCore SqlBridge SqlCoreTest.SchemaExamples SqlCoreTest.BridgeDiff SqlCoreTest.DuckdbDiff

/-- The test schema, elaborated with sqlite's choices. -/
def namedSqlite : NamedSchema := { named with config := SqlEquiv.Dialect.sqlite.config }

/-- Queries that must elaborate in the sqlite dialect and agree with sqlite. -/
def corpus : List String := [
  -- one MAX/MIN: the bare column comes from the row where it is extreme
  "SELECT department, MAX(age), name FROM users GROUP BY department",
  "SELECT department, MIN(age), name FROM users GROUP BY department",
  "SELECT MAX(age), name FROM users",
  "SELECT user_id, MAX(amount), product FROM orders GROUP BY user_id",
  "SELECT MAX(staff), name FROM museum",
  "SELECT MIN(staff), name FROM museum",
  -- every MAX argument NULL: the group's last row. sqlite's choice here depends on the query plan
  -- (registry T9): with `WHERE staff IS NULL` its MAX optimisation returns the first row instead,
  -- so that form is not in the corpus.
  "SELECT MAX(staff), name FROM museum WHERE name IN ('m3', 'm6')",
  "SELECT department, MAX(id * 0 + NULL), name FROM users GROUP BY department",
  -- MAX only in HAVING, or with other aggregates
  "SELECT department, name FROM users GROUP BY department HAVING MAX(age) > 26",
  "SELECT department, COUNT(*), SUM(age), MAX(age), name FROM users GROUP BY department",
  "SELECT department, name, MAX(age) FROM users GROUP BY department ORDER BY MAX(age)",
  -- no MIN/MAX: the group's first row
  "SELECT department, COUNT(*), name FROM users GROUP BY department",
  "SELECT department, name FROM users GROUP BY department",
  "SELECT COUNT(*), name FROM users",
  "SELECT user_id, product FROM orders GROUP BY user_id",
  -- a scalar subquery with several rows: sqlite takes the first row (registry T17)
  "SELECT name FROM users WHERE age > (SELECT age FROM users)",
  "SELECT name FROM users WHERE age > (SELECT age FROM users ORDER BY age DESC)"
]

/-- Queries that stay unsupported in the sqlite dialect, with the error category. -/
def rejected : List (String × String) := [
  ("SELECT MIN(age), MAX(age), name FROM users", "unsupported: bare column with several MIN/MAX"),
  ("SELECT MAX(DISTINCT age), name FROM users", "unsupported: bare column with MIN/MAX DISTINCT")
]

def runSqlite (sql : String) : IO (Except String (List (List String))) := do
  let child ← IO.Process.spawn {
    cmd := "sqlite3", args := #[":memory:", "-list", "-header", "-nullvalue", "NULL"],
    stdin := .piped, stdout := .piped, stderr := .piped }
  child.stdin.putStr (setupSql ++ sql ++ ";\n")
  child.stdin.flush
  let (_, child) ← child.takeStdin
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  if (← child.wait) != 0 || !err.isEmpty then return .error err
  let lines := out.splitOn "\n" |>.filter (· ≠ "")
  return .ok ((lines.drop 1).map fun l => (l.splitOn "|").map parseCell)

def sqliteAvailable : IO Bool := do
  try return (← IO.Process.output { cmd := "sqlite3", args := #["--version"] }).exitCode == 0
  catch _ => return false

/-- (compared, failures); `none` when sqlite3 is missing. -/
def run : IO (Option (Nat × List String)) := do
  unless ← sqliteAvailable do return none
  let mut n := 0
  let mut fails : List String := []
  for sql in corpus do
    let .ok stmt := SqlEquiv.parse sql (dialect := .sqlite) | fails := s!"{sql}: parse error" :: fails
    match elabStmt namedSqlite stmt with
    | .error e => fails := s!"{sql}: did not elaborate: {e.category}" :: fails
    | .ok e =>
      let .ok rs := e.q.eval db | fails := s!"{sql}: SqlCore error" :: fails
      let ours := bagOf sql (rs.map fun r => (List.finRange e.n).map fun i => normCell (r i))
      n := n + 1
      match ← runSqlite sql with
      | .error err => fails := s!"{sql}: sqlite error {err}" :: fails
      | .ok theirs =>
        let theirs := bagOf sql theirs
        if ours != theirs then fails := s!"{sql}:\n    SqlCore {ours}\n    sqlite  {theirs}" :: fails
  for (sql, cat) in rejected do
    let .ok stmt := SqlEquiv.parse sql (dialect := .sqlite) | fails := s!"{sql}: parse error" :: fails
    match elabStmt namedSqlite stmt with
    | .error e =>
      unless e.category.startsWith cat do fails := s!"{sql}: expected {cat}, got {e.category}" :: fails
    | .ok _ => fails := s!"{sql}: expected rejection {cat}, but it elaborated" :: fails
  -- The default (standard) dialect still rejects bare columns.
  for sql in corpus.take 3 do
    let .ok stmt := SqlEquiv.parse sql | fails := s!"{sql}: parse error" :: fails
    if (elabStmt named stmt).toOption.isSome then
      fails := s!"{sql}: elaborated in the standard dialect" :: fails
  return some (n, fails.reverse)

end SqlCoreTest.SqliteDiff
