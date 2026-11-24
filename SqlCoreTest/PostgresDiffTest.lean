/-
  Typed core phase 9.0 (#458): parsed SQL through `SqlBridge` + `SqlCore` against Postgres.

  Postgres and DuckDB are the primary references (decision 9), and the oracle for the features
  phase 9 ports (decision D4). This is `SqlCoreTest.DuckdbDiff` for Postgres: the same typed
  test database as temporary tables, the same corpus, results compared as bags of rows (in
  order when the query sorts), decimals as exact rationals.

  A disagreement fails the test unless the query is in `expectedDifferences`, which cites the
  row of `docs/IMPLEMENTATION_DEFINED.md` that records it. Without a reachable Postgres
  (`psql -c 'select 1'`) the test is skipped with a notice (CI starts the runner's Postgres).
-/
import SqlCoreTest.DuckdbDiffTest

namespace SqlCoreTest.PostgresDiff
open SqlCore SqlBridge SqlCoreTest.SchemaExamples SqlCoreTest.BridgeDiff SqlCoreTest.DuckdbDiff

/-- Queries on which Postgres legitimately differs, with the registry row. -/
def expectedDifferences : List (String × String) := []

/-- Text columns get the `C` collation, so strings order by code point as in the typed core
(registry row 9). -/
def pgType : SqlType → String
  | .text => "TEXT COLLATE \"C\""
  | τ => sqlType τ

/-- `CREATE TEMP TABLE` and `INSERT` statements for the typed test database. Column names are
not quoted: Postgres folds unquoted names to lowercase on both sides, so `Name` in a query finds
the column declared `Name` (quoted, it would be case-sensitive). -/
def setupSql : String := String.join <| tables.map fun t =>
  let cs := schema.columns t
  let n := schema.arity t
  let decl := ", ".intercalate ((List.finRange n).map fun i => s!"{(cs i).name} {pgType (cs i).type}")
  let rows := (db t).map fun r => "(" ++ ", ".intercalate ((List.finRange n).map fun i => sqlLit (r i)) ++ ")"
  s!"CREATE TEMP TABLE {tableName t} ({decl});\n" ++
    (if rows.isEmpty then "" else s!"INSERT INTO {tableName t} VALUES {", ".intercalate rows};\n")

/-- A psql cell: as `DuckdbDiff.parseCell`, with Postgres's `t`/`f` booleans. The test data has
no strings `t` or `f`. -/
def parseCell (s : String) : String :=
  if s == "t" then "b:true" else if s == "f" then "b:false" else DuckdbDiff.parseCell s

def runPostgres (sql : String) : IO (Except String (List (List String))) := do
  let child ← IO.Process.spawn {
    cmd := "psql",
    args := #["-X", "-q", "-A", "-t", "-F", "|", "-P", "null=NULL", "-v", "ON_ERROR_STOP=1"],
    stdin := .piped, stdout := .piped, stderr := .piped }
  child.stdin.putStr (setupSql ++ sql ++ ";\n")
  child.stdin.flush
  let (_, child) ← child.takeStdin
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  if (← child.wait) != 0 then return .error err
  let lines := out.splitOn "\n" |>.filter (· ≠ "")
  return .ok (lines.map fun l => (l.splitOn "|").map parseCell)

def postgresAvailable : IO Bool := do
  try
    let r ← IO.Process.output { cmd := "psql", args := #["-X", "-At", "-c", "select 1"] }
    return r.exitCode == 0 && r.stdout.trimAscii.toString == "1"
  catch _ => return false

/-- (compared, documented differences, failures); `none` when Postgres is not reachable. -/
def run : IO (Option (Nat × Nat × List String)) := do
  unless ← postgresAvailable do return none
  let mut n := 0
  let mut documented := 0
  let mut fails : List String := []
  for (sql, ex) in corpus do
    match ex with
    | .rejected _ => continue
    | .rowsDiffer _ => continue
    | _ => pure ()
    let .ok stmt := SqlEquiv.parse sql | fails := s!"{sql}: parse error" :: fails
    let .ok e := elabStmt named stmt | fails := s!"{sql}: did not elaborate" :: fails
    let .ok rs := e.q.eval db | fails := s!"{sql}: SqlCore error" :: fails
    let ours := bagOf sql (rs.map fun r => (List.finRange e.n).map fun i => normCell (r i))
    n := n + 1
    match ← runPostgres sql with
    | .error err => fails := s!"{sql}: Postgres error {err}" :: fails
    | .ok theirs =>
      let theirs := bagOf sql theirs
      if ours != theirs then
        if expectedDifferences.any (·.1 == sql) then documented := documented + 1
        else fails := s!"{sql}:\n    SqlCore  {ours}\n    Postgres {theirs}" :: fails
  return some (n, documented, fails.reverse)

end SqlCoreTest.PostgresDiff
