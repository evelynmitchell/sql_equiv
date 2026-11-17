/-
  Typed core phase 6 (#295): parsed SQL through `SqlBridge` + `SqlCore`
  against DuckDB.

  The DuckDB tables are generated from the typed test database
  (`SqlCoreTest.SchemaExamples`): declared column types become
  `INTEGER`/`TEXT`/`BOOLEAN`/`DECIMAL(10,2)` and its rows become `INSERT`s,
  so the data cannot drift. Each in-fragment query of `BridgeDiff.corpus` is
  elaborated and evaluated by `SqlCore`, run by the `duckdb` CLI, and the
  results are compared as bags of rows, decimals as exact rationals.

  A disagreement fails the test unless the query is in `expectedDifferences`,
  which cites the row of `docs/IMPLEMENTATION_DEFINED.md` that records it.
  Without a `duckdb` binary the test is skipped with a notice (CI installs it).
-/
import SqlCoreTest.BridgeDiffTest

namespace SqlCoreTest.DuckdbDiff
open SqlCore SqlBridge SqlCoreTest.SchemaExamples SqlCoreTest.BridgeDiff

/-- Queries on which DuckDB legitimately differs, with the registry row. -/
def expectedDifferences : List (String × String) := [
  ("SELECT id * 10 + 1, age - 1, age / 7, age % 7 FROM users",
    "integer `/`: DuckDB divides as DOUBLE (registry row 6)"),
  ("SELECT name, staff FROM museum ORDER BY staff DESC, name",
    "default NULL position: DuckDB puts NULLs last under DESC, the standard dialect first (registry row 1)")
]

def sqlType : SqlType → String
  | .int => "INTEGER" | .text => "TEXT" | .bool => "BOOLEAN" | .decimal => "DECIMAL(10,2)"

def sqlLit : Datum → String
  | none => "NULL"
  | some (.int z) => toString z
  | some (.text s) => "'" ++ s.replace "'" "''" ++ "'"
  | some (.bool b) => if b then "TRUE" else "FALSE"
  | some (.decimal q) => s!"CAST({q.num} AS DECIMAL(20,2)) / {q.den}"

def tables : List T := [.users, .orders, .products, .items, .singer, .museum]

/-- `CREATE TABLE` and `INSERT` statements for the typed test database. -/
def setupSql : String := String.join <| tables.map fun t =>
  let cs := schema.columns t
  let n := schema.arity t
  let decl := ", ".intercalate ((List.finRange n).map fun i => s!"\"{(cs i).name}\" {sqlType (cs i).type}")
  let rows := (db t).map fun r => "(" ++ ", ".intercalate ((List.finRange n).map fun i => sqlLit (r i)) ++ ")"
  s!"CREATE TABLE {tableName t} ({decl});\n" ++
    (if rows.isEmpty then "" else s!"INSERT INTO {tableName t} VALUES {", ".intercalate rows};\n")

/-- A cell, normalised: numbers as exact rationals tagged int/decimal-free, so
`3` and `3.00` compare equal only through the rational. -/
def normCell : Datum → String
  | none => "NULL"
  | some (.int z) => s!"n:{(z : ℚ)}"
  | some (.decimal q) => s!"n:{q}"
  | some (.text s) => s!"t:{s}"
  | some (.bool b) => s!"b:{b}"

/-- A DuckDB `-list` cell: NULL, boolean, integer, decimal, otherwise text. The test data has no
numeric-looking strings, no `true`/`false` strings and no `|`. -/
def parseCell (s : String) : String :=
  if s == "NULL" then "NULL"
  else if s == "true" then "b:true" else if s == "false" then "b:false"
  else match s.toInt? with
  | some z => s!"n:{(z : ℚ)}"
  | none =>
    match s.splitOn "." with
    | [ip, fp] =>
      match (ip ++ fp).toInt?, fp.all Char.isDigit && !fp.isEmpty with
      | some u, true => s!"n:{(u : ℚ) / (10 ^ fp.length : ℕ)}"
      | _, _ => s!"t:{s}"
    | _ => s!"t:{s}"

def runDuckdb (sql : String) : IO (Except String (List (List String))) := do
  let child ← IO.Process.spawn {
    cmd := "duckdb", args := #["-list", "-nullvalue", "NULL"],
    stdin := .piped, stdout := .piped, stderr := .piped }
  child.stdin.putStr (setupSql ++ sql ++ ";\n")
  child.stdin.flush
  let (_, child) ← child.takeStdin
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  if (← child.wait) != 0 then return .error err
  let lines := out.splitOn "\n" |>.filter (· ≠ "")
  return .ok ((lines.drop 1).map fun l => (l.splitOn "|").map parseCell)

def duckdbAvailable : IO Bool := do
  try return (← IO.Process.output { cmd := "duckdb", args := #["--version"] }).exitCode == 0
  catch _ => return false

/-- Rows in order when the query sorts, as a bag otherwise. -/
def bagOf (sql : String) (rows : List (List String)) : List String :=
  let rs := rows.map fun r => " | ".intercalate r
  if (sql.splitOn "ORDER BY").length > 1 then rs else rs.mergeSort (· ≤ ·)

/-- Queries parsed in the `duckdb` dialect, for behaviour that the default dialect rejects at
parse time. Registry row 5 (`firstRow`): `SELECT DISTINCT … ORDER BY` a key that is not selected
sorts each distinct row by the key of its first source row. The keys are chosen so that the first
row, the last row and MIN/MAX give different orders. -/
def duckdbDialectCorpus : List String := [
  "SELECT DISTINCT user_id FROM orders ORDER BY amount",
  "SELECT DISTINCT user_id FROM orders ORDER BY amount DESC",
  "SELECT DISTINCT user_id FROM orders ORDER BY amount DESC LIMIT 2",
  "SELECT DISTINCT department FROM users GROUP BY department, age ORDER BY age",
  "SELECT DISTINCT department FROM users ORDER BY age DESC, department"
]

/-- (compared, documented differences, failures); `none` when DuckDB is missing. -/
def run : IO (Option (Nat × Nat × List String)) := do
  unless ← duckdbAvailable do return none
  let mut n := 0
  let mut documented := 0
  let mut fails : List String := []
  for (sql, ex) in corpus do
    match ex with
    | .rejected _ => continue
    | _ => pure ()
    let .ok stmt := SqlEquiv.parse sql | fails := s!"{sql}: parse error" :: fails
    let .ok e := elabStmt named stmt | fails := s!"{sql}: did not elaborate" :: fails
    let .ok rs := e.q.eval db | fails := s!"{sql}: SqlCore error" :: fails
    let ours := bagOf sql (rs.map fun r => (List.finRange e.n).map fun i => normCell (r i))
    n := n + 1
    match ← runDuckdb sql with
    | .error err => fails := s!"{sql}: DuckDB error {err}" :: fails
    | .ok theirs =>
      let theirs := bagOf sql theirs
      if ours != theirs then
        if expectedDifferences.any (·.1 == sql) then documented := documented + 1
        else fails := s!"{sql}:\n    SqlCore {ours}\n    DuckDB  {theirs}" :: fails
  for sql in duckdbDialectCorpus do
    let .ok stmt := SqlEquiv.parse sql (dialect := .duckdb) | fails := s!"{sql}: parse error" :: fails
    let .ok e := elabStmt named stmt | fails := s!"{sql}: did not elaborate" :: fails
    let .ok rs := e.q.eval db | fails := s!"{sql}: SqlCore error" :: fails
    let ours := bagOf sql (rs.map fun r => (List.finRange e.n).map fun i => normCell (r i))
    n := n + 1
    match ← runDuckdb sql with
    | .error err => fails := s!"{sql}: DuckDB error {err}" :: fails
    | .ok theirs =>
      let theirs := bagOf sql theirs
      if ours != theirs then fails := s!"{sql}:\n    SqlCore {ours}\n    DuckDB  {theirs}" :: fails
  return some (n, documented, fails.reverse)

end SqlCoreTest.DuckdbDiff
