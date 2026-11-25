/-
  Spider evaluation on the typed core (phase 9.8, #466): the Spider evaluate harness
  (`tools/spider_eval_baseline.py`) writes a manifest of synthetic tables and queries; this module
  builds a typed instance of each database from it (cells converted by the declared column type),
  elaborates each query in the sqlite dialect and evaluates it with `SqlCore.Query.eval`.

  Manifest format (the one `sql_equiv --spider-eval` reads), one item per line:
    #DB <db_id>          start a database
    #TABLE <name>        start a table (within the current database)
    col1|col2            header row of the current table
    v1|v2                data row (`NULL`, or the cell's text)
    #QUERY <db_id>       the next line is the SQL (one line)
  Output per query: `#RESULT <i> ok`, the rows (pipe-separated), `#END`; or `#RESULT <i> err <why>`.
-/
import SqlBridge.Spider

namespace SqlBridge.SpiderEval

open SqlCore SqlBridge SqlBridge.Spider

/-- A manifest cell as a datum of the declared type: `some d`, or `none` when the cell does not fit
the type (the database then has no conforming instance). -/
def cellDatum (τ : SqlType) (c : String) : Option Datum :=
  if c == "NULL" then some none
  else match τ with
  | .int => c.toInt?.map fun z => some (.int z)
  | .bool => if c == "1" then some (some (.bool true))
    else if c == "0" then some (some (.bool false)) else none
  | .text => some (some (.text c))
  | .decimal =>
    match c.splitOn "." with
    | [ip] => ip.toInt?.map fun z => some (.decimal z)
    | [ip, fp] => (ip ++ fp).toInt?.map fun u => some (.decimal ((u : ℚ) / 10 ^ fp.length))
    | _ => none

/-- A database's tables from the manifest: table name (lowercased) ↦ header and rows of cells. -/
abbrev RawDb := List (String × (List String × List (List String)))

/-- The typed instance of a database: each table's rows, the cells placed by column name and
converted by the column's type (a column missing from the manifest is `NULL`). -/
def instanceOf (ts : Array TableInfo) (raw : RawDb) : Except String (Database (schemaOf ts).S) := do
  let mut tables : Array (List (Array Datum)) := #[]
  for t in ts do
    let (hdr, rows) := (raw.lookup t.name).getD ([], [])
    let hdr := hdr.map String.toLower
    let mut out : List (Array Datum) := []
    for row in rows do
      let mut cells : Array Datum := #[]
      for (cn, τ) in t.cols do
        let cell := match hdr.idxOf? cn with
          | some k => row[k]?.getD "NULL"
          | none => "NULL"
        match cellDatum τ cell with
        | some d => cells := cells.push d
        | none => throw s!"cell {cell} of {t.name}.{cn} is not a {repr τ}"
      out := out ++ [cells]
    tables := tables.push out
  let final := tables
  return fun t => (final[t.val]?.getD []).map fun cells => fun i => cells[i.val]?.getD none

/-- A rational with at most 15 decimal places, as the harness prints numbers. -/
def renderRat (q : ℚ) : String :=
  if q.den == 1 then toString q.num
  else
    let scaled : ℤ := (q * 10 ^ 15).floor
    let neg := scaled < 0
    let a := scaled.natAbs
    let ip := a / 10 ^ 15
    let fp := toString (a % 10 ^ 15)
    let fp := "".pushn '0' (15 - fp.length) ++ fp
    let fp := (fp.toList.reverse.dropWhile (· == '0')).reverse
    (if neg then "-" else "") ++ toString ip ++ (if fp.isEmpty then "" else "." ++ String.ofList fp)

/-- A datum as the harness reads it: sqlite's rendering (booleans as `1`/`0`). -/
def renderDatum : Datum → String
  | none => "NULL"
  | some (.int z) => toString z
  | some (.text s) => s
  | some (.bool b) => if b then "1" else "0"
  | some (.decimal q) => renderRat q

/-- Parse a manifest: the databases' raw tables and the queries, in order. -/
def parseManifest (content : String) : List (String × RawDb) × List (String × String) := Id.run do
  let mut dbs : List (String × RawDb) := []
  let mut curDb := ""
  let mut curTable := ""
  let mut curCols : List String := []
  let mut curRows : List (List String) := []
  let mut queries : List (String × String) := []
  let mut pending : Option String := none
  let flush := fun (dbs : List (String × RawDb)) (db tbl : String) (cols : List String)
      (rows : List (List String)) =>
    if db == "" || tbl == "" then dbs
    else
      let entry := (tbl.toLower, (cols, rows.reverse))
      match dbs.lookup db with
      | some tbls => (db, entry :: tbls) :: dbs.filter (·.1 != db)
      | none => (db, [entry]) :: dbs
  for line in content.splitOn "\n" do
    match pending with
    | some qdb =>
      queries := queries ++ [(qdb, line)]
      pending := none
    | none =>
      if line.startsWith "#DB " then
        dbs := flush dbs curDb curTable curCols curRows
        curDb := (line.drop 4).trimAscii.toString
        curTable := ""; curCols := []; curRows := []
      else if line.startsWith "#TABLE " then
        dbs := flush dbs curDb curTable curCols curRows
        curTable := (line.drop 7).trimAscii.toString
        curCols := []; curRows := []
      else if line.startsWith "#QUERY " then
        dbs := flush dbs curDb curTable curCols curRows
        curTable := ""; curCols := []; curRows := []
        pending := some ((line.drop 7).trimAscii.toString)
      else if line.trimAscii.isEmpty then
        pure ()
      else if curTable != "" && curCols.isEmpty then
        curCols := line.splitOn "|"
      else if curTable != "" then
        curRows := line.splitOn "|" :: curRows
  dbs := flush dbs curDb curTable curCols curRows
  return (dbs, queries)

/-- Evaluate one query on the typed core: the rendered rows, or why not. -/
def evalOne (ts : Array TableInfo) (raw : RawDb) (sql : String) :
    Except String (List (List String)) := do
  let N := { schemaOf ts with config := SqlEquiv.Dialect.sqlite.config }
  let D ← instanceOf ts raw
  let stmt ← (SqlEquiv.parse sql (dialect := .sqlite)).mapError fun _ => "parse"
  let e ← (elabStmt N stmt).mapError fun err => s!"elab {err.category}"
  let rs ← (e.q.eval D).mapError fun err => s!"eval {repr err}"
  return rs.map fun r => (List.finRange e.n).map fun i => renderDatum (r i)

end SqlBridge.SpiderEval
