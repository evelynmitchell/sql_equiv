/-
  `lake exe spider_elab`: elaborate every Spider dev query into the typed core
  (#295). Prints one line per query, `ok` or `err` with the failure category,
  for `tools/spider_elab_baseline.py`. An `ok` line also lists the features that put the query
  outside the elaborator-correctness theorem's fragment (`SqlBridge.Coverage`, #352).
-/
import SqlBridge.Spider
import SqlBridge.Coverage

open Lean SqlBridge SqlBridge.Spider

def main (args : List String) : IO UInt32 := do
  let [tablesPath, queriesPath] := args
    | IO.eprintln "usage: spider_elab TABLES.json QUERIES.jsonl"; return 2
  let tj ← IO.ofExcept (Json.parse (← IO.FS.readFile tablesPath))
  let arr ← IO.ofExcept (tj.getArr?)
  let mut schemas : Std.HashMap String (Array TableInfo) := {}
  for j in arr do
    let (db, ts) ← IO.ofExcept (tablesOfJson j)
    schemas := schemas.insert db ts
  let lines := (← IO.FS.readFile queriesPath).splitOn "\n" |>.filter (· ≠ "")
  for line in lines do
    let j ← IO.ofExcept (Json.parse line)
    let db ← IO.ofExcept (j.getObjValAs? String "db")
    let q ← IO.ofExcept (j.getObjValAs? String "query")
    let some ts := schemas[db]? | IO.println s!"err\tunknown database {db}"; continue
    -- Spider's queries are sqlite's; the test-corpus metric (#458) names a dialect per query
    let dialect := ((j.getObjValAs? String "dialect").toOption.bind
      SqlEquiv.Dialect.ofString?).getD .sqlite
    let N := { schemaOf ts with config := dialect.config }
    match SqlEquiv.parse q (dialect := dialect) with
    | .error _ => IO.println "err\tparse error"
    | .ok (.query q) =>
      let stmt := SqlEquiv.Stmt.query q
      match elabStmt N stmt with
      -- second field: the features outside the correctness theorem's fragment (#352)
      | .ok _ => IO.println s!"ok\t{",".intercalate (SqlBridge.Coverage.outsideFragment stmt)}"
      | .error e => IO.println s!"err\t{e.category}"
    | .ok stmt =>
      -- INSERT, UPDATE, DELETE (phase 9.7, #465)
      match elabDml N stmt with
      | .ok _ => IO.println "ok\tdml"
      | .error e => IO.println s!"err\t{e.category}"
  return 0
