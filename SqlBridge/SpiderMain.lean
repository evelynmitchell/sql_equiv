/-
  `lake exe spider_elab`: elaborate every Spider dev query into the typed core
  (#295). Prints one line per query, `ok` or `err` with the failure category,
  for `tools/spider_elab_baseline.py`.
-/
import SqlBridge.Spider

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
    let N := { schemaOf ts with config := SqlEquiv.Dialect.sqlite.config }
    match SqlEquiv.parse q (dialect := .sqlite) with
    | .error _ => IO.println "err\tparse error"
    | .ok stmt =>
      match elabStmt N stmt with
      | .ok _ => IO.println "ok"
      | .error e => IO.println s!"err\t{e.category}"
  return 0
