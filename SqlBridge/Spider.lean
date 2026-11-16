/-
  Typed core phase 6 (#295): Spider schemas for the elaborator.

  `schemaOfJson` builds a `NamedSchema` from one database of Spider's
  `tables.json`. Names are lowercased in the schema, and `fold` lowercases
  references, so lookup stays exact (decision 7) after normalisation; Spider's
  queries were written against sqlite, whose names are case-insensitive.

  Column types: `number` is `int` (comparisons with decimal literals promote;
  integer division stays well-typed), `text`, `time` and `others` are `text`,
  `boolean` is `bool`. Spider declares no decimal columns.
-/
import Lean.Data.Json
import SqlBridge.Elab

namespace SqlBridge.Spider

open Lean SqlCore

def spiderType : String → SqlType
  | "number" => .int
  | "boolean" => .bool
  | _ => .text

/-- One table: its name and columns (name, type), names lowercased. -/
structure TableInfo where
  name : String
  cols : Array (String × SqlType)

/-- A schema whose tables are positions in an array. -/
def schemaOf (ts : Array TableInfo) : NamedSchema where
  S := {
    Table := Fin ts.size
    arity := fun t => ts[t].cols.size
    columns := fun t i => ⟨some ts[t].name, ts[t].cols[i].1, ts[t].cols[i].2⟩ }
  tables := (List.finRange ts.size).map fun t => (ts[t].name, t)
  fold := String.toLower

/-- The tables of one database entry of `tables.json`. -/
def tablesOfJson (j : Json) : Except String (String × Array TableInfo) := do
  let db ← j.getObjValAs? String "db_id"
  let tnames ← j.getObjValAs? (Array String) "table_names_original"
  let cols ← j.getObjValAs? (Array Json) "column_names_original"
  let types ← j.getObjValAs? (Array String) "column_types"
  let mut ts : Array TableInfo := tnames.map fun t => ⟨t.toLower, #[]⟩
  for h : k in [0:cols.size] do
    let c := cols[k]
    let ti ← c.getArrVal? 0 >>= (·.getInt?)
    let cn ← c.getArrVal? 1 >>= (·.getStr?)
    if ti ≥ 0 then
      let ti := ti.toNat
      if h' : ti < ts.size then
        let τ := spiderType (types[k]?.getD "text")
        ts := ts.set ti { ts[ti] with cols := ts[ti].cols.push (cn.toLower, τ) }
  return (db, ts)

end SqlBridge.Spider
