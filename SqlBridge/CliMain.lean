/-
  `lake exe sqlcore` (#296): check two SQL queries for equivalence on the
  typed core.

    sqlcore check TABLES.json DB_ID "SQL1" "SQL2"

  Each query is parsed (`SqlEquiv.parse`), elaborated against the schema of
  `DB_ID` in a Spider-format `tables.json` (`SqlBridge.Spider`), and the two
  are compared by the certified checker `SqlCore.Query.checkEquiv`
  (simplification, then syntactic comparison). The answer is `equivalent`,
  backed by a kernel-checked proof of `Query.Equiv .ordered` and so of
  equivalence at every level, or `unknown`. The checker is incomplete, so
  `unknown` does not mean the queries differ.

  Exit codes: 0 equivalent, 1 unknown or different arity, 2 usage or
  elaboration error.
-/
import SqlBridge.Spider

open Lean SqlCore SqlBridge SqlBridge.Spider

def elaborate (ts : Array TableInfo) (sql : String) : Except String (Elaborated (schemaOf ts).S) := do
  let stmt ← SqlEquiv.parse sql |>.mapError (s!"parse error: {·}")
  elabStmt (schemaOf ts) stmt |>.mapError fun e => s!"does not elaborate: {e.category}"

/-- The verdict and the exit code. -/
def checkPair (ts : Array TableInfo) (sql₁ sql₂ : String) : String × UInt32 :=
  match elaborate ts sql₁, elaborate ts sql₂ with
  | .error e, _ => (s!"query 1 {e}", 2)
  | _, .error e => (s!"query 2 {e}", 2)
  | .ok e₁, .ok e₂ =>
    if h : e₂.n = e₁.n then
      match Query.checkEquiv e₁.q (h ▸ e₂.q) with
      | Check.proved _ => ("equivalent (certified: Query.Equiv .ordered, kernel-checked)", 0)
      | Check.unknown =>
        ("unknown (the checker is incomplete; the queries may still be equivalent)", 1)
    else (s!"not equivalent: the queries have {e₁.n} and {e₂.n} columns", 1)

def main (args : List String) : IO UInt32 := do
  let ["check", tablesPath, db, sql₁, sql₂] := args
    | IO.eprintln "usage: sqlcore check TABLES.json DB_ID \"SQL1\" \"SQL2\""; return 2
  let tj ← IO.ofExcept (Json.parse (← IO.FS.readFile tablesPath))
  let arr ← IO.ofExcept tj.getArr?
  let mut found : Option (Array TableInfo) := none
  for j in arr do
    let (d, ts) ← IO.ofExcept (tablesOfJson j)
    if d == db then found := some ts
  let some ts := found | IO.eprintln s!"no database {db} in {tablesPath}"; return 2
  let (msg, code) := checkPair ts sql₁ sql₂
  IO.println msg
  return code
