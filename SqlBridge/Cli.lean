/-
  The CLI on the typed core (phase 9.8, #466): the REPL's `eval` and `equiv` commands and the
  batch mode elaborate into the typed core and evaluate there. `SqlEquiv`'s evaluator stays as a
  labelled reference oracle (decision D7); the CLI shows its answer only where the two disagree.

  `Main.lean` calls `typedRun` and `typedEquiv` with the sample database it already has (an
  `SqlEquiv.Database`); this module builds the typed schema and instance from it.
-/
import SqlBridge.Spider
import SqlBridge.SpiderEval

namespace SqlBridge.Cli

open SqlCore SqlBridge SqlBridge.Spider

/-- A sample table's declaration: its name and typed columns. -/
abbrev TableDecl := String × List (String × SqlType)

/-- The typed schema of the sample tables. -/
def schemaOfDecls (decls : List TableDecl) : Array TableInfo :=
  (decls.map fun (t, cs) => ({ name := t.toLower, cols := cs.toArray.map fun (c, τ) =>
    (c.toLower, τ) } : TableInfo)).toArray

/-- An `SqlEquiv` value as a typed datum (decimals are exact). -/
def datumOf : SqlEquiv.Value → Datum
  | .int z => some (.int z)
  | .string s => some (.text s)
  | .bool b => some (.bool b)
  | .decimal u s => some (.decimal ((u : ℚ) / 10 ^ s))
  | .null _ => none

/-- The typed instance of an `SqlEquiv` database over the sample schema: each column read by
name from the row. -/
def instanceOf (ts : Array TableInfo) (db : SqlEquiv.Database) : Database (schemaOf ts).S :=
  fun t => (db (ts[t.val]'t.isLt).name).map fun row => fun i =>
    let cn := ((ts[t.val]'t.isLt).cols[i.val]?.map (·.1)).getD ""
    ((row.find? fun (k, _) => k.toLower == cn).map fun (_, v) => datumOf v).getD none

/-- A query's result on the typed core: the column names and the rendered rows. -/
structure Result where
  columns : List String
  rows : List (List String)

/-- Run a statement on the typed core: a query's rows, or (INSERT, UPDATE, DELETE) the rows of the
table it writes after the statement. The message of an error says where it arose. -/
def typedRun (decls : List TableDecl) (db : SqlEquiv.Database) (dialect : SqlEquiv.Dialect)
    (stmt : SqlEquiv.Stmt) : Except String Result := do
  let ts := schemaOfDecls decls
  let N := { schemaOf ts with config := dialect.config }
  let D := instanceOf ts db
  match stmt with
  | .query _ =>
    let e ← (elabStmt N stmt).mapError fun err => s!"does not elaborate: {err.category}"
    let rs ← (e.q.eval D).mapError fun err => s!"evaluation error: {repr err}"
    return { columns := (List.finRange e.n).map fun i => (e.cols i).name
             rows := rs.map fun r => (List.finRange e.n).map fun i =>
               SpiderEval.renderDatum (r i) }
  | _ =>
    let s ← (elabDml N stmt).mapError fun err => s!"does not elaborate: {err.category}"
    let t : (schemaOf ts).S.Table ← match s with
      | .insert t _ => pure t
      | .update t _ _ => pure t
      | .delete t _ => pure t
    let D' ← (s.exec D).mapError fun err => s!"evaluation error: {repr err}"
    let k := (schemaOf ts).S.arity t
    return { columns := (List.finRange k).map fun i => ((schemaOf ts).S.columns t i).name
             rows := (D' t).map fun r => (List.finRange k).map fun i =>
               SpiderEval.renderDatum (r i) }

/-- The typed core's verdict on two queries. -/
inductive Verdict where
  /-- `Query.checkEquiv` proved them equivalent on every conforming instance. -/
  | proved
  /-- Not proved; the sample database gives the same rows (as bags). -/
  | sameOnSample
  /-- Not proved; the sample database tells them apart. -/
  | differOnSample (why : String)
  /-- One of them does not elaborate. -/
  | notElaborated (why : String)

/-- Check two queries on the typed core: a proof from the checker, or a comparison on the sample
database. -/
def typedEquiv (decls : List TableDecl) (db : SqlEquiv.Database) (dialect : SqlEquiv.Dialect)
    (s₁ s₂ : SqlEquiv.Stmt) : Verdict :=
  let ts := schemaOfDecls decls
  let N := { schemaOf ts with config := dialect.config }
  let D := instanceOf ts db
  match elabStmt N s₁, elabStmt N s₂ with
  | .ok e₁, .ok e₂ =>
    if h : e₂.n = e₁.n then
      match Query.checkEquiv e₁.q (h ▸ e₂.q) with
      | .proved _ => .proved
      | .unknown =>
        match e₁.q.eval D, e₂.q.eval D with
        | .ok r₁, .ok r₂ =>
          let render := fun {k : ℕ} (rs : List (Row k)) => (rs.map fun r =>
            ((List.finRange k).map fun i => SpiderEval.renderDatum (r i))).mergeSort
              (fun a b => decide (toString a ≤ toString b))
          if render r₁ == render r₂ then .sameOnSample
          else .differOnSample "different rows on the sample database"
        | .error e, _ => .differOnSample s!"query 1 fails: {repr e}"
        | _, .error e => .differOnSample s!"query 2 fails: {repr e}"
    else .differOnSample "different numbers of columns"
  | .error e, _ => .notElaborated s!"query 1: {e.category}"
  | _, .error e => .notElaborated s!"query 2: {e.category}"

end SqlBridge.Cli
