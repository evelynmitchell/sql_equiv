/-
  Typed core phase 9.7 (#465): INSERT, UPDATE and DELETE through `SqlBridge.elabDml` and
  `SqlCore.Stmt.exec`, checked against DuckDB and Postgres. Each case runs the statement on the
  typed test database, then compares the table it writes, as a bag of rows, with the table the
  engine holds after the same statement (`SELECT * FROM t`).

  The dialect of a case says where it runs: `standard` on both engines, `duckdb` or `postgres` on
  that engine only (behaviour that differs, registry T19 and row 6).

  `SqlEquiv` is not an oracle here (#465): its `UPDATE` lets each `SET` see the earlier ones, and its
  `INSERT` without a column list makes up column names.
-/
import SqlCoreTest.PostgresDiffTest

namespace SqlCoreTest.DmlDiff
open SqlCore SqlBridge SqlCoreTest.SchemaExamples SqlCoreTest.BridgeDiff

/-- What a case should do. -/
inductive Expect where
  /-- Both sides succeed with the same table. -/
  | agree
  /-- Both sides fail when the statement runs (division by zero). -/
  | runtimeError
  /-- The typed core rejects the statement at elaboration, with an error of this category; the
  engine is not consulted (it may accept the statement, registry T20). -/
  | rejected (category : String)
  deriving Repr

instance : DecidableEq schema.Table := inferInstanceAs (DecidableEq T)

def corpus : List (SqlEquiv.Dialect × String × Expect) := [
  -- UPDATE: every SET reads the old row (the engines swap; SqlEquiv gives id = age = old age)
  (.standard, "UPDATE users SET id = age, age = id", .agree),
  (.standard, "UPDATE users SET age = age + 1 WHERE department = 'Sales'", .agree),
  (.standard, "UPDATE users SET name = 'X', department = NULL WHERE id > 3", .agree),
  (.standard, "UPDATE users SET age = NULL WHERE id = 2", .agree),
  (.standard, "UPDATE items SET price = price * 2 WHERE price IS NOT NULL", .agree),
  (.standard, "UPDATE items SET price = 7", .agree),
  (.standard, "UPDATE museum SET staff = staff + 1 WHERE staff > 10", .agree),
  (.standard, "UPDATE users SET age = 99 WHERE FALSE", .agree),
  -- the assignments are evaluated only on the rows WHERE keeps
  (.postgres, "UPDATE users SET age = id / (age - 30) WHERE age <> 30", .agree),
  (.postgres, "UPDATE users SET age = id / (age - 30)", .runtimeError),
  -- DELETE
  (.standard, "DELETE FROM users WHERE department = 'Sales'", .agree),
  (.standard, "DELETE FROM museum WHERE staff > 10", .agree),
  (.standard, "DELETE FROM users", .agree),
  (.standard, "DELETE FROM items WHERE price IS NULL OR price > 2", .agree),
  (.postgres, "DELETE FROM users WHERE id / (age - 30) > 0", .runtimeError),
  -- INSERT … VALUES: by position, by a column list (the others NULL), several rows
  (.standard, "INSERT INTO users VALUES (6, 'Fay', 41, 'Ops')", .agree),
  (.standard, "INSERT INTO users (name, age) VALUES ('Gus', 19), ('Hal', 50)", .agree),
  (.standard, "INSERT INTO users (age, id) VALUES (33, 7)", .agree),
  (.standard, "INSERT INTO users VALUES (8, NULL, NULL, 'Ops'), (9, 'Ivy', 2 * 20, 'Ops')", .agree),
  -- an integer into a DECIMAL column is promoted (registry T20)
  (.standard, "INSERT INTO items VALUES (5, 'Pin', 4)", .agree),
  (.standard, "INSERT INTO items (id, name, price) VALUES (6, 'Cap', NULL), (7, 'Rod', 1.5)", .agree),
  -- INSERT … SELECT reads the instance before the statement
  (.standard, "INSERT INTO orders SELECT id + 10, id, age, name FROM users WHERE age > 25", .agree),
  (.standard, "INSERT INTO users SELECT * FROM users WHERE id = 1", .agree),
  (.standard, "INSERT INTO museum (name) SELECT name FROM users", .agree),
  (.standard, "INSERT INTO museum SELECT department, COUNT(*) FROM users GROUP BY department", .agree),
  (.postgres, "INSERT INTO users (id) SELECT id / (age - 30) FROM users", .runtimeError),
  -- fewer values than columns, no column list (registry T19): Postgres pads with NULL
  (.postgres, "INSERT INTO users VALUES (6, 'Fay')", .agree),
  (.postgres, "INSERT INTO users SELECT id + 10, name FROM users", .agree),
  (.duckdb, "INSERT INTO users VALUES (6, 'Fay')",
    .rejected "typeError"),
  (.standard, "INSERT INTO users VALUES (6, 'Fay')", .rejected "typeError"),
  -- found by the self-review: rows of different lengths are an error in every engine, padding
  -- included; a NULL literal column of the SELECT takes its target column's type
  (.postgres, "INSERT INTO users VALUES (6, 'Fay', 41, 'Ops'), (7, 'Gil')",
    .rejected "typeError"),
  (.standard, "INSERT INTO museum SELECT NULL, NULL", .agree),
  (.standard, "INSERT INTO museum (name, staff) SELECT name, NULL FROM users", .agree),
  (.standard, "INSERT INTO users SELECT id + 10, NULL, NULL, department FROM users", .agree),
  (.standard, "INSERT INTO museum VALUES (NULL, NULL)", .agree),
  (.standard, "UPDATE users SET age = users.age * 2 WHERE users.id < 3", .agree),
  (.standard, "INSERT INTO museum SELECT name, age FROM users ORDER BY age DESC LIMIT 2", .agree),
  (.standard, "DELETE FROM users WHERE NOT (age > 25)", .agree),
  -- a value of another type (registry T20): the engines cast, the typed core rejects
  (.standard, "INSERT INTO users (id, name) VALUES (6, 7)", .rejected "typeError"),
  (.standard, "UPDATE users SET age = 'old'", .rejected "typeError"),
  (.standard, "UPDATE users SET age = 2.5", .rejected "typeError"),
  -- errors in every engine too
  (.standard, "INSERT INTO users VALUES (6, 'Fay', 41, 'Ops', 1)", .rejected "typeError"),
  (.standard, "INSERT INTO users (id, id) VALUES (6, 7)", .rejected "typeError"),
  (.standard, "UPDATE users SET age = 1, age = 2", .rejected "typeError"),
  (.standard, "UPDATE users SET nope = 1", .rejected "unknownColumn"),
  (.standard, "DELETE FROM nowhere", .rejected "unknownTable"),
  (.standard, "DELETE FROM users WHERE age", .rejected "typeError")
]

/-- The table a statement writes. -/
def target : SqlEquiv.Stmt → Option String
  | .insert i => some i.table
  | .update u => some u.table
  | .delete d => some d.table
  | .query _ => none

/-- A row as the harnesses print it. -/
def showRow {n : ℕ} (r : Row n) : String :=
  " | ".intercalate ((List.finRange n).map fun i => DuckdbDiff.normCell (r i))

/-- The typed core's side: the written table as a sorted bag, `.error (true, _)` for an
elaboration error (with its category) and `.error (false, _)` for a runtime error. -/
def ours (d : SqlEquiv.Dialect) (sql : String) : Except (Bool × String) (List String) := do
  let stmt ← (SqlEquiv.parse sql (dialect := d)).mapError fun e => (true, s!"parse error {e}")
  let N : NamedSchema := { named with config := d.config }
  let s ← (elabDml N stmt).mapError fun e => (true, e.category)
  let some name := target stmt | throw (true, "not DML")
  let some t := named.tables.lookup name | throw (true, "unknownTable")
  match Stmt.exec (S := schema) db s with
  | .error e => throw (false, repr e |>.pretty)
  | .ok D' => pure (((D' t).map showRow).mergeSort (· ≤ ·))

/-- Run the statement and read the table back on an engine. -/
def theirs (run : String → IO (Except String (List (List String)))) (sql table : String) :
    IO (Except String (List String)) := do
  match ← run s!"{sql};\nSELECT * FROM {table}" with
  | .error e => return .error e
  | .ok rows => return .ok ((rows.map (" | ".intercalate ·)).mergeSort (· ≤ ·))

/-- (cases compared, failures). Engines that are missing are skipped. -/
def run : IO (Nat × List String) := do
  let duck ← DuckdbDiff.duckdbAvailable
  let pg ← PostgresDiff.postgresAvailable
  let mut n := 0
  let mut fails : List String := []
  for (d, sql, ex) in corpus do
    let mine := ours d sql
    match ex, mine with
    | .rejected cat, .error (true, c) =>
      n := n + 1
      unless c.startsWith cat do fails := s!"{sql}: rejected as {c}, expected {cat}" :: fails
      continue
    | .rejected cat, _ =>
      fails := s!"{sql}: expected a rejection ({cat}), got {repr mine}" :: fails
      continue
    | _, .error (true, c) =>
      fails := s!"{sql}: did not elaborate: {c}" :: fails
      continue
    | _, _ => pure ()
    let table := (SqlEquiv.parse sql (dialect := d)).toOption.bind target |>.getD "?"
    let engines : List (String × (String → IO (Except String (List (List String))))) :=
      (if duck && d != .postgres then [("DuckDB", DuckdbDiff.runDuckdb)] else []) ++
      (if pg && d != .duckdb then [("Postgres", PostgresDiff.runPostgres)] else [])
    for (eng, runE) in engines do
      n := n + 1
      let other ← theirs runE sql table
      match ex, mine, other with
      | .agree, .ok a, .ok b =>
        if a != b then fails := s!"{sql} ({eng}):\n    SqlCore {a}\n    {eng} {b}" :: fails
      | .runtimeError, .error (false, _), .error _ => pure ()
      | _, _, _ =>
        fails := s!"{sql} ({eng}): expected {repr ex}; SqlCore {repr mine}; {eng} {repr other}" ::
          fails
  return (n, fails.reverse)

end SqlCoreTest.DmlDiff
