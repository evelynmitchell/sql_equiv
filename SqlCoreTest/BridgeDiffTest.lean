/-
  Typed core phase 6 (#295): parsed SQL through both pipelines.

  Each query in the corpus is parsed by `SqlEquiv.parse`, then
  * evaluated by `SqlEquiv.evalStmt` on `SemanticsTest.testDb`, and
  * elaborated by `SqlBridge.elabStmt` and evaluated by `SqlCore.Query.eval`
    on its typed transcription (`SqlCoreTest.SchemaExamples.db`).
  The results are compared as bags of value rows (typed NULLs as untyped).
  Queries outside the fragment must fail to elaborate with the expected
  category; queries inside must agree.
-/
import SqlBridge.Elab
import SqlCoreTest.SchemaDiffTest

namespace SqlCoreTest.BridgeDiff
open SqlCore SqlBridge SqlCoreTest.SchemaExamples

def named : NamedSchema where
  S := schema
  tables := [("users", .users), ("orders", .orders), ("products", .products), ("items", .items),
    ("singer", .singer), ("museum", .museum)]

/-- What a corpus query should do. -/
inductive Expect where
  | agree
  /-- Elaboration fails, with an error whose category starts with this. -/
  | rejected (category : String)
  /-- `SqlEquiv` is wrong here (the issue is cited); the query must elaborate and evaluate, and
  `DuckdbDiffTest` checks it against DuckDB instead. -/
  | sqlEquivBug (issue : String)

def corpus : List (String × Expect) := [
  -- projection, selection, star
  ("SELECT * FROM users", .agree),
  ("SELECT name, age FROM users", .agree),
  ("SELECT name FROM users WHERE age > 25", .agree),
  ("SELECT name FROM users WHERE age > 25 AND department = 'Engineering'", .agree),
  ("SELECT name FROM users WHERE NOT (age < 30) OR department = 'Sales'", .agree),
  ("SELECT id * 10 + 1, age - 1, age / 7, age % 7 FROM users", .agree),
  ("SELECT -age FROM users", .agree),
  ("SELECT name || '!' FROM users", .agree),
  ("SELECT name FROM users WHERE age BETWEEN 25 AND 30", .agree),
  ("SELECT name FROM users WHERE department IN ('Sales', 'Marketing')", .agree),
  ("SELECT name FROM users WHERE department NOT IN ('Sales', 'Marketing')", .agree),
  ("SELECT name FROM users WHERE age IN (25, NULL)", .agree),
  ("SELECT name FROM users WHERE age NOT IN (25, NULL)", .agree),
  ("SELECT CASE WHEN age > 28 THEN 'old' ELSE 'young' END FROM users", .agree),
  ("SELECT CASE WHEN age > 30 THEN 1 WHEN age > 25 THEN 2 ELSE 3 END FROM users", .agree),
  ("SELECT CASE WHEN age > 30 THEN name END FROM users", .agree),
  ("SELECT DISTINCT department FROM users", .agree),
  ("SELECT u.name FROM users u WHERE u.age = 30", .agree),
  -- NULLs and decimals
  ("SELECT name, staff FROM museum WHERE staff IS NULL", .agree),
  ("SELECT name FROM museum WHERE staff IS NOT NULL AND staff > 10", .agree),
  ("SELECT name FROM museum WHERE staff > 20 OR staff IS NULL", .agree),
  ("SELECT staff + 1 FROM museum", .agree),
  ("SELECT name FROM items WHERE price > 2", .agree),
  ("SELECT name FROM items WHERE price = 3", .agree),
  ("SELECT price * 2, price + 1, price - 0.25 FROM items", .agree),
  ("SELECT name FROM items WHERE price IS NULL", .agree),
  ("SELECT DISTINCT price FROM items", .agree),
  -- joins
  ("SELECT u.name, o.product FROM users u JOIN orders o ON u.id = o.user_id", .agree),
  ("SELECT u.name, o.amount FROM users u INNER JOIN orders o ON u.id = o.user_id WHERE o.amount > 100", .agree),
  ("SELECT * FROM users u JOIN orders o ON u.id = o.user_id", .agree),
  ("SELECT u.name, p.name FROM users u CROSS JOIN products p", .agree),
  ("SELECT o.product, p.price FROM orders o JOIN products p ON o.product = p.name", .agree),
  -- set operations
  ("SELECT name FROM users UNION ALL SELECT name FROM products", .agree),
  ("SELECT department FROM users UNION SELECT name FROM products", .agree),
  ("SELECT age FROM users WHERE age > 30 UNION ALL SELECT age FROM users WHERE age < 25", .agree),
  -- Spider-style original-case names
  ("SELECT Name FROM singer WHERE Age > 20", .agree),
  -- ORDER BY, LIMIT, OFFSET (phase 8b); queries with ORDER BY are compared as lists, on tie-free keys
  ("SELECT name FROM users ORDER BY age", .agree),
  ("SELECT name, age FROM users ORDER BY age DESC", .agree),
  ("SELECT name FROM users ORDER BY department, name DESC", .agree),
  ("SELECT name AS n FROM users ORDER BY n DESC", .agree),
  ("SELECT name, age FROM users ORDER BY 2", .sqlEquivBug "#316: positional ORDER BY"),
  ("SELECT name FROM users ORDER BY age * -1", .agree),
  ("SELECT name FROM users WHERE age > 22 ORDER BY id LIMIT 2", .agree),
  ("SELECT name FROM users ORDER BY id LIMIT 2 OFFSET 1", .agree),
  ("SELECT name FROM users ORDER BY id LIMIT 10 OFFSET 4", .agree),
  ("SELECT name FROM users ORDER BY id OFFSET 3", .agree),
  ("SELECT name FROM users ORDER BY id LIMIT 0", .agree),
  ("SELECT name, staff FROM museum ORDER BY staff NULLS FIRST, name", .agree),
  ("SELECT name, staff FROM museum ORDER BY staff DESC NULLS LAST, name", .agree),
  ("SELECT name FROM items ORDER BY price DESC NULLS LAST", .agree),
  ("SELECT name FROM items ORDER BY price NULLS FIRST", .agree),
  -- no NULLS clause: the parser's dialect rule (standard: NULL largest, so first under DESC)
  ("SELECT name, staff FROM museum ORDER BY staff DESC, name", .agree),
  ("SELECT DISTINCT department FROM users ORDER BY department", .agree),
  ("SELECT DISTINCT department FROM users ORDER BY 1 DESC LIMIT 2", .sqlEquivBug "#316: positional ORDER BY"),
  ("SELECT department, COUNT(*) FROM users GROUP BY department ORDER BY department", .agree),
  ("SELECT department FROM users GROUP BY department ORDER BY COUNT(*) DESC, department", .agree),
  ("SELECT department, SUM(age) AS total FROM users GROUP BY department ORDER BY total LIMIT 2", .agree),
  ("SELECT u.name, o.amount FROM users u JOIN orders o ON u.id = o.user_id ORDER BY o.amount DESC", .agree),
  ("SELECT name FROM users LIMIT 2", .agree),
  ("SELECT DISTINCT department FROM users ORDER BY age", .rejected "unsupported: ORDER BY key not selected"),
  ("SELECT name FROM users ORDER BY 3", .rejected "unsupported: ORDER BY position"),
  ("SELECT name FROM users ORDER BY name + 1", .rejected "typeError"),
  ("SELECT name, age AS name FROM users ORDER BY name", .rejected "ambiguousColumn"),
  -- #317: the parser binds a trailing ORDER BY/LIMIT to the last branch, so the bridge rejects it
  ("SELECT name FROM users UNION ALL SELECT name FROM products ORDER BY 1",
    .rejected "unsupported: ORDER BY/LIMIT in a compound"),
  -- outside the fragment, or ill-typed
  -- GROUP BY and aggregates (phase 8a, #313)
  ("SELECT COUNT(*) FROM users", .agree),
  ("SELECT department, COUNT(*) FROM users GROUP BY department", .agree),
  ("SELECT department, SUM(age), MIN(age), MAX(name) FROM users GROUP BY department", .agree),
  ("SELECT COUNT(DISTINCT department), COUNT(age) FROM users", .agree),
  ("SELECT department FROM users GROUP BY department HAVING COUNT(*) > 1", .agree),
  ("SELECT department, COUNT(*) + 1 FROM users WHERE age > 22 GROUP BY department", .agree),
  ("SELECT staff, COUNT(*) FROM museum GROUP BY staff", .sqlEquivBug "#315: typed NULLs group apart"),
  ("SELECT COUNT(staff), SUM(staff), MAX(staff) FROM museum", .agree),
  ("SELECT SUM(price), MIN(price), COUNT(price) FROM items", .agree),
  ("SELECT u.name, COUNT(*) FROM users u JOIN orders o ON u.id = o.user_id GROUP BY u.name", .agree),
  ("SELECT COUNT(*) FROM users WHERE age > 100", .agree),
  ("SELECT AVG(age) FROM users", .rejected "unsupported: AVG"),
  ("SELECT name, COUNT(*) FROM users", .rejected "unsupported: column not in GROUP BY"),
  ("SELECT SUM(name) FROM users", .rejected "typeError"),
  ("SELECT * FROM users GROUP BY department", .rejected "unsupported: *"),
  ("SELECT name FROM users WHERE name LIKE 'A%'", .rejected "unsupported: LIKE"),
  ("SELECT UPPER(name) FROM users", .rejected "unsupported: function"),
  ("SELECT u.name FROM users u LEFT JOIN orders o ON u.id = o.user_id", .rejected "unsupported: LEFT JOIN"),
  ("SELECT name FROM users WHERE id IN (SELECT user_id FROM orders)", .rejected "unsupported: subquery"),
  ("SELECT name FROM users INTERSECT SELECT name FROM products", .rejected "unsupported: INTERSECT"),
  ("SELECT id FROM users u JOIN orders o ON u.id = o.user_id", .rejected "ambiguousColumn"),
  ("SELECT nosuch FROM users", .rejected "unknownColumn"),
  ("SELECT NAME FROM users", .rejected "unknownColumn"),
  ("SELECT * FROM nosuch", .rejected "unknownTable"),
  ("SELECT name FROM users WHERE name > 3", .rejected "typeError"),
  ("SELECT name + 1 FROM users", .rejected "typeError"),
  ("SELECT name FROM users WHERE age", .rejected "typeError"),
  ("SELECT name FROM users UNION ALL SELECT age FROM users", .rejected "typeError")
]

def eraseNullType : SqlEquiv.Value → SqlEquiv.Value
  | .null _ => .null none
  | v => v

/-- A bag of rows as a sorted list of printed rows. -/
def bag (rows : List (List SqlEquiv.Value)) : List String :=
  (rows.map fun r => toString (repr (r.map eraseNullType))).mergeSort (· ≤ ·)

/-- Rows in order when the query sorts, as a bag otherwise. -/
def rowsFor (sql : String) (rows : List (List SqlEquiv.Value)) : List String :=
  if (sql.splitOn "ORDER BY").length > 1 then rows.map fun r => toString (repr (r.map eraseNullType))
  else bag rows

def newRows (e : Elaborated schema) : Except EvalError (List (List SqlEquiv.Value)) :=
  (e.q.eval db).map fun rs => rs.map fun r =>
    (List.finRange e.n).map fun i => (ScalarDiff.datumToOld (r i)).getD (.null none)

/-- (checked, failures) -/
def run : Nat × List String := Id.run do
  let mut fails : List String := []
  for (sql, ex) in corpus do
    match SqlEquiv.parse sql with
    | .error err => fails := s!"{sql}: parse error {err}" :: fails
    | .ok stmt =>
      match ex, elabStmt named stmt with
      | .rejected cat, .error err =>
        unless err.category.startsWith cat do
          fails := s!"{sql}: expected rejection {cat}, got {err.category}" :: fails
      | .rejected cat, .ok _ => fails := s!"{sql}: expected rejection {cat}, but it elaborated" :: fails
      | .agree, .error err => fails := s!"{sql}: did not elaborate: {err.category}" :: fails
      | .sqlEquivBug _, .error err => fails := s!"{sql}: did not elaborate: {err.category}" :: fails
      | .sqlEquivBug _, .ok e =>
        if (newRows e).toOption.isNone then fails := s!"{sql}: SqlCore error" :: fails
      | .agree, .ok e =>
        let old := (SqlEquiv.evalStmt SemanticsTest.testDb stmt).2.map fun t => t.map (·.map (·.2))
        match newRows e, old with
        | .ok nr, some or_ =>
          if rowsFor sql nr != rowsFor sql or_ then
            fails := s!"{sql}:\n    SqlCore {rowsFor sql nr}\n    SqlEquiv {rowsFor sql or_}" :: fails
        | .error err, _ => fails := s!"{sql}: SqlCore error {repr err}" :: fails
        | _, none => fails := s!"{sql}: SqlEquiv returned no table" :: fails
  return (corpus.length, fails.reverse)

end SqlCoreTest.BridgeDiff
