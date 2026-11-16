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
  -- outside the fragment, or ill-typed
  ("SELECT COUNT(*) FROM users", .rejected "unsupported: aggregate"),
  ("SELECT department, COUNT(*) FROM users GROUP BY department", .rejected "unsupported"),
  ("SELECT name FROM users ORDER BY age", .rejected "unsupported: ORDER BY"),
  ("SELECT name FROM users LIMIT 2", .rejected "unsupported: LIMIT/OFFSET"),
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
      | .agree, .ok e =>
        let old := (SqlEquiv.evalStmt SemanticsTest.testDb stmt).2.map fun t => t.map (·.map (·.2))
        match newRows e, old with
        | .ok nr, some or_ =>
          if bag nr != bag or_ then
            fails := s!"{sql}:\n    SqlCore {bag nr}\n    SqlEquiv {bag or_}" :: fails
        | .error err, _ => fails := s!"{sql}: SqlCore error {repr err}" :: fails
        | _, none => fails := s!"{sql}: SqlEquiv returned no table" :: fails
  return (corpus.length, fails.reverse)

end SqlCoreTest.BridgeDiff
