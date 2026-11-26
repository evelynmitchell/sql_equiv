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
import SqlBridge.CorrectAvg

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
  /-- `SqlEquiv`'s rows equal the typed rows with every decimal rounded half away from zero to 16
  places: a repeating `AVG` (registry row 7; `SqlBridge.CorrectAvg.AvgRel`, step 3c). -/
  | agreeRounded
  /-- The two evaluators return the same rows in a different order (registry T18: plain
  `DISTINCT` keeps the last copy of a row in the typed core, the first in `SqlEquiv`). The test
  fails if the orders ever coincide, so the registry row stays true. -/
  | orderDiffers
  /-- The two evaluators return different rows, by a documented, implementation-defined choice
  (the registry row is cited). The test fails if they ever agree. -/
  | rowsDiffer (registry : String)

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
  ("SELECT name FROM users WHERE age NOT BETWEEN 25 AND 30", .agree),
  -- BETWEEN with a NULL bound or operand: `e >= lo AND e <= hi` in three-valued logic
  ("SELECT name FROM users WHERE age BETWEEN NULL AND 30", .agree),
  ("SELECT name FROM users WHERE NOT (age BETWEEN 28 AND NULL)", .agree),
  ("SELECT name, staff BETWEEN 10 AND 30 FROM museum", .agree),
  ("SELECT department FROM users GROUP BY department HAVING COUNT(*) BETWEEN 2 AND 3", .agree),
  ("SELECT department, COUNT(*) FROM users GROUP BY department HAVING department BETWEEN 'A' AND 'N'", .agree),
  ("SELECT name FROM users WHERE department IN ('Sales', 'Marketing')", .agree),
  ("SELECT name FROM users WHERE department NOT IN ('Sales', 'Marketing')", .agree),
  ("SELECT name FROM users WHERE age IN (25, NULL)", .agree),
  ("SELECT name FROM users WHERE age NOT IN (25, NULL)", .agree),
  ("SELECT CASE WHEN age > 28 THEN 'old' ELSE 'young' END FROM users", .agree),
  ("SELECT CASE WHEN age > 30 THEN 1 WHEN age > 25 THEN 2 ELSE 3 END FROM users", .agree),
  ("SELECT CASE WHEN age > 30 THEN name END FROM users", .agree),
  ("SELECT DISTINCT department FROM users", .agree),
  -- plain DISTINCT: the same rows, in a different order; with LIMIT and no ORDER BY, different
  -- rows (registry T18). Rows 2..5 are Sales, Engineering, Marketing, Sales.
  ("SELECT DISTINCT department FROM users WHERE id > 1", .orderDiffers),
  ("SELECT DISTINCT department FROM users WHERE id > 1 LIMIT 1",
    .rowsDiffer "T18: DISTINCT keeps the last copy in the typed core, the first in SqlEquiv"),
  ("SELECT DISTINCT u.department, o.product FROM users u JOIN orders o ON u.id = o.user_id", .agree),
  ("SELECT DISTINCT staff FROM museum", .agree),
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
  -- `*` next to other items, under WHERE, over a cross join and in a set operation (#407)
  ("SELECT name, *, age FROM users WHERE age > 25", .agree),
  ("SELECT * FROM users u JOIN orders o ON u.id = o.user_id WHERE o.amount > 100 AND u.age > 20", .agree),
  ("SELECT * FROM users CROSS JOIN products", .agree),
  ("SELECT * FROM users WHERE age > 28 UNION SELECT * FROM users WHERE department = 'Sales'", .agree),
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
  ("SELECT name, age FROM users ORDER BY 2", .agree),
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
  ("SELECT DISTINCT department FROM users ORDER BY 1 DESC LIMIT 2", .agree),
  ("SELECT department, COUNT(*) FROM users GROUP BY department ORDER BY department", .agree),
  ("SELECT COUNT(*) FROM users GROUP BY department ORDER BY department DESC", .agree),
  ("SELECT COUNT(*) AS department FROM users GROUP BY department ORDER BY department", .agree),
  ("SELECT department FROM users GROUP BY department ORDER BY COUNT(*) DESC, department", .agree),
  ("SELECT department, SUM(age) AS total FROM users GROUP BY department ORDER BY total LIMIT 2", .agree),
  ("SELECT u.name, o.amount FROM users u JOIN orders o ON u.id = o.user_id ORDER BY o.amount DESC", .agree),
  ("SELECT name FROM users LIMIT 2", .agree),
  -- `ORDER BY 3` with one item is now a parse error in SqlEquiv (#316), as in every engine; with a
  -- `*` item the parser cannot count columns, so SqlEquiv still sorts by the constant there.
  ("SELECT * FROM users ORDER BY 3", .sqlEquivBug "#316: positions after * are not resolved"),
  ("SELECT name FROM users ORDER BY name + 1", .rejected "typeError"),
  ("SELECT name, age AS name FROM users ORDER BY name", .rejected "ambiguousColumn"),
  -- #317: a trailing ORDER BY/LIMIT/OFFSET applies to the whole compound query
  ("SELECT name FROM users UNION ALL SELECT name FROM products ORDER BY 1", .agree),
  ("SELECT name FROM users WHERE id < 3 UNION ALL SELECT name FROM products ORDER BY 1 LIMIT 1", .agree),
  ("SELECT name FROM users UNION SELECT name FROM products ORDER BY name DESC LIMIT 3", .agree),
  ("SELECT name AS n FROM users INTERSECT SELECT name AS n FROM users WHERE age > 25 ORDER BY n", .agree),
  ("SELECT name AS n FROM users INTERSECT SELECT name FROM users WHERE age > 25 ORDER BY n", .agree),
  ("SELECT name FROM users EXCEPT SELECT name FROM users WHERE age > 29 ORDER BY 1 LIMIT 2 OFFSET 1", .agree),
  ("SELECT name AS n FROM users WHERE id < 3 UNION ALL SELECT name FROM products ORDER BY n DESC", .agree),
  -- #340: an empty first branch still names the columns
  ("SELECT name AS n FROM users WHERE id > 100 UNION ALL SELECT name FROM products ORDER BY n DESC", .agree),
  ("SELECT n FROM (SELECT name AS n FROM users WHERE id > 100 UNION SELECT name FROM products) AS t", .agree),
  -- INTERSECT, EXCEPT, LIKE (phase 8c, #322); set operations compared as bags. Since #324
  -- SqlEquiv matches set-operation rows by position and value, NULLs equal whatever their tag
  ("SELECT name FROM users INTERSECT SELECT name FROM products", .agree),
  ("SELECT department FROM users INTERSECT SELECT department FROM users WHERE age > 26", .agree),
  ("SELECT department FROM users EXCEPT SELECT department FROM users WHERE age > 29", .agree),
  ("SELECT user_id FROM orders INTERSECT SELECT id FROM users", .agree),
  ("SELECT id FROM users EXCEPT SELECT user_id FROM orders", .agree),
  ("SELECT staff FROM museum INTERSECT SELECT staff FROM museum WHERE staff IS NULL OR staff > 20", .agree),
  ("SELECT staff FROM museum EXCEPT SELECT staff FROM museum WHERE staff > 20", .agree),
  ("SELECT name FROM users UNION SELECT name FROM products EXCEPT SELECT name FROM users WHERE age > 26", .agree),
  -- `elabStmt_correct_inSub` (#352 step 6b): the rows in order, ORDER BY and LIMIT on the outer
  -- query included; a join in the body; a body with no rows
  ("SELECT name FROM users WHERE id NOT IN (SELECT user_id FROM orders) ORDER BY name LIMIT 2", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT o.user_id FROM orders o JOIN users u ON o.user_id = u.id WHERE u.age > 26) ORDER BY name", .agree),
  ("SELECT name FROM users WHERE id NOT IN (SELECT user_id FROM orders WHERE amount > 100000)", .agree),
  -- step 6c (`SubWhere`): the node on either side of `AND`, scalar subqueries on the right of a
  -- comparison, over an empty body (NULL), under DISTINCT and under aggregates
  ("SELECT name FROM users WHERE id NOT IN (SELECT user_id FROM orders) AND age > 20", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT MAX(user_id) FROM orders)", .agree),
  -- #411: a body that picks rows with ORDER BY … LIMIT, plain (key not selected) or grouped
  ("SELECT name FROM users WHERE age = (SELECT age FROM users ORDER BY id DESC LIMIT 1)", .agree),
  ("SELECT name FROM users WHERE age > (SELECT age FROM users ORDER BY age LIMIT 1 OFFSET 1) ORDER BY name", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT user_id FROM orders ORDER BY amount DESC LIMIT 2)", .agree),
  ("SELECT name FROM users WHERE id = (SELECT user_id FROM orders GROUP BY user_id ORDER BY COUNT(*) DESC, user_id LIMIT 1)", .agree),
  ("SELECT name FROM users WHERE id NOT IN (SELECT user_id FROM orders GROUP BY user_id ORDER BY SUM(amount) LIMIT 1)", .agree),
  -- #410: a set-operation body under IN / NOT IN
  ("SELECT name FROM users WHERE id NOT IN (SELECT user_id FROM orders UNION SELECT id FROM products)", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT user_id FROM orders INTERSECT SELECT id FROM users WHERE age > 26) ORDER BY name", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT id FROM users EXCEPT SELECT user_id FROM orders)", .agree),
  ("SELECT name FROM users WHERE age > 20 AND id NOT IN (SELECT user_id FROM orders UNION ALL SELECT MAX(id) FROM products)", .agree),
  -- #409: a grouped body, with and without HAVING, key and aggregate items, and as a scalar
  ("SELECT name FROM users WHERE id NOT IN (SELECT user_id FROM orders GROUP BY user_id HAVING SUM(amount) > 200)", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT user_id FROM orders GROUP BY user_id)", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT COUNT(*) FROM orders GROUP BY user_id) ORDER BY name", .agree),
  ("SELECT name FROM users WHERE age > 20 AND id NOT IN (SELECT user_id FROM orders WHERE amount > 100 GROUP BY user_id HAVING COUNT(*) >= 1)", .agree),
  ("SELECT name FROM users WHERE age = (SELECT MIN(age) FROM users) AND id > 0 ORDER BY name", .agree),
  ("SELECT name FROM users WHERE age < (SELECT MAX(age) FROM users WHERE id > 99)", .agree),
  ("SELECT u.name FROM users u JOIN orders o ON u.id = o.user_id WHERE o.amount = (SELECT MAX(amount) FROM orders)", .agree),
  ("SELECT COUNT(*), MAX(age) FROM users WHERE age > (SELECT MIN(age) FROM users)", .agree),
  ("SELECT DISTINCT department FROM users WHERE age <> (SELECT MAX(age) FROM users)", .orderDiffers),
  -- an `AVG` body (`AvgWhere`): SqlEquiv compares with the average rounded to 16 places, the
  -- typed core with the exact one; against an integer the outcome is the same
  ("SELECT name FROM users WHERE age < (SELECT AVG(age) FROM users WHERE id < 4)", .agree),
  ("SELECT name FROM users WHERE id > 1 AND age >= (SELECT AVG(age) FROM users)", .agree),
  ("SELECT name FROM users WHERE 27 > (SELECT AVG(age) FROM users WHERE id > 99)", .agree),
  ("SELECT department, COUNT(*) FROM users WHERE age > (SELECT AVG(age) FROM users) GROUP BY department", .agree),
  ("SELECT COUNT(*) FROM users WHERE age <> (SELECT AVG(age) FROM users)", .agree),
  -- `HAVING AVG(c) op k` (`HavingAvgOk`): the same rounding argument, per group
  ("SELECT department, COUNT(*) FROM users GROUP BY department HAVING AVG(age) > 27", .agree),
  ("SELECT department, AVG(age) FROM users GROUP BY department HAVING AVG(age) <= 30 ORDER BY department", .agree),
  ("SELECT department FROM users GROUP BY department HAVING COUNT(*) >= 1 AND AVG(age) <> 30", .agree),
  ("SELECT user_id, SUM(amount) FROM orders GROUP BY user_id HAVING AVG(amount) < 100", .agree),
  -- set operations keep the same rows in a different order (T18, `elabStmt_correct_setOp`): the
  -- typed core keeps the last copy of a duplicate, SqlEquiv the first; with LIMIT and no ORDER
  -- BY the rows differ
  ("SELECT department FROM users UNION SELECT department FROM users WHERE age > 100", .orderDiffers),
  ("SELECT department FROM users INTERSECT SELECT department FROM users", .orderDiffers),
  ("SELECT department FROM users EXCEPT SELECT department FROM users WHERE age > 100", .orderDiffers),
  ("SELECT department FROM users WHERE id > 1 UNION SELECT department FROM users WHERE id > 1 LIMIT 1",
    .rowsDiffer "T18: a set operation keeps the last copy in the typed core, the first in SqlEquiv"),
  ("SELECT name FROM users WHERE name LIKE 'A%'", .agree),
  ("SELECT name FROM users WHERE name LIKE '%e'", .agree),
  ("SELECT name FROM users WHERE name LIKE '%a%'", .agree),
  ("SELECT name FROM users WHERE name NOT LIKE '%a%'", .agree),
  ("SELECT name FROM users WHERE name LIKE 'a%'", .agree),
  ("SELECT name LIKE 'B%' FROM users", .agree),
  ("SELECT name FROM museum WHERE name LIKE NULL", .agree),
  ("SELECT name FROM users WHERE name LIKE '_ob'", .agree),
  ("SELECT name FROM users WHERE name LIKE 'C%l'", .agree),
  -- `Translates.like` (#352): under `AND`/`NOT`, with `%` and `_` together, the empty pattern,
  -- a pattern that is only wildcards, and against a NULL text
  ("SELECT name FROM users WHERE name LIKE '%a%' AND NOT (department LIKE 'S_les')", .agree),
  ("SELECT name FROM users WHERE name LIKE ''", .agree),
  ("SELECT name FROM users WHERE name LIKE '%_%_%'", .agree),
  ("SELECT COUNT(*) FROM users WHERE department LIKE '%ing'", .agree),
  ("SELECT name FROM users WHERE age LIKE '3%'", .rejected "typeError"),
  ("SELECT name FROM users INTERSECT SELECT age FROM users", .rejected "typeError"),
  -- uncorrelated subqueries in WHERE (phase 8f, #329)
  ("SELECT name FROM users WHERE id IN (SELECT user_id FROM orders)", .agree),
  ("SELECT name FROM users WHERE id NOT IN (SELECT user_id FROM orders)", .agree),
  ("SELECT name FROM users WHERE age > (SELECT AVG(age) FROM users)", .agree),
  ("SELECT name FROM users WHERE age = (SELECT MAX(age) FROM users)", .agree),
  ("SELECT name FROM users WHERE department = 'Engineering' AND age > (SELECT MIN(age) FROM users WHERE department = 'Sales')", .agree),
  -- #330: NOT IN (subquery) is unknown when a NULL takes part
  ("SELECT name FROM museum WHERE staff NOT IN (SELECT staff FROM museum WHERE name = 'm3')", .agree),
  ("SELECT name FROM museum WHERE staff NOT IN (SELECT staff FROM museum WHERE name = 'm1')", .agree),
  ("SELECT name FROM museum WHERE staff NOT IN (SELECT staff FROM museum WHERE name = 'zz')", .agree),
  ("SELECT name FROM museum WHERE staff IN (SELECT staff FROM museum WHERE name = 'm3' OR name = 'm1')", .agree),
  ("SELECT name FROM users WHERE age > (SELECT age FROM users WHERE id > 99)", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT user_id FROM orders WHERE amount > (SELECT AVG(amount) FROM orders))", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT user_id FROM orders UNION SELECT id FROM products)", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT user_id FROM orders) AND age < (SELECT MAX(age) FROM users)", .agree),
  ("SELECT department, COUNT(*) FROM users WHERE id NOT IN (SELECT user_id FROM orders) GROUP BY department", .agree),
  ("SELECT name FROM users WHERE id IN (SELECT id, age FROM users)", .rejected "typeError"),
  ("SELECT name FROM users WHERE name IN (SELECT id FROM users)", .rejected "typeError"),
  -- derived tables (phase 8f): the subquery's columns, requalified by the alias
  ("SELECT COUNT(*) FROM (SELECT name FROM users WHERE age > 25) AS t", .agree),
  ("SELECT t.n FROM (SELECT name AS n, age FROM users) AS t WHERE t.age > 28", .agree),
  ("SELECT u.name, t.total FROM users u JOIN (SELECT user_id, SUM(amount) AS total FROM orders GROUP BY user_id) AS t ON u.id = t.user_id", .agree),
  ("SELECT name FROM (SELECT name, age FROM users UNION ALL SELECT name, price FROM products) AS t WHERE age > 30", .agree),
  -- #412: COUNT(*) over a derived table whose body is a set operation (`elabStmt_correct_countDerived`);
  -- the body's rows are related only up to order, which COUNT(*) does not see
  ("SELECT COUNT(*) FROM (SELECT department FROM users INTERSECT SELECT department FROM users WHERE age > 26)", .agree),
  ("SELECT COUNT(*), COUNT(*) AS n FROM (SELECT name FROM users UNION SELECT name FROM products)", .agree),
  ("SELECT COUNT(*) FROM (SELECT user_id FROM orders EXCEPT SELECT id FROM users WHERE age > 26) AS t", .agree),
  ("SELECT COUNT(*) FROM (SELECT department FROM users GROUP BY department UNION ALL SELECT name FROM products)", .agree),
  ("SELECT COUNT(*) FROM (SELECT staff FROM museum INTERSECT SELECT staff FROM museum WHERE staff IS NULL OR staff > 20)", .agree),
  -- SELECT without FROM (phase 9.1a, #459): one source row with no columns (`Query.one`). The
  -- parser rejects WHERE or a trailing ORDER BY after a FROM-less SELECT, so those go through a
  -- derived table
  ("SELECT 1", .agree),
  ("SELECT 1 + 2, 'a' || 'b', TRUE AND FALSE, 0.1 + 0.2", .agree),
  ("SELECT NULL", .agree),
  ("SELECT COUNT(*)", .agree),
  ("SELECT DISTINCT 1", .agree),
  ("SELECT 1 LIMIT 0", .agree),
  ("SELECT 1 AS a UNION ALL SELECT 2", .agree),
  ("SELECT a FROM (SELECT 2 AS a UNION SELECT 1 UNION SELECT 2) AS t ORDER BY a", .agree),
  ("SELECT a FROM (SELECT 1 AS a) AS t WHERE a > 0", .agree),
  ("SELECT a FROM (SELECT 1 AS a) AS t WHERE a > 1", .agree),
  ("SELECT * FROM (SELECT 1 AS a, 'x' AS b) AS t", .agree),
  ("SELECT name FROM users WHERE age IN (SELECT 30)", .agree),
  ("SELECT name FROM users WHERE age = (SELECT 30)", .agree),
  -- 9.4b (#462, decision D6): correlated subqueries and EXISTS in WHERE, as `Query.lateral` columns
  ("SELECT * FROM users WHERE EXISTS (SELECT 1 FROM orders WHERE orders.user_id = users.id)", .agree),
  ("SELECT * FROM users WHERE NOT EXISTS (SELECT 1 FROM orders WHERE orders.user_id = users.id)", .agree),
  ("SELECT name FROM users WHERE EXISTS (SELECT 1 FROM orders WHERE amount > age * 10)", .agree),
  ("SELECT name FROM users WHERE EXISTS (SELECT 1 / 0 FROM orders WHERE orders.user_id = users.id)", .agree),
  ("SELECT id FROM users WHERE EXISTS (SELECT 1 FROM orders)", .agree),
  ("SELECT id FROM users WHERE EXISTS (SELECT 1 FROM orders WHERE amount > 1000000)", .agree),
  ("SELECT name FROM users u WHERE age > (SELECT AVG(age) FROM users v WHERE v.department = u.department)", .agree),
  ("SELECT name FROM users u WHERE age = (SELECT MAX(age) FROM users v WHERE v.department = u.department)", .agree),
  ("SELECT name FROM users u WHERE (SELECT COUNT(*) FROM orders o WHERE o.user_id = u.id) > 1", .agree),
  ("SELECT name FROM users u WHERE (SELECT COUNT(*) FROM orders o WHERE o.user_id = u.id) = 0", .agree),
  ("SELECT name FROM users u WHERE id IN (SELECT user_id FROM orders o WHERE o.amount > u.age)", .agree),
  ("SELECT name FROM users u WHERE id NOT IN (SELECT user_id FROM orders o WHERE o.amount > u.age)", .agree),
  ("SELECT name FROM users u WHERE age > 20 AND EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id AND o.amount > 50)", .agree),
  ("SELECT name FROM users u WHERE (SELECT amount FROM orders o WHERE o.user_id = u.id LIMIT 1) > 50", .agree),
  -- a positive LIMIT in an EXISTS body changes nothing; LIMIT 0 is not expressed
  ("SELECT name FROM users u WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id LIMIT 1)", .agree),
  ("SELECT name FROM users u WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id LIMIT 0)",
    .rejected "unsupported: EXISTS over LIMIT 0"),
  -- a name the body has twice is ambiguous there, not the outer row's
  ("SELECT name FROM users u WHERE EXISTS (SELECT 1 FROM orders o, orders p WHERE id > 1)",
    .rejected "ambiguousColumn"),
  -- 9.4b step 3 (#462): subqueries in the SELECT list, in HAVING and over the groups, correlated
  -- or not; FROM-less outer queries
  ("SELECT (SELECT MAX(amount) FROM orders WHERE orders.user_id = users.id) FROM users WHERE id = 1", .agree),
  ("SELECT name, (SELECT COUNT(*) FROM orders WHERE orders.user_id = users.id) FROM users", .agree),
  ("SELECT name, (SELECT MAX(age) FROM users) AS m FROM users", .agree),
  ("SELECT u.name, (SELECT COUNT(*) FROM orders o WHERE o.user_id = u.id) AS c FROM users u ORDER BY c DESC, u.name", .agree),
  ("SELECT name, (SELECT amount FROM orders o WHERE o.user_id = u.id ORDER BY amount LIMIT 1) AS a FROM users u",
    .rejected "unsupported: correlated subquery body shape"),
  ("SELECT name, id IN (SELECT user_id FROM orders) AS buyer FROM users", .agree),
  ("SELECT name, EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id AND o.amount > 100) AS big FROM users u", .agree),
  ("SELECT 7 IN (SELECT 5 UNION SELECT NULL)", .agree),
  ("SELECT 5 IN (SELECT 5 UNION SELECT NULL)", .agree),
  ("SELECT (SELECT MAX(price) FROM products)", .agree),
  ("SELECT MIN(age) IN (SELECT age FROM users WHERE department = 'Sales') AS r FROM users", .agree),
  ("SELECT department, COUNT(*) IN (SELECT user_id FROM orders WHERE user_id > 1) AS r FROM users GROUP BY department ORDER BY department", .agree),
  ("SELECT department FROM users GROUP BY department HAVING COUNT(*) NOT IN (SELECT user_id FROM orders WHERE user_id > 1) ORDER BY department", .agree),
  ("SELECT department FROM users GROUP BY department HAVING MAX(age) IN (SELECT age FROM users WHERE id > 3) ORDER BY department", .agree),
  ("SELECT department, (SELECT MAX(amount) FROM orders) AS m FROM users GROUP BY department ORDER BY department", .agree),
  ("SELECT department, (SELECT COUNT(*) FROM users v WHERE v.department = users.department) AS c FROM users GROUP BY department ORDER BY department", .agree),
  ("SELECT department FROM users GROUP BY department HAVING COUNT(*) < (SELECT COUNT(*) FROM orders) ORDER BY department", .agree),
  ("SELECT name FROM users WHERE NOT EXISTS (SELECT product FROM orders EXCEPT SELECT name FROM products)", .agree),
  -- #384 holds on this path too: `id` is ambiguous in the FROM scope, though only one key has it
  ("SELECT u.id, (SELECT MAX(amount) FROM orders) FROM users u JOIN orders o ON u.id = o.user_id GROUP BY u.id HAVING id > 0",
    .rejected "ambiguousColumn"),
  ("SELECT CASE WHEN id > 0 THEN 0 ELSE (SELECT MAX(age) FROM users) END FROM users",
    .rejected "unsupported: subquery in a CASE branch"),
  -- scalar functions (phase 9.1, #459): ROUND, LOWER, UPPER, LENGTH as operators; COALESCE,
  -- NULLIF, ABS, CONCAT written with CASE; IN over non-literals as OR
  ("SELECT ROUND(2.5), ROUND(-2.5), ROUND(7.45, 1), ROUND(123.456, -1)", .agree),
  ("SELECT ROUND(25, -1), ROUND(-25, -1), ROUND(7), ROUND(1.25, 5)", .agree),
  ("SELECT ROUND(age, -1), ROUND(price, 1) FROM users, items WHERE users.id = items.id", .agree),
  ("SELECT ROUND(NULL), ROUND(2.5, NULL)", .agree),
  ("SELECT LOWER(name), UPPER(department), LENGTH(name) FROM users", .agree),
  ("SELECT name FROM users WHERE LOWER(name) LIKE 'a%'", .agree),
  ("SELECT COALESCE(NULL, 99), COALESCE(1, 2), COALESCE(NULL, NULL, 7), COALESCE(42)", .agree),
  ("SELECT COALESCE(NULL, 'fallback'), COALESCE(NULLIF(1, 1), 99), NULLIF(5, 3)", .agree),
  ("SELECT name, COALESCE(age, -1) FROM users", .agree),
  ("SELECT NULLIF(department, 'Sales') FROM users", .agree),
  ("SELECT ABS(-2.50), ABS(3), ABS(age - 30) FROM users", .agree),
  ("SELECT department, ABS(COUNT(*) - 3) AS k FROM users GROUP BY department ORDER BY department", .agree),
  -- SqlEquiv's CONCAT takes two arguments and propagates NULL; the engines take any number and
  -- skip NULLs (decision D4: checked against the engines, SqlEquiv left as is)
  ("SELECT CONCAT(name, '-', department) FROM users", .sqlEquivBug "CONCAT arity and NULL"),
  ("SELECT CONCAT(name, NULL) FROM users", .sqlEquivBug "CONCAT arity and NULL"),
  ("SELECT name, age IN (id, 30) AS r FROM users", .agree),
  ("SELECT name FROM users WHERE age NOT IN (id * 10, 25)", .agree),
  ("SELECT name FROM users WHERE 30 IN (age, NULL)", .agree),
  -- #472: set operations across INT/DECIMAL and an untyped NULL branch; CASE and COALESCE
  -- promote an integer next to a decimal
  ("SELECT 1 UNION SELECT 1.0",
    .sqlEquivBug "#472 result type: the engines promote INT to DECIMAL, SqlEquiv keeps each value's type"),
  ("SELECT 2 UNION ALL SELECT 1.5",
    .sqlEquivBug "#472 result type: the engines promote INT to DECIMAL, SqlEquiv keeps each value's type"),
  ("SELECT 1 INTERSECT SELECT 1.0",
    .sqlEquivBug "#472 result type: the engines promote INT to DECIMAL, SqlEquiv keeps each value's type"),
  ("SELECT id FROM users WHERE id < 3 EXCEPT SELECT 1.0",
    .sqlEquivBug "#472 result type: the engines promote INT to DECIMAL, SqlEquiv keeps each value's type"),
  ("SELECT COUNT(DISTINCT v) AS c FROM (SELECT 1 AS v UNION ALL SELECT 1.0) AS t", .agree),
  ("SELECT v, COUNT(*) FROM (SELECT 1 AS v UNION ALL SELECT 1.0 UNION ALL SELECT 2) AS t GROUP BY v ORDER BY v",
    .sqlEquivBug "#472 result type: the engines promote INT to DECIMAL, SqlEquiv keeps each value's type"),
  ("SELECT price FROM items WHERE price > 2 UNION ALL SELECT NULL", .agree),
  ("SELECT name FROM users WHERE id = 1 UNION ALL SELECT NULL", .agree),
  ("SELECT DISTINCT p FROM (SELECT price AS p FROM items WHERE price IS NULL UNION ALL SELECT NULL) AS t", .agree),
  ("SELECT name, CASE WHEN age > 28 THEN 1 ELSE 0.5 END FROM users",
    .sqlEquivBug "#472 result type: the engines promote INT to DECIMAL, SqlEquiv keeps each value's type"),
  ("SELECT COALESCE(NULL, 1, 2.5), COALESCE(2.5, 1)",
    .sqlEquivBug "#472 result type: the engines promote INT to DECIMAL, SqlEquiv keeps each value's type"),
  -- window functions (phase 9.5, #463): tie-free sort keys where the function depends on the
  -- order of tied rows (ROW_NUMBER)
  ("SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users", .agree),
  ("SELECT name, ROW_NUMBER() OVER (PARTITION BY department ORDER BY age DESC) AS rn FROM users", .agree),
  ("SELECT name, RANK() OVER (ORDER BY department) AS r FROM users", .agree),
  ("SELECT name, DENSE_RANK() OVER (ORDER BY department) AS dr FROM users", .agree),
  ("SELECT name, SUM(age) OVER (PARTITION BY department) AS s FROM users", .agree),
  ("SELECT name, SUM(age) OVER (ORDER BY age) AS s FROM users", .agree),
  ("SELECT name, SUM(age) OVER (ORDER BY department) AS s FROM users", .agree),
  ("SELECT name, AVG(age) OVER (PARTITION BY department) AS a FROM users", .agree),
  ("SELECT name, COUNT(*) OVER () AS c FROM users", .agree),
  ("SELECT name, MIN(age) OVER (PARTITION BY department) AS lo, MAX(age) OVER (PARTITION BY department) AS hi FROM users", .agree),
  ("SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS r FROM users ORDER BY r", .agree),
  ("SELECT name FROM users ORDER BY ROW_NUMBER() OVER (ORDER BY age DESC)", .agree),
  ("SELECT name, age, SUM(age) OVER (PARTITION BY department) - age AS rest FROM users", .agree),
  ("SELECT name, CASE WHEN SUM(age) OVER (PARTITION BY department) > 50 THEN 'big' ELSE 'small' END AS r FROM users", .agree),
  ("SELECT department, RANK() OVER (ORDER BY SUM(age) DESC) AS r FROM users GROUP BY department", .agree),
  ("SELECT department, SUM(SUM(age)) OVER () AS s FROM users GROUP BY department", .agree),
  ("SELECT COUNT(*) AS c, ROW_NUMBER() OVER () AS r FROM users", .agree),
  ("SELECT department, COUNT(*) AS c, SUM(COUNT(*)) OVER (PARTITION BY COUNT(*)) AS s FROM users GROUP BY department ORDER BY department", .agree),
  ("SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users WHERE age > 24 ORDER BY rn LIMIT 2", .agree),
  ("SELECT *, ROW_NUMBER() OVER (ORDER BY id) AS rn FROM users", .agree),
  ("SELECT name, SUM(age) OVER (PARTITION BY department) IN (65, 28) AS r FROM users", .agree),
  ("SELECT name, COUNT(*) OVER (PARTITION BY price) AS c FROM items", .agree),
  ("SELECT name, RANK() OVER (ORDER BY price) AS r FROM items", .agree),
  ("SELECT name, RANK() OVER (ORDER BY price DESC) AS r FROM items", .agree),
  ("SELECT department, ROW_NUMBER() OVER (ORDER BY department) AS rn FROM users GROUP BY department HAVING COUNT(*) = 2", .agree),
  ("SELECT name, COUNT(price) OVER () AS c, SUM(price) OVER () AS s FROM items", .agree),
  ("SELECT name, RANK() OVER (ORDER BY price DESC NULLS LAST) AS r FROM items", .agree),
  ("SELECT name, ROW_NUMBER() OVER (ORDER BY price NULLS FIRST, name) AS r FROM items", .agree),
  -- probes from the self-review
  ("SELECT COUNT(*) AS c, ROW_NUMBER() OVER () AS r FROM users WHERE age > 100", .agree),
  ("SELECT name, ROW_NUMBER() OVER () AS r FROM users WHERE age > 100", .agree),
  ("SELECT u.name, o.amount, RANK() OVER (PARTITION BY u.id ORDER BY o.amount DESC) AS r FROM users u JOIN orders o ON u.id = o.user_id", .agree),
  ("SELECT name, SUM(age) OVER (PARTITION BY age > 25) AS s FROM users", .agree),
  ("SELECT name, SUM(price) OVER (ORDER BY name) AS s FROM items", .agree),
  ("SELECT name, AVG(price) OVER (ORDER BY name) AS a FROM items", .agree),
  ("SELECT name, MIN(name) OVER (ORDER BY age DESC) AS m FROM users", .agree),
  ("SELECT department, MAX(age) - MIN(age) AS spread, DENSE_RANK() OVER (ORDER BY MAX(age) - MIN(age)) AS d FROM users GROUP BY department", .agree),
  ("SELECT name, ROW_NUMBER() OVER (ORDER BY age) * 10 AS r FROM users ORDER BY 2 DESC", .agree),
  -- DISTINCT after the windows: duplicates of the window columns collapse
  ("SELECT DISTINCT department, COUNT(*) OVER (PARTITION BY department) AS c FROM users", .agree),
  ("SELECT DISTINCT department, RANK() OVER (ORDER BY department) AS r FROM users ORDER BY r", .agree),
  ("SELECT DISTINCT COUNT(*) AS c, RANK() OVER (ORDER BY COUNT(*)) AS r FROM users GROUP BY department ORDER BY r", .agree),
  -- a window function as the probe of `IN (subquery)` (windows attached first); a subquery inside
  -- a window's argument is not attached
  ("SELECT name, SUM(age) OVER (PARTITION BY department) IN (SELECT amount - 35 FROM orders) AS r FROM users", .agree),
  ("SELECT name, ROW_NUMBER() OVER (ORDER BY age) NOT IN (SELECT id FROM users WHERE id < 3) AS r FROM users", .agree),
  ("SELECT name, CASE WHEN SUM(age) OVER (PARTITION BY department) IN (SELECT amount - 35 FROM orders) THEN 1 ELSE 0 END AS r FROM users", .agree),
  ("SELECT name, SUM(age + (SELECT MAX(amount) FROM orders)) OVER (PARTITION BY department) AS s FROM users",
    .rejected "unsupported: subquery"),
  ("SELECT name, (SELECT COUNT(*) FROM orders o WHERE o.user_id = users.id) AS n, RANK() OVER (ORDER BY age) AS r FROM users", .agree),
  -- non-recursive WITH (phase 9.2, #460), inlined as derived tables
  ("WITH c AS (SELECT name, age FROM users WHERE age > 25) SELECT name FROM c", .agree),
  -- #482 (fixed): a CTE's rows are stored with bare column keys, so `c.id` resolves (it was
  -- `c.users.id`: the join gave no rows and `SELECT c.name FROM c` gave NULLs)
  ("WITH c AS (SELECT * FROM users) SELECT c.name, o.amount FROM c JOIN orders o ON c.id = o.user_id", .agree),
  ("WITH c AS (SELECT * FROM users) SELECT c.name FROM c", .agree),
  ("WITH c AS (SELECT * FROM users) SELECT x.name FROM c AS x WHERE x.age > 25", .agree),
  ("WITH c AS (SELECT users.name, users.age FROM users) SELECT c.name FROM c ORDER BY c.age", .agree),
  -- #445 (registry row 22): an aggregate only in ORDER BY makes the query one group
  ("SELECT 1 AS one FROM users ORDER BY COUNT(*)", .agree),
  ("SELECT 1 AS one FROM users WHERE age > 100 ORDER BY COUNT(*)", .agree),
  ("SELECT 1 AS one FROM users ORDER BY MAX(age) DESC LIMIT 1", .agree),
  ("SELECT ROW_NUMBER() OVER () AS r FROM users ORDER BY COUNT(*)", .agree),
  ("SELECT name FROM users ORDER BY COUNT(*)", .rejected "unsupported: column not in GROUP BY"),
  ("WITH a AS (SELECT id, age FROM users), b AS (SELECT id FROM a WHERE age > 25) SELECT * FROM b", .agree),
  ("WITH c AS (SELECT department, COUNT(*) AS n FROM users GROUP BY department) SELECT department FROM c WHERE n > 1", .agree),
  ("WITH c AS (SELECT id FROM users WHERE age > 28) SELECT name FROM users WHERE id IN (SELECT id FROM c)", .agree),
  ("WITH users AS (SELECT * FROM users WHERE age > 25) SELECT COUNT(*) FROM users", .agree),
  ("WITH c AS (SELECT 1 AS x UNION ALL SELECT 2) SELECT x FROM c", .agree),
  ("WITH c AS (SELECT age FROM users) SELECT x.age FROM c AS x WHERE x.age < 30", .agree),
  ("WITH c AS (SELECT age FROM users) SELECT a.age, b.age FROM c a, c b WHERE a.age + 3 = b.age", .agree),
  ("WITH c AS (SELECT 1 / 0 AS x) SELECT name FROM users", .agree),
  ("WITH c AS (SELECT name, age FROM users ORDER BY age LIMIT 2) SELECT name FROM c", .agree),
  -- an `EXISTS` body over a CTE is a body over a derived table, which the 9.4b body elaborator
  -- (`elabCorrBody`, used for every `EXISTS`) does not take yet ("richer bodies"); `IN` above is
  -- elaborated as an ordinary subquery
  ("WITH c AS (SELECT age FROM users) SELECT name FROM users WHERE EXISTS (SELECT 1 FROM c WHERE c.age > 30)",
    .rejected "unsupported: nested subquery in a correlated body"),
  ("WITH c AS (SELECT age FROM users) SELECT name FROM users u WHERE EXISTS (SELECT 1 FROM c WHERE c.age > u.age + 9)",
    .rejected "unsupported: nested subquery in a correlated body"),
  ("WITH c AS (SELECT name, age FROM users) SELECT name FROM c ORDER BY age DESC", .agree),
  ("WITH c AS (SELECT department FROM users) SELECT DISTINCT department FROM c", .agree),
  ("WITH c AS (SELECT name FROM users) SELECT name, (SELECT COUNT(*) FROM c) AS n FROM users", .agree),
  ("WITH c AS (SELECT name, age FROM users) SELECT d.name FROM (SELECT * FROM c WHERE age > 25) d", .agree),
  ("WITH c AS (SELECT department FROM users) SELECT department FROM c UNION SELECT department FROM c", .agree),
  ("WITH c AS (SELECT age FROM users) SELECT age FROM c UNION ALL SELECT age + 100 FROM c ORDER BY age DESC", .agree),
  ("WITH a AS (SELECT * FROM b), b AS (SELECT 1 AS x) SELECT * FROM a", .rejected "unknownTable"),
  -- every CTE body must elaborate, used or not, as Postgres checks it (registry T23; DuckDB
  -- skips an unused one)
  ("WITH c AS (SELECT nope FROM users) SELECT name FROM users", .rejected "unknownColumn"),
  ("WITH c AS (SELECT 1), c AS (SELECT 2) SELECT * FROM c", .rejected "typeError"),
  -- WITH RECURSIVE (phase 9.6, #464): linear recursion, Postgres's rules (registry T24)
  ("WITH RECURSIVE c AS (SELECT 1 AS n UNION ALL SELECT n + 1 FROM c WHERE n < 5) SELECT n FROM c", .agree),
  ("WITH RECURSIVE r AS (SELECT 1 AS n UNION SELECT (n % 3) + 1 FROM r) SELECT n FROM r", .agree),
  ("WITH RECURSIVE r AS (SELECT id, age FROM users WHERE id = 1 UNION ALL SELECT u.id, u.age FROM r JOIN users u ON u.id = r.id + 1 WHERE u.id <= 3) SELECT id, age FROM r", .agree),
  ("WITH RECURSIVE r AS (SELECT user_id AS u FROM orders WHERE id = 1 UNION SELECT o.user_id + 1 FROM r JOIN orders o ON o.user_id = r.u) SELECT u FROM r", .agree),
  ("WITH RECURSIVE c AS (SELECT 1 AS n UNION ALL SELECT n + 1 FROM c WHERE n < 10) SELECT SUM(n), COUNT(*) FROM c", .agree),
  ("WITH RECURSIVE c AS (SELECT 1 AS n UNION ALL SELECT n + 1 FROM c WHERE n < 3) SELECT u.name FROM users u JOIN c ON u.id = c.n", .agree),
  ("WITH RECURSIVE base AS (SELECT 2 AS n), c AS (SELECT n FROM base UNION ALL SELECT n + 2 FROM c WHERE n < 8) SELECT n FROM c", .agree),
  ("WITH RECURSIVE c AS (SELECT 1 AS n UNION ALL SELECT n + 1 FROM c WHERE n < 4), d AS (SELECT n * 10 AS m FROM c) SELECT m FROM d", .agree),
  ("WITH RECURSIVE r AS (SELECT department AS d FROM users UNION SELECT d FROM r) SELECT d FROM r", .agree),
  ("WITH RECURSIVE r AS (SELECT department AS d FROM users UNION ALL SELECT d FROM r WHERE FALSE) SELECT d FROM r", .agree),
  ("WITH RECURSIVE c AS (SELECT 1 AS n, 'a' AS s UNION ALL SELECT n + 1, s FROM c WHERE n < 3) SELECT n, s FROM c ORDER BY n DESC", .agree),
  ("WITH RECURSIVE c AS (SELECT 1 AS n UNION ALL SELECT n + 1 FROM c WHERE n < 6) SELECT name FROM users WHERE id IN (SELECT n FROM c WHERE n > 3)", .agree),
  ("WITH RECURSIVE r AS (SELECT 1 AS n UNION ALL SELECT 10 UNION ALL SELECT n + 1 FROM r WHERE n < 3) SELECT n FROM r", .agree),
  ("WITH RECURSIVE c AS (SELECT 1 AS n UNION ALL SELECT n + 1 FROM c WHERE n < 4) SELECT a.n, b.n FROM c a, c b WHERE a.n + 1 = b.n", .agree),
  ("WITH RECURSIVE r AS (SELECT 0.5 AS x UNION ALL SELECT x * 2 FROM r WHERE x < 4) SELECT x FROM r", .agree),
  ("WITH RECURSIVE r AS (SELECT 'a' AS s UNION ALL SELECT s || 'b' FROM r WHERE LENGTH(s) < 3) SELECT s FROM r", .agree),
  ("WITH RECURSIVE r AS (SELECT 1 AS n UNION ALL SELECT u.id FROM users u JOIN r ON u.id = r.n + 2) SELECT n FROM r", .agree),
  -- outside Postgres's rules: the CTE twice, an aggregate in the step, a subquery naming it, the
  -- CTE in the base part (registry T24); a column type that changes (Postgres: an error)
  ("WITH RECURSIVE r AS (SELECT 1 AS n UNION ALL SELECT a.n + b.n FROM r a, r b WHERE a.n < 4) SELECT n FROM r",
    .rejected "unsupported: WITH RECURSIVE: a recursive step outside"),
  ("WITH RECURSIVE r AS (SELECT 1 AS n UNION ALL SELECT MAX(n) + 1 FROM r WHERE n < 3) SELECT n FROM r",
    .rejected "unsupported: WITH RECURSIVE: a recursive step outside"),
  ("WITH RECURSIVE r AS (SELECT 1 AS n UNION ALL SELECT n + 1 FROM r WHERE n IN (SELECT n FROM r)) SELECT n FROM r",
    .rejected "unsupported: WITH RECURSIVE: a recursive step outside"),
  ("WITH RECURSIVE r AS (SELECT 1 AS n UNION ALL SELECT n + 0.5 FROM r WHERE n < 2) SELECT n FROM r",
    .rejected "typeError"),
  ("WITH RECURSIVE r AS (SELECT n FROM r UNION ALL SELECT 1 AS n) SELECT n FROM r",
    .rejected "unsupported: WITH RECURSIVE: the CTE in its base part"),
  -- outer joins (phase 9.3, #461): unmatched rows padded with NULL
  ("SELECT u.name, o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id", .agree),
  ("SELECT u.name, o.amount FROM orders o RIGHT JOIN users u ON u.id = o.user_id", .agree),
  ("SELECT u.name, o.id FROM users u FULL JOIN orders o ON u.id = o.user_id + 2", .agree),
  ("SELECT u.name FROM users u LEFT JOIN orders o ON u.id = o.user_id WHERE o.id IS NULL", .agree),
  ("SELECT u.name, COUNT(o.id) AS n FROM users u LEFT JOIN orders o ON u.id = o.user_id GROUP BY u.name", .agree),
  ("SELECT m.name, i.name FROM museum m LEFT JOIN items i ON m.staff = i.id", .agree),
  ("SELECT u.name, o.amount, p.price FROM users u LEFT JOIN orders o ON u.id = o.user_id LEFT JOIN products p ON o.product = p.name", .agree),
  ("SELECT u.name, o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id AND o.amount > 150", .agree),
  ("SELECT u.name, o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id WHERE o.amount > 150", .agree),
  ("SELECT * FROM users u RIGHT JOIN orders o ON u.id = o.user_id", .agree),
  ("SELECT u.name, o.amount FROM users u FULL JOIN orders o ON u.id = o.user_id ORDER BY u.name, o.amount", .agree),
  ("SELECT p.name, SUM(o.amount) AS total FROM products p LEFT JOIN orders o ON o.product = p.name GROUP BY p.name", .agree),
  -- an empty right side: SqlEquiv gives the left rows without the right columns (registry T26)
  ("SELECT u.name, o.amount FROM users u LEFT JOIN (SELECT * FROM orders WHERE id > 100) o ON u.id = o.user_id",
    .sqlEquivBug "registry T26: LEFT JOIN against an empty side drops the right columns"),
  -- outside the fragment, or ill-typed
  -- GROUP BY and aggregates (phase 8a, #313)
  ("SELECT COUNT(*) FROM users", .agree),
  ("SELECT department, COUNT(*) FROM users GROUP BY department", .agree),
  ("SELECT department, SUM(age), MIN(age), MAX(name) FROM users GROUP BY department", .agree),
  ("SELECT COUNT(DISTINCT department), COUNT(age) FROM users", .agree),
  ("SELECT department FROM users GROUP BY department HAVING COUNT(*) > 1", .agree),
  ("SELECT department, COUNT(*) + 1 FROM users WHERE age > 22 GROUP BY department", .agree),
  ("SELECT staff, COUNT(*) FROM museum GROUP BY staff", .agree),
  ("SELECT COUNT(staff), SUM(staff), MAX(staff) FROM museum", .agree),
  ("SELECT SUM(price), MIN(price), COUNT(price) FROM items", .agree),
  ("SELECT u.name, COUNT(*) FROM users u JOIN orders o ON u.id = o.user_id GROUP BY u.name", .agree),
  ("SELECT COUNT(*) FROM users WHERE age > 100", .agree),
  -- AVG and decimal `/` (phase 8d): exact rationals (registry T3, T10). `SqlEquiv`'s AVG is exact
  -- when the quotient terminates within 16 places and rounded to 16 otherwise (registry row 7), so
  -- terminating averages agree and a repeating one agrees once rounded (`AvgRel`, step 3c);
  -- decimal `/` is unimplemented there (#201).
  ("SELECT AVG(age) FROM users", .agree),
  ("SELECT department, AVG(age) FROM users GROUP BY department", .agree),
  ("SELECT AVG(age) FROM users WHERE id IN (1, 2, 4)", .agreeRounded),
  ("SELECT u.department, AVG(u.age), COUNT(*) FROM users u JOIN orders o ON u.id = o.user_id GROUP BY u.department",
    .agreeRounded),
  ("SELECT AVG(price), AVG(DISTINCT id) FROM items", .agree),
  ("SELECT department FROM users GROUP BY department HAVING AVG(age) > 26", .agree),
  ("SELECT AVG(staff) FROM museum WHERE staff > 100", .agree),
  ("SELECT price / 2, age / 2.0 FROM items, users WHERE items.id = users.id", .sqlEquivBug "#201: decimal / unimplemented"),
  ("SELECT AVG(name) FROM users", .rejected "typeError"),
  ("SELECT name, COUNT(*) FROM users", .rejected "unsupported: column not in GROUP BY"),
  ("SELECT SUM(name) FROM users", .rejected "typeError"),
  ("SELECT * FROM users GROUP BY department", .rejected "unsupported: *"),
  ("SELECT UPPER(name) FROM users", .agree),
  ("SELECT u.name FROM users u LEFT JOIN orders o ON u.id = o.user_id", .agree),
  ("SELECT id FROM users u JOIN orders o ON u.id = o.user_id", .rejected "ambiguousColumn"),
  -- #384: with GROUP BY too (the aggregate's output keeps only the keys' names)
  ("SELECT id FROM users u JOIN orders o ON u.id = o.user_id GROUP BY u.id", .rejected "ambiguousColumn"),
  ("SELECT u.id FROM users u JOIN orders o ON u.id = o.user_id GROUP BY u.id HAVING id > 1",
    .rejected "ambiguousColumn"),
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

/-- The SQL text with every parenthesised part removed, so that `OVER (ORDER BY …)` and an
`ORDER BY` inside a subquery do not count as sorting the result. -/
def topLevel (sql : String) : String := Id.run do
  let mut depth := 0
  let mut out := ""
  for c in sql.toList do
    if c == '(' then depth := depth + 1
    else if c == ')' then depth := depth - 1
    else if depth == 0 then out := out.push c
  return out

/-- Rows in order when the query sorts, as a bag otherwise. -/
def rowsFor (sql : String) (rows : List (List SqlEquiv.Value)) : List String :=
  if ((topLevel sql).splitOn "ORDER BY").length > 1 then rows.map fun r => toString (repr (r.map eraseNullType))
  else bag rows

def newRows (e : Elaborated schema) : Except EvalError (List (List SqlEquiv.Value)) :=
  (e.q.eval db).map fun rs => rs.map fun r =>
    (List.finRange e.n).map fun i => (ScalarDiff.datumToOld (r i)).getD (.null none)

/-- The typed rows with every decimal rounded half away from zero to 16 places, as `SqlEquiv`
rounds a repeating `AVG` (registry row 7). -/
def newRowsRounded (e : Elaborated schema) : Except EvalError (List (List SqlEquiv.Value)) :=
  (e.q.eval db).map fun rs => rs.map fun r =>
    (List.finRange e.n).map fun i => match r i with
      | some (.decimal q) =>
        SqlEquiv.Value.mkDecimal (SqlBridge.CorrectAvg.roundHalfAway (q * 10 ^ 16)) 16
      | d => (ScalarDiff.datumToOld d).getD (.null none)

/-- Queries parsed in the `sqlite` dialect: `LIKE` is ASCII case-insensitive there (registry
row 8; `BinOp.like true`). -/
def sqliteCorpus : List String := [
  "SELECT name FROM users WHERE name LIKE '_OB'",
  "SELECT name FROM users WHERE name LIKE 'c%L'",
  "SELECT name FROM users WHERE name LIKE 'a%'",
  "SELECT name FROM users WHERE name LIKE '%E'",
  "SELECT name FROM users WHERE name NOT LIKE '%A%'",
  "SELECT name FROM users WHERE department LIKE 'sales'"
]

/-- (checked, failures) -/
def run : Nat × List String := Id.run do
  let mut fails : List String := []
  for sql in sqliteCorpus do
    match SqlEquiv.parse sql (dialect := .sqlite) with
    | .error err => fails := s!"{sql}: parse error {err}" :: fails
    | .ok stmt =>
      match elabStmt named stmt with
      | .error err => fails := s!"{sql} (sqlite): did not elaborate: {err.category}" :: fails
      | .ok e =>
        let old := (SqlEquiv.evalStmt SemanticsTest.testDb stmt).2.map fun t => t.map (·.map (·.2))
        match newRows e, old with
        | .ok nr, some or_ =>
          if bag nr != bag or_ || nr.isEmpty then
            fails := s!"{sql} (sqlite):\n    SqlCore {bag nr}\n    SqlEquiv {bag or_}" :: fails
        | _, _ => fails := s!"{sql} (sqlite): evaluation failed" :: fails
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
      | .orderDiffers, .error err | .rowsDiffer _, .error err =>
        fails := s!"{sql}: did not elaborate: {err.category}" :: fails
      | .orderDiffers, .ok e =>
        let old := (SqlEquiv.evalStmt SemanticsTest.testDb stmt).2.map fun t => t.map (·.map (·.2))
        match newRows e, old with
        | .ok nr, some or_ =>
          if bag nr != bag or_ then
            fails := s!"{sql}: different rows:\n    SqlCore {bag nr}\n    SqlEquiv {bag or_}" :: fails
          if nr == or_ then
            fails := s!"{sql}: the orders agree (update registry T18 and use .agree)" :: fails
        | _, _ => fails := s!"{sql}: evaluation failed" :: fails
      | .rowsDiffer _, .ok e =>
        let old := (SqlEquiv.evalStmt SemanticsTest.testDb stmt).2.map fun t => t.map (·.map (·.2))
        match newRows e, old with
        | .ok nr, some or_ =>
          if bag nr == bag or_ then
            fails := s!"{sql}: the rows agree (update the registry and use .agree)" :: fails
        | _, _ => fails := s!"{sql}: evaluation failed" :: fails
      | .agreeRounded, .error err => fails := s!"{sql}: did not elaborate: {err.category}" :: fails
      | .agreeRounded, .ok e =>
        let old := (SqlEquiv.evalStmt SemanticsTest.testDb stmt).2.map fun t => t.map (·.map (·.2))
        match newRowsRounded e, newRows e, old with
        | .ok nr, .ok exact, some or_ =>
          if rowsFor sql nr != rowsFor sql or_ then
            fails := s!"{sql}:\n    SqlCore rounded {rowsFor sql nr}\n    SqlEquiv {rowsFor sql or_}" :: fails
          -- the case must exercise the rounding: the exact rows differ
          if rowsFor sql exact == rowsFor sql or_ then
            fails := s!"{sql}: no repeating AVG (use .agree)" :: fails
        | _, _, _ => fails := s!"{sql}: evaluation failed" :: fails
      | .agree, .ok e =>
        let old := (SqlEquiv.evalStmt SemanticsTest.testDb stmt).2.map fun t => t.map (·.map (·.2))
        match newRows e, old with
        | .ok nr, some or_ =>
          if rowsFor sql nr != rowsFor sql or_ then
            fails := s!"{sql}:\n    SqlCore {rowsFor sql nr}\n    SqlEquiv {rowsFor sql or_}" :: fails
        | .error err, _ => fails := s!"{sql}: SqlCore error {repr err}" :: fails
        | _, none => fails := s!"{sql}: SqlEquiv returned no table" :: fails
  return (corpus.length + sqliteCorpus.length, fails.reverse)

end SqlCoreTest.BridgeDiff
