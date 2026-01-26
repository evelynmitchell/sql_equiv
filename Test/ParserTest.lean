/-
  Parser Tests: Round-trip and parsing verification

  Tests that SQL parses correctly and round-trips through pretty-printing.
-/
import SqlEquiv
import Test.Common

namespace ParserTest

open SqlEquiv
open Test

/-- Run a test that should succeed -/
def testParse (name : String) (sql : String) : TestResult :=
  match parse sql with
  | .ok _ => .pass name
  | .error e => .fail name s!"Parse failed: {e}"

/-- Test that parsing succeeds and round-trips -/
def testRoundTrip (name : String) (sql : String) : TestResult :=
  match parse sql with
  | .error e => .fail name s!"Initial parse failed: {e}"
  | .ok stmt =>
    let pretty := stmt.toSql
    match parse pretty with
    | .error e => .fail name s!"Re-parse failed: {e}\nPretty: {pretty}"
    | .ok stmt2 =>
      if stmt == stmt2 then .pass name
      else .fail name s!"Round-trip mismatch:\n  Original: {sql}\n  Pretty: {pretty}\n  AST differs"

/-- Test that parsing fails (for invalid SQL) -/
def testParseFail (name : String) (sql : String) : TestResult :=
  match parse sql with
  | .ok _ => .fail name "Expected parse to fail but it succeeded"
  | .error _ => .pass name

-- ============================================================================
-- Basic SELECT Tests
-- ============================================================================

def basicSelectTests : List TestResult := [
  testRoundTrip "select_star" "SELECT * FROM users",
  testRoundTrip "select_columns" "SELECT name, age FROM users",
  testRoundTrip "select_qualified" "SELECT u.name, u.age FROM users u",
  testRoundTrip "select_table_star" "SELECT u.* FROM users u",
  testRoundTrip "select_alias" "SELECT name AS n FROM users",
  testRoundTrip "select_distinct" "SELECT DISTINCT name FROM users",
  testRoundTrip "select_no_from" "SELECT 1",
  testRoundTrip "select_literal_string" "SELECT 'hello'",
  testRoundTrip "select_literal_bool" "SELECT TRUE, FALSE",
  testRoundTrip "select_null" "SELECT NULL"
]

-- ============================================================================
-- WHERE Clause Tests
-- ============================================================================

def whereTests : List TestResult := [
  testRoundTrip "where_eq" "SELECT * FROM users WHERE id = 1",
  testRoundTrip "where_ne" "SELECT * FROM users WHERE status <> 'active'",
  testRoundTrip "where_lt" "SELECT * FROM users WHERE age < 18",
  testRoundTrip "where_le" "SELECT * FROM users WHERE age <= 18",
  testRoundTrip "where_gt" "SELECT * FROM users WHERE age > 21",
  testRoundTrip "where_ge" "SELECT * FROM users WHERE age >= 21",
  testRoundTrip "where_and" "SELECT * FROM users WHERE age > 18 AND status = 'active'",
  testRoundTrip "where_or" "SELECT * FROM users WHERE age < 18 OR age > 65",
  testRoundTrip "where_not" "SELECT * FROM users WHERE NOT verified",
  testRoundTrip "where_is_null" "SELECT * FROM users WHERE email IS NULL",
  testRoundTrip "where_is_not_null" "SELECT * FROM users WHERE email IS NOT NULL",
  testRoundTrip "where_between" "SELECT * FROM users WHERE age BETWEEN 18 AND 65",
  testRoundTrip "where_in" "SELECT * FROM users WHERE status IN ('active', 'pending')",
  testRoundTrip "where_like" "SELECT * FROM users WHERE name LIKE 'A%'",
  testRoundTrip "where_complex" "SELECT * FROM users WHERE (age > 18 AND status = 'active') OR admin = TRUE"
]

-- ============================================================================
-- JOIN Tests
-- ============================================================================

def joinTests : List TestResult := [
  testRoundTrip "inner_join" "SELECT * FROM users u INNER JOIN orders o ON u.id = o.user_id",
  testRoundTrip "left_join" "SELECT * FROM users u LEFT JOIN orders o ON u.id = o.user_id",
  testRoundTrip "right_join" "SELECT * FROM users u RIGHT JOIN orders o ON u.id = o.user_id",
  testRoundTrip "full_join" "SELECT * FROM users u FULL JOIN orders o ON u.id = o.user_id",
  testRoundTrip "cross_join" "SELECT * FROM users CROSS JOIN products",
  testRoundTrip "multi_join" "SELECT * FROM users u INNER JOIN orders o ON u.id = o.user_id INNER JOIN products p ON o.product_id = p.id"
]

-- ============================================================================
-- GROUP BY / HAVING / ORDER BY Tests
-- ============================================================================

def groupOrderTests : List TestResult := [
  testRoundTrip "group_by" "SELECT department, COUNT(*) FROM employees GROUP BY department",
  testRoundTrip "group_by_multi" "SELECT department, role, COUNT(*) FROM employees GROUP BY department, role",
  testRoundTrip "having" "SELECT department, COUNT(*) FROM employees GROUP BY department HAVING COUNT(*) > 5",
  testRoundTrip "order_by_asc" "SELECT * FROM users ORDER BY name ASC",
  testRoundTrip "order_by_desc" "SELECT * FROM users ORDER BY age DESC",
  testRoundTrip "order_by_multi" "SELECT * FROM users ORDER BY department ASC, name DESC",
  testRoundTrip "limit" "SELECT * FROM users LIMIT 10",
  testRoundTrip "offset" "SELECT * FROM users LIMIT 10 OFFSET 20",
  testRoundTrip "full_query" "SELECT department, COUNT(*) FROM employees WHERE active = TRUE GROUP BY department HAVING COUNT(*) > 5 ORDER BY department ASC LIMIT 10"
]

-- ============================================================================
-- Aggregate Function Tests (Spider compatibility)
-- ============================================================================

def aggregateTests : List TestResult := [
  testRoundTrip "count_star" "SELECT COUNT(*) FROM users",
  testRoundTrip "count_col" "SELECT COUNT(id) FROM users",
  testRoundTrip "count_distinct" "SELECT COUNT(DISTINCT department) FROM employees",
  testRoundTrip "sum" "SELECT SUM(salary) FROM employees",
  testRoundTrip "avg" "SELECT AVG(age) FROM users",
  testRoundTrip "min" "SELECT MIN(price) FROM products",
  testRoundTrip "max" "SELECT MAX(price) FROM products",
  testRoundTrip "multi_agg" "SELECT COUNT(*), SUM(amount), AVG(amount), MIN(amount), MAX(amount) FROM orders"
]

-- ============================================================================
-- Subquery Tests (Spider compatibility)
-- ============================================================================

def subqueryTests : List TestResult := [
  testRoundTrip "in_subquery" "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders)",
  testRoundTrip "not_in_subquery" "SELECT * FROM users WHERE id NOT IN (SELECT user_id FROM banned)",
  testRoundTrip "exists" "SELECT * FROM users WHERE EXISTS (SELECT 1 FROM orders WHERE orders.user_id = users.id)",
  testRoundTrip "not_exists" "SELECT * FROM users WHERE NOT EXISTS (SELECT 1 FROM banned WHERE banned.user_id = users.id)",
  testRoundTrip "scalar_subquery" "SELECT name, (SELECT COUNT(*) FROM orders WHERE orders.user_id = users.id) FROM users",
  testRoundTrip "from_subquery" "SELECT * FROM (SELECT name, age FROM users WHERE age > 21) AS adults",
  testRoundTrip "nested_subquery" "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders WHERE product_id IN (SELECT id FROM products WHERE price > 100))"
]

-- ============================================================================
-- Set Operation Tests (Spider compatibility)
-- ============================================================================

def setOpTests : List TestResult := [
  testRoundTrip "union" "SELECT name FROM users UNION SELECT name FROM admins",
  testRoundTrip "union_all" "SELECT name FROM users UNION ALL SELECT name FROM admins",
  testRoundTrip "intersect" "SELECT id FROM users INTERSECT SELECT user_id FROM orders",
  testRoundTrip "except" "SELECT id FROM users EXCEPT SELECT user_id FROM banned"
]

-- ============================================================================
-- Expression Tests
-- ============================================================================

def exprTests : List TestResult := [
  testRoundTrip "arithmetic" "SELECT price * quantity FROM orders",
  testRoundTrip "arithmetic_complex" "SELECT (price * quantity) + tax FROM orders",
  testRoundTrip "concat" "SELECT first_name || ' ' || last_name FROM users",
  testRoundTrip "case_simple" "SELECT CASE WHEN age < 18 THEN 'minor' ELSE 'adult' END FROM users",
  testRoundTrip "case_multi" "SELECT CASE WHEN age < 13 THEN 'child' WHEN age < 20 THEN 'teen' ELSE 'adult' END FROM users",
  testRoundTrip "function_call" "SELECT UPPER(name) FROM users",
  testRoundTrip "nested_function" "SELECT COALESCE(nickname, name) FROM users"
]

-- ============================================================================
-- INSERT Tests
-- ============================================================================

def insertTests : List TestResult := [
  testRoundTrip "insert_values" "INSERT INTO users (name, age) VALUES ('Alice', 30)",
  testRoundTrip "insert_multi_row" "INSERT INTO users (name, age) VALUES ('Alice', 30), ('Bob', 25)",
  testRoundTrip "insert_select" "INSERT INTO archive SELECT * FROM users WHERE active = FALSE"
]

-- ============================================================================
-- UPDATE Tests
-- ============================================================================

def updateTests : List TestResult := [
  testRoundTrip "update_simple" "UPDATE users SET status = 'inactive'",
  testRoundTrip "update_where" "UPDATE users SET status = 'inactive' WHERE last_login < '2024-01-01'",
  testRoundTrip "update_multi" "UPDATE users SET status = 'inactive', updated_at = '2024-01-01' WHERE id = 1"
]

-- ============================================================================
-- DELETE Tests
-- ============================================================================

def deleteTests : List TestResult := [
  testRoundTrip "delete_all" "DELETE FROM temp_data",
  testRoundTrip "delete_where" "DELETE FROM sessions WHERE expired = TRUE"
]

-- ============================================================================
-- Parse Failure Tests (invalid SQL)
-- ============================================================================

def parseFailTests : List TestResult := [
  testParseFail "empty" "",
  testParseFail "gibberish" "asdf qwer",
  testParseFail "incomplete_select" "SELECT FROM",
  testParseFail "missing_table" "SELECT * FROM",
  testParseFail "unclosed_paren" "SELECT * FROM (SELECT 1",
  testParseFail "invalid_keyword" "SELECTT * FROM users"
]

-- ============================================================================
-- CTE (WITH clause) Tests
-- ============================================================================

def cteTests : List TestResult := [
  testRoundTrip "cte_simple" "WITH t AS (SELECT 1) SELECT * FROM t",
  testRoundTrip "cte_from_table" "WITH active AS (SELECT * FROM users WHERE active = TRUE) SELECT * FROM active",
  testRoundTrip "cte_multiple" "WITH a AS (SELECT 1), b AS (SELECT 2) SELECT * FROM a, b",
  testRoundTrip "cte_reference_earlier" "WITH a AS (SELECT 1 AS x), b AS (SELECT x FROM a) SELECT * FROM b",
  testRoundTrip "cte_with_join" "WITH t AS (SELECT * FROM users) SELECT * FROM t INNER JOIN orders ON t.id = orders.user_id"
]

-- ============================================================================
-- Test Runner
-- ============================================================================

def allParserTests : List TestResult :=
  basicSelectTests ++ whereTests ++ joinTests ++ groupOrderTests ++
  aggregateTests ++ subqueryTests ++ setOpTests ++ exprTests ++
  insertTests ++ updateTests ++ deleteTests ++ parseFailTests ++ cteTests

def runParserTests : IO (Nat × Nat) :=
  runTests "Parser Tests" allParserTests

end ParserTest
