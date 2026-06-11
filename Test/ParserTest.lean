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
  testRoundTrip "select_string_with_quote" "SELECT 'it''s a test'",
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
  testRoundTrip "nested_subquery" "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders WHERE product_id IN (SELECT id FROM products WHERE price > 100))",
  -- Set-operation subqueries (#218)
  testRoundTrip "not_in_union_subquery" "SELECT AirportName FROM Airports WHERE AirportCode NOT IN (SELECT SourceAirport FROM Flights UNION SELECT DestAirport FROM Flights)",
  testRoundTrip "in_union_all_subquery" "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders UNION ALL SELECT user_id FROM refunds)",
  testRoundTrip "from_intersect_subquery" "SELECT * FROM (SELECT department FROM users INTERSECT SELECT department FROM admins) AS d",
  testRoundTrip "exists_except_subquery" "SELECT * FROM users WHERE EXISTS (SELECT id FROM orders EXCEPT SELECT id FROM refunds)",
  testRoundTrip "scalar_union_subquery" "SELECT (SELECT MAX(id) FROM users UNION SELECT MAX(id) FROM admins) FROM users",
  testRoundTrip "in_union_chain_subquery" "SELECT * FROM users WHERE id IN (SELECT a FROM t1 UNION SELECT b FROM t2 UNION SELECT c FROM t3)"
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
  testParseFail "invalid_keyword" "SELECTT * FROM users",
  -- WITH (CTE) is rejected inside subqueries (#218)
  testParseFail "with_inside_from_subquery" "SELECT * FROM (WITH t AS (SELECT 1) SELECT * FROM t) AS x",
  testParseFail "with_inside_exists_subquery" "SELECT * FROM users WHERE EXISTS (WITH t AS (SELECT 1) SELECT * FROM t)"
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
-- Recursive CTE (WITH RECURSIVE) Tests
-- ============================================================================

def recursiveCTETests : List TestResult := [
  testRoundTrip "recursive_simple" "WITH RECURSIVE nums AS (SELECT 1 AS n UNION ALL SELECT n FROM nums WHERE n < 5) SELECT * FROM nums",
  testRoundTrip "recursive_self_ref" "WITH RECURSIVE cnt AS (SELECT 1 AS x UNION ALL SELECT x FROM cnt) SELECT * FROM cnt",
  testRoundTrip "recursive_tree" "WITH RECURSIVE tree AS (SELECT id, parent_id FROM nodes UNION ALL SELECT n.id, n.parent_id FROM nodes n) SELECT * FROM tree",
  testRoundTrip "recursive_multiple_ctes" "WITH RECURSIVE a AS (SELECT 1), b AS (SELECT * FROM a UNION ALL SELECT * FROM b) SELECT * FROM b"
]

-- ============================================================================
-- Window Function Tests (#214)
-- ============================================================================

def windowParserTests : List TestResult := [
  -- Round trips for the supported forms
  testRoundTrip "window_row_number"
    "SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users",
  testRoundTrip "window_rank_desc"
    "SELECT RANK() OVER (ORDER BY age DESC) AS r FROM users",
  testRoundTrip "window_dense_rank"
    "SELECT DENSE_RANK() OVER (ORDER BY age) AS dr FROM users",
  testRoundTrip "window_sum_partition"
    "SELECT SUM(age) OVER (PARTITION BY department) AS s FROM users",
  testRoundTrip "window_avg_empty_over"
    "SELECT AVG(price) OVER () AS a FROM items",
  testRoundTrip "window_partition_and_order"
    "SELECT ROW_NUMBER() OVER (PARTITION BY department ORDER BY age DESC) AS rn FROM users",
  testRoundTrip "window_count_star_over"
    "SELECT COUNT(*) OVER () AS c FROM users",
  testRoundTrip "window_count_arg_multi_partition"
    "SELECT COUNT(id) OVER (PARTITION BY department, age) AS c FROM users",
  testRoundTrip "window_lowercase"
    "select name, row_number() over (order by age) as rn from users",
  testRoundTrip "window_next_to_plain_agg"
    "SELECT department, COUNT(*) AS c FROM users GROUP BY department",
  -- Loud-error cases (#214: these used to silently misparse/swallow)
  testParseFail "window_row_number_without_over"
    "SELECT name, ROW_NUMBER() FROM users",
  testParseFail "window_rank_without_over"
    "SELECT RANK() FROM users",
  testParseFail "window_dense_rank_without_over"
    "SELECT DENSE_RANK() AS dr FROM users",
  testParseFail "window_stray_over_after_column"
    "SELECT name OVER (ORDER BY age) FROM users",
  testParseFail "window_stray_over_second_item"
    "SELECT name, age OVER (ORDER BY age) FROM users",
  testParseFail "window_stray_over_after_from"
    "SELECT name FROM users OVER (ORDER BY age)",
  testParseFail "window_distinct_rejected"
    "SELECT SUM(DISTINCT age) OVER () FROM users",
  testParseFail "window_ranking_takes_no_args"
    "SELECT ROW_NUMBER(age) OVER (ORDER BY age) FROM users"
]

-- ============================================================================
-- Test Runner
-- ============================================================================

/-- Double-quoted string literals (#215): Spider/SQLite dialect. Strictly
    additive — any input containing `"` was previously a lex error, so no
    existing parse changes meaning. -/
def doubleQuoteTests : List TestResult := [
  (match parse "SELECT count(*) FROM AIRLINES WHERE Country = \"USA\"" with
   | .ok _ => .pass "dquote_string_literal (Spider style)"
   | .error e => .fail "dquote_string_literal (Spider style)" s!"{e}"),
  -- Double- and single-quoted literals produce the same AST
  (match parse "SELECT 'USA'", parse "SELECT \"USA\"" with
   | .ok a, .ok b =>
     if a == b then .pass "dquote_same_ast_as_squote"
     else .fail "dquote_same_ast_as_squote" "ASTs differ"
   | _, _ => .fail "dquote_same_ast_as_squote" "parse failure"),
  -- Doubled-quote escaping
  (match parse "SELECT \"it\"\"s\"" with
   | .ok (.query (.simple sel)) =>
     (match sel.items with
      | [.exprItem (.lit (.string v)) _] =>
        if v == "it\"s" then .pass "dquote_escaping"
        else .fail "dquote_escaping" s!"got {v}"
      | _ => .fail "dquote_escaping" "unexpected items")
   | _ => .fail "dquote_escaping" "parse failure"),
  -- Unterminated double quote is a loud error
  (match parse "SELECT \"oops" with
   | .error _ => .pass "dquote_unterminated_errors"
   | .ok _ => .fail "dquote_unterminated_errors" "should not parse"),
  -- ON-less JOIN (Spider/SQLite: bare `A JOIN B WHERE ...` = cross product)
  (match parse "SELECT T1.a FROM t1 AS T1 JOIN t2 AS T2 WHERE T1.a < 5" with
   | .ok _ => .pass "join_without_on (Spider style)"
   | .error e => .fail "join_without_on (Spider style)" s!"{e}"),
  -- JOIN with ON still parses identically
  (match parse "SELECT a FROM t1 JOIN t2 ON t1.x = t2.x" with
   | .ok _ => .pass "join_with_on_unaffected"
   | .error e => .fail "join_with_on_unaffected" s!"{e}")
]

def allParserTests : List TestResult :=
  basicSelectTests ++ whereTests ++ joinTests ++ groupOrderTests ++
  aggregateTests ++ subqueryTests ++ setOpTests ++ exprTests ++
  insertTests ++ updateTests ++ deleteTests ++ parseFailTests ++ cteTests ++
  recursiveCTETests ++ doubleQuoteTests ++ windowParserTests

def runParserTests : IO (Nat × Nat) :=
  runTests "Parser Tests" allParserTests

end ParserTest
