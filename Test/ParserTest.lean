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
  -- NOT BETWEEN parses as NOT (x BETWEEN a AND b) (#354)
  testRoundTrip "where_not_between" "SELECT * FROM users WHERE age NOT BETWEEN 18 AND 65",
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

/-- Non-ASCII identifiers (#370): parse, and print back unchanged. -/
def nonAsciiIdentTests : List TestResult := [
  testRoundTrip "non_ascii_table_and_column" "SELECT Élan FROM Été",
  testRoundTrip "non_ascii_alias_and_qualifier" "SELECT é.Élan AS 日本 FROM Été AS é WHERE é.Élan > 1",
  testRoundTrip "non_ascii_symbols" "SELECT a€b, x😀 FROM t",
  testRoundTrip "non_ascii_after_digit" "SELECT é1 FROM t",
  (match parse "SELECT ÉLAN FROM t" with
   | .ok (.query (.simple sel)) =>
     (match sel.items with
      | [.exprItem (.col ⟨none, "ÉLAN"⟩) none] => .pass "non_ascii_word_is_identifier"
      | _ => .fail "non_ascii_word_is_identifier" "wrong AST shape")
   | _ => .fail "non_ascii_word_is_identifier" "parse failure"),
  -- typographic quotes stay a parse error: as identifier characters they would name an
  -- unknown column, which evaluates to a quiet NULL here (the engines fail the query)
  (match parse "SELECT name FROM t WHERE name = ‘Alice’" with
   | .error e => if (e.splitOn "Typographic quote").length > 1 then .pass "typographic_quote_rejected"
                 else .fail "typographic_quote_rejected" e
   | .ok _ => .fail "typographic_quote_rejected" "parsed"),
  testParseFail "typographic_double_quote_rejected" "SELECT “name” FROM t",
  testParseFail "typographic_quote_inside_word_rejected" "SELECT O’Brien FROM t",
  -- a pasted no-break space would otherwise glue `25` into an unknown column name
  (match parse "SELECT name FROM t WHERE age >\u00a025" with
   | .error e => if (e.splitOn "Non-ASCII space (U+A0)").length > 1 then .pass "no_break_space_rejected"
                 else .fail "no_break_space_rejected" e
   | .ok _ => .fail "no_break_space_rejected" "parsed"),
  testParseFail "ideographic_space_rejected" "SELECT a\u3000b FROM t"
]

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

/-- Full-input consumption (#228): trailing tokens are loud errors, and the
    grammar gaps the old silent-discard masked now genuinely parse. -/
def trailingInputTests : List TestResult := [
  (match parse "SELECT * FROM users GARBAGE here" with
   | .error e =>
     if (s!"{e}").startsWith "Parse error" then .pass "trailing_garbage_errors"
     else .fail "trailing_garbage_errors" s!"wrong error: {e}"
   | .ok _ => .fail "trailing_garbage_errors" "should not parse"),
  (match parse "SELECT 1; extra" with
   | .error _ => .pass "trailing_after_semicolon_errors"
   | .ok _ => .fail "trailing_after_semicolon_errors" "should not parse"),
  (match parse "SELECT 1;" with
   | .ok _ => .pass "trailing_semicolon_ok"
   | .error e => .fail "trailing_semicolon_ok" s!"{e}"),
  -- Previously masked: select-item arithmetic from a bare column
  (match parse "SELECT age + 10 * 2 FROM users" with
   | .ok (.query (.simple sel)) =>
     (match sel.items with
      | [.exprItem (.binOp .add _ (.binOp .mul _ _)) _] => .pass "select_item_arithmetic_precedence"
      | _ => .fail "select_item_arithmetic_precedence" "wrong AST shape")
   | _ => .fail "select_item_arithmetic_precedence" "parse failure"),
  -- Previously masked: comma-separated FROM = implicit cross join
  (match parse "SELECT * FROM users, orders" with
   | .ok (.query (.simple sel)) =>
     (match sel.fromClause with
      | some (.join _ .cross _ none) => .pass "comma_join_is_cross"
      | _ => .fail "comma_join_is_cross" "wrong FROM shape")
   | _ => .fail "comma_join_is_cross" "parse failure")
]


-- ============================================================================
-- Dialect-faithful printing (#267): toSqlIn
-- ============================================================================

private def allDialects : List Dialect := [.standard, .sqlite, .duckdb, .postgres]

/-- Queries exercising every dialect choice the parser records: NULL position, LIKE case,
    MIN/MAX mode (with and without a bare column), SUM/AVG over booleans, windows. -/
private def dialectCorpus : List String := [
  "SELECT name FROM users ORDER BY age",
  "SELECT name FROM users ORDER BY age DESC",
  "SELECT name FROM users ORDER BY age NULLS FIRST",
  "SELECT name FROM users ORDER BY age DESC NULLS LAST, name",
  "SELECT name FROM users WHERE name LIKE 'al%'",
  "SELECT name FROM users WHERE name NOT LIKE 'A_ice'",
  "SELECT MAX(age), MIN(name) FROM users",
  "SELECT MAX(age), name FROM users",
  "SELECT department, MIN(age) FROM users GROUP BY department HAVING MAX(age) > 25",
  "SELECT SUM(age > 26), AVG(age) FROM users",
  "SELECT name, MIN(age) OVER (PARTITION BY department) FROM users",
  "SELECT name, SUM(age) OVER (ORDER BY age) FROM users",
  "SELECT DISTINCT department FROM users ORDER BY department"
]

/-- Same dialect both ways: `toSqlIn d` succeeds and parses back to the identical AST. -/
private def roundTripIn (d : Dialect) (sql : String) : TestResult :=
  let name := s!"to_sql_in_round_trip_{d.name}: {sql}"
  match parse sql (dialect := d) with
  | .error e => .fail name s!"parse: {e}"
  | .ok st =>
    match st.toSqlIn d with
    | .error e => .fail name s!"refused: {e}"
    | .ok out =>
      match parse out (dialect := d) with
      | .ok st2 => if st2 == st then .pass name else .fail name s!"AST differs: {out}"
      | .error e => .fail name s!"re-parse: {e}"

/-- `toSqlIn dst` of a query parsed in `src` refuses, with a message containing `needle`. -/
private def expectRefusal (name : String) (src dst : Dialect) (sql needle : String) : TestResult :=
  match parse sql (dialect := src) with
  | .error e => .fail name s!"parse: {e}"
  | .ok st =>
    match st.toSqlIn dst with
    | .ok out => .fail name s!"expected a refusal, printed: {out}"
    | .error e => if (e.splitOn needle).length > 1 then .pass name
                  else .fail name s!"refusal without '{needle}': {e}"

/-- `toSqlIn dst` of a query parsed in `src` succeeds, the output re-parses in `dst`, and both
    statements evaluate to the same result on `db`. -/
private def expectFaithful (name : String) (src dst : Dialect) (sql : String)
    (db : Database) : TestResult :=
  match parse sql (dialect := src) with
  | .error e => .fail name s!"parse: {e}"
  | .ok st =>
    match st.toSqlIn dst with
    | .error e => .fail name s!"refused: {e}"
    | .ok out =>
      match parse out (dialect := dst) with
      | .error e => .fail name s!"re-parse: {e}"
      | .ok st2 =>
        if (evalStmt db st).2 == (evalStmt db st2).2 then .pass name
        else .fail name s!"results differ for {out}"

/-- Mixed letter case, non-ASCII letters, NULLs and non-strings, for the LIKE folding cases. -/
private def caseTable : Table := [
  [("s", .string "Alice"), ("p", .string "al%")],
  [("s", .string "ÉCOLE"), ("p", .string "école")],
  [("s", .string "BOB"), ("p", .string "b_b")],
  [("s", .null none), ("p", .string "a%")],
  [("s", .string "x"), ("p", .null none)],
  [("s", .int 5), ("p", .string "5")]]

private def caseDb : Database := fun n => if n == "t" then caseTable else []

/-- Users with a NULL age and a boolean-friendly spread, so NULL positions and SUM over
    booleans are observable. -/
private def usersDb : Database := fun n =>
  if n == "users" then [
    [("name", .string "Alice"), ("age", .int 30), ("department", .string "Eng")],
    [("name", .string "Bob"),   ("age", .null (some .int)), ("department", .string "Ops")],
    [("name", .string "Carol"), ("age", .int 22), ("department", .string "Eng")]]
  else []

def dialectPrintTests : List TestResult :=
  (allDialects.flatMap fun d => dialectCorpus.map (roundTripIn d)) ++ [
  -- likeCI survives a cross-dialect trip as LOWER(x) LIKE LOWER(p): same AST shape, same rows
  (match parse "SELECT s FROM t WHERE s LIKE p" (dialect := .sqlite) with
   | .ok st => match st.toSqlIn .standard with
     | .ok out => if out == "SELECT s FROM t WHERE (LOWER(s) LIKE LOWER(p))" then
         .pass "to_sql_in_likeci_prints_lower" else .fail "to_sql_in_likeci_prints_lower" out
     | .error e => .fail "to_sql_in_likeci_prints_lower" e
   | .error e => .fail "to_sql_in_likeci_prints_lower" e),
  expectFaithful "to_sql_in_likeci_same_rows_standard" .sqlite .standard
    "SELECT s, p, s LIKE p AS m FROM t" caseDb,
  expectFaithful "to_sql_in_likeci_same_rows_postgres" .sqlite .postgres
    "SELECT s FROM t WHERE s NOT LIKE p" caseDb,
  -- default toSql prints for standard, so it folds likeCI too
  (match parse "SELECT s FROM t WHERE s LIKE 'a%'" (dialect := .sqlite) with
   | .ok st => if (st.toSql.splitOn "LOWER(s)").length > 1 then .pass "to_sql_default_folds_likeci"
               else .fail "to_sql_default_folds_likeci" st.toSql
   | .error e => .fail "to_sql_default_folds_likeci" e),
  -- NULL positions survive across dialects (explicit NULLS where the target's rule differs)
  expectFaithful "to_sql_in_nulls_sqlite_to_postgres" .sqlite .postgres
    "SELECT name FROM users ORDER BY age LIMIT 1" usersDb,
  -- (postgres ASC already matches the standard rule, so only a target-relative printer
  -- writes NULLS LAST for sqlite)
  expectFaithful "to_sql_in_nulls_postgres_to_sqlite" .postgres .sqlite
    "SELECT name FROM users ORDER BY age LIMIT 1" usersDb,
  expectFaithful "to_sql_in_nulls_duckdb_to_sqlite" .duckdb .sqlite
    "SELECT name FROM users ORDER BY age DESC LIMIT 1" usersDb,
  -- choices with no SQL spelling are refused when the target would read them differently
  expectRefusal "to_sql_in_refuses_case_sensitive_like_for_sqlite" .standard .sqlite
    "SELECT name FROM users WHERE name LIKE 'A%'" "case-sensitive LIKE",
  expectRefusal "to_sql_in_refuses_minmax_mode" .sqlite .standard
    "SELECT MAX(age) FROM users" "mixed=typeClass",
  expectRefusal "to_sql_in_refuses_bare_row" .sqlite .duckdb
    "SELECT MAX(age), name FROM users" "bareRow=true",
  expectRefusal "to_sql_in_refuses_bool_sum" .duckdb .postgres
    "SELECT SUM(age > 26) FROM users" "bools=asInt",
  expectRefusal "to_sql_in_refuses_window_minmax" .sqlite .postgres
    "SELECT MIN(age) OVER () FROM users" "mixed=typeClass",
  -- …and printed when the target records the same choice
  expectFaithful "to_sql_in_bool_sum_duckdb_to_sqlite" .duckdb .sqlite
    "SELECT SUM(age > 26) AS s FROM users" usersDb,
  expectFaithful "to_sql_in_minmax_postgres_to_standard" .postgres .standard
    "SELECT MAX(age) AS m FROM users" usersDb
]

-- ============================================================================
-- Operator precedence (#400, registry row 21)
-- ============================================================================

/-- `sql` parses to the same AST as its fully parenthesised spelling `explicit`, in every
    dialect. -/
private def sameParse (name sql explicit : String) : List TestResult :=
  allDialects.map fun d =>
    let n := s!"{name}_{d.name}"
    match parse sql (dialect := d), parse explicit (dialect := d) with
    | .ok a, .ok b => if a == b then .pass n else .fail n s!"parsed as {a.toSql}"
    | .error e, _ => .fail n s!"parse: {e}"
    | _, .error e => .fail n s!"parse of the explicit form: {e}"

/-- `sql` is a parse error whose message contains `needle`. -/
private def failsWith (name sql needle : String) : TestResult :=
  match parse sql with
  | .ok st => .fail name s!"parsed as {st.toSql}"
  | .error e => if (e.splitOn needle).length > 1 then .pass name
                else .fail name s!"error without '{needle}': {e}"

/-- The single value `SELECT <expr>` evaluates to. -/
private def evalsTo (name sql : String) (expected : Value) : TestResult :=
  match parse sql with
  | .error e => .fail name s!"parse: {e}"
  | .ok st => match (evalStmt (fun _ => []) st).2 with
    | some [[(_, v)]] => if v == expected then .pass name
                         else .fail name s!"got {repr v}"
    | other => .fail name s!"got {repr other}"

def precedenceTests : List TestResult :=
  -- A predicate takes the whole arithmetic expression on its left
  sameParse "prec_add_in" "SELECT a + b IN (1, 2) FROM t" "SELECT (a + b) IN (1, 2) FROM t" ++
  sameParse "prec_sub_not_in" "SELECT a - b NOT IN (1) FROM t" "SELECT (a - b) NOT IN (1) FROM t" ++
  sameParse "prec_mul_between" "SELECT a * b BETWEEN 1 AND 2 FROM t"
    "SELECT (a * b) BETWEEN 1 AND 2 FROM t" ++
  sameParse "prec_div_not_between" "SELECT a / b NOT BETWEEN 1 AND 2 FROM t"
    "SELECT (a / b) NOT BETWEEN 1 AND 2 FROM t" ++
  sameParse "prec_mod_is_null" "SELECT a % b IS NULL FROM t" "SELECT (a % b) IS NULL FROM t" ++
  sameParse "prec_add_is_not_null" "SELECT a + b IS NOT NULL FROM t"
    "SELECT (a + b) IS NOT NULL FROM t" ++
  sameParse "prec_concat_like" "SELECT a || b LIKE 'x%' FROM t" "SELECT (a || b) LIKE 'x%' FROM t" ++
  sameParse "prec_concat_not_like" "SELECT a || b NOT LIKE 'x%' FROM t"
    "SELECT (a || b) NOT LIKE 'x%' FROM t" ++
  sameParse "prec_mixed_arith_in" "SELECT a * 2 + b IN (1) FROM t" "SELECT ((a * 2) + b) IN (1) FROM t" ++
  sameParse "prec_neg_add_in" "SELECT - a + b IN (1) FROM t" "SELECT ((- a) + b) IN (1) FROM t" ++
  sameParse "prec_in_subquery" "SELECT x FROM t WHERE a + 1 NOT IN (SELECT b FROM u)"
    "SELECT x FROM t WHERE (a + 1) NOT IN (SELECT b FROM u)" ++
  -- Operands to the right of a predicate are arithmetic expressions
  sameParse "prec_like_pattern_concat" "SELECT a LIKE b || '%' FROM t"
    "SELECT a LIKE (b || '%') FROM t" ++
  sameParse "prec_between_bounds" "SELECT a BETWEEN b + 1 AND c * 2 FROM t"
    "SELECT a BETWEEN (b + 1) AND (c * 2) FROM t" ++
  -- NOT is looser than comparisons and predicates, tighter than AND
  sameParse "prec_not_eq" "SELECT x FROM t WHERE NOT a = b" "SELECT x FROM t WHERE NOT (a = b)" ++
  sameParse "prec_not_in" "SELECT x FROM t WHERE NOT a IN (1)" "SELECT x FROM t WHERE NOT (a IN (1))" ++
  sameParse "prec_not_is_null" "SELECT x FROM t WHERE NOT a IS NULL"
    "SELECT x FROM t WHERE NOT (a IS NULL)" ++
  sameParse "prec_not_between" "SELECT x FROM t WHERE NOT a + 1 BETWEEN 1 AND 2"
    "SELECT x FROM t WHERE NOT ((a + 1) BETWEEN 1 AND 2)" ++
  sameParse "prec_not_and" "SELECT x FROM t WHERE NOT a = b AND c = d"
    "SELECT x FROM t WHERE (NOT (a = b)) AND (c = d)" ++
  sameParse "prec_not_not" "SELECT x FROM t WHERE NOT NOT a = b"
    "SELECT x FROM t WHERE NOT (NOT (a = b))" ++
  -- IS NULL takes everything to its left; predicates and comparisons may follow it
  sameParse "prec_eq_is_null" "SELECT a = b IS NULL FROM t" "SELECT (a = b) IS NULL FROM t" ++
  sameParse "prec_is_null_eq" "SELECT a IS NULL = b FROM t" "SELECT (a IS NULL) = b FROM t" ++
  sameParse "prec_is_null_in" "SELECT a IS NULL IN (b) FROM t" "SELECT (a IS NULL) IN (b) FROM t" ++
  sameParse "prec_is_null_twice" "SELECT a IS NULL IS NOT NULL FROM t"
    "SELECT (a IS NULL) IS NOT NULL FROM t" ++
  sameParse "prec_eq_is_null_in" "SELECT a = b IS NULL IN (c) FROM t"
    "SELECT ((a = b) IS NULL) IN (c) FROM t" ++
  sameParse "prec_in_eq" "SELECT a IN (1) = b FROM t" "SELECT (a IN (1)) = b FROM t" ++
  sameParse "prec_in_in" "SELECT a IN (1) IN (b) FROM t" "SELECT (a IN (1)) IN (b) FROM t" ++
  sameParse "prec_between_eq" "SELECT a BETWEEN 1 AND 2 = b FROM t"
    "SELECT (a BETWEEN 1 AND 2) = b FROM t" ++
  sameParse "prec_between_and" "SELECT x FROM t WHERE a BETWEEN 1 AND 2 AND b = 1"
    "SELECT x FROM t WHERE (a BETWEEN 1 AND 2) AND (b = 1)" ++
  -- Registry row 21: a comparison followed by a predicate, as Postgres and DuckDB
  sameParse "prec_row21_eq_in" "SELECT a = b IN (c) FROM t" "SELECT a = (b IN (c)) FROM t" ++
  sameParse "prec_row21_eq_between" "SELECT a = b BETWEEN 1 AND 2 FROM t"
    "SELECT a = (b BETWEEN 1 AND 2) FROM t" ++
  sameParse "prec_row21_eq_like" "SELECT a = b LIKE 'x' FROM t" "SELECT a = (b LIKE 'x') FROM t" ++
  -- A SELECT item that starts with a name continues through AND / OR
  sameParse "prec_item_and_or" "SELECT a = 1 AND b + 1 IN (2) OR c IS NULL FROM t"
    "SELECT ((a = 1) AND ((b + 1) IN (2))) OR (c IS NULL) FROM t" ++
  sameParse "prec_item_qualified" "SELECT t.a * 2 BETWEEN 1 AND 2 AND t.b IN (1) FROM t"
    "SELECT ((t.a * 2) BETWEEN 1 AND 2) AND (t.b IN (1)) FROM t" ++
  sameParse "prec_item_agg" "SELECT COUNT(*) + 1 IN (2) FROM t" "SELECT (COUNT(*) + 1) IN (2) FROM t" ++ [
  -- Round trips through the pretty-printer
  testRoundTrip "prec_round_trip_in" "SELECT x FROM t WHERE a + 1 IN (2) AND NOT b = c",
  testRoundTrip "prec_round_trip_is_null" "SELECT a = b IS NULL, a * 2 IS NOT NULL FROM t",
  testRoundTrip "prec_round_trip_between_like"
    "SELECT x FROM t WHERE a - 1 NOT BETWEEN 1 AND 2 OR a || b NOT LIKE 'x' || '%'",
  -- Shapes the engines disagree on or reject are parse errors (row 21)
  failsWith "prec_chained_comparison_rejected" "SELECT 1 = 1 = 1" "do not chain",
  failsWith "prec_chained_lt_eq_rejected" "SELECT 1 < 2 = TRUE" "do not chain",
  failsWith "prec_chain_after_is_null_rejected" "SELECT 1 IS NULL = FALSE = TRUE" "do not chain",
  failsWith "prec_between_then_in_rejected" "SELECT 5 BETWEEN 1 AND 9 IN (TRUE)" "needs parentheses",
  failsWith "prec_between_then_between_rejected" "SELECT 1 BETWEEN 0 AND 2 BETWEEN 0 AND 1"
    "needs parentheses",
  failsWith "prec_like_then_like_rejected" "SELECT 'a' LIKE 'a' LIKE 'a'" "needs parentheses",
  failsWith "prec_like_then_not_in_rejected" "SELECT 'a' LIKE 'a' NOT IN (TRUE)" "needs parentheses",
  testParseFail "prec_arithmetic_after_predicate_rejected" "SELECT 2 IN (2) + 1",
  -- The queries of #400, as sqlite, DuckDB and Postgres evaluate them
  evalsTo "prec_eval_add_in" "SELECT 1 + 1 IN (2)" (.bool true),
  evalsTo "prec_eval_add_not_in" "SELECT 1 + 1 NOT IN (2)" (.bool false),
  evalsTo "prec_eval_add_between" "SELECT 1 + 1 BETWEEN 2 AND 3" (.bool true),
  evalsTo "prec_eval_mul_in" "SELECT 2 * 3 IN (6)" (.bool true),
  evalsTo "prec_eval_add_is_null" "SELECT 1 + 1 IS NULL" (.bool false),
  evalsTo "prec_eval_concat_like" "SELECT 'a' || 'b' LIKE 'ab'" (.bool true),
  evalsTo "prec_eval_not_eq" "SELECT NOT 1 = 2" (.bool true),
  evalsTo "prec_eval_not_null_is_null" "SELECT NOT NULL IS NULL" (.bool false),
  evalsTo "prec_eval_eq_is_null" "SELECT NULL = 1 IS NULL" (.bool true),
  evalsTo "prec_eval_case" "SELECT CASE WHEN 1 + 1 IN (2) THEN 'y' ELSE 'n' END" (.string "y")
]

def allParserTests : List TestResult :=
  basicSelectTests ++ whereTests ++ joinTests ++ groupOrderTests ++
  aggregateTests ++ subqueryTests ++ setOpTests ++ exprTests ++
  insertTests ++ updateTests ++ deleteTests ++ nonAsciiIdentTests ++ parseFailTests ++ cteTests ++
  recursiveCTETests ++ doubleQuoteTests ++ trailingInputTests ++ windowParserTests ++
  dialectPrintTests ++ precedenceTests

def runParserTests : IO (Nat × Nat) :=
  runTests "Parser Tests" allParserTests

end ParserTest
