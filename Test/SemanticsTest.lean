/-
  Semantics Tests: Evaluation against mock databases

  Tests that SQL evaluates correctly against sample data.
-/
import SqlEquiv
import Test.Common

namespace SemanticsTest

open SqlEquiv
open Test

-- ============================================================================
-- Sample Database
-- ============================================================================

/-- Sample users table -/
def usersTable : Table := [
  [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")],
  [("id", .int 2), ("name", .string "Bob"), ("age", .int 25), ("department", .string "Sales")],
  [("id", .int 3), ("name", .string "Carol"), ("age", .int 35), ("department", .string "Engineering")],
  [("id", .int 4), ("name", .string "Dave"), ("age", .int 28), ("department", .string "Marketing")],
  [("id", .int 5), ("name", .string "Eve"), ("age", .int 22), ("department", .string "Sales")]
]

/-- Sample orders table -/
def ordersTable : Table := [
  [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")],
  [("id", .int 2), ("user_id", .int 1), ("amount", .int 200), ("product", .string "Gadget")],
  [("id", .int 3), ("user_id", .int 2), ("amount", .int 150), ("product", .string "Widget")],
  [("id", .int 4), ("user_id", .int 3), ("amount", .int 300), ("product", .string "Gizmo")]
]

/-- Sample products table -/
def productsTable : Table := [
  [("id", .int 1), ("name", .string "Widget"), ("price", .int 50)],
  [("id", .int 2), ("name", .string "Gadget"), ("price", .int 100)],
  [("id", .int 3), ("name", .string "Gizmo"), ("price", .int 150)]
]

/-- Items with DECIMAL prices (canonical form), including a NULL price -/
def itemsTable : Table := [
  [("id", .int 1), ("name", .string "Bolt"), ("price", .decimal 25 1)],     -- 2.5
  [("id", .int 2), ("name", .string "Nut"),  ("price", .decimal 125 2)],    -- 1.25
  [("id", .int 3), ("name", .string "Washer"), ("price", .decimal 3 0)],    -- 3
  [("id", .int 4), ("name", .string "Shim"), ("price", .null (some .decimal))]
]

/-- NULL-ordering fixture: staff counts 9, 17, NULL, 25, 41, NULL (two NULLs,
    one in the middle, as in the Spider `museum` query that exposed the old
    "NULL equals everything" comparator). -/
def museumTable : Table := [
  [("name", .string "m1"), ("staff", .int 9)],
  [("name", .string "m2"), ("staff", .int 17)],
  [("name", .string "m3"), ("staff", .null none)],
  [("name", .string "m4"), ("staff", .int 25)],
  [("name", .string "m5"), ("staff", .int 41)],
  [("name", .string "m6"), ("staff", .null (some .int))]
]

/-- Spider-style table: original-case column names (queries lowercase them) -/
def singerTable : Table := [
  [("Singer_ID", .int 1), ("Name", .string "Joe"), ("Country", .string "France"), ("Age", .int 52)],
  [("Singer_ID", .int 2), ("Name", .string "Tribal King"), ("Country", .string "France"), ("Age", .int 25)],
  [("Singer_ID", .int 3), ("Name", .string "Rose White"), ("Country", .string "UK"), ("Age", .int 18)]
]

def testDb : Database := fun name =>
  match name with
  | "users" => usersTable
  | "orders" => ordersTable
  | "products" => productsTable
  | "items" => itemsTable
  | "singer" => singerTable
  | "museum" => museumTable
  | _ => []

-- ============================================================================
-- Test Helpers
-- ============================================================================

/-- Parse and evaluate a query (full statement grammar, so set operations
    and CTEs are visible — parseSelectStr would silently see only the first
    SELECT, #228) -/
def evalQuery (sql : String) : Except String Table :=
  match parse sql with
  | .error e => .error e
  | .ok stmt =>
    match (evalStmt testDb stmt).2 with
    | some t => .ok t
    | none => .error "statement produced no result table"

/-- Parse for a dialect, then evaluate. -/
def evalQueryIn (dialect : Dialect) (sql : String) : Except String Table :=
  match parse sql (dialect := dialect) with
  | .error e => .error e
  | .ok stmt =>
    match (evalStmt testDb stmt).2 with
    | some t => .ok t
    | none => .error "statement produced no result table"

/-- Parse with a given NULL-ordering rule (other choices: default dialect),
    then evaluate. -/
def evalQueryWith (ordering : NullOrdering) (sql : String) : Except String Table :=
  match parse sql (config := { defaultDialect.config with nullOrdering := ordering }) with
  | .error e => .error e
  | .ok stmt =>
    match (evalStmt testDb stmt).2 with
    | some t => .ok t
    | none => .error "statement produced no result table"

/-- Exact `name` column order under a NULL-ordering rule. -/
def testNameOrder (testName : String) (ordering : NullOrdering) (sql : String)
    (expected : List String) : TestResult :=
  match evalQueryWith ordering sql with
  | .error e => .fail testName s!"Parse/eval error: {e}"
  | .ok result =>
    let actual := result.map fun row =>
      match row.find? (fun (k, _) => k == "name") with
      | some (_, .string n) => n
      | _ => "?"
    if actual == expected then .pass testName
    else .fail testName s!"expected {expected}, got {actual}"

/-- First value of the result, parsed for a dialect -/
def testContainsValueIn (name : String) (dialect : Dialect) (sql : String) (expected : Value) :
    TestResult :=
  match evalQueryIn dialect sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    match result.head?.bind (·.head?) with
    | some (_, actual) =>
      if actual == expected then .pass name
      else .fail name s!"First value: expected {expected.toSql}, got {actual.toSql}"
    | none => .fail name "Could not get first value"

/-- Check if result has expected number of rows -/
def testRowCount (name : String) (sql : String) (expected : Nat) : TestResult :=
  match evalQuery sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    if result.length == expected then .pass name
    else .fail name s!"Expected {expected} rows, got {result.length}"

/-- Check if a specific value appears in the first column of results -/
def testContainsValue (name : String) (sql : String) (expected : Value) : TestResult :=
  match evalQuery sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    let values := result.filterMap fun row => row.head?.map (·.2)
    if values.contains expected then .pass name
    else .fail name s!"Expected to find {expected.toSql} in results"

/-- Check if result is empty -/
def testEmpty (name : String) (sql : String) : TestResult :=
  match evalQuery sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    if result.isEmpty then .pass name
    else .fail name s!"Expected empty result, got {result.length} rows"

/-- Check if result is non-empty -/
def testNonEmpty (name : String) (sql : String) : TestResult :=
  match evalQuery sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    if !result.isEmpty then .pass name
    else .fail name "Expected non-empty result"

/-- Check exact result (for small results) -/
def testExactRows (name : String) (sql : String) (expected : Nat) (checkFirst : Option Value := none) : TestResult :=
  match evalQuery sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    if result.length != expected then
      .fail name s!"Expected {expected} rows, got {result.length}"
    else
      match checkFirst with
      | none => .pass name
      | some v =>
        match result.head?.bind (·.head?) with
        | some (_, actual) =>
          if actual == v then .pass name
          else .fail name s!"First value: expected {v.toSql}, got {actual.toSql}"
        | none => .fail name "Could not get first value"

/-- Check the values of one named output column, in result-row order. -/
def testColumn (name : String) (sql : String) (col : String) (expected : List Value) : TestResult :=
  match evalQuery sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    let actual := result.map fun row =>
      ((row.find? (fun (k, _) => k == col)).map (·.2)).getD (.null none)
    if actual == expected then .pass name
    else .fail name
      s!"Column {col}: expected {expected.map (·.toSql)}, got {actual.map (·.toSql)}"

-- ============================================================================
-- Basic Query Tests
-- ============================================================================

def basicQueryTests : List TestResult := [
  testRowCount "select_all_users" "SELECT * FROM users" 5,
  testRowCount "select_all_orders" "SELECT * FROM orders" 4,
  testRowCount "select_all_products" "SELECT * FROM products" 3,
  testNonEmpty "select_columns" "SELECT name, age FROM users",
  testNonEmpty "select_with_alias" "SELECT name AS n FROM users"
]

-- ============================================================================
-- WHERE Clause Tests
-- ============================================================================

def whereQueryTests : List TestResult := [
  testRowCount "where_eq_int" "SELECT * FROM users WHERE age = 30" 1,
  testRowCount "where_gt" "SELECT * FROM users WHERE age > 25" 3,
  testRowCount "where_lt" "SELECT * FROM users WHERE age < 25" 1,
  testRowCount "where_ge" "SELECT * FROM users WHERE age >= 30" 2,
  testRowCount "where_le" "SELECT * FROM users WHERE age <= 25" 2,
  testRowCount "where_eq_string" "SELECT * FROM users WHERE department = 'Engineering'" 2,
  testRowCount "where_and" "SELECT * FROM users WHERE age > 25 AND department = 'Engineering'" 2,
  testRowCount "where_or" "SELECT * FROM users WHERE age < 25 OR age > 30" 2,
  testRowCount "where_complex" "SELECT * FROM users WHERE (department = 'Engineering' OR department = 'Sales') AND age > 25" 2,
  testEmpty "where_no_match" "SELECT * FROM users WHERE age > 100"
]

-- ============================================================================
-- JOIN Tests
-- ============================================================================

def joinQueryTests : List TestResult := [
  -- Basic JOIN tests
  testNonEmpty "inner_join" "SELECT * FROM users u INNER JOIN orders o ON u.id = o.user_id",
  testRowCount "inner_join_count" "SELECT * FROM users u INNER JOIN orders o ON u.id = o.user_id" 4,
  -- Users 4 and 5 have no orders, so left join should have more rows with NULLs
  testNonEmpty "left_join" "SELECT * FROM users u LEFT JOIN orders o ON u.id = o.user_id",
  testNonEmpty "cross_join" "SELECT * FROM users CROSS JOIN products",

  -- LEFT JOIN preserves all left rows (5 users, some with NULL order data)
  testRowCount "left_join_preserves_left" "SELECT * FROM users u LEFT JOIN orders o ON u.id = o.user_id" 6,

  -- CROSS JOIN cardinality: 5 users × 3 products = 15 rows
  testRowCount "cross_join_cardinality" "SELECT * FROM users CROSS JOIN products" 15,

  -- JOIN with additional WHERE filter
  testRowCount "join_with_where" "SELECT * FROM users u INNER JOIN orders o ON u.id = o.user_id WHERE o.amount > 150" 2,

  -- Self-join: users in same department
  testNonEmpty "self_join" "SELECT u1.name, u2.name FROM users u1 INNER JOIN users u2 ON u1.department = u2.department AND u1.id < u2.id",

  -- Multiple JOINs
  testNonEmpty "triple_join" "SELECT u.name, o.amount, p.price FROM users u INNER JOIN orders o ON u.id = o.user_id INNER JOIN products p ON o.product = p.name",

  -- JOIN on TRUE = CROSS JOIN equivalent
  testRowCount "join_on_true" "SELECT * FROM users u INNER JOIN products p ON 1 = 1" 15,

  -- JOIN on FALSE = empty
  testRowCount "join_on_false" "SELECT * FROM users u INNER JOIN orders o ON 1 = 0" 0
]

-- ============================================================================
-- Edge Case Tests
-- ============================================================================

def edgeCaseTests : List TestResult := [
  -- Empty result from WHERE FALSE
  testEmpty "where_false" "SELECT * FROM users WHERE 1 = 0",

  -- WHERE TRUE returns all rows
  testRowCount "where_true" "SELECT * FROM users WHERE 1 = 1" 5,

  -- LIMIT 0 returns empty
  testEmpty "limit_zero" "SELECT * FROM users LIMIT 0",

  -- OFFSET beyond row count returns empty
  testEmpty "offset_beyond" "SELECT * FROM users OFFSET 100",

  -- Empty IN list
  testEmpty "empty_in_subquery" "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders WHERE amount > 1000)",

  -- NOT IN with no matches returns all
  testRowCount "not_in_no_match" "SELECT * FROM users WHERE id NOT IN (SELECT user_id FROM orders WHERE amount > 1000)" 5,

  -- NULL handling in comparisons
  testNonEmpty "null_safe_query" "SELECT * FROM users WHERE name IS NOT NULL",

  -- COALESCE-like behavior
  testNonEmpty "case_null" "SELECT CASE WHEN name IS NULL THEN 'Unknown' ELSE name END FROM users",

  -- Empty table behavior (nonexistent table returns empty)
  testEmpty "empty_table" "SELECT * FROM nonexistent_table",

  -- DISTINCT on single value
  testRowCount "distinct_single" "SELECT DISTINCT 1 FROM users" 1,

  -- ORDER BY with LIMIT
  testRowCount "order_limit" "SELECT * FROM users ORDER BY age DESC LIMIT 2" 2,

  -- Complex nested conditions
  testNonEmpty "nested_conditions" "SELECT * FROM users WHERE (age > 25 AND department = 'Engineering') OR (age < 30 AND department = 'Sales')"
]

-- ============================================================================
-- Projection Tests
-- ============================================================================

def projectionTests : List TestResult := [
  testNonEmpty "select_single_col" "SELECT name FROM users",
  testNonEmpty "select_multi_col" "SELECT name, age FROM users",
  testNonEmpty "select_expression" "SELECT age FROM users WHERE age > 25"
]

-- ============================================================================
-- DISTINCT Tests
-- ============================================================================

def distinctTests : List TestResult := [
  testRowCount "distinct_department" "SELECT DISTINCT department FROM users" 3,
  testRowCount "non_distinct_department" "SELECT department FROM users" 5
]

-- ============================================================================
-- ORDER BY Tests
-- ============================================================================

def orderByTests : List TestResult := [
  testNonEmpty "order_by_asc" "SELECT * FROM users ORDER BY age ASC",
  testNonEmpty "order_by_desc" "SELECT * FROM users ORDER BY age DESC",
  testNonEmpty "order_by_multi" "SELECT * FROM users ORDER BY department ASC, age DESC"
]

-- ============================================================================
-- LIMIT/OFFSET Tests
-- ============================================================================

-- Grouped ORDER BY (#234): sort keys may be aggregates or non-projected
-- grouping columns, evaluated per group. The aggregate / non-projected cases
-- fail on the pre-fix evaluator (groups left in encounter order; checked);
-- the two alias cases passed before too and guard that output columns still
-- take precedence over source columns.
-- orders: user 1 → 2 rows (100, 200), user 2 → 1 (150), user 3 → 1 (300);
--         Widget → 2 rows (100, 150), Gadget → 1 (200), Gizmo → 1 (300).
def groupedOrderByTests : List TestResult := [
  -- COUNT(*) ASC: first count-1 group is user 2 (encounter order would give user 1)
  testColumn "group_order_count_asc"
    "SELECT user_id FROM orders GROUP BY user_id ORDER BY COUNT(*) ASC LIMIT 1"
    "user_id" [.int 2],
  -- SUM(amount) DESC, not projected: Gizmo 300, Widget 250, Gadget 200
  testColumn "group_order_sum_desc"
    "SELECT product FROM orders GROUP BY product ORDER BY SUM(amount) DESC"
    "product" [.string "Gizmo", .string "Widget", .string "Gadget"],
  -- Expression over an aggregate: 0 - COUNT(*) DESC puts count-1 groups first
  testColumn "group_order_agg_expr"
    "SELECT user_id FROM orders GROUP BY user_id ORDER BY 0 - COUNT(*) DESC LIMIT 1"
    "user_id" [.int 2],
  -- Projected aggregate via alias (output column)
  testColumn "group_order_alias"
    "SELECT product, SUM(amount) AS total FROM orders GROUP BY product ORDER BY total"
    "product" [.string "Gadget", .string "Widget", .string "Gizmo"],
  -- Output alias wins over a source column of the same name: `amount` here is
  -- COUNT(*) (Widget 2, others 1), not orders.amount (which would give Gizmo first)
  testColumn "group_order_alias_shadows_source"
    "SELECT product, COUNT(*) AS amount FROM orders GROUP BY product ORDER BY amount DESC"
    "product" [.string "Widget", .string "Gadget", .string "Gizmo"],
  -- Mixed output alias + aggregate (sqlite agrees): total + COUNT(*) gives
  -- Gadget 201, Widget 252, Gizmo 301
  testColumn "group_order_alias_plus_agg"
    "SELECT product, SUM(amount) AS total FROM orders GROUP BY product ORDER BY total + COUNT(*)"
    "product" [.string "Gadget", .string "Widget", .string "Gizmo"],
  -- Non-projected grouping column: Engineering 2, Marketing 1, Sales 2
  testColumn "group_order_nonprojected_group_col"
    "SELECT COUNT(*) AS c FROM users GROUP BY department ORDER BY department"
    "c" [.int 2, .int 1, .int 2],
  -- With HAVING: Sales (avg 23) before Engineering (avg 32)
  testColumn "group_order_having_avg"
    "SELECT department FROM users GROUP BY department HAVING COUNT(*) > 1 ORDER BY AVG(age) ASC"
    "department" [.string "Sales", .string "Engineering"]
]

-- NULL ordering (configurable): NULLs sort together, placed by the item's
-- NULLS FIRST/LAST, which defaults per engine rule. staff: m1 9, m2 17,
-- m3 NULL, m4 25, m5 41, m6 NULL. Ties keep input order (stable sort).
def nullOrderingTests : List TestResult := [
  -- sqlite rule: NULL smallest
  testNameOrder "nulls_sqlite_asc" .nullsSmallest
    "SELECT name FROM museum ORDER BY staff" ["m3", "m6", "m1", "m2", "m4", "m5"],
  -- the old comparator put 25 first here (NULL "equal to everything")
  testNameOrder "nulls_sqlite_desc" .nullsSmallest
    "SELECT name FROM museum ORDER BY staff DESC" ["m5", "m4", "m2", "m1", "m3", "m6"],
  -- Postgres rule (and the standard dialect's choice): NULL largest
  testNameOrder "nulls_postgres_asc" .nullsLargest
    "SELECT name FROM museum ORDER BY staff" ["m1", "m2", "m4", "m5", "m3", "m6"],
  testNameOrder "nulls_postgres_desc" .nullsLargest
    "SELECT name FROM museum ORDER BY staff DESC" ["m3", "m6", "m5", "m4", "m2", "m1"],
  -- DuckDB rule: NULLs last both ways
  testNameOrder "nulls_duckdb_asc" .nullsAlwaysLast
    "SELECT name FROM museum ORDER BY staff" ["m1", "m2", "m4", "m5", "m3", "m6"],
  testNameOrder "nulls_duckdb_desc" .nullsAlwaysLast
    "SELECT name FROM museum ORDER BY staff DESC" ["m5", "m4", "m2", "m1", "m3", "m6"],
  -- Explicit NULLS FIRST/LAST overrides the rule
  testNameOrder "nulls_explicit_overrides_rule" .nullsSmallest
    "SELECT name FROM museum ORDER BY staff DESC NULLS FIRST" ["m3", "m6", "m5", "m4", "m2", "m1"],
  testNameOrder "nulls_explicit_last_asc" .nullsSmallest
    "SELECT name FROM museum ORDER BY staff ASC NULLS LAST" ["m1", "m2", "m4", "m5", "m3", "m6"],
  -- LIMIT makes the cut observable (the Spider museum shape)
  testNameOrder "nulls_desc_limit" .nullsSmallest
    "SELECT name FROM museum ORDER BY staff DESC LIMIT 1" ["m5"],
  -- Pretty-printing: the clause is printed only when it differs from the
  -- default dialect's rule (standard: NULL largest, so DESC → NULLS FIRST)
  (match parseSelectStr "SELECT name FROM museum ORDER BY staff DESC NULLS LAST",
         parseSelectStr "SELECT name FROM museum ORDER BY staff DESC" with
   | .ok s1, .ok s2 =>
     if (s1.toSql.splitOn "NULLS LAST").length == 2 && (s2.toSql.splitOn "NULLS").length == 1
     then .pass "nulls_pretty_print"
     else .fail "nulls_pretty_print" s!"got: {s1.toSql} / {s2.toSql}"
   | _, _ => .fail "nulls_pretty_print" "parse error"),
  -- Columns named first/last are still ordinary identifiers
  (match parseSelectStr "SELECT first, last FROM t ORDER BY last" with
   | .ok _ => .pass "nulls_words_not_reserved"
   | .error e => .fail "nulls_words_not_reserved" e),
  -- docs/IMPLEMENTATION_DEFINED.md row 12 (#235, decided): a TEXT value
  -- compared with a number is a type error in our core semantics, so the
  -- row is dropped. sqlite would compare as text (column affinity); the
  -- Spider harness emulates that by quoting the literal, the core does not.
  testRowCount "text_vs_number_is_type_error" "SELECT * FROM singer WHERE Country >= 2014" 0,
  testRowCount "text_vs_quoted_number_compares_as_text"
    "SELECT * FROM singer WHERE Country >= '2014'" 3
]

def limitOffsetTests : List TestResult := [
  testRowCount "limit" "SELECT * FROM users LIMIT 3" 3,
  testRowCount "limit_offset" "SELECT * FROM users LIMIT 2 OFFSET 2" 2,
  testRowCount "limit_large" "SELECT * FROM users LIMIT 100" 5,
  testRowCount "offset_large" "SELECT * FROM users LIMIT 10 OFFSET 10" 0
]

-- ============================================================================
-- Subquery Tests
-- ============================================================================

/-- Row count of a query parsed for a dialect -/
def testRowCountIn (name : String) (dialect : Dialect) (sql : String) (expected : Nat) :
    TestResult :=
  match evalQueryIn dialect sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    if result.length == expected then .pass name
    else .fail name s!"Expected {expected} rows, got {result.length}"

-- Pins for implementation-defined behaviour (docs/IMPLEMENTATION_DEFINED.md,
-- #262), so none of these can change silently.
def registryPinTests : List TestResult := [
  -- Row 8: LIKE letter case is per dialect. standard/duckdb/postgres:
  -- case-sensitive; sqlite: ASCII case-insensitive.
  testRowCount "like_case_sensitive_standard"
    "SELECT name FROM users WHERE name LIKE 'al%'" 0,
  testRowCountIn "like_case_sensitive_duckdb" .duckdb
    "SELECT name FROM users WHERE name LIKE 'al%'" 0,
  testRowCountIn "like_case_sensitive_postgres" .postgres
    "SELECT name FROM users WHERE name LIKE 'AL%'" 0,
  testRowCountIn "like_ascii_ci_sqlite" .sqlite
    "SELECT name FROM users WHERE name LIKE 'al%'" 1,
  testRowCountIn "like_ascii_ci_sqlite_whole" .sqlite
    "SELECT name FROM users WHERE name LIKE 'ALICE'" 1,
  -- sqlite only folds ASCII: 'ÄBC' LIKE 'äbc' is false
  testRowCountIn "like_ci_non_ascii_exact_sqlite" .sqlite
    "SELECT name FROM users WHERE 'ÄBC' LIKE 'äbc'" 0,
  -- NOT LIKE uses the dialect's LIKE
  testRowCount "not_like_case_sensitive_standard"
    "SELECT name FROM users WHERE name NOT LIKE 'al%'" 5,
  testRowCountIn "not_like_ascii_ci_sqlite" .sqlite
    "SELECT name FROM users WHERE name NOT LIKE 'al%'" 4,
  testRowCountIn "like_ci_null_pattern_sqlite" .sqlite
    "SELECT name FROM users WHERE name LIKE NULL" 0,
  -- the dialect's choice is recorded on the AST (BinOp.likeCI)
  (match parse "SELECT a FROM t WHERE a LIKE 'x'" (dialect := .sqlite),
         parse "SELECT a FROM t WHERE a LIKE 'x'" with
   | .ok a, .ok b =>
     if ((reprStr a).splitOn "likeCI").length == 2 && ((reprStr b).splitOn "likeCI").length == 1
     then .pass "like_mode_recorded_in_ast"
     else .fail "like_mode_recorded_in_ast" s!"{reprStr a} / {reprStr b}"
   | _, _ => .fail "like_mode_recorded_in_ast" "parse error"),
  -- Row 5 (per dialect): DISTINCT with a non-selected sort key. standard and
  -- postgres reject it at parse time, as Postgres does; sqlite and duckdb
  -- accept it.
  (match parse "SELECT DISTINCT department FROM users ORDER BY age",
         parse "SELECT DISTINCT department FROM users ORDER BY age" (dialect := .postgres),
         parse "SELECT DISTINCT department FROM users ORDER BY age" (dialect := .sqlite),
         parse "SELECT DISTINCT department FROM users ORDER BY age" (dialect := .duckdb) with
   | .error e1, .error e2, .ok _, .ok _ =>
     if (e1.splitOn "must appear in select list").length == 2 &&
        (e2.splitOn "must appear in select list").length == 2
     then .pass "distinct_order_by_unselected_per_dialect"
     else .fail "distinct_order_by_unselected_per_dialect" s!"{e1} / {e2}"
   | _, _, _, _ => .fail "distinct_order_by_unselected_per_dialect" "wrong accept/reject pattern"),
  -- Selected keys stay accepted in the rejecting dialects: the expression, an
  -- alias, a position, a qualified name, a `*` item, and an expression key.
  (let ok := [
      "SELECT DISTINCT department FROM users ORDER BY department",
      "SELECT DISTINCT department AS d FROM users ORDER BY d DESC",
      "SELECT DISTINCT department FROM users ORDER BY 1",
      "SELECT DISTINCT u.department FROM users u ORDER BY u.department",
      "SELECT DISTINCT department FROM users u ORDER BY u.department",
      "SELECT DISTINCT * FROM users ORDER BY age",
      "SELECT DISTINCT age + 1 FROM users ORDER BY age + 1"]
   match ok.filter (fun q => (parse q).toOption.isNone) with
   | [] => .pass "distinct_order_by_selected_accepted"
   | bad => .fail "distinct_order_by_selected_accepted" s!"rejected: {bad}"),
  -- In the sqlite and duckdb dialects SqlEquiv still ties the key, so output
  -- keeps input order; the engines sort by each value's first source row
  -- (Sales, Marketing, Engineering). Gap, #320; SqlCore implements it.
  (match evalQueryIn .sqlite "SELECT DISTINCT department FROM users ORDER BY age" with
   | .ok t =>
     let col := t.map fun row => ((row.find? (·.1 == "department")).map (·.2)).getD (.null none)
     if col == [.string "Engineering", .string "Sales", .string "Marketing"]
     then .pass "distinct_order_by_unselected_keeps_input_order"
     else .fail "distinct_order_by_unselected_keeps_input_order" s!"{col.map (·.toSql)}"
   | .error e => .fail "distinct_order_by_unselected_keeps_input_order" e),
  -- #317: a trailing ORDER BY/LIMIT sorts and limits the whole compound query,
  -- not its last branch (sqlite, DuckDB, Postgres: one row, Alice).
  testColumn "compound_order_by_limit_whole"
    "SELECT name FROM users WHERE id < 3 UNION ALL SELECT name FROM products ORDER BY 1 LIMIT 1"
    "name" [.string "Alice"],
  testColumn "compound_order_by_name_desc"
    "SELECT name FROM users WHERE id < 3 UNION ALL SELECT name FROM products ORDER BY name DESC"
    "name" [.string "Widget", .string "Gizmo", .string "Gadget", .string "Bob", .string "Alice"],
  (match parse "SELECT name FROM users ORDER BY name UNION SELECT name FROM products",
         parse "SELECT name FROM users UNION SELECT name FROM products ORDER BY 2",
         parse "SELECT age + 1 FROM users UNION SELECT id FROM users ORDER BY 1",
         parse "SELECT name FROM users UNION SELECT name FROM products ORDER BY users.name",
         parse "SELECT name FROM users UNION SELECT name FROM products ORDER BY lower(name)",
         parse "SELECT name FROM users UNION SELECT title AS t FROM products ORDER BY t" with
   | .error e1, .error e2, .error e3, .error e4, .error e5, .error e6 =>
     if (e1.splitOn "after the last branch").length == 2 && (e2.splitOn "not in the select list").length == 2 &&
        (e3.splitOn "without an alias").length == 2 && (e4.splitOn "must name an output column").length == 2 &&
        (e5.splitOn "must name an output column").length == 2 && (e6.splitOn "not a column of its first branch").length == 2
     then .pass "compound_order_by_errors" else .fail "compound_order_by_errors" s!"{e1} / {e2} / {e3} / {e4} / {e5} / {e6}"
   | _, _, _, _, _, _ => .fail "compound_order_by_errors" "parsed"),
  -- #316: `ORDER BY k` sorts by the k-th SELECT item (sqlite, DuckDB and
  -- Postgres); out of range is an error in all three.
  testColumn "order_by_position"
    "SELECT name, age FROM users ORDER BY 2" "name"
    [.string "Eve", .string "Bob", .string "Dave", .string "Alice", .string "Carol"],
  testColumn "order_by_position_desc_with_alias"
    "SELECT age AS a, name FROM users ORDER BY 1 DESC" "name"
    [.string "Carol", .string "Alice", .string "Dave", .string "Bob", .string "Eve"],
  (match parse "SELECT name, age FROM users ORDER BY 3", parse "SELECT name FROM users ORDER BY 0" with
   | .error e1, .error e2 =>
     if (e1.splitOn "not in the select list").length == 2 && (e2.splitOn "not in the select list").length == 2
     then .pass "order_by_position_out_of_range" else .fail "order_by_position_out_of_range" s!"{e1} / {e2}"
   | _, _ => .fail "order_by_position_out_of_range" "parsed"),
  -- #315: NULLs group together whatever their static type tag (museum has an
  -- untyped and an int-typed NULL staff): one NULL group of 2, as every engine.
  testRowCount "group_by_typed_nulls_one_group"
    "SELECT staff, COUNT(*) FROM museum GROUP BY staff" 5,
  (match evalQuery "SELECT staff, COUNT(*) FROM museum WHERE staff IS NULL GROUP BY staff" with
   | .ok [row] =>
     if (row.map (·.2)).getLast? == some (.int 2) then .pass "group_by_typed_nulls_count"
     else .fail "group_by_typed_nulls_count" s!"{row.map (·.2.toSql)}"
   | .ok t => .fail "group_by_typed_nulls_count" s!"{t.length} groups"
   | .error e => .fail "group_by_typed_nulls_count" e),
  -- Row 11 (decided, #254: keep): a number compared with a numeric-looking
  -- string is a type error, so the row is dropped. sqlite, DuckDB and
  -- Postgres all convert the string and return Alice (age 30). Kept as a
  -- documented divergence; see docs/IMPLEMENTATION_DEFINED.md row 11.
  testRowCount "int_vs_numeric_string_literal_drops_row"
    "SELECT name FROM users WHERE age = '30'" 0,
  testRowCount "numeric_string_literal_vs_int_drops_row"
    "SELECT name FROM users WHERE '30' = age" 0,
  testRowCount "int_in_numeric_string_list_drops_row"
    "SELECT name FROM users WHERE age IN ('30', '25')" 0,
  testRowCount "int_between_numeric_strings_drops_row"
    "SELECT name FROM users WHERE age BETWEEN '20' AND '40'" 0,
  -- Row 6: integer division truncates (sqlite, Postgres; DuckDB's / gives 3.5)
  testContainsValue "int_division_truncates" "SELECT 7 / 2 FROM users LIMIT 1" (.int 3),
  -- …toward zero for negatives, as all three engines do (was Euclidean: -4 / 1)
  testContainsValue "int_division_truncates_negative" "SELECT -7 / 2 FROM users LIMIT 1" (.int (-3)),
  testContainsValue "int_mod_sign_of_dividend" "SELECT -7 % 2 FROM users LIMIT 1" (.int (-1)),
  testContainsValue "int_division_negative_divisor" "SELECT 7 / (0 - 2) FROM users LIMIT 1" (.int (-3)),
  testContainsValue "avg_truncates_toward_zero" "SELECT AVG(0 - age) FROM users WHERE id < 3" (.int (-27)),
  -- Row 9: strings order by code point ('B' = 66 < 'a' = 97), in every dialect
  testRowCount "string_order_code_point" "SELECT name FROM users WHERE 'a' < 'B'" 0,
  testRowCount "string_order_code_point_upper_first" "SELECT name FROM users WHERE 'B' < 'a'" 5
]

def subqueryTests : List TestResult := [
  -- Users who have orders
  testRowCount "in_subquery" "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders)" 3,
  -- Users who don't have orders
  testRowCount "not_in_subquery" "SELECT * FROM users WHERE id NOT IN (SELECT user_id FROM orders)" 2,
  -- EXISTS - users with at least one order (correlated)
  testNonEmpty "exists_subquery" "SELECT * FROM users WHERE EXISTS (SELECT 1 FROM orders WHERE orders.user_id = users.id)",
  -- Correlated IN subquery - users with high-value orders (amount > 150)
  -- Alice has order 200, Carol has order 300 = 2 users
  testRowCount "in_subquery_correlated" "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders WHERE orders.amount > 150)" 2,
  -- Correlated scalar subquery - get first order amount for Alice
  -- Alice's first order (id=1) has amount=100
  testContainsValue "scalar_subquery_correlated" "SELECT (SELECT amount FROM orders WHERE orders.user_id = users.id LIMIT 1) FROM users WHERE id = 1" (.int 100),
  -- Correlated scalar subquery with MAX aggregate - get max order amount for Alice
  -- Alice has orders 100 and 200, so max is 200
  testContainsValue "scalar_subquery_max" "SELECT (SELECT MAX(amount) FROM orders WHERE orders.user_id = users.id) FROM users WHERE id = 1" (.int 200),
  -- Name resolution is inner-first (#253): an unqualified column inside a
  -- subquery binds to the subquery's own FROM before the outer row.
  -- singer ages 52, 25, 18. Outer-first resolution gave 52 / 0 rows / 3 rows.
  testContainsValue "scope_scalar_same_table"
    "SELECT (SELECT MIN(age) FROM singer) FROM singer" (.int 18),
  testRowCount "scope_where_min_same_table"
    "SELECT name FROM singer WHERE age > (SELECT MIN(age) FROM singer)" 2,
  testRowCount "scope_where_max_minus_same_table"
    "SELECT name FROM singer WHERE age > (SELECT MAX(age) - 11 FROM singer)" 1,
  -- `id` is products.id (1..3), not the outer users.id (outer-first gave 5)
  testRowCount "scope_in_shadowed_column"
    "SELECT name FROM users WHERE id IN (SELECT id FROM products)" 3,
  -- Columns the subquery lacks still fall through to the outer row:
  -- amount > age * 10 holds for Bob (250), Dave (280), Eve (220)
  testRowCount "scope_outer_fallthrough"
    "SELECT name FROM users WHERE EXISTS (SELECT 1 FROM orders WHERE amount > age * 10)" 3,
  -- Outer row from a derived table has *unqualified* keys (`age`); the inner
  -- table's keys are qualified (`users.age`). Unqualified lookup is a single
  -- first-match pass, so the inner key still wins (MIN = 22 → 4 rows; an
  -- exact-match-first lookup gave the outer `age` and 0 rows)
  testRowCount "scope_derived_outer_unqualified_keys"
    "SELECT name FROM (SELECT name, age FROM users) AS d WHERE age > (SELECT MIN(age) FROM users)" 4,
  -- #257 (fixed): a derived table's alias qualifies its columns, as in
  -- sqlite and DuckDB (each query checked against both on users 1–4; the
  -- fixture here also has Eve, 5th row). Unqualified
  -- references keep working.
  testColumn "derived_unqualified_ref_works"
    "SELECT name FROM (SELECT name, id FROM users WHERE id < 3) AS x" "name"
    [.string "Alice", .string "Bob"],
  testColumn "derived_alias_qualified_ref"
    "SELECT x.name FROM (SELECT name, id FROM users) AS x" "name"
    [.string "Alice", .string "Bob", .string "Carol", .string "Dave", .string "Eve"],
  testColumn "derived_alias_qualified_where"
    "SELECT d.name FROM (SELECT name, age FROM users) AS d WHERE d.age > 26" "name"
    [.string "Alice", .string "Carol", .string "Dave"],
  -- SELECT * inside: `users.name` is re-qualified as `x.name`
  testColumn "derived_star_requalified"
    "SELECT x.name FROM (SELECT * FROM users) AS x WHERE x.id < 3" "name"
    [.string "Alice", .string "Bob"],
  -- nested derived tables: the outer alias wins
  testColumn "derived_nested_alias"
    "SELECT y.name FROM (SELECT x.name FROM (SELECT name FROM users) AS x) AS y" "name"
    [.string "Alice", .string "Bob", .string "Carol", .string "Dave", .string "Eve"],
  -- derived table over a join
  testColumn "derived_over_join"
    "SELECT d.name FROM (SELECT u.name, v.age FROM users u JOIN users v ON u.id = v.id) AS d WHERE d.age > 29" "name"
    [.string "Alice", .string "Carol"],
  -- the inner table's qualifier is out of scope outside the derived table
  -- (engines reject `users.name` here; ours finds no such column: NULL)
  testContainsValue "derived_inner_qualifier_out_of_scope"
    "SELECT users.name FROM (SELECT * FROM users) AS x" (.null none)
]

-- ============================================================================
-- Aggregate Tests
-- ============================================================================

def aggregateTests : List TestResult := [
  -- COUNT(*) - count all orders
  testContainsValue "count_star" "SELECT COUNT(*) FROM orders" (.int 4),
  -- COUNT(column) - count non-null values
  testContainsValue "count_col" "SELECT COUNT(amount) FROM orders" (.int 4),
  -- SUM - sum of all order amounts (100 + 200 + 150 + 300 = 750)
  testContainsValue "sum" "SELECT SUM(amount) FROM orders" (.int 750),
  -- AVG - average order amount (750 / 4 = 187 integer division)
  testContainsValue "avg" "SELECT AVG(amount) FROM orders" (.int 187),
  -- MIN - minimum order amount
  testContainsValue "min" "SELECT MIN(amount) FROM orders" (.int 100),
  -- MAX - maximum order amount
  testContainsValue "max" "SELECT MAX(amount) FROM orders" (.int 300),
  -- Aggregate with WHERE clause - sum of orders over 150
  testContainsValue "sum_where" "SELECT SUM(amount) FROM orders WHERE amount > 150" (.int 500),
  -- COUNT with WHERE - orders over 100
  testContainsValue "count_where" "SELECT COUNT(*) FROM orders WHERE amount > 100" (.int 3),
  -- Multiple aggregates in one query
  testNonEmpty "multi_agg" "SELECT COUNT(*), SUM(amount), MAX(amount) FROM orders"
]

-- ============================================================================
-- DISTINCT Aggregate Tests
-- ============================================================================

def distinctAggTests : List TestResult := [
  -- COUNT(DISTINCT department): Engineering, Sales, Marketing = 3
  testContainsValue "count_distinct_dept" "SELECT COUNT(DISTINCT department) FROM users" (.int 3),
  -- COUNT(DISTINCT user_id) in orders: 1, 2, 3 = 3 distinct
  testContainsValue "count_distinct_user" "SELECT COUNT(DISTINCT user_id) FROM orders" (.int 3),
  -- COUNT(DISTINCT product): Widget, Gadget, Gizmo = 3 distinct
  testContainsValue "count_distinct_product" "SELECT COUNT(DISTINCT product) FROM orders" (.int 3),
  -- SUM(DISTINCT user_id): 1+2+3 = 6 (vs SUM = 1+1+2+3 = 7)
  testContainsValue "sum_distinct_user" "SELECT SUM(DISTINCT user_id) FROM orders" (.int 6),
  -- Verify non-distinct SUM is different: 1+1+2+3 = 7
  testContainsValue "sum_user_nodistinct" "SELECT SUM(user_id) FROM orders" (.int 7),
  -- AVG(DISTINCT user_id): (1+2+3)/3 = 2
  testContainsValue "avg_distinct_user" "SELECT AVG(DISTINCT user_id) FROM orders" (.int 2),
  -- MIN/MAX with DISTINCT (should be same as without)
  testContainsValue "min_distinct" "SELECT MIN(DISTINCT amount) FROM orders" (.int 100),
  testContainsValue "max_distinct" "SELECT MAX(DISTINCT amount) FROM orders" (.int 300),
  -- MIN/MAX over strings order by code point (#256; was NULL)
  testContainsValue "max_string" "SELECT MAX(name) FROM users" (.string "Eve"),
  testContainsValue "min_string" "SELECT MIN(name) FROM users" (.string "Alice"),
  -- NULLs are skipped: names of users over 26 are Alice, Carol, Dave
  testContainsValue "max_string_skips_null"
    "SELECT MAX(CASE WHEN age > 26 THEN name END) FROM users" (.string "Dave"),
  -- Grouped and windowed paths: Engineering = {Alice, Carol}
  testContainsValue "max_string_grouped"
    "SELECT MAX(name) FROM users GROUP BY department HAVING department = 'Engineering'"
    (.string "Carol"),
  testContainsValue "max_string_window"
    "SELECT MAX(name) OVER (PARTITION BY department) AS m FROM users WHERE id = 1"
    (.string "Alice"),
  -- Mixed numeric/string input (registry row 13) depends on the dialect:
  -- strings Alice/Carol/Dave, ints 25, 22.
  -- standard (default) / duckdb / postgres: an error (shown as NULL)
  testContainsValue "minmax_mixed_standard_is_error"
    "SELECT MAX(CASE WHEN age > 26 THEN name ELSE age END) FROM users" (.null none),
  testContainsValueIn "minmax_mixed_duckdb_is_error" .duckdb
    "SELECT MIN(CASE WHEN age > 26 THEN name ELSE age END) FROM users" (.null none),
  -- …and in HAVING the error drops the group (sqlite keeps it)
  testRowCount "minmax_mixed_error_in_having"
    "SELECT COUNT(*) FROM users HAVING MAX(CASE WHEN age > 26 THEN name ELSE age END) IS NOT NULL" 0,
  (match evalQueryIn .sqlite
      "SELECT COUNT(*) FROM users HAVING MAX(CASE WHEN age > 26 THEN name ELSE age END) IS NOT NULL" with
   | .ok rows => if rows.length == 1 then .pass "minmax_mixed_sqlite_in_having"
                 else .fail "minmax_mixed_sqlite_in_having" s!"expected 1 row, got {rows.length}"
   | .error e => .fail "minmax_mixed_sqlite_in_having" e),
  -- sqlite: numbers before strings → MAX the greatest string, MIN the least number
  testContainsValueIn "max_mixed_sqlite_type_class" .sqlite
    "SELECT MAX(CASE WHEN age > 26 THEN name ELSE age END) FROM users" (.string "Dave"),
  testContainsValueIn "min_mixed_sqlite_type_class" .sqlite
    "SELECT MIN(CASE WHEN age > 26 THEN name ELSE age END) FROM users" (.int 22),
  -- Unmixed input is the same in every dialect
  testContainsValueIn "max_string_sqlite" .sqlite "SELECT MAX(name) FROM users" (.string "Eve"),
  -- Booleans (registry row 14). age > 26: Alice, Carol, Dave true; Bob, Eve false
  -- standard / postgres: not orderable → error (NULL in SELECT, dropped in HAVING)
  testContainsValue "max_bool_standard_is_error" "SELECT MAX(age > 26) FROM users" (.null none),
  testContainsValueIn "max_bool_postgres_is_error" .postgres "SELECT MAX(age > 26) FROM users" (.null none),
  testRowCount "max_bool_error_in_having"
    "SELECT COUNT(*) FROM users HAVING MAX(age > 26) IS NOT NULL" 0,
  -- sqlite: booleans are 1/0
  testContainsValueIn "max_bool_sqlite_int" .sqlite "SELECT MAX(age > 26) FROM users" (.int 1),
  testContainsValueIn "min_bool_sqlite_int" .sqlite "SELECT MIN(age > 26) FROM users" (.int 0),
  -- duckdb: booleans only → boolean result (false < true)
  testContainsValueIn "max_bool_duckdb_bool" .duckdb "SELECT MAX(age > 26) FROM users" (.bool true),
  testContainsValueIn "min_bool_duckdb_bool" .duckdb "SELECT MIN(age > 26) FROM users" (.bool false),
  testContainsValueIn "max_bool_duckdb_where_all_true" .duckdb
    "SELECT MIN(age > 26) FROM users WHERE age > 26" (.bool true),
  -- with integers, booleans act as 1/0 (sqlite and duckdb): Alice/Carol true,
  -- Dave false (28 > 29 is false), Bob 25, Eve 22 → MAX 25, MIN 0
  testContainsValueIn "max_bool_and_int_sqlite" .sqlite
    "SELECT MAX(CASE WHEN age > 26 THEN age > 29 ELSE age END) FROM users" (.int 25),
  testContainsValueIn "min_bool_and_int_duckdb" .duckdb
    "SELECT MIN(CASE WHEN age > 26 THEN age > 29 ELSE age END) FROM users" (.int 0),
  -- duckdb: booleans with strings → error (DuckDB: cannot convert to BOOL)
  testContainsValueIn "max_bool_and_string_duckdb_error" .duckdb
    "SELECT MAX(CASE WHEN age > 26 THEN age > 29 ELSE name END) FROM users" (.null none),
  -- windowed path
  testContainsValueIn "max_bool_window_sqlite" .sqlite
    "SELECT MAX(age > 26) OVER (PARTITION BY department) AS m FROM users WHERE id = 2" (.int 0),
  -- The dialect's choice is recorded on the AST node
  (match parse "SELECT MAX(x) FROM t" (dialect := .sqlite), parse "SELECT MAX(x) FROM t" with
   | .ok a, .ok b =>
     if ((reprStr a).splitOn "typeClass").length == 2 && ((reprStr a).splitOn "asInt").length == 2 &&
        ((reprStr b).splitOn "MixedMinMax.error").length == 2 && ((reprStr b).splitOn "BoolMinMax.error").length == 2
     then .pass "minmax_mode_recorded_in_ast"
     else .fail "minmax_mode_recorded_in_ast" s!"{reprStr a} / {reprStr b}"
   | _, _ => .fail "minmax_mode_recorded_in_ast" "parse error")
]

-- ============================================================================
-- GROUP BY Tests
-- ============================================================================

def groupByTests : List TestResult := [
  -- GROUP BY department: Engineering (2), Sales (2), Marketing (1) = 3 groups
  testRowCount "group_by_count" "SELECT department, COUNT(*) FROM users GROUP BY department" 3,
  -- GROUP BY user_id for orders: user 1 (2 orders), user 2 (1), user 3 (1) = 3 groups
  testRowCount "group_by_user" "SELECT user_id, COUNT(*) FROM orders GROUP BY user_id" 3,
  -- SUM per user: user 1 = 100+200=300, user 2 = 150, user 3 = 300
  testRowCount "group_by_sum" "SELECT user_id, SUM(amount) FROM orders GROUP BY user_id" 3,
  -- GROUP BY product: Widget (2), Gadget (1), Gizmo (1) = 3 groups
  testRowCount "group_by_product" "SELECT product, COUNT(*) FROM orders GROUP BY product" 3,
  -- MAX per product: Widget max=150, Gadget=200, Gizmo=300
  testNonEmpty "group_by_max" "SELECT product, MAX(amount) FROM orders GROUP BY product",
  -- HAVING clause: only departments with count > 1 (Engineering, Sales)
  testRowCount "group_by_having" "SELECT department, COUNT(*) FROM users GROUP BY department HAVING COUNT(*) > 1" 2,
  -- Multiple GROUP BY columns
  testNonEmpty "group_by_multi" "SELECT department, COUNT(*) FROM users GROUP BY department"
]

-- ============================================================================
-- Set Operation Tests
-- ============================================================================

def setOpQueryTests : List TestResult := [
  -- UNION removes duplicates
  testNonEmpty "union" "SELECT department FROM users WHERE age > 30 UNION SELECT department FROM users WHERE age < 25",
  -- UNION ALL keeps duplicates
  testNonEmpty "union_all" "SELECT department FROM users UNION ALL SELECT department FROM users"
]

-- ============================================================================
-- Set-Operation Subquery Tests (#218): UNION/INTERSECT/EXCEPT inside
-- IN / NOT IN / FROM subquery positions, parsed and evaluated end-to-end.
-- ============================================================================

def setOpSubqueryTests : List TestResult := [
  -- IN with UNION subquery: user_ids with amount>250 {3} ∪ amount<120 {1} = {1,3} → Alice, Carol
  testRowCount "in_union_subquery"
    "SELECT name FROM users WHERE id IN (SELECT user_id FROM orders WHERE amount > 250 UNION SELECT user_id FROM orders WHERE amount < 120)" 2,
  -- NOT IN with UNION subquery (Airports/Flights shape): user_ids with
  -- amount<250 {1,2} ∪ amount>250 {3} = {1,2,3} → Dave, Eve remain.
  testRowCount "not_in_union_subquery"
    "SELECT name FROM users WHERE id NOT IN (SELECT user_id FROM orders WHERE amount < 250 UNION SELECT user_id FROM orders WHERE amount > 250)" 2,
  -- FROM with INTERSECT subquery: departments of (age>25) ∩ (age<30) = {Marketing}
  testRowCount "from_intersect_subquery"
    "SELECT * FROM (SELECT department FROM users WHERE age > 25 INTERSECT SELECT department FROM users WHERE age < 30) AS d" 1,
  -- IN with EXCEPT subquery: orders.user_id [1,1,2,3] minus user_ids with amount>150 {1,3} = {2} → Bob
  testRowCount "in_except_subquery"
    "SELECT name FROM users WHERE id IN (SELECT user_id FROM orders EXCEPT SELECT user_id FROM orders WHERE amount > 150)" 1,
  -- UNION ALL inside IN keeps duplicates but IN semantics unchanged: {1,3} ∪ₐ {1} → Alice, Carol
  testRowCount "in_union_all_subquery"
    "SELECT name FROM users WHERE id IN (SELECT user_id FROM orders WHERE amount > 150 UNION ALL SELECT user_id FROM orders WHERE amount < 120)" 2,
  -- Scalar subquery with UNION: head of (MAX=300 then MIN=100) is 300
  testContainsValue "scalar_union_subquery"
    "SELECT (SELECT MAX(amount) FROM orders UNION SELECT MIN(amount) FROM orders) FROM users WHERE id = 1" (.int 300),
  -- EXISTS with EXCEPT subquery: all order products appear in products (shared
  -- alias p so the row keys match) → EXCEPT is empty → NOT EXISTS for every user
  testRowCount "not_exists_except_subquery"
    "SELECT name FROM users WHERE NOT EXISTS (SELECT orders.product AS p FROM orders EXCEPT SELECT products.name AS p FROM products)" 5
]

-- ============================================================================
-- Arithmetic Expression Tests
-- ============================================================================

def arithmeticTests : List TestResult := [
  testNonEmpty "add" "SELECT age + 10 FROM users",
  testNonEmpty "subtract" "SELECT age - 10 FROM users",
  testNonEmpty "multiply" "SELECT amount * 2 FROM orders"
]

-- ============================================================================
-- INSERT/UPDATE/DELETE Tests
-- ============================================================================

def mutationTests : List TestResult := [
  -- These just test that the operations parse and evaluate without error
  -- We can't easily check the result without more infrastructure
  testNonEmpty "after_theoretical_insert"
    "SELECT * FROM users"  -- Just verify database still works
]

-- ============================================================================
-- Subquery Unnesting Semantic Tests
-- ============================================================================

/-- Compare two query results for set equality (same rows, ignoring order) -/
def resultsSetEqual (r1 r2 : Table) : Bool :=
  let sorted1 := r1.mergeSort (fun a b =>
    match a.head?, b.head? with
    | some (_, v1), some (_, v2) => v1.toSql < v2.toSql
    | _, _ => true)
  let sorted2 := r2.mergeSort (fun a b =>
    match a.head?, b.head? with
    | some (_, v1), some (_, v2) => v1.toSql < v2.toSql
    | _, _ => true)
  sorted1 == sorted2

/-- Test that IN subquery and JOIN produce same rows (set equality) -/
def testUnnestEquiv (name : String) (inSql joinSql : String) : TestResult :=
  match parseSelectStr inSql, parseSelectStr joinSql with
  | .error e, _ => .fail name s!"Parse error in IN query: {e}"
  | _, .error e => .fail name s!"Parse error in JOIN query: {e}"
  | .ok sel1, .ok sel2 =>
    let result1 := evalSelect testDb sel1
    let result2 := evalSelect testDb sel2
    if resultsSetEqual result1 result2 then .pass name
    else .fail name s!"Set mismatch: IN returned {result1.length} rows, JOIN returned {result2.length} rows"

def subqueryUnnestingTests : List TestResult := [
  -- Users with orders: Alice (1), Bob (2), Carol (3) - only Alice and Bob have orders
  -- IN subquery form
  testRowCount "unnest_in_count"
    "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders)" 3,

  -- Semi-join form should return same count (with DISTINCT to eliminate duplicates)
  testRowCount "unnest_join_count"
    "SELECT DISTINCT users.* FROM users INNER JOIN orders ON users.id = orders.user_id" 3,

  -- Test equivalence: IN subquery vs semi-join
  testUnnestEquiv "unnest_in_vs_join"
    "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders)"
    "SELECT DISTINCT users.* FROM users INNER JOIN orders ON users.id = orders.user_id",

  -- NOT IN subquery: users without orders (Dave and Eve)
  testRowCount "unnest_not_in_count"
    "SELECT * FROM users WHERE id NOT IN (SELECT user_id FROM orders)" 2,

  -- Anti-join form should return same rows
  testRowCount "unnest_antijoin_count"
    "SELECT users.* FROM users LEFT JOIN orders ON users.id = orders.user_id WHERE orders.user_id IS NULL" 2,

  -- Test equivalence: NOT IN vs anti-join
  testUnnestEquiv "unnest_not_in_vs_antijoin"
    "SELECT * FROM users WHERE id NOT IN (SELECT user_id FROM orders)"
    "SELECT users.* FROM users LEFT JOIN orders ON users.id = orders.user_id WHERE orders.user_id IS NULL",

  -- Filtered subquery: users with high-value orders (>150)
  -- Alice has order 200, Carol has order 300
  testRowCount "unnest_filtered_in"
    "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders WHERE amount > 150)" 2,

  -- Empty subquery case: no users match
  testEmpty "unnest_empty_in"
    "SELECT * FROM users WHERE id IN (SELECT user_id FROM orders WHERE amount > 1000)",

  -- Empty NOT IN returns all users
  testRowCount "unnest_empty_not_in"
    "SELECT * FROM users WHERE id NOT IN (SELECT user_id FROM orders WHERE amount > 1000)" 5
]

-- ============================================================================
-- COALESCE / NULLIF Function Tests
-- ============================================================================

/-- Database with NULL values for COALESCE testing -/
def nullTestDb : Database := fun name =>
  match name with
  | "employees" => [
    [("id", .int 1), ("name", .string "Alice"), ("bonus", .int 500)],
    [("id", .int 2), ("name", .string "Bob"), ("bonus", .null none)],
    [("id", .int 3), ("name", .string "Carol"), ("bonus", .int 300)],
    [("id", .int 4), ("name", .string "Dave"), ("bonus", .null none)]
  ]
  | _ => []

/-- Parse and evaluate against the null test database -/
def evalNullQuery (sql : String) : Except String Table :=
  match parseSelectStr sql with
  | .error e => .error e
  | .ok sel => .ok (evalSelect nullTestDb sel)

/-- Test row count against null database -/
def testNullRowCount (name : String) (sql : String) (expected : Nat) : TestResult :=
  match evalNullQuery sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    if result.length == expected then .pass name
    else .fail name s!"Expected {expected} rows, got {result.length}"

/-- Test that a specific value appears in the first column of null db results -/
def testNullContainsValue (name : String) (sql : String) (expected : Value) : TestResult :=
  match evalNullQuery sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    let values := result.filterMap fun row => row.head?.map (·.2)
    if values.contains expected then .pass name
    else .fail name s!"Expected to find {expected.toSql} in results, got {values.map (·.toSql)}"

/-- Test first value in first row of null db results -/
def testNullFirstValue (name : String) (sql : String) (expected : Value) : TestResult :=
  match evalNullQuery sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    match result.head?.bind (·.head?) with
    | some (_, actual) =>
      if actual == expected then .pass name
      else .fail name s!"Expected {expected.toSql}, got {actual.toSql}"
    | none => .fail name "No result returned"

def coalesceTests : List TestResult := [
  -- COALESCE with non-null first arg returns first arg
  testContainsValue "coalesce_nonnull_first"
    "SELECT COALESCE(1, 2)" (.int 1),

  -- COALESCE with single non-null value
  testContainsValue "coalesce_single_nonnull"
    "SELECT COALESCE(42)" (.int 42),

  -- COALESCE with NULL first arg and non-null second returns second
  testContainsValue "coalesce_null_then_value"
    "SELECT COALESCE(NULL, 99)" (.int 99),

  -- COALESCE with multiple NULLs then a value
  testContainsValue "coalesce_multi_null_then_value"
    "SELECT COALESCE(NULL, NULL, 7)" (.int 7),

  -- COALESCE with string values
  testContainsValue "coalesce_string"
    "SELECT COALESCE(NULL, 'fallback')" (.string "fallback"),

  -- COALESCE with non-null string skips rest
  testContainsValue "coalesce_string_nonnull"
    "SELECT COALESCE('first', 'second')" (.string "first"),

  -- COALESCE replacing NULLs in column data
  testNullRowCount "coalesce_column_count"
    "SELECT COALESCE(bonus, 0) FROM employees" 4,

  -- COALESCE with column: non-null bonus stays, null bonus becomes 0
  testNullContainsValue "coalesce_column_nonnull"
    "SELECT COALESCE(bonus, 0) FROM employees" (.int 500),

  testNullContainsValue "coalesce_column_null_replaced"
    "SELECT COALESCE(bonus, 0) FROM employees" (.int 0),

  -- NULLIF: equal values produce NULL
  testContainsValue "nullif_equal"
    "SELECT COALESCE(NULLIF(1, 1), 99)" (.int 99),

  -- NULLIF: different values return first
  testContainsValue "nullif_different"
    "SELECT NULLIF(5, 3)" (.int 5)
]

-- ============================================================================
-- Cross-Type vs NULL Semantics (drift guards for mismatched_types_error, #201)
-- ============================================================================

/-- Direct value-level check helper -/
private def checkEval (name : String) (actual expected : Option Value) : TestResult :=
  if actual == expected then .pass name
  else .fail name s!"expected {repr expected}, got {repr actual}"

/-- DECIMAL end-to-end (#201): SQL text → parser → scaled-int evaluation.
    Covers exact arithmetic, scale alignment, canonicalization (trailing
    zeros stripped), int↔decimal promotion, and NULL propagation. -/
def decimalTests : List TestResult := [
  -- Literal parses to canonical form: 2.50 → decimal 25 1
  testContainsValue "decimal_literal_canonical"
    "SELECT 2.50" (.decimal 25 1),
  -- Exact arithmetic with scale alignment: 1.5 + 2.25 = 3.75
  testContainsValue "decimal_add_scale_align"
    "SELECT 1.5 + 2.25" (.decimal 375 2),
  -- Result renormalizes: 0.5 + 0.5 = 1 (scale 0, still decimal-typed)
  testContainsValue "decimal_add_canonicalizes"
    "SELECT 0.5 + 0.5" (.decimal 1 0),
  -- The classic float failure is exact here: 0.1 + 0.2 = 0.3
  testContainsValue "decimal_no_float_drift"
    "SELECT 0.1 + 0.2" (.decimal 3 1),
  -- Multiplication: scales add then renormalize: 1.5 * 2.0 = 3
  testContainsValue "decimal_mul"
    "SELECT 1.5 * 2.0" (.decimal 3 0),
  -- int↔decimal promotion: 1 + 2.5 = 3.5
  testContainsValue "decimal_int_promotion_add"
    "SELECT 1 + 2.5" (.decimal 35 1),
  -- Promotion in comparison: 2 = 2.0 is TRUE (and WHERE keeps the row)
  testRowCount "decimal_int_promotion_eq"
    "SELECT id FROM users WHERE 2 = 2.0" 5,
  -- Cross-scale comparison: 1.5 < 2 is TRUE
  testRowCount "decimal_lt_int"
    "SELECT id FROM users WHERE 1.5 < 2" 5,
  -- NULL propagation per the invariant: NULL + 1.5 is NULL, not error
  checkEval "decimal_null_propagation"
    (evalBinOp .add (some (.null none)) (some (.decimal 15 1))) (some (.null none)),
  -- Cross-type with non-numeric stays an error
  checkEval "decimal_string_mismatch_error"
    (evalBinOp .add (some (.decimal 15 1)) (some (.string "a"))) none,
  -- Unary negation: -1.5
  testContainsValue "decimal_negation"
    "SELECT -1.5" (.decimal (-15) 1),

  -- ---- Aggregates over a decimal column (items: 2.5, 1.25, 3, NULL) ----
  -- SUM skips the NULL and scale-aligns: 2.5 + 1.25 + 3 = 6.75
  testContainsValue "decimal_agg_sum"
    "SELECT SUM(price) FROM items" (.decimal 675 2),
  -- MIN/MAX return the original stored values
  testContainsValue "decimal_agg_min"
    "SELECT MIN(price) FROM items" (.decimal 125 2),
  testContainsValue "decimal_agg_max"
    "SELECT MAX(price) FROM items" (.decimal 3 0),
  -- AVG: 6.75 / 3 = 2.25
  testContainsValue "decimal_agg_avg"
    "SELECT AVG(price) FROM items" (.decimal 225 2),
  -- int aggregates keep int results (no behavior change)
  testContainsValue "decimal_agg_int_unchanged"
    "SELECT SUM(age) FROM users" (.int 140),
  -- ORDER BY over the decimal column (scale-aware comparison)
  testContainsValue "decimal_order_by"
    "SELECT name, price FROM items WHERE price IS NOT NULL ORDER BY price LIMIT 1"
    (.string "Nut"),
  -- ORDER BY on a NON-projected column (#206 fix): sort keys resolve against
  -- the source row, so projecting the key is no longer required
  testContainsValue "order_by_non_projected"
    "SELECT name FROM items WHERE price IS NOT NULL ORDER BY price LIMIT 1"
    (.string "Nut"),
  testContainsValue "order_by_non_projected_desc"
    "SELECT name FROM users ORDER BY age DESC LIMIT 1"
    (.string "Carol"),
  -- Projected (aliased) sort keys still win on name clashes and DISTINCT
  -- still sorts by output columns only
  testContainsValue "order_by_distinct_output_col"
    "SELECT DISTINCT department FROM users ORDER BY department LIMIT 1"
    (.string "Engineering"),

  -- COUNT(col) skips NULLs per the SQL standard (3 non-null prices of 4 rows;
  -- regression for the bug the DuckDB oracle found)
  testContainsValue "decimal_count_skips_nulls"
    "SELECT COUNT(price) FROM items" (.int 3),

  -- ---- Lexer edges ----
  -- Leading-dot literal: .5 = 0.5
  testContainsValue "decimal_leading_dot"
    "SELECT .5" (.decimal 5 1),
  -- Trailing-dot literal: 1. = 1
  testContainsValue "decimal_trailing_dot"
    "SELECT 1." (.decimal 1 0),
  -- Exponent literals are rejected loudly, not misparsed as `1 AS e5`
  (match parse "SELECT 1e5" with
   | .error _ => .pass "decimal_exponent_rejected"
   | .ok _ => .fail "decimal_exponent_rejected" "1e5 should be a parse error"),
  (match parse "SELECT 1.5e2" with
   | .error _ => .pass "decimal_frac_exponent_rejected"
   | .ok _ => .fail "decimal_frac_exponent_rejected" "1.5e2 should be a parse error"),
  -- Qualified columns still tokenize (dot not consumed by number lexing)
  testRowCount "decimal_qualified_col_unaffected"
    "SELECT u.id FROM users u WHERE u.age > 25" 3,

  -- ---- Pretty printer ----
  (if Value.toSql (.decimal (-5) 2) == "-0.05"
   then .pass "decimal_print_negative_pad"
   else .fail "decimal_print_negative_pad" s!"got {Value.toSql (.decimal (-5) 2)}"),
  (if Value.toSql (.decimal 5 2) == "0.05"
   then .pass "decimal_print_zero_pad"
   else .fail "decimal_print_zero_pad" s!"got {Value.toSql (.decimal 5 2)}"),
  (if Value.toSql (.decimal 1050 2) == "10.50"
   then .pass "decimal_print_noncanonical_faithful"
   else .fail "decimal_print_noncanonical_faithful" s!"got {Value.toSql (.decimal 1050 2)}")
]

/-- Type mismatches are errors (`none`); NULL operands are SQL NULL — never
    confuse the two. Mirrors the proven `mismatched_types_error` lemma and the
    NULL Semantics Invariant in docs/SQL_TYPES_CONCRETE_PLAN.md. -/
def crossTypeTests : List TestResult := [
  checkEval "mismatched_types_error (int + string is error)"
    (evalBinOp .add (some (.int 1)) (some (.string "a"))) none,
  checkEval "mismatched_types_error (int < bool is error)"
    (evalBinOp .lt (some (.int 1)) (some (.bool true))) none,
  checkEval "mismatched_types_error (string = bool is error)"
    (evalBinOp .eq (some (.string "t")) (some (.bool true))) none,
  -- Contrast: NULL operands propagate as SQL NULL, not error
  checkEval "mismatched_types_error (NULL + int is NULL, not error)"
    (evalBinOp .add (some (.null none)) (some (.int 1))) (some (.null none)),
  checkEval "mismatched_types_error (NULL = string is NULL, not error)"
    (evalBinOp .eq (some (.null none)) (some (.string "a"))) (some (.null none))
]

-- ============================================================================
-- Window Function Tests (#214)
-- ============================================================================
-- Output rows stay in source-row order (users: Alice 30 Eng, Bob 25 Sales,
-- Carol 35 Eng, Dave 28 Mktg, Eve 22 Sales); expectations verified against
-- DuckDB v1.5.3.

def windowTests : List TestResult := [
  -- ROW_NUMBER over ORDER BY: ages 30,25,35,28,22 → positions 4,2,5,3,1
  testColumn "window_row_number_order_by"
    "SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users"
    "rn" [.int 4, .int 2, .int 5, .int 3, .int 1],
  -- RANK with ties (departments: Eng,Eng tie at 1; Marketing 3; Sales,Sales 4)
  testColumn "window_rank_ties"
    "SELECT name, RANK() OVER (ORDER BY department) AS r FROM users"
    "r" [.int 1, .int 4, .int 1, .int 3, .int 4],
  -- DENSE_RANK with ties (no gaps: Eng 1, Marketing 2, Sales 3)
  testColumn "window_dense_rank_ties"
    "SELECT name, DENSE_RANK() OVER (ORDER BY department) AS dr FROM users"
    "dr" [.int 1, .int 3, .int 1, .int 2, .int 3],
  -- SUM over PARTITION BY: Eng 30+35=65, Sales 25+22=47, Marketing 28
  testColumn "window_sum_partition_by"
    "SELECT name, SUM(age) OVER (PARTITION BY department) AS s FROM users"
    "s" [.int 65, .int 47, .int 65, .int 28, .int 47],
  -- AVG over PARTITION BY (truncating int division: 65/2=32, 47/2=23)
  testColumn "window_avg_partition_by"
    "SELECT name, AVG(age) OVER (PARTITION BY department) AS a FROM users"
    "a" [.int 32, .int 23, .int 32, .int 28, .int 23],
  -- MIN/MAX over PARTITION BY
  testColumn "window_min_partition_by"
    "SELECT name, MIN(age) OVER (PARTITION BY department) AS lo FROM users"
    "lo" [.int 30, .int 22, .int 30, .int 28, .int 22],
  testColumn "window_max_partition_by"
    "SELECT name, MAX(age) OVER (PARTITION BY department) AS hi FROM users"
    "hi" [.int 35, .int 25, .int 35, .int 28, .int 25],
  -- Window aggregates over a DECIMAL column (items: 2.5, 1.25, 3, NULL;
  -- NULL price row still gets the partition-wide value, NULL is skipped)
  testColumn "window_sum_decimal"
    "SELECT name, SUM(price) OVER () AS s FROM items"
    "s" [.decimal 675 2, .decimal 675 2, .decimal 675 2, .decimal 675 2],
  testColumn "window_avg_decimal"
    "SELECT name, AVG(price) OVER () AS a FROM items"
    "a" [.decimal 225 2, .decimal 225 2, .decimal 225 2, .decimal 225 2],
  -- COUNT(*) OVER () counts the whole partition on every row
  testColumn "window_count_star"
    "SELECT name, COUNT(*) OVER () AS c FROM users"
    "c" [.int 5, .int 5, .int 5, .int 5, .int 5],
  -- PARTITION BY + ORDER BY combined: row numbers restart per department
  testColumn "window_partition_and_order"
    "SELECT name, ROW_NUMBER() OVER (PARTITION BY department ORDER BY age) AS rn FROM users"
    "rn" [.int 1, .int 2, .int 2, .int 1, .int 1],
  -- Aggregate window with ORDER BY uses the default frame (running sum,
  -- RANGE: peers included): sorted ages 22,25,28,30,35 → 22,47,75,105,140
  testColumn "window_running_sum"
    "SELECT name, SUM(age) OVER (ORDER BY age) AS s FROM users"
    "s" [.int 105, .int 47, .int 140, .int 75, .int 22],
  -- Running sum with ties: department peers share the frame total
  -- (Eng 65,65; Marketing 93; Sales 140,140)
  testColumn "window_running_sum_peers"
    "SELECT name, SUM(age) OVER (ORDER BY department) AS s FROM users"
    "s" [.int 65, .int 140, .int 65, .int 93, .int 140],
  -- Window fn + outer ORDER BY on a NON-projected column (#208 aligned-sort
  -- path): rows come out age-sorted with their window values intact
  testColumn "window_outer_order_by_nonprojected_rn"
    "SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users ORDER BY age"
    "rn" [.int 1, .int 2, .int 3, .int 4, .int 5],
  testColumn "window_outer_order_by_nonprojected_names"
    "SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users ORDER BY age"
    "name" [.string "Eve", .string "Bob", .string "Dave", .string "Alice", .string "Carol"]
]

-- ============================================================================
-- Case-Insensitive Identifier Resolution (#231)
-- ============================================================================

/-- SQL identifiers are case-insensitive: Spider queries write `country`
    against a schema column `Country`. These mirror the probe on #231. -/
def caseInsensitiveTests : List TestResult := [
  -- The #231 probe: lowercase WHERE/SELECT identifiers, original-case schema
  testColumn "ci_where_lowercase"
    "SELECT DISTINCT country FROM singer WHERE age > 20"
    "country" [.string "France"],
  testColumn "ci_qualified_alias"
    "SELECT T1.name AS n FROM singer AS T1 WHERE T1.age < 20"
    "n" [.string "Rose White"],
  testContainsValue "ci_upper_ref_lower_schema"
    "SELECT NAME FROM users WHERE AGE = 30" (.string "Alice"),
  testColumn "ci_order_by"
    "SELECT name FROM singer ORDER BY age"
    "name" [.string "Rose White", .string "Tribal King", .string "Joe"],
  testRowCount "ci_group_by"
    "SELECT country, COUNT(*) FROM singer GROUP BY country" 2,
  -- First match wins on a case-only collision (same shadowing List.lookup
  -- gave exact duplicates)
  (if Row.get [("a", .int 1), ("A", .int 2)] "A" == some (.int 1)
   then .pass "ci_collision_first_key_wins"
   else .fail "ci_collision_first_key_wins" "expected leftmost case-insensitive match"),
  (if Row.getQualified [("T.Country", .string "x")] none "COUNTRY" == some (.string "x")
   then .pass "ci_qualified_suffix_fallback"
   else .fail "ci_qualified_suffix_fallback" "expected case-insensitive .col suffix fallback"),
  (if Row.getQualified [("T.Country", .string "x")] (some "t") "country" == some (.string "x")
   then .pass "ci_qualified_table"
   else .fail "ci_qualified_table" "expected case-insensitive qualified lookup")
]

-- ============================================================================
-- Test Runner
-- ============================================================================

def allSemanticsTests : List TestResult :=
  basicQueryTests ++ whereQueryTests ++ joinQueryTests ++
  projectionTests ++ distinctTests ++ orderByTests ++ groupedOrderByTests ++ nullOrderingTests ++
  registryPinTests ++
  limitOffsetTests ++ subqueryTests ++ aggregateTests ++
  distinctAggTests ++ groupByTests ++ setOpQueryTests ++
  setOpSubqueryTests ++
  arithmeticTests ++ edgeCaseTests ++ mutationTests ++
  subqueryUnnestingTests ++ coalesceTests ++ crossTypeTests ++ decimalTests ++
  windowTests ++ caseInsensitiveTests

def runSemanticsTests : IO (Nat × Nat) :=
  runTests "Semantics Tests" allSemanticsTests

end SemanticsTest
