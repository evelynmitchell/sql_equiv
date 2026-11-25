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

/-- Non-ASCII table and column names (#370) -/
def eteTable : Table := [
  [("Élan", .int 1), ("日本", .string "a")],
  [("Élan", .int 2), ("日本", .string "b")]
]

def testDb : Database := fun name =>
  match name with
  | "Été" => eteTable
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
def evalQueryDialect (dialect : Dialect) (sql : String) : Except String Table :=
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
  match evalQueryDialect dialect sql with
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
    "department" [.string "Sales", .string "Engineering"],
  -- Aggregates under BETWEEN, CASE, IN (list) and function calls are evaluated over the group
  -- (Spider `HAVING count(*) BETWEEN 1 AND 2`; these were NULL, and CASE fell to ELSE).
  -- Group sizes: Engineering 2, Marketing 1, Sales 2. sqlite and DuckDB agree.
  testColumn "group_having_agg_between"
    "SELECT department FROM users GROUP BY department HAVING COUNT(*) BETWEEN 1 AND 1"
    "department" [.string "Marketing"],
  testColumn "group_case_on_agg"
    "SELECT department, CASE WHEN COUNT(*) > 1 THEN 'many' ELSE 'one' END AS k FROM users GROUP BY department ORDER BY department"
    "k" [.string "many", .string "one", .string "many"],
  testColumn "group_in_list_on_agg"
    "SELECT department, COUNT(*) IN (1, 3) AS k FROM users GROUP BY department ORDER BY department"
    "k" [.bool false, .bool true, .bool false],
  testColumn "group_func_on_agg"
    "SELECT department, ABS(COUNT(*) - 3) AS k FROM users GROUP BY department ORDER BY department"
    "k" [.int 1, .int 2, .int 1],
  -- Without an aggregate inside, BETWEEN in HAVING goes to the row evaluator as before
  testColumn "group_having_between_no_agg"
    "SELECT department FROM users GROUP BY department HAVING department BETWEEN 'A' AND 'N' ORDER BY department"
    "department" [.string "Engineering", .string "Marketing"]
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
  match evalQueryDialect dialect sql with
  | .error e => .fail name s!"Parse/eval error: {e}"
  | .ok result =>
    if result.length == expected then .pass name
    else .fail name s!"Expected {expected} rows, got {result.length}"

-- Pins for implementation-defined behaviour (docs/IMPLEMENTATION_DEFINED.md,
-- #262), so none of these can change silently.

/-- The aggregate `fn` of a column over the users table evaluates to an error (`none`), not to
    a NULL value (registry rows 17 and 18). -/
def aggIsError (name : String) (fn : AggFunc) (col : String) : TestResult :=
  match evalAggOverTableParam (fun d r e => evalExprWithDb d r e) testDb fn
      (some (.col ⟨none, col⟩)) false usersTable with
  | none => .pass name
  | some v => .fail name s!"expected an error, got {repr v}"

/-- The same for `fn (age > 26)`, a boolean argument. -/
def aggBoolIsError (name : String) (fn : AggFunc) : TestResult :=
  match evalAggOverTableParam (fun d r e => evalExprWithDb d r e) testDb fn
      (some (.binOp .gt (.col ⟨none, "age"⟩) (.lit (.int 26)))) false usersTable with
  | none => .pass name
  | some v => .fail name s!"expected an error, got {repr v}"

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
  -- Bare columns next to one MIN/MAX of a column (registry T9): sqlite reads the row where the
  -- argument is extreme; other dialects, or several MIN/MAX calls, read the first row.
  -- Ages: Alice 30, Bob 25, Carol 35, Dave 28, Eve 22.
  testContainsValueIn "bare_column_max_sqlite" .sqlite
    "SELECT name, MAX(age) FROM users" (.string "Carol"),
  testContainsValueIn "bare_column_min_sqlite" .sqlite
    "SELECT name, MIN(age) FROM users" (.string "Eve"),
  testContainsValueIn "bare_column_max_standard_first_row" .standard
    "SELECT name, MAX(age) FROM users" (.string "Alice"),
  testContainsValueIn "bare_column_two_minmax_sqlite_first_row" .sqlite
    "SELECT name, MAX(age), MIN(age) FROM users" (.string "Alice"),
  -- …and for MIN/MAX of any expression, not only a column
  testContainsValueIn "bare_column_max_expr_sqlite" .sqlite
    "SELECT name, MAX(age + 0) FROM users" (.string "Carol"),
  testContainsValueIn "bare_column_min_negated_sqlite" .sqlite
    "SELECT name, MIN(0 - age) FROM users" (.string "Carol"),
  testContainsValueIn "bare_column_max_grouped_sqlite" .sqlite
    "SELECT name, MAX(age) FROM users GROUP BY department ORDER BY department" (.string "Carol"),
  -- the same MIN/MAX written twice is one call, as in sqlite: the row where it is extreme
  testContainsValueIn "bare_column_repeated_max_sqlite" .sqlite
    "SELECT name, MAX(age), MAX(age) FROM users" (.string "Carol"),
  testContainsValueIn "bare_column_max_item_and_having_sqlite" .sqlite
    "SELECT name, MAX(age) FROM users HAVING MAX(age) > 0" (.string "Carol"),
  -- AVG/SUM over a string is a type error, as in DuckDB and Postgres; sqlite converts it to a
  -- number (registry row 17). The aggregate's value is the error (`none`); in a SELECT item it
  -- shows as NULL, and since #423 `IS NULL` reads it as NULL on every path, as the row
  -- evaluator always has, so HAVING keeps the group.
  aggIsError "avg_text_column_error" (.avg .error) "name",
  aggIsError "sum_text_column_error" (.sum .error) "name",
  testRowCount "avg_text_column_error_is_null_in_having"
    "SELECT COUNT(*) FROM users HAVING AVG(name) IS NULL" 1,
  testRowCount "sum_text_column_error_not_a_value_in_having"
    "SELECT COUNT(*) FROM users HAVING SUM(name) IS NOT NULL" 0,
  -- a mix of numbers and strings is an error too (strings used to be skipped)
  testRowCount "avg_mixed_text_error_in_having"
    "SELECT COUNT(*) FROM users HAVING AVG(CASE WHEN age > 26 THEN name ELSE age END) IS NOT NULL" 0,
  -- numbers only: unchanged
  testRowCount "avg_numbers_in_having" "SELECT COUNT(*) FROM users HAVING AVG(age) > 20" 1,
  -- SUM/AVG over booleans per dialect (registry row 18): sqlite reads them as 1/0; DuckDB too for
  -- SUM but rejects AVG; standard and Postgres reject both. Ages over 26: Alice, Carol, Dave.
  testRowCountIn "sum_bool_sqlite" .sqlite
    "SELECT COUNT(*) FROM users HAVING SUM(age > 26) = 3" 1,
  testContainsValueIn "avg_bool_sqlite" .sqlite
    "SELECT AVG(age > 26) FROM users" (.decimal 6 1),
  testRowCountIn "sum_bool_duckdb" .duckdb
    "SELECT COUNT(*) FROM users HAVING SUM(age > 26) = 3" 1,
  -- the error modes give no value (the error reads as NULL to `IS NULL`, #423)
  testRowCountIn "avg_bool_duckdb_error" .duckdb
    "SELECT COUNT(*) FROM users HAVING AVG(age > 26) IS NOT NULL" 0,
  testRowCount "sum_bool_standard_error"
    "SELECT COUNT(*) FROM users HAVING SUM(age > 26) IS NOT NULL" 0,
  testRowCountIn "avg_bool_postgres_error" .postgres
    "SELECT COUNT(*) FROM users HAVING AVG(age > 26) IS NOT NULL" 0,
  aggBoolIsError "sum_bool_error_mode" (.sum .error),
  aggBoolIsError "avg_bool_error_mode" (.avg .error),
  -- ROUND keeps the input type and rounds half away from zero (registry row 16, #355)
  testContainsValue "round_int_unchanged" "SELECT ROUND(age) FROM users WHERE id = 1" (.int 30),
  testContainsValue "round_int_negative_places" "SELECT ROUND(25, -1) FROM users WHERE id = 1" (.int 30),
  testContainsValue "round_int_negative_places_neg" "SELECT ROUND(-25, -1) FROM users WHERE id = 1" (.int (-30)),
  testContainsValue "round_decimal_half_away" "SELECT ROUND(2.5) FROM users WHERE id = 1" (.decimal 3 0),
  testContainsValue "round_decimal_half_away_neg" "SELECT ROUND(-2.5) FROM users WHERE id = 1" (.decimal (-3) 0),
  testContainsValue "round_decimal_places" "SELECT ROUND(7.45, 1) FROM users WHERE id = 1" (.decimal 75 1),
  testContainsValue "round_decimal_more_places_unchanged" "SELECT ROUND(1.25, 5) FROM users WHERE id = 1" (.decimal 125 2),
  testContainsValue "round_decimal_negative_places" "SELECT ROUND(123.456, -1) FROM users WHERE id = 1" (.decimal 120 0),
  testContainsValue "round_null" "SELECT ROUND(NULL) FROM users WHERE id = 1" (.null none),
  testContainsValue "round_null_places" "SELECT ROUND(2.5, NULL) FROM users WHERE id = 1" (.null none),
  testContainsValue "abs_decimal" "SELECT ABS(-2.50) FROM users WHERE id = 1" (.decimal 25 1),
  -- LOWER/UPPER fold ASCII letters only, in every dialect, as sqlite (registry row 19;
  -- DuckDB and Postgres also fold non-ASCII letters)
  testContainsValue "lower_non_ascii_ascii_only" "SELECT LOWER('ÉCOLE') FROM users WHERE id = 1"
    (.string "École"),
  testContainsValue "upper_non_ascii_ascii_only" "SELECT UPPER('école') FROM users WHERE id = 1"
    (.string "éCOLE"),
  testContainsValue "lower_ascii" "SELECT LOWER('AbC') FROM users WHERE id = 1" (.string "abc"),
  -- Non-ASCII identifiers (#370): any character from U+0080 is an identifier character, as
  -- in sqlite and Postgres; names fold ASCII letters only, so élan is not Élan
  testContainsValue "non_ascii_column" "SELECT Élan FROM Été WHERE Élan = 2" (.int 2),
  testContainsValue "non_ascii_cjk_column_and_alias"
    "SELECT 日本 AS a€b FROM Été AS é WHERE é.Élan = 1" (.string "a"),
  testContainsValue "non_ascii_name_folds_ascii_only"
    "SELECT élan FROM Été WHERE 日本 = 'a'" (.null none),
  testRowCount "non_ascii_ascii_letters_still_fold"
    "SELECT name FROM users WHERE AGE > 26" 3,
  -- Table names reach the Database exactly as written (registry row 20, #372): testDb
  -- matches exactly, so USERS is an unknown (empty) table here; the engines fold ASCII
  -- letters and would find users. Column names do fold (above).
  testRowCount "table_name_matched_exactly" "SELECT name FROM USERS" 0,
  testRowCount "table_name_exact_spelling_found" "SELECT name FROM users" 5,
  -- NOT BETWEEN (#354): ages 30, 25, 35, 28, 22, so Carol (35) and Eve (22)
  testRowCount "not_between" "SELECT name FROM users WHERE age NOT BETWEEN 25 AND 30" 2,
  -- three-valued: NOT (age >= NULL AND age <= 30) is TRUE only where age > 30 (sqlite, DuckDB)
  testRowCount "not_between_null_bound" "SELECT name FROM users WHERE age NOT BETWEEN NULL AND 30" 1,
  -- the AND after the upper bound belongs to the WHERE, not to NOT BETWEEN
  testRowCount "not_between_then_and"
    "SELECT name FROM users WHERE age NOT BETWEEN 25 AND 30 AND name <> 'Eve'" 1,
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
  -- In the sqlite and duckdb dialects each distinct row sorts by the key of its first source
  -- row, as the engines do (#320): Sales, Marketing, Engineering.
  (match evalQueryDialect .sqlite "SELECT DISTINCT department FROM users ORDER BY age" with
   | .ok t =>
     let col := t.map fun row => ((row.find? (·.1 == "department")).map (·.2)).getD (.null none)
     if col == [.string "Sales", .string "Marketing", .string "Engineering"]
     then .pass "distinct_order_by_unselected_first_row"
     else .fail "distinct_order_by_unselected_first_row" s!"{col.map (·.toSql)}"
   | .error e => .fail "distinct_order_by_unselected_first_row" e),
  -- The issue's example: `a = 1` sorts by its first row's `b = 5`, not MIN 1 (sqlite: 2 3 1)
  (match evalQueryDialect .sqlite ("SELECT DISTINCT a FROM (SELECT 1 AS a, 5 AS b UNION ALL " ++
      "SELECT 2, 3 UNION ALL SELECT 1, 1 UNION ALL SELECT 3, 4) AS t ORDER BY b") with
   | .ok t =>
     let col := t.map fun row => ((row.find? (·.1 == "a")).map (·.2)).getD (.null none)
     if col == [.int 2, .int 3, .int 1] then .pass "distinct_order_by_first_row_not_min"
     else .fail "distinct_order_by_first_row_not_min" s!"{col.map (·.toSql)}"
   | .error e => .fail "distinct_order_by_first_row_not_min" e),
  -- DISTINCT over GROUP BY sorts by the first group's key (duckdb: Sales, Marketing, Engineering)
  (match evalQueryDialect .duckdb
      "SELECT DISTINCT department FROM users GROUP BY department, age ORDER BY age" with
   | .ok t =>
     let col := t.map fun row => ((row.find? (·.1 == "department")).map (·.2)).getD (.null none)
     if col == [.string "Sales", .string "Marketing", .string "Engineering"]
     then .pass "distinct_group_by_order_by_first_group"
     else .fail "distinct_group_by_order_by_first_group" s!"{col.map (·.toSql)}"
   | .error e => .fail "distinct_group_by_order_by_first_group" e),
  -- #323: LIKE wildcards anywhere in the pattern (sqlite, DuckDB agree)
  testExactRows "like_underscore" "SELECT 'ab' LIKE '_b'" 1 (some (.bool true)),
  testExactRows "like_interior_percent" "SELECT 'abc' LIKE 'a%c'" 1 (some (.bool true)),
  testExactRows "like_double_percent" "SELECT 'ab' LIKE 'a%%b'" 1 (some (.bool true)),
  testExactRows "like_percent_underscore_percent" "SELECT 'a' LIKE '%_%'" 1 (some (.bool true)),
  testExactRows "like_underscore_needs_a_character" "SELECT '' LIKE '_'" 1 (some (.bool false)),
  testExactRows "like_literal_mismatch" "SELECT 'abd' LIKE 'a%c'" 1 (some (.bool false)),
  testColumn "like_underscore_in_where" "SELECT name FROM users WHERE name LIKE '_ob'" "name"
    [.string "Bob"],
  -- #315: DISTINCT, aggregate DISTINCT and GROUP BY compare values as set operations do
  -- (`Value.setKey`): NULLs equal whatever their type tag, numbers by value
  testColumn "distinct_typed_nulls_one_row" "SELECT DISTINCT staff FROM museum" "staff"
    [.int 9, .int 17, .null none, .int 25, .int 41],
  testExactRows "count_distinct_numbers_by_value"
    "SELECT COUNT(DISTINCT v) FROM (SELECT 1 AS v UNION ALL SELECT 1.0) AS t" 1 (some (.int 1)),
  testExactRows "distinct_numbers_by_value"
    "SELECT DISTINCT v FROM (SELECT 1 AS v UNION ALL SELECT 1.0) AS t" 1 (some (.int 1)),
  testExactRows "group_by_numbers_by_value"
    "SELECT v, COUNT(*) FROM (SELECT 1 AS v UNION ALL SELECT 1.0) AS t GROUP BY v" 1 (some (.int 1)),
  -- #330: [NOT] IN (subquery) is three-valued (museum: staff 9, 17, NULL, 25, 41, NULL)
  testEmpty "not_in_subquery_null_in_subquery"
    "SELECT name FROM museum WHERE staff NOT IN (SELECT staff FROM museum WHERE name = 'm3')",
  testColumn "not_in_subquery_null_probe_dropped"
    "SELECT name FROM museum WHERE staff NOT IN (SELECT staff FROM museum WHERE name = 'm1')"
    "name" [.string "m2", .string "m4", .string "m5"],
  testRowCount "not_in_empty_subquery_keeps_null_probe"
    "SELECT name FROM museum WHERE staff NOT IN (SELECT staff FROM museum WHERE name = 'zz')" 6,
  testExactRows "in_subquery_null_is_unknown" "SELECT 5 IN (SELECT NULL)" 1 (some (.null none)),
  testExactRows "in_subquery_match_beats_null" "SELECT 5 IN (SELECT 5 UNION SELECT NULL)" 1
    (some (.bool true)),
  -- #324: set operations match rows by position and value (sqlite, DuckDB, Postgres agree)
  testColumn "set_op_intersect_by_position"
    "SELECT user_id FROM orders INTERSECT SELECT id FROM users" "user_id"
    [.int 1, .int 2, .int 3],
  testColumn "set_op_except_by_position"
    "SELECT id FROM users EXCEPT SELECT user_id FROM orders" "id" [.int 4, .int 5],
  -- a typed and an untyped NULL are one row (museum holds one of each)
  testColumn "set_op_typed_nulls_one_row"
    "SELECT staff FROM museum INTERSECT SELECT staff FROM museum WHERE staff IS NULL OR staff > 20"
    "staff" [.null none, .int 25, .int 41],
  -- numbers compare by value, as `=` does: 1 and 1.0 are one row (sqlite, DuckDB: one row)
  testExactRows "set_op_union_numbers_by_value" "SELECT 1 UNION SELECT 1.0" 1 (some (.int 1)),
  testExactRows "set_op_intersect_numbers_by_value" "SELECT 1 INTERSECT SELECT 1.0" 1 (some (.int 1)),
  testExactRows "set_op_except_numbers_by_value" "SELECT 1.50 EXCEPT SELECT 1.5" 0,
  -- the later branch's rows take the first branch's column names, so `n` sorts them too
  testColumn "set_op_rows_take_first_branch_names"
    "SELECT name AS n FROM users WHERE id < 3 UNION ALL SELECT name FROM products ORDER BY n DESC"
    "n" [.string "Widget", .string "Gizmo", .string "Gadget", .string "Bob", .string "Alice"],
  -- #340: the first branch names the columns from its SELECT list, even when it has no rows
  testColumn "set_op_empty_first_branch_names"
    "SELECT name AS n FROM users WHERE id > 100 UNION ALL SELECT name FROM products ORDER BY n DESC"
    "n" [.string "Widget", .string "Gizmo", .string "Gadget"],
  -- the same through a derived table (a subquery body): the outer query reads `n`
  testColumn "set_op_empty_first_branch_derived"
    "SELECT n FROM (SELECT name AS n FROM users WHERE id > 100 UNION ALL SELECT name FROM products) AS t"
    "n" [.string "Widget", .string "Gadget", .string "Gizmo"],
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
  -- AVG is exact (registry row 7): (-30 - 25) / 2 = -27.5
  testContainsValue "avg_negative_exact" "SELECT AVG(0 - age) FROM users WHERE id < 3" (.decimal (-275) 1),
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
  -- AVG - average order amount: 750 / 4 = 187.5, exact (registry row 7)
  testContainsValue "avg" "SELECT AVG(amount) FROM orders" (.decimal 1875 1),
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
  testContainsValue "avg_distinct_user" "SELECT AVG(DISTINCT user_id) FROM orders" (.decimal 2 0),
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
  (match evalQueryDialect .sqlite
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
  testNonEmpty "multiply" "SELECT amount * 2 FROM orders",
  -- `-NULL` is NULL, not an error: an error looks like NULL in a result (and `<error> IS NULL`
  -- is TRUE), so only the value or a strict dialect tells them apart. The one survivor of the
  -- first mutation-testing trial (#210).
  (if evalUnaryOp .neg (some (.null none)) == some (.null none) then .pass "neg_null_is_null"
   else .fail "neg_null_is_null" "-NULL must be NULL, not an error")
]

/-- One value-level check: `got` must be `want`. -/
def valueIs (name : String) (got want : Option Value) : TestResult :=
  if got == want then .pass name else .fail name s!"expected {repr want}, got {repr got}"

/-- Arms the first full mutation-testing run (#210) found no test sensitive to: decimal
    subtraction (no test computed a decimal difference), and NULL propagation, which a query
    cannot tell from an error (an error shows as NULL, `<error> IS NULL` is TRUE). -/
def valueArmTests : List TestResult :=
  let nul : Option Value := some (.null none)
  [ valueIs "decimal_minus_decimal" (evalBinOp .sub (some (Value.mkDecimal 25 1)) (some (Value.mkDecimal 125 2)))
      (some (Value.mkDecimal 125 2)),
    valueIs "int_minus_decimal" (evalBinOp .sub (some (.int 3)) (some (Value.mkDecimal 125 2)))
      (some (Value.mkDecimal 175 2)),
    valueIs "decimal_minus_int" (evalBinOp .sub (some (Value.mkDecimal 25 1)) (some (.int 1)))
      (some (Value.mkDecimal 15 1)),
    valueIs "null_mod_int_is_null" (evalBinOp .mod nul (some (.int 3))) nul,
    valueIs "int_mod_null_is_null" (evalBinOp .mod (some (.int 3)) nul) nul,
    valueIs "null_concat_is_null" (evalBinOp .concat nul (some (.string "a"))) nul,
    valueIs "concat_null_is_null" (evalBinOp .concat (some (.string "a")) nul) nul,
    valueIs "like_null_pattern_is_null" (evalBinOp .like (some (.string "a")) nul) nul,
    valueIs "null_likeCI_is_null" (evalBinOp .likeCI nul (some (.string "a"))) nul,
    valueIs "likeCI_null_pattern_is_null" (evalBinOp .likeCI (some (.string "a")) nul) nul,
    valueIs "round_null_is_null" (evalFunc "ROUND" [nul]) nul,
    valueIs "round_null_places_is_null" (evalFunc "ROUND" [nul, some (.int 1)]) nul,
    valueIs "round_by_null_places_is_null" (evalFunc "ROUND" [some (Value.mkDecimal 25 1), nul]) nul ]

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
-- Errors combine alike on every evaluation path (#423)
-- ============================================================================
-- `1 = 'a'` is a type error (registry row 10). The row evaluator passes the error to
-- `evalBinOp` / `evalUnaryOp`, which absorb it (`FALSE AND <error>` is FALSE, `<error> IS NULL`
-- is TRUE). The aggregate and window paths now do the same, so an item's value does not
-- depend on whether another item has an aggregate or a window function.

-- Window functions over groups (#429): the groups are formed and filtered by HAVING first, then
-- each window runs over one row per group, with aggregates evaluated per group. Groups in order:
-- Engineering (Alice 30, Carol 35: sum 65, count 2), Sales (Bob 25, Eve 22: 47, 2),
-- Marketing (Dave 28: 28, 1). Values agree with sqlite, DuckDB and Postgres.
def groupedWindowTests : List TestResult := [
  testColumn "grouped_window_rank_over_sum"
    "SELECT department, RANK() OVER (ORDER BY SUM(age) DESC) AS r FROM users GROUP BY department"
    "r" [.int 1, .int 2, .int 3],
  testColumn "grouped_window_sum_of_sums"
    "SELECT department, SUM(SUM(age)) OVER () AS s FROM users GROUP BY department"
    "s" [.int 140, .int 140, .int 140],
  testColumn "grouped_window_after_having"
    "SELECT department, ROW_NUMBER() OVER (ORDER BY department) AS rn FROM users GROUP BY department HAVING COUNT(*) = 2"
    "rn" [.int 1, .int 2],
  testColumn "grouped_window_partition_by_aggregate"
    "SELECT COUNT(*) AS c, SUM(COUNT(*)) OVER (PARTITION BY COUNT(*)) AS s FROM users GROUP BY department"
    "s" [.int 4, .int 4, .int 1],
  testColumn "aggregate_query_window"
    "SELECT COUNT(*) AS c, ROW_NUMBER() OVER () AS rn FROM users"
    "rn" [.int 1],
  testColumn "aggregate_query_window_no_rows"
    "SELECT COUNT(*) AS c, ROW_NUMBER() OVER () AS rn FROM users WHERE age > 100"
    "c" [.int 0],
  testColumn "grouped_window_order_by_alias"
    "SELECT department, RANK() OVER (ORDER BY SUM(age)) AS r FROM users GROUP BY department ORDER BY r"
    "department" [.string "Marketing", .string "Sales", .string "Engineering"],
  testColumn "grouped_window_under_operator"
    "SELECT department, SUM(COUNT(*)) OVER () + 1 AS r FROM users GROUP BY department"
    "r" [.int 6, .int 6, .int 6],
  testColumn "grouped_window_distinct_order_by_alias"
    "SELECT DISTINCT COUNT(*) AS c, RANK() OVER (ORDER BY COUNT(*)) AS r FROM users GROUP BY department ORDER BY r"
    "c" [.int 1, .int 2],
  testColumn "grouped_window_having_keeps_none"
    "SELECT department, ROW_NUMBER() OVER () AS rn FROM users GROUP BY department HAVING COUNT(*) > 5"
    "rn" [],
  -- #438: no GROUP BY, an aggregate only inside a window or in HAVING: one group, as the
  -- engines do (sum of all ages 140; COUNT(*) of the one group is 5)
  testColumn "window_over_aggregate_one_group"
    "SELECT SUM(SUM(age)) OVER () AS s FROM users"
    "s" [.int 140],
  testColumn "window_order_key_aggregate_one_group"
    "SELECT RANK() OVER (ORDER BY COUNT(*)) AS r FROM users"
    "r" [.int 1],
  testColumn "window_having_aggregate_one_group"
    "SELECT ROW_NUMBER() OVER () AS r FROM users HAVING COUNT(*) > 1"
    "r" [.int 1],
  testColumn "window_having_aggregate_no_group"
    "SELECT ROW_NUMBER() OVER () AS r FROM users HAVING SUM(age) > 1000"
    "r" [],
  testColumn "window_over_aggregate_no_rows"
    "SELECT SUM(SUM(age)) OVER () AS s FROM users WHERE age > 100"
    "s" [.null none],
  -- #435: a window function as an ORDER BY key sorts the rows, as in the engines
  -- (ages: Alice 30, Bob 25, Carol 35, Dave 28, Eve 22)
  testColumn "order_by_window_key"
    "SELECT name FROM users ORDER BY ROW_NUMBER() OVER (ORDER BY age DESC)"
    "name" [.string "Carol", .string "Alice", .string "Dave", .string "Bob", .string "Eve"],
  testColumn "order_by_window_position"
    "SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users ORDER BY 2 DESC"
    "rn" [.int 5, .int 4, .int 3, .int 2, .int 1],
  testColumn "order_by_window_partition_then_column"
    "SELECT name FROM users ORDER BY SUM(age) OVER (PARTITION BY department), name"
    "name" [.string "Dave", .string "Bob", .string "Eve", .string "Alice", .string "Carol"],
  testColumn "order_by_window_after_where_limit"
    "SELECT name FROM users WHERE age > 24 ORDER BY RANK() OVER (ORDER BY name DESC) LIMIT 2"
    "name" [.string "Dave", .string "Carol"],
  testColumn "grouped_order_by_window_key"
    "SELECT department FROM users GROUP BY department ORDER BY RANK() OVER (ORDER BY SUM(age))"
    "department" [.string "Marketing", .string "Sales", .string "Engineering"],
  -- #440 (registry row 22): a HAVING without GROUP BY and without an aggregate in the select
  -- list makes the query one group, as in the standard, DuckDB and Postgres
  testColumn "having_without_group_by_one_group"
    "SELECT 1 AS one FROM users HAVING COUNT(*) > 1"
    "one" [.int 1],
  testColumn "having_without_group_by_no_group"
    "SELECT 1 AS one FROM users HAVING SUM(age) > 1000"
    "one" [],
  testColumn "having_true_over_no_rows_one_group"
    "SELECT 1 AS one FROM users WHERE age > 100 HAVING 1 = 1"
    "one" [.int 1],
  testColumn "having_one_group_order_by_aggregate"
    "SELECT 1 AS one FROM users HAVING COUNT(*) > 1 ORDER BY COUNT(*)"
    "one" [.int 1],
  testColumn "grouped_window_in_derived_table"
    "SELECT MAX(r) AS m FROM (SELECT department, RANK() OVER (ORDER BY SUM(age)) AS r FROM users GROUP BY department) t"
    "m" [.int 3]
]

def errorPathTests : List TestResult := [
  testColumn "error_and_false_plain"
    "SELECT name, (1 = 'a') AND FALSE AS r FROM users WHERE id = 1" "r" [.bool false],
  testColumn "error_and_false_beside_aggregate"
    "SELECT (1 = 'a') AND FALSE AS r, COUNT(*) AS n FROM users" "r" [.bool false],
  testColumn "error_or_true_beside_window"
    "SELECT (1 = 'a') OR TRUE AS r, ROW_NUMBER() OVER (ORDER BY id) AS n FROM users WHERE id < 3"
    "r" [.bool true, .bool true],
  testColumn "error_is_null_plain"
    "SELECT (1 = 'a') IS NULL AS r FROM users WHERE id = 1" "r" [.bool true],
  testColumn "error_is_null_beside_aggregate"
    "SELECT (1 = 'a') IS NULL AS r, COUNT(*) AS n FROM users" "r" [.bool true],
  testColumn "error_is_null_beside_window"
    "SELECT (1 = 'a') IS NULL AS r, ROW_NUMBER() OVER (ORDER BY id) AS n FROM users WHERE id = 1"
    "r" [.bool true],
  -- HAVING reads like WHERE: the error side of OR does not drop the group
  testColumn "error_or_in_having"
    "SELECT department FROM users GROUP BY department HAVING (1 = 'a') OR COUNT(*) = 1"
    "department" [.string "Marketing"],
  testColumn "error_or_in_where"
    "SELECT department FROM users WHERE (1 = 'a') OR id = 4" "department" [.string "Marketing"]
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
  -- AVG over PARTITION BY, exact (registry row 7): 65/2 = 32.5, 47/2 = 23.5, 28
  testColumn "window_avg_partition_by"
    "SELECT name, AVG(age) OVER (PARTITION BY department) AS a FROM users"
    "a" [.decimal 325 1, .decimal 235 1, .decimal 325 1, .decimal 28 0, .decimal 235 1],
  -- a non-terminating average is rounded half away from zero to 16 places:
  -- (30 + 25 + 28) / 3 = 27.666… (ids 1, 2, 4)
  testContainsValue "avg_rounded_16_places"
    "SELECT AVG(age) FROM users WHERE id IN (1, 2, 4)" (.decimal 276666666666666667 16),
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
  -- Window functions under IN (list), BETWEEN, CASE and a function call (#418); expectations
  -- verified against DuckDB v1.5.3 (DiffDuckdb runs the same queries)
  -- sums per department: 65, 47, 65, 28, 47
  testColumn "window_in_list"
    "SELECT name, SUM(age) OVER (PARTITION BY department) IN (65, 28) AS r FROM users"
    "r" [.bool true, .bool false, .bool true, .bool true, .bool false],
  testColumn "window_not_in_list"
    "SELECT name, SUM(age) OVER (PARTITION BY department) NOT IN (65) AS r FROM users"
    "r" [.bool false, .bool true, .bool false, .bool true, .bool true],
  -- row numbers 4, 2, 5, 3, 1, so the lists are {25, 30}, {23, 30}, {26, 30}, {24, 30}, {22, 30}
  testColumn "window_inside_in_list"
    "SELECT name, age IN (ROW_NUMBER() OVER (ORDER BY age) + 21, 30) AS r FROM users"
    "r" [.bool true, .bool false, .bool false, .bool false, .bool true],
  testColumn "window_between"
    "SELECT name, SUM(age) OVER (PARTITION BY department) BETWEEN 40 AND 50 AS r FROM users"
    "r" [.bool false, .bool true, .bool false, .bool false, .bool true],
  -- upper bounds 28, 24, 30, 26, 22
  testColumn "window_between_bound"
    "SELECT name, age BETWEEN 22 AND 20 + ROW_NUMBER() OVER (ORDER BY age) * 2 AS r FROM users"
    "r" [.bool false, .bool false, .bool false, .bool false, .bool true],
  -- the condition is a window value: before #418 every row took the ELSE branch
  testColumn "window_case_condition"
    "SELECT name, CASE WHEN SUM(age) OVER (PARTITION BY department) > 50 THEN 'big' ELSE 'small' END AS r FROM users"
    "r" [.string "big", .string "small", .string "big", .string "small", .string "small"],
  testColumn "window_case_result"
    "SELECT name, CASE WHEN age > 26 THEN ROW_NUMBER() OVER (ORDER BY age) ELSE 0 END AS r FROM users"
    "r" [.int 4, .int 0, .int 5, .int 3, .int 0],
  testColumn "window_case_later_branch_no_else"
    "SELECT name, CASE WHEN age > 100 THEN 1 WHEN COUNT(*) OVER () = 5 THEN 2 END AS r FROM users"
    "r" [.int 2, .int 2, .int 2, .int 2, .int 2],
  testColumn "window_case_else"
    "SELECT name, CASE WHEN age > 100 THEN 1 ELSE MIN(age) OVER (PARTITION BY department) END AS r FROM users"
    "r" [.int 30, .int 22, .int 30, .int 28, .int 22],
  testColumn "window_function_argument"
    "SELECT name, ABS(age - MAX(age) OVER (PARTITION BY department)) AS r FROM users"
    "r" [.int 5, .int 0, .int 0, .int 0, .int 3],
  -- function call inside IN inside CASE inside BETWEEN
  testColumn "window_nested"
    "SELECT name, CASE WHEN ABS(SUM(age) OVER (PARTITION BY department)) IN (65) THEN age + 1 ELSE age END BETWEEN 31 AND 36 AS r FROM users"
    "r" [.bool true, .bool false, .bool true, .bool false, .bool false],
  -- no match against a list holding NULL is unknown
  testColumn "window_in_list_with_null"
    "SELECT name, MAX(age) OVER (PARTITION BY department) IN (NULL, 35) AS r FROM users"
    "r" [.bool true, .null none, .bool true, .null none, .null none],
  -- an item without a window function, next to one with, is unchanged
  testColumn "window_beside_plain_in"
    "SELECT name, age IN (25, 30) AS r, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users"
    "r" [.bool true, .bool true, .bool false, .bool false, .bool false],
  testColumn "window_outer_order_by_nonprojected_names"
    "SELECT name, ROW_NUMBER() OVER (ORDER BY age) AS rn FROM users ORDER BY age"
    "name" [.string "Eve", .string "Bob", .string "Dave", .string "Alice", .string "Carol"],
  -- A window function or an aggregate left of IN (subquery) (#422): before, the item was NULL
  -- and HAVING dropped every group. Expectations agree with DuckDB, sqlite and Postgres.
  -- department sums 65, 47, 65, 28, 47 against amount - 35 = 65, 165, 115, 265
  testColumn "window_in_subquery"
    "SELECT name, SUM(age) OVER (PARTITION BY department) IN (SELECT amount - 35 FROM orders) AS r FROM users"
    "r" [.bool true, .bool false, .bool true, .bool false, .bool false],
  -- row numbers 4, 2, 5, 3, 1 against {NULL, 2, 3}: no match with a NULL is unknown
  testColumn "window_not_in_subquery_with_null"
    "SELECT name, ROW_NUMBER() OVER (ORDER BY age) NOT IN (SELECT CASE WHEN id = 1 THEN NULL ELSE id END FROM products) AS r FROM users"
    "r" [.null none, .bool false, .null none, .bool false, .null none],
  testColumn "agg_in_subquery_whole_table"
    "SELECT MIN(age) IN (SELECT age FROM users WHERE department = 'Sales') AS r FROM users"
    "r" [.bool true],
  -- counts per department: Engineering 2, Marketing 1, Sales 2
  testColumn "agg_in_subquery_grouped"
    "SELECT department, COUNT(*) IN (SELECT user_id FROM orders WHERE user_id > 1) AS r FROM users GROUP BY department ORDER BY department"
    "r" [.bool true, .bool false, .bool true],
  testColumn "agg_expr_in_subquery_grouped"
    "SELECT department, MAX(age) - 20 IN (SELECT price / 10 FROM products) AS r FROM users GROUP BY department ORDER BY department"
    "r" [.bool true, .bool false, .bool true],
  testColumn "agg_not_in_subquery_with_null"
    "SELECT department, COUNT(*) NOT IN (SELECT CASE WHEN id = 1 THEN NULL ELSE id END FROM products) AS r FROM users GROUP BY department ORDER BY department"
    "r" [.bool false, .null none, .bool false],
  testColumn "agg_in_empty_subquery"
    "SELECT department, COUNT(*) IN (SELECT id FROM products WHERE id > 100) AS r FROM users GROUP BY department ORDER BY department"
    "r" [.bool false, .bool false, .bool false],
  testColumn "agg_not_in_empty_subquery"
    "SELECT department, MAX(age) NOT IN (SELECT id FROM products WHERE id > 100) AS r FROM users GROUP BY department ORDER BY department"
    "r" [.bool true, .bool true, .bool true],
  -- maxima 35, 28, 25 against ages {28, 22}
  testColumn "having_agg_in_subquery"
    "SELECT department FROM users GROUP BY department HAVING MAX(age) IN (SELECT age FROM users WHERE id > 3)"
    "department" [.string "Marketing"],
  testColumn "having_agg_not_in_subquery"
    "SELECT department FROM users GROUP BY department HAVING COUNT(*) NOT IN (SELECT user_id FROM orders WHERE user_id > 1)"
    "department" [.string "Marketing"],
  -- sqlite's bare-column rule (registry T9) counts a MIN/MAX left of IN (subquery), as sqlite
  -- 3 does: `name` comes from the extreme row
  testContainsValueIn "bare_column_max_in_subquery_sqlite" .sqlite
    "SELECT name, MAX(age) IN (SELECT 35) AS r FROM users" (.string "Carol"),
  testContainsValueIn "bare_column_min_in_subquery_sqlite" .sqlite
    "SELECT name, MIN(age) IN (SELECT 1) AS r FROM users" (.string "Eve"),
  testContainsValueIn "bare_column_max_in_subquery_standard_first_row" .standard
    "SELECT name, MAX(age) IN (SELECT 35) AS r FROM users" (.string "Alice")
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
-- Evaluation errors per dialect (#270, registry row 23)
-- ============================================================================

/-- Parse for a dialect, then evaluate under the dialect's error mode. -/
def evalStrict (dialect : Dialect) (sql : String) : Except String Table :=
  match parse sql (dialect := dialect) with
  | .error e => .error s!"parse error: {e}"
  | .ok stmt =>
    match evalStmtIn dialect.config.errors testDb stmt with
    | .ok (_, some t) => .ok t
    | .ok (_, none) => .error "statement produced no result table"
    | .error e => .error e

/-- `none`: the statement succeeds; `some what`: it fails with an error in clause `what`. -/
def testStrict (name : String) (dialect : Dialect) (sql : String) (expected : Option String) :
    TestResult :=
  match evalStrict dialect sql, expected with
  | .ok _, none => .pass name
  | .ok _, some what => .fail name s!"expected an error in {what}, got rows"
  | .error e, none => .fail name s!"expected rows, got: {e}"
  | .error e, some what =>
    if e == s!"evaluation error in {what}" then .pass name
    else .fail name s!"expected an error in {what}, got: {e}"

def strictErrorTests : List TestResult := [
  testStrict "strict: division by zero in SELECT (postgres)" .postgres
    "SELECT id / (age - 30) AS x FROM users" (some "SELECT"),
  testStrict "strict: division by zero in SELECT (standard)" .standard
    "SELECT id / (age - 30) AS x FROM users" (some "SELECT"),
  testStrict "quiet: division by zero is NULL (sqlite)" .sqlite
    "SELECT id / (age - 30) AS x FROM users" none,
  testStrict "strictDivZeroNull: division by zero is not an error (duckdb)" .duckdb
    "SELECT id / (age - 30) AS x FROM users" none,
  testStrict "strictDivZeroNull: modulo by zero is not an error (duckdb)" .duckdb
    "SELECT id % (age - 30) AS x FROM users" none,
  testStrict "strictDivZeroNull: a type error still is (duckdb)" .duckdb
    "SELECT name + 1 AS x FROM users" (some "SELECT"),
  testStrict "strictDivZeroNull: an error in the dividend still is (duckdb)" .duckdb
    "SELECT (name + 1) % (age - age) AS x FROM users" (some "SELECT"),
  testStrict "strictDivZeroNull: an error in the dividend still is, under a division (duckdb)" .duckdb
    "SELECT (name + 1) / 0 AS x FROM users" (some "SELECT"),
  testStrict "strictDivZeroNull: a string divisor still is (duckdb)" .duckdb
    "SELECT id / name AS x FROM users" (some "SELECT"),
  -- /audit 25 Nov 2026: a dividend of the wrong type over a zero divisor (DuckDB: binder error)
  testStrict "strictDivZeroNull: a string dividend over zero still is (duckdb)" .duckdb
    "SELECT name / 0 AS x FROM users" (some "SELECT"),
  testStrict "strictDivZeroNull: a string dividend modulo zero still is (duckdb)" .duckdb
    "SELECT name % (age - age) AS x FROM users" (some "SELECT"),
  testStrict "strictDivZeroNull: a boolean dividend over zero still is (duckdb)" .duckdb
    "SELECT (age > 1) / 0 AS x FROM users" (some "SELECT"),
  testStrict "strictDivZeroNull: a decimal dividend over zero is NULL (duckdb)" .duckdb
    "SELECT (age + 0.5) / (age - age) AS x FROM users" none,
  testStrict "strictDivZeroNull: a NULL dividend over zero is NULL (duckdb)" .duckdb
    "SELECT NULL / 0 AS x FROM users" none,
  testStrict "strict: -NULL is NULL, not an error (#210)" .postgres "SELECT -NULL AS x" none,
  testStrict "strict: WHERE" .postgres
    "SELECT id FROM users WHERE name > 1" (some "WHERE"),
  testStrict "strict: FALSE AND <error> is FALSE, no error" .postgres
    "SELECT id FROM users WHERE FALSE AND id / 0 > 1" none,
  testStrict "strict: lazy CASE, no error" .postgres
    "SELECT CASE WHEN age = 30 THEN 0 ELSE id / (age - 30) END AS x FROM users" none,
  testStrict "strict: WHERE drops the row before SELECT sees it" .postgres
    "SELECT id / (age - 30) AS x FROM users WHERE age <> 30" none,
  testStrict "strict: join ON" .postgres
    "SELECT u.id FROM users u JOIN orders o ON u.id / (o.amount - o.amount) = 1" (some "ON"),
  testStrict "strict: GROUP BY key" .postgres
    "SELECT COUNT(*) AS c FROM users GROUP BY id / (age - 30)" (some "GROUP BY"),
  testStrict "strict: aggregate argument" .postgres
    "SELECT SUM(id / (age - 30)) AS s FROM users" (some "aggregate argument"),
  testStrict "strict: aggregate argument under GROUP BY" .postgres
    "SELECT department, MAX(id / (age - 30)) AS m FROM users GROUP BY department" (some "aggregate argument"),
  testStrict "strict: HAVING" .postgres
    "SELECT department FROM users GROUP BY department HAVING SUM(age) / (COUNT(*) - 2) > 0" (some "HAVING"),
  testStrict "strict: select item of a surviving group" .postgres
    "SELECT department, SUM(age) / (COUNT(*) - 2) AS r FROM users GROUP BY department" (some "SELECT"),
  testStrict "strict: select item of a group HAVING removes, no error" .postgres
    "SELECT department, SUM(age) / (COUNT(*) - 2) AS r FROM users GROUP BY department HAVING COUNT(*) = 1" none,
  testStrict "strict: ORDER BY key" .postgres
    "SELECT id FROM users ORDER BY id / (age - 30)" (some "ORDER BY"),
  testStrict "strict: derived table" .postgres
    "SELECT x FROM (SELECT id / (age - 30) AS x FROM users) d" (some "SELECT"),
  testStrict "strict: set-operation branch" .postgres
    "SELECT id FROM users UNION SELECT id / (age - 30) FROM users" (some "SELECT"),
  testStrict "strict: CTE body" .postgres
    "WITH c AS (SELECT id / (age - 30) AS x FROM users) SELECT x FROM c" (some "SELECT"),
  testStrict "strict: rows after LIMIT are not evaluated" .postgres
    "SELECT id / (id - 5) AS x FROM users LIMIT 4" none,
  testStrict "strict: rows OFFSET skips are evaluated" .postgres
    "SELECT id / (age - 30) AS x FROM users LIMIT 2 OFFSET 2" (some "SELECT"),
  testStrict "strict: with DISTINCT every row is" .postgres
    "SELECT DISTINCT id / (id - 5) AS x FROM users LIMIT 1" (some "SELECT"),
  testStrict "strict: with ORDER BY every row is" .postgres
    "SELECT id / (age - 30) AS x FROM users ORDER BY id LIMIT 2 OFFSET 2" (some "SELECT"),
  -- #448: expression subqueries, window queries, grouped ORDER BY keys, DML, recursive CTEs
  testStrict "strict: an IN subquery is evaluated in full" .postgres
    "SELECT id FROM users WHERE id IN (SELECT id / (age - 30) FROM users)" (some "SELECT"),
  testStrict "strict: a scalar subquery" .postgres
    "SELECT id, (SELECT MAX(id) / 0 FROM orders) AS x FROM users" (some "SELECT"),
  testStrict "strict: a correlated scalar subquery sees the outer row" .postgres
    "SELECT id, (SELECT 1 / (u.age - 30) FROM orders o WHERE o.user_id = u.id LIMIT 1) AS x FROM users u"
    (some "SELECT"),
  testStrict "strict: a correlated subquery for rows that never hit the error" .postgres
    "SELECT id, (SELECT 1 / (u.age - 30) FROM orders o WHERE o.user_id = u.id LIMIT 1) AS x FROM users u WHERE u.age <> 30"
    none,
  testStrict "strict: a scalar subquery's own WHERE filters first" .postgres
    "SELECT (SELECT id / (age - 30) FROM users WHERE age <> 30 LIMIT 1) AS x" none,
  testStrict "strict: a subquery in a join ON" .postgres
    "SELECT u.id FROM users u JOIN orders o ON o.user_id = (SELECT MAX(id) / 0 FROM users)" (some "SELECT"),
  testStrict "strict gap (#448): a subquery under AND is not checked (engines short-circuit)" .postgres
    "SELECT id FROM users WHERE id = 99 AND id IN (SELECT 1 / (age - 30) FROM users)" none,
  testStrict "strict gap (#448): a subquery past a CASE's first condition is not checked" .postgres
    "SELECT CASE WHEN id > 0 THEN 0 ELSE (SELECT MAX(1 / (age - 30)) FROM users) END AS x FROM users" none,
  testStrict "strict gap (#448): EXISTS is not checked (engines differ)" .postgres
    "SELECT id FROM users WHERE EXISTS (SELECT 1 / (amount - 100) FROM orders)" none,
  testStrict "strict: a window query's plain item" .postgres
    "SELECT id / (age - 30) AS x, ROW_NUMBER() OVER () AS n FROM users" (some "SELECT"),
  testStrict "strict: a window query's items under LIMIT are not checked (rows unknown)" .postgres
    "SELECT id / (id - 5) AS x, ROW_NUMBER() OVER () AS n FROM users LIMIT 1" none,
  testStrict "strict: a window argument under LIMIT is, on every row" .postgres
    "SELECT SUM(id / (id - 5)) OVER () AS s FROM users LIMIT 1" (some "window"),
  testStrict "strict: a window function's argument" .postgres
    "SELECT SUM(id / (age - 30)) OVER () AS s FROM users" (some "window"),
  testStrict "strict: a window's PARTITION BY key" .postgres
    "SELECT ROW_NUMBER() OVER (PARTITION BY id / (age - 30)) AS n FROM users" (some "window"),
  testStrict "strict: a window over groups" .postgres
    "SELECT department, SUM(COUNT(*) / (COUNT(*) - 2)) OVER () AS s FROM users GROUP BY department"
    (some "window"),
  testStrict "strict: a window query without errors" .postgres
    "SELECT id, ROW_NUMBER() OVER (ORDER BY age) AS n FROM users ORDER BY n" none,
  testStrict "strict: a grouped ORDER BY key" .postgres
    "SELECT department FROM users GROUP BY department ORDER BY SUM(age) / (COUNT(*) - 2)" (some "ORDER BY"),
  testStrict "strict: a grouped ORDER BY on an output alias" .postgres
    "SELECT department, COUNT(*) AS c FROM users GROUP BY department ORDER BY c" none,
  testStrict "strict: a grouped ORDER BY key of a group HAVING removes is not evaluated" .postgres
    "SELECT department FROM users GROUP BY department HAVING COUNT(*) = 1 ORDER BY SUM(age) / (COUNT(*) - 2)"
    none,
  testStrict "strict: a recursive CTE's iterations" .postgres
    "WITH RECURSIVE c AS (SELECT 1 AS n UNION ALL SELECT n + 1 AS n FROM c WHERE 10 / (3 - n) > 0) SELECT n FROM c"
    (some "WHERE"),
  testStrict "strict: a recursive CTE that stops before the error" .postgres
    "WITH RECURSIVE c AS (SELECT 1 AS n UNION ALL SELECT n + 1 AS n FROM c WHERE n < 2 AND 10 / (3 - n) > 0) SELECT n FROM c"
    none,
  testStrict "strict gap (#448): a type error on no evaluated row is not seen (engines reject at bind time)" .postgres
    "SELECT id FROM users WHERE FALSE AND name > 1" none
]

/-- A DML statement under a dialect's error mode: `none` succeeds, `some what` fails in `what`. -/
def testStrictDml (name : String) (dialect : Dialect) (sql : String) (expected : Option String) :
    TestResult :=
  match parse sql (dialect := dialect) with
  | .error e => .fail name s!"parse error: {e}"
  | .ok stmt =>
    match evalStmtIn dialect.config.errors testDb stmt, expected with
    | .ok _, none => .pass name
    | .ok _, some what => .fail name s!"expected an error in {what}, got success"
    | .error e, none => .fail name s!"expected success, got: {e}"
    | .error e, some what =>
      if e == s!"evaluation error in {what}" then .pass name
      else .fail name s!"expected an error in {what}, got: {e}"

def strictDmlTests : List TestResult := [
  testStrictDml "strict DML: INSERT VALUES" .postgres
    "INSERT INTO users (id, name) VALUES (6, 1 / 0)" (some "VALUES"),
  testStrictDml "strict DML: INSERT SELECT" .postgres
    "INSERT INTO users (id) SELECT id / (age - 30) FROM users" (some "SELECT"),
  testStrictDml "strict DML: UPDATE SET" .postgres
    "UPDATE users SET age = id / (age - 30)" (some "SET"),
  testStrictDml "strict DML: UPDATE SET only on the rows WHERE keeps" .postgres
    "UPDATE users SET age = id / (age - 30) WHERE age <> 30" none,
  testStrictDml "strict DML: UPDATE WHERE" .postgres
    "UPDATE users SET age = 1 WHERE name > 1" (some "WHERE"),
  testStrictDml "strict DML: DELETE WHERE" .postgres
    "DELETE FROM users WHERE id / (age - 30) > 0" (some "WHERE"),
  testStrictDml "quiet DML: sqlite" .sqlite
    "DELETE FROM users WHERE id / (age - 30) > 0" none,
  testStrictDml "strictDivZeroNull DML: duckdb" .duckdb
    "DELETE FROM users WHERE id % (age - 30) > 0" none
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
  windowTests ++ groupedWindowTests ++ errorPathTests ++ caseInsensitiveTests ++
  strictErrorTests ++ strictDmlTests ++ valueArmTests

def runSemanticsTests : IO (Nat × Nat) :=
  runTests "Semantics Tests" allSemanticsTests

end SemanticsTest
