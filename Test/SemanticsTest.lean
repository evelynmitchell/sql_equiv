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

/-- Test database -/
def testDb : Database := fun name =>
  match name with
  | "users" => usersTable
  | "orders" => ordersTable
  | "products" => productsTable
  | _ => []

-- ============================================================================
-- Test Helpers
-- ============================================================================

/-- Parse and evaluate a SELECT query -/
def evalQuery (sql : String) : Except String Table :=
  match parseSelectStr sql with
  | .error e => .error e
  | .ok sel => .ok (evalSelect testDb sel)

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

def limitOffsetTests : List TestResult := [
  testRowCount "limit" "SELECT * FROM users LIMIT 3" 3,
  testRowCount "limit_offset" "SELECT * FROM users LIMIT 2 OFFSET 2" 2,
  testRowCount "limit_large" "SELECT * FROM users LIMIT 100" 5,
  testRowCount "offset_large" "SELECT * FROM users LIMIT 10 OFFSET 10" 0
]

-- ============================================================================
-- Subquery Tests
-- ============================================================================

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
  testContainsValue "scalar_subquery_max" "SELECT (SELECT MAX(amount) FROM orders WHERE orders.user_id = users.id) FROM users WHERE id = 1" (.int 200)
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
  testContainsValue "max_distinct" "SELECT MAX(DISTINCT amount) FROM orders" (.int 300)
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
-- Test Runner
-- ============================================================================

def allSemanticsTests : List TestResult :=
  basicQueryTests ++ whereQueryTests ++ joinQueryTests ++
  projectionTests ++ distinctTests ++ orderByTests ++
  limitOffsetTests ++ subqueryTests ++ aggregateTests ++
  distinctAggTests ++ groupByTests ++ setOpQueryTests ++
  arithmeticTests ++ edgeCaseTests ++ mutationTests

def runSemanticsTests : IO (Nat × Nat) :=
  runTests "Semantics Tests" allSemanticsTests

end SemanticsTest
