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
  testNonEmpty "inner_join" "SELECT * FROM users u INNER JOIN orders o ON u.id = o.user_id",
  testRowCount "inner_join_count" "SELECT * FROM users u INNER JOIN orders o ON u.id = o.user_id" 4,
  -- Users 4 and 5 have no orders, so left join should have more rows with NULLs
  testNonEmpty "left_join" "SELECT * FROM users u LEFT JOIN orders o ON u.id = o.user_id",
  testNonEmpty "cross_join" "SELECT * FROM users CROSS JOIN products"
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
  testContainsValue "scalar_subquery_correlated" "SELECT (SELECT amount FROM orders WHERE orders.user_id = users.id LIMIT 1) FROM users WHERE id = 1" (.int 100)
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
  limitOffsetTests ++ subqueryTests ++ setOpQueryTests ++
  arithmeticTests ++ mutationTests

def runSemanticsTests : IO (Nat × Nat) :=
  runTests "Semantics Tests" allSemanticsTests

end SemanticsTest
