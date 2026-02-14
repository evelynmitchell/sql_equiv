/-
  Property-based and unit tests for query-level optimizer correctness.

  Tests that optimizeSelectStmt, optimizeQuery, and optimize preserve
  evaluation semantics on fixed query templates with random scalar parameters.
  These are the highest-value query-level tests: the three critical axioms
  (optimizeSelectStmt_equiv, optimize_equiv) are unproven, so SlimCheck
  is the only runtime defense against query-level optimizer bugs.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace QueryOptimizer

-- ============================================================================
-- Test Database (matches Test/SemanticsTest.lean)
-- ============================================================================

private def usersTable : Table := [
  [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")],
  [("id", .int 2), ("name", .string "Bob"), ("age", .int 25), ("department", .string "Sales")],
  [("id", .int 3), ("name", .string "Carol"), ("age", .int 35), ("department", .string "Engineering")],
  [("id", .int 4), ("name", .string "Dave"), ("age", .int 28), ("department", .string "Marketing")],
  [("id", .int 5), ("name", .string "Eve"), ("age", .int 22), ("department", .string "Sales")]
]

private def ordersTable : Table := [
  [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")],
  [("id", .int 2), ("user_id", .int 1), ("amount", .int 200), ("product", .string "Gadget")],
  [("id", .int 3), ("user_id", .int 2), ("amount", .int 150), ("product", .string "Widget")],
  [("id", .int 4), ("user_id", .int 3), ("amount", .int 300), ("product", .string "Gizmo")]
]

private def productsTable : Table := [
  [("id", .int 1), ("name", .string "Widget"), ("price", .int 50)],
  [("id", .int 2), ("name", .string "Gadget"), ("price", .int 100)],
  [("id", .int 3), ("name", .string "Gizmo"), ("price", .int 150)]
]

private def testDb : Database := fun name =>
  match name with
  | "users" => usersTable
  | "orders" => ordersTable
  | "products" => productsTable
  | _ => []

-- ============================================================================
-- Helpers
-- ============================================================================

private def selectOptOk (s : SelectStmt) : Bool :=
  evalSelect testDb (optimizeSelectStmt s) == evalSelect testDb s

private def queryOptOk (q : Query) : Bool :=
  evalQuery testDb (optimizeQuery q) == evalQuery testDb q

/-- SELECT * with optional WHERE from a single table. -/
private def mkSelectWhere (tblName : String) (where_ : Option Expr) : SelectStmt :=
  .mk false [.star none] (some (.table ⟨tblName, none⟩)) where_ [] none [] none none

/-- Qualified column ref: e.g., ⟨some "users", "age"⟩ -/
private def qcol (tbl col : String) : Expr := .col ⟨some tbl, col⟩

-- ============================================================================
-- A. Simple WHERE
-- ============================================================================

private def mkWhereAge (op : BinOp) (val : Int) : SelectStmt :=
  mkSelectWhere "users" (some (.binOp op (qcol "users" "age") (.lit (.int val))))

private def simpleWhereCmpOk (cmp : CmpOp) (age : AgeInt) : Bool :=
  selectOptOk (mkWhereAge cmp.op age.val)

private def simpleWhereRangeOk (lo hi : AgeInt) : Bool :=
  let cond := Expr.binOp .and
    (.binOp .gt (qcol "users" "age") (.lit (.int lo.val)))
    (.binOp .lt (qcol "users" "age") (.lit (.int hi.val)))
  selectOptOk (mkSelectWhere "users" (some cond))

def simpleWhereTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "WHERE age {cmp} {val}" (∀ cmp : CmpOp, ∀ age : AgeInt, simpleWhereCmpOk cmp age) $
  check (cfg := cfg) "WHERE age > lo AND age < hi" (∀ lo hi : AgeInt, simpleWhereRangeOk lo hi) $
  test "WHERE department = 'Engineering'" (selectOptOk
    (mkSelectWhere "users" (some (.binOp .eq (qcol "users" "department") (.lit (.string "Engineering")))))) $
  test "WHERE department = 'Sales'" (selectOptOk
    (mkSelectWhere "users" (some (.binOp .eq (qcol "users" "department") (.lit (.string "Sales")))))) $
  test "WHERE department = 'NonExistent'" (selectOptOk
    (mkSelectWhere "users" (some (.binOp .eq (qcol "users" "department") (.lit (.string "NonExistent"))))))

-- ============================================================================
-- B. JOINs
-- ============================================================================

private def mkJoinQuery (jt : JoinType) (ageVal : Int) : SelectStmt :=
  let usersFrom := FromClause.table ⟨"users", none⟩
  let ordersFrom := FromClause.table ⟨"orders", none⟩
  let onCond := Expr.binOp .eq (qcol "users" "id") (qcol "orders" "user_id")
  let joinOn := if jt == .cross then none else some onCond
  let joinFrom := FromClause.join usersFrom jt ordersFrom joinOn
  let where_ := some (Expr.binOp .gt (qcol "users" "age") (.lit (.int ageVal)))
  .mk false [.star none] (some joinFrom) where_ [] none [] none none

private def joinOptOk (jt : JoinType) (age : AgeInt) : Bool :=
  selectOptOk (mkJoinQuery jt age.val)

def joinTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "JOIN {type} WHERE age > {val}" (∀ jt : JoinType, ∀ age : AgeInt, joinOptOk jt age) $
  test "INNER JOIN age > 25" (selectOptOk (mkJoinQuery .inner 25)) $
  test "LEFT JOIN age > 25" (selectOptOk (mkJoinQuery .left 25)) $
  test "RIGHT JOIN age > 25" (selectOptOk (mkJoinQuery .right 25)) $
  test "FULL JOIN age > 25" (selectOptOk (mkJoinQuery .full 25)) $
  test "CROSS JOIN age > 25" (selectOptOk (mkJoinQuery .cross 25))

-- ============================================================================
-- C. Subquery
-- ============================================================================

private def mkSubqueryWhere (ageVal : Int) : SelectStmt :=
  -- SELECT * FROM (SELECT * FROM users) AS sub WHERE sub.users.age > val
  let innerSel := mkSelectWhere "users" none
  let subFrom := FromClause.subquery innerSel "sub"
  -- Double-qualification: inner columns are "users.age", outer qualifies as "sub.users.age"
  let where_ := some (Expr.binOp .gt (.col ⟨some "sub", "users.age"⟩) (.lit (.int ageVal)))
  .mk false [.star none] (some subFrom) where_ [] none [] none none

private def subqueryOptOk (age : AgeInt) : Bool :=
  selectOptOk (mkSubqueryWhere age.val)

def subqueryTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "subquery WHERE sub.users.age > {val}" (∀ age : AgeInt, subqueryOptOk age)

-- ============================================================================
-- D. ORDER BY + LIMIT + OFFSET
-- ============================================================================

private def mkOrderLimitOffset (limitVal : Option Nat) (offsetVal : Option Nat) : SelectStmt :=
  let orderBy := [OrderByItem.mk (qcol "users" "age") .asc]
  .mk false [.star none] (some (.table ⟨"users", none⟩)) none [] none orderBy limitVal offsetVal

private def orderLimitOffsetOk (lim off : SmallNat) : Bool :=
  selectOptOk (mkOrderLimitOffset (some lim.val) (some off.val))

def orderLimitOffsetTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "ORDER BY age LIMIT n OFFSET m" (∀ lim off : SmallNat, orderLimitOffsetOk lim off) $
  test "LIMIT only" (selectOptOk (mkOrderLimitOffset (some 3) none)) $
  test "OFFSET only" (selectOptOk (mkOrderLimitOffset none (some 2))) $
  test "neither LIMIT nor OFFSET" (selectOptOk (mkOrderLimitOffset none none)) $
  test "LIMIT 0" (selectOptOk (mkOrderLimitOffset (some 0) none)) $
  test "OFFSET > row count" (selectOptOk (mkOrderLimitOffset none (some 100)))

-- ============================================================================
-- E. Dead code elimination (WHERE TRUE / WHERE FALSE)
-- ============================================================================

def deadCodeTests : TestSeq :=
  test "WHERE TRUE = no WHERE" (
    evalSelect testDb (mkSelectWhere "users" (some (.lit (.bool true)))) ==
    evalSelect testDb (mkSelectWhere "users" none)) $
  test "WHERE FALSE = empty" (
    (evalSelect testDb (mkSelectWhere "users" (some (.lit (.bool false))))).length == 0) $
  test "optimizer preserves WHERE TRUE" (selectOptOk
    (mkSelectWhere "users" (some (.lit (.bool true))))) $
  test "optimizer preserves WHERE FALSE" (selectOptOk
    (mkSelectWhere "users" (some (.lit (.bool false))))) $
  test "optimizer preserves WHERE 1=1" (selectOptOk
    (mkSelectWhere "users" (some (.binOp .eq (.lit (.int 1)) (.lit (.int 1))))))

-- ============================================================================
-- F. Compound queries (UNION ALL)
-- ============================================================================

private def mkUnionAll (v1 v2 : Int) : Query :=
  let sel1 := mkWhereAge .gt v1
  let sel2 := mkWhereAge .gt v2
  .compound (.simple sel1) .unionAll (.simple sel2)

private def unionAllOptOk (a1 a2 : AgeInt) : Bool :=
  queryOptOk (mkUnionAll a1.val a2.val)

def compoundTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "UNION ALL WHERE age > v1, age > v2" (∀ a1 a2 : AgeInt, unionAllOptOk a1 a2)

-- ============================================================================
-- G. DISTINCT
-- ============================================================================

private def mkDistinctWhere (ageVal : Int) : SelectStmt :=
  let where_ := some (Expr.binOp .gt (qcol "users" "age") (.lit (.int ageVal)))
  .mk true [.star none] (some (.table ⟨"users", none⟩)) where_ [] none [] none none

private def distinctOptOk (age : AgeInt) : Bool :=
  selectOptOk (mkDistinctWhere age.val)

def distinctTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "SELECT DISTINCT WHERE age > {val}" (∀ age : AgeInt, distinctOptOk age)

-- ============================================================================
-- H. Statement-level (optimize wrapper)
-- ============================================================================

private def stmtOptOk (age : AgeInt) : Bool :=
  let sel := mkWhereAge .gt age.val
  let stmt := Stmt.query (.simple sel)
  (evalStmt testDb (optimize stmt)).2 == (evalStmt testDb stmt).2

def stmtTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "optimize (Stmt.query ...) preserves semantics" (∀ age : AgeInt, stmtOptOk age)

-- ============================================================================
-- I. Projection (SELECT specific columns)
-- ============================================================================

private def mkProjection (ageVal : Int) : SelectStmt :=
  let items := [
    SelectItem.exprItem (qcol "users" "name") (some "name"),
    SelectItem.exprItem (qcol "users" "age") (some "age")
  ]
  let where_ := some (Expr.binOp .gt (qcol "users" "age") (.lit (.int ageVal)))
  .mk false items (some (.table ⟨"users", none⟩)) where_ [] none [] none none

private def projectionOptOk (age : AgeInt) : Bool :=
  selectOptOk (mkProjection age.val)

def projectionTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "SELECT name, age WHERE age > {val}" (∀ age : AgeInt, projectionOptOk age)

-- ============================================================================
-- Anti-vacuity guards
-- ============================================================================

def antiVacuityTests : TestSeq :=
  test "sanity: WHERE age > 25 returns 2-4 rows" (
    let n := (evalSelect testDb (mkWhereAge .gt 25)).length
    n > 0 && n < 5) $
  test "sanity: INNER JOIN age > 25 returns non-empty" (
    (evalSelect testDb (mkJoinQuery .inner 25)).length > 0) $
  test "sanity: subquery WHERE age > 25 returns non-empty" (
    (evalSelect testDb (mkSubqueryWhere 25)).length > 0) $
  test "sanity: projection WHERE age > 25 returns non-empty" (
    (evalSelect testDb (mkProjection 25)).length > 0)

-- ============================================================================
-- All query optimizer tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Anti-Vacuity" antiVacuityTests $
  group "Simple WHERE" (simpleWhereTests cfg) $
  group "JOINs" (joinTests cfg) $
  group "Subquery" (subqueryTests cfg) $
  group "ORDER BY/LIMIT/OFFSET" (orderLimitOffsetTests cfg) $
  group "Dead Code Elimination" deadCodeTests $
  group "Compound Queries" (compoundTests cfg) $
  group "DISTINCT" (distinctTests cfg) $
  group "Statement-Level" (stmtTests cfg) $
  group "Projection" (projectionTests cfg)

end QueryOptimizer
