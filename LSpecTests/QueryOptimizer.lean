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
import LSpecTests.QueryHelpers

open LSpec SlimCheck
open SqlEquiv
open QueryHelpers

namespace QueryOptimizer

-- ============================================================================
-- A. Simple WHERE
-- ============================================================================

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

private def subqueryOptOk (age : AgeInt) : Bool :=
  selectOptOk (mkSubqueryWhere age.val)

def subqueryTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "subquery WHERE sub.users.age > {val}" (∀ age : AgeInt, subqueryOptOk age)

-- ============================================================================
-- D. ORDER BY + LIMIT + OFFSET
-- ============================================================================

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

private def unionAllOptOk (a1 a2 : AgeInt) : Bool :=
  queryOptOk (mkUnionAll a1.val a2.val)

def compoundTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "UNION ALL WHERE age > v1, age > v2" (∀ a1 a2 : AgeInt, unionAllOptOk a1 a2)

-- ============================================================================
-- G. DISTINCT
-- ============================================================================

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
