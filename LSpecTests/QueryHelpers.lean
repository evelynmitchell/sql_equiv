/-
  Shared helpers for query-level property and unit tests.

  Provides the standard test database (users, orders, products), query
  constructors (mkWhereAge, mkJoinQuery, etc.), and database-parameterized
  comparison helpers used across Tiers 3A–3F.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace QueryHelpers

-- ============================================================================
-- Test Database (matches Test/SemanticsTest.lean)
-- ============================================================================

def usersTable : Table := [
  [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")],
  [("id", .int 2), ("name", .string "Bob"), ("age", .int 25), ("department", .string "Sales")],
  [("id", .int 3), ("name", .string "Carol"), ("age", .int 35), ("department", .string "Engineering")],
  [("id", .int 4), ("name", .string "Dave"), ("age", .int 28), ("department", .string "Marketing")],
  [("id", .int 5), ("name", .string "Eve"), ("age", .int 22), ("department", .string "Sales")]
]

def ordersTable : Table := [
  [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")],
  [("id", .int 2), ("user_id", .int 1), ("amount", .int 200), ("product", .string "Gadget")],
  [("id", .int 3), ("user_id", .int 2), ("amount", .int 150), ("product", .string "Widget")],
  [("id", .int 4), ("user_id", .int 3), ("amount", .int 300), ("product", .string "Gizmo")]
]

def productsTable : Table := [
  [("id", .int 1), ("name", .string "Widget"), ("price", .int 50)],
  [("id", .int 2), ("name", .string "Gadget"), ("price", .int 100)],
  [("id", .int 3), ("name", .string "Gizmo"), ("price", .int 150)]
]

def testDb : Database := fun name =>
  match name with
  | "users" => usersTable
  | "orders" => ordersTable
  | "products" => productsTable
  | _ => []

-- ============================================================================
-- Core comparison helpers
-- ============================================================================

-- ============================================================================
-- Query constructors
-- ============================================================================

/-- Qualified column ref: e.g., ⟨some "users", "age"⟩ -/
def qcol (tbl col : String) : Expr := .col ⟨some tbl, col⟩

/-- SELECT * with optional WHERE from a single table. -/
def mkSelectWhere (tblName : String) (where_ : Option Expr) : SelectStmt :=
  .mk false [.star none] (some (.table ⟨tblName, none⟩)) where_ [] none [] none none

/-- SELECT * FROM users WHERE users.age {op} {val}. -/
def mkWhereAge (op : BinOp) (val : Int) : SelectStmt :=
  mkSelectWhere "users" (some (.binOp op (qcol "users" "age") (.lit (.int val))))

/-- JOIN query: SELECT * FROM users {jt} JOIN orders ON ... WHERE users.age > {ageVal}. -/
def mkJoinQuery (jt : JoinType) (ageVal : Int) : SelectStmt :=
  let usersFrom := FromClause.table ⟨"users", none⟩
  let ordersFrom := FromClause.table ⟨"orders", none⟩
  let onCond := Expr.binOp .eq (qcol "users" "id") (qcol "orders" "user_id")
  let joinOn := if jt == .cross then none else some onCond
  let joinFrom := FromClause.join usersFrom jt ordersFrom joinOn
  let where_ := some (Expr.binOp .gt (qcol "users" "age") (.lit (.int ageVal)))
  .mk false [.star none] (some joinFrom) where_ [] none [] none none

/-- SELECT DISTINCT * FROM users WHERE users.age > {ageVal}. -/
def mkDistinctWhere (ageVal : Int) : SelectStmt :=
  let where_ := some (Expr.binOp .gt (qcol "users" "age") (.lit (.int ageVal)))
  .mk true [.star none] (some (.table ⟨"users", none⟩)) where_ [] none [] none none

/-- SELECT * FROM (SELECT * FROM users) AS sub WHERE users.age > {ageVal}. -/
def mkSubqueryWhere (ageVal : Int) : SelectStmt :=
  let innerSel := mkSelectWhere "users" none
  let subFrom := FromClause.subquery (.simple innerSel) "sub"
  let where_ := some (Expr.binOp .gt (qcol "users" "age") (.lit (.int ageVal)))
  .mk false [.star none] (some subFrom) where_ [] none [] none none

/-- UNION ALL of two WHERE queries. -/
def mkUnionAll (v1 v2 : Int) : Query :=
  let sel1 := mkWhereAge .gt v1
  let sel2 := mkWhereAge .gt v2
  .compound (.simple sel1) .unionAll (.simple sel2)

/-- ORDER BY users.age ASC with optional LIMIT/OFFSET. -/
def mkOrderLimitOffset (limitVal : Option Nat) (offsetVal : Option Nat) : SelectStmt :=
  let orderBy := [OrderByItem.mk (qcol "users" "age") .asc]
  .mk false [.star none] (some (.table ⟨"users", none⟩)) none [] none orderBy limitVal offsetVal

/-- SELECT name, age FROM users WHERE users.age > {ageVal}. -/
def mkProjection (ageVal : Int) : SelectStmt :=
  let items := [
    SelectItem.exprItem (qcol "users" "name") (some "name"),
    SelectItem.exprItem (qcol "users" "age") (some "age")
  ]
  let where_ := some (Expr.binOp .gt (qcol "users" "age") (.lit (.int ageVal)))
  .mk false items (some (.table ⟨"users", none⟩)) where_ [] none [] none none

end QueryHelpers
