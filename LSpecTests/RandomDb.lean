/-
  Tier 3B: Random database generator.

  Reuses query templates from Tier 3A but tests against randomly generated
  databases instead of the single fixed testDb. Multiplies coverage of all
  query-level tests by varying the data patterns.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators
import LSpecTests.QueryHelpers

open LSpec SlimCheck
open SqlEquiv
open QueryHelpers

namespace RandomDb

-- ============================================================================
-- RandomDb type with Repr (stores tables explicitly for printing)
-- ============================================================================

/-- A randomly generated database with the same schema as testDb.
    Stores tables explicitly (not as a function) so we can derive Repr
    for counterexample reporting. -/
structure RandomDb where
  users : Table
  orders : Table
  products : Table
  deriving Repr

/-- Convert to Database function. -/
def RandomDb.toDb (rdb : RandomDb) : Database := fun name =>
  match name with
  | "users" => rdb.users
  | "orders" => rdb.orders
  | "products" => rdb.products
  | _ => []

-- ============================================================================
-- Generators
-- ============================================================================

private def names : Array String := #["Alice", "Bob", "Carol", "Dave", "Eve", "Fay", "Gus", "Hank"]
private def departments : Array String := #["Engineering", "Sales", "Marketing", "HR", "Finance"]
private def productNames : Array String := #["Widget", "Gadget", "Gizmo", "Doohickey", "Thingamajig"]

/-- With ~15% probability, replace a value with NULL. -/
private partial def maybeNull (v : Value) : Gen Value := do
  let n ← Gen.choose Nat 0 6
  if n == 0 then pure (.null none) else pure v

/-- Generate a random user row with the given id. ~15% chance of NULL per nullable field. -/
private partial def genUsersRow (id : Nat) : Gen Row := do
  let name ← Gen.elements names >>= fun s => maybeNull (.string s)
  let age ← Gen.choose Int 18 65 >>= fun n => maybeNull (.int n)
  let dept ← Gen.elements departments >>= fun s => maybeNull (.string s)
  pure [("id", .int id), ("name", name), ("age", age), ("department", dept)]

/-- Generate a random order row with the given id and user_id. -/
private partial def genOrdersRow (id userId : Nat) : Gen Row := do
  let amount ← Gen.choose Int 10 500 >>= fun n => maybeNull (.int n)
  let product ← Gen.elements productNames >>= fun s => maybeNull (.string s)
  pure [("id", .int id), ("user_id", .int userId), ("amount", amount), ("product", product)]

/-- Generate a random product row with the given id. -/
private partial def genProductsRow (id : Nat) : Gen Row := do
  let name ← Gen.elements productNames >>= fun s => maybeNull (.string s)
  let price ← Gen.choose Int 10 300 >>= fun n => maybeNull (.int n)
  pure [("id", .int id), ("name", name), ("price", price)]

/-- Generate a RandomDb with 1–8 users, 0–6 orders, and 1–5 products (valid foreign keys). -/
private partial def genRandomDb : Gen RandomDb := do
  let numUsers ← Gen.choose Nat 1 8
  let users ← (List.range numUsers).mapM fun i => genUsersRow (i + 1)
  let numOrders ← Gen.choose Nat 0 6
  let orders ← (List.range numOrders).mapM fun i => do
    let uid ← Gen.choose Nat 1 numUsers
    genOrdersRow (i + 1) uid
  let numProducts ← Gen.choose Nat 1 5
  let prods ← (List.range numProducts).mapM fun i => genProductsRow (i + 1)
  pure ⟨users, orders, prods⟩

-- ============================================================================
-- SampleableExt and Shrinkable instances
-- ============================================================================

/-- Extract the integer value of a named field from a row, if present. -/
private def getIntField (row : Row) (field : String) : Option Int :=
  row.find? (·.1 == field) |>.bind fun (_, v) =>
    match v with | .int n => some n | _ => none

instance : Shrinkable RandomDb where
  shrink rdb :=
    -- Remove one user row at a time (also remove orders referencing that user),
    -- but never shrink below 1 user (matching the generator's minimum).
    (List.range rdb.users.length).filterMap (fun i =>
      let remainingUsers := rdb.users.take i ++ rdb.users.drop (i + 1)
      if remainingUsers.isEmpty then none
      else
        -- Safe: i < rdb.users.length is guaranteed by List.range
        let removedUser := rdb.users[i]!
        let removedId := getIntField removedUser "id"
        let remainingOrders := rdb.orders.filter fun row =>
          getIntField row "user_id" != removedId
        some ⟨remainingUsers, remainingOrders, rdb.products⟩) ++
    -- Remove one order row at a time
    (List.range rdb.orders.length).map (fun i =>
      ⟨rdb.users, rdb.orders.take i ++ rdb.orders.drop (i + 1), rdb.products⟩) ++
    -- Remove one product row at a time, but never shrink below 1 product
    (List.range rdb.products.length).filterMap (fun i =>
      let remainingProducts := rdb.products.take i ++ rdb.products.drop (i + 1)
      if remainingProducts.isEmpty then none
      else some ⟨rdb.users, rdb.orders, remainingProducts⟩)

instance : SampleableExt RandomDb :=
  SampleableExt.mkSelfContained genRandomDb

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Check optimizer correctness for a SelectStmt against a random database. -/
private def rdbSelectOk (rdb : RandomDb) (s : SelectStmt) : Bool :=
  selectOptOkDb rdb.toDb s

/-- Check optimizer correctness for a Query against a random database. -/
private def rdbQueryOk (rdb : RandomDb) (q : Query) : Bool :=
  queryOptOkDb rdb.toDb q

-- ============================================================================
-- Property tests: existing templates × random databases
-- ============================================================================

/-- A. Simple WHERE against random database. -/
private def randomDbWhereOk (rdb : RandomDb) (cmp : CmpOp) (age : AgeInt) : Bool :=
  rdbSelectOk rdb (mkWhereAge cmp.op age.val)

/-- B. JOIN against random database. -/
private def randomDbJoinOk (rdb : RandomDb) (jt : JoinType) (age : AgeInt) : Bool :=
  rdbSelectOk rdb (mkJoinQuery jt age.val)

/-- C. Subquery against random database. -/
private def randomDbSubqueryOk (rdb : RandomDb) (age : AgeInt) : Bool :=
  rdbSelectOk rdb (mkSubqueryWhere age.val)

/-- D. ORDER BY + LIMIT + OFFSET against random database. -/
private def randomDbOrderLimitOk (rdb : RandomDb) (lim off : SmallNat) : Bool :=
  rdbSelectOk rdb (mkOrderLimitOffset (some lim.val) (some off.val))

/-- E. DISTINCT against random database. -/
private def randomDbDistinctOk (rdb : RandomDb) (age : AgeInt) : Bool :=
  rdbSelectOk rdb (mkDistinctWhere age.val)

/-- F. UNION ALL against random database. -/
private def randomDbUnionOk (rdb : RandomDb) (a1 a2 : AgeInt) : Bool :=
  rdbQueryOk rdb (mkUnionAll a1.val a2.val)

/-- G. Projection against random database. -/
private def randomDbProjectionOk (rdb : RandomDb) (age : AgeInt) : Bool :=
  rdbSelectOk rdb (mkProjection age.val)

/-- H. Statement-level against random database. -/
private def randomDbStmtOk (rdb : RandomDb) (age : AgeInt) : Bool :=
  let sel := mkWhereAge .gt age.val
  let stmt := Stmt.query (.simple sel)
  let db := rdb.toDb
  (evalStmt db (optimize stmt)).2 == (evalStmt db stmt).2

-- ============================================================================
-- Anti-vacuity guards
-- ============================================================================

/-- Verify the generator produces non-trivial databases. -/
private def genProducesUsers (rdb : RandomDb) : Bool :=
  rdb.users.length > 0

/-- Check whether a table contains at least one NULL value. -/
private def tableHasNull (t : Table) : Bool :=
  t.any fun row => row.any fun (_, v) => match v with | .null _ => true | _ => false

def antiVacuityTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "generator produces non-empty users table" (∀ rdb : RandomDb, genProducesUsers rdb) $
  -- Deterministic: verify optimizer handles NULL-containing databases correctly
  test "optimizer handles database with NULLs" (
    let nullDb : RandomDb := ⟨
      [[("id", .int 1), ("name", .null none), ("age", .int 30), ("department", .null none)],
       [("id", .int 2), ("name", .string "Bob"), ("age", .null none), ("department", .string "Sales")]],
      [[("id", .int 1), ("user_id", .int 1), ("amount", .null none), ("product", .string "Widget")]],
      [[("id", .int 1), ("name", .null none), ("price", .int 50)]]
    ⟩
    -- Verify NULLs are present (anti-vacuity for the detector)
    tableHasNull nullDb.users &&
    -- Verify optimizer preserves semantics on NULL-containing data
    rdbSelectOk nullDb (mkWhereAge .gt 25) &&
    rdbSelectOk nullDb (mkJoinQuery .inner 25) &&
    rdbSelectOk nullDb (mkJoinQuery .left 20)
  )

-- ============================================================================
-- All random database tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Anti-Vacuity" (antiVacuityTests cfg) $
  group "Random DB" (
    check (cfg := cfg) "WHERE {cmp} {age} on random db" (∀ rdb : RandomDb, ∀ cmp : CmpOp, ∀ age : AgeInt, randomDbWhereOk rdb cmp age) $
    check (cfg := cfg) "JOIN {type} on random db" (∀ rdb : RandomDb, ∀ jt : JoinType, ∀ age : AgeInt, randomDbJoinOk rdb jt age) $
    check (cfg := cfg) "subquery on random db" (∀ rdb : RandomDb, ∀ age : AgeInt, randomDbSubqueryOk rdb age) $
    check (cfg := cfg) "ORDER BY LIMIT OFFSET on random db" (∀ rdb : RandomDb, ∀ lim off : SmallNat, randomDbOrderLimitOk rdb lim off) $
    check (cfg := cfg) "DISTINCT on random db" (∀ rdb : RandomDb, ∀ age : AgeInt, randomDbDistinctOk rdb age) $
    check (cfg := cfg) "UNION ALL on random db" (∀ rdb : RandomDb, ∀ a1 a2 : AgeInt, randomDbUnionOk rdb a1 a2) $
    check (cfg := cfg) "projection on random db" (∀ rdb : RandomDb, ∀ age : AgeInt, randomDbProjectionOk rdb age) $
    check (cfg := cfg) "stmt-level on random db" (∀ rdb : RandomDb, ∀ age : AgeInt, randomDbStmtOk rdb age)
  )

end RandomDb
