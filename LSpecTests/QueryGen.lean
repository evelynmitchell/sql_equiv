/-
  Tier 3C: Schema-aware query generation.

  Generates random WHERE predicates, projections, and full queries that
  reference valid columns with type-compatible literals. Tests optimizer
  correctness with structurally diverse queries beyond the fixed templates.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators
import LSpecTests.QueryHelpers
import LSpecTests.RandomDb

open LSpec SlimCheck
open SqlEquiv
open QueryHelpers

namespace QueryGen

-- ============================================================================
-- Schema definition
-- ============================================================================

/-- Column metadata for schema-aware generation. -/
private structure ColMeta where
  name : String
  qualifier : String
  typ : SqlType
  deriving Inhabited

private def usersSchema : Array ColMeta := #[
  ⟨"id", "users", .int⟩,
  ⟨"name", "users", .string⟩,
  ⟨"age", "users", .int⟩,
  ⟨"department", "users", .string⟩
]

private def ordersSchema : Array ColMeta := #[
  ⟨"id", "orders", .int⟩,
  ⟨"user_id", "orders", .int⟩,
  ⟨"amount", "orders", .int⟩,
  ⟨"product", "orders", .string⟩
]

-- ============================================================================
-- Type-compatible literal generator
-- ============================================================================

/-- Generate a literal expression compatible with a given SQL type. -/
private partial def genLitForType (typ : SqlType) : Gen Expr := do
  match typ with
  | .int => do
    let n ← Gen.choose Int 0 100
    pure (.lit (.int n))
  | .string => do
    let s ← Gen.elements #["Alice", "Bob", "Carol", "Dave", "Eve",
                            "Engineering", "Sales", "Marketing", "HR",
                            "Widget", "Gadget", "Gizmo"]
    pure (.lit (.string s))
  | .bool => do
    let b ← Gen.chooseAny Bool
    pure (.lit (.bool b))
  | .unknown => pure (.lit (.null none))

-- ============================================================================
-- Schema-aware WHERE predicate generator
-- ============================================================================

/-- Generate a WHERE predicate referencing valid columns with type-matched literals. -/
private partial def genWherePred (schema : Array ColMeta) (depth : Nat) : Gen Expr := do
  if depth == 0 then
    -- Leaf: column {cmp} literal (type-matched)
    let cm ← Gen.elements schema
    let cmpOp ← Gen.elements #[BinOp.eq, .ne, .lt, .le, .gt, .ge]
    let lit ← genLitForType cm.typ
    pure (.binOp cmpOp (.col ⟨some cm.qualifier, cm.name⟩) lit)
  else
    Gen.frequency #[
      (3, genWherePred schema 0),
      (2, do
        let l ← genWherePred schema (depth - 1)
        let r ← genWherePred schema (depth - 1)
        pure (.binOp .and l r)),
      (1, do
        let l ← genWherePred schema (depth - 1)
        let r ← genWherePred schema (depth - 1)
        pure (.binOp .or l r)),
      (1, do
        let inner ← genWherePred schema (depth - 1)
        pure (.unaryOp .not inner))
    ] (genWherePred schema 0)

-- ============================================================================
-- Schema-aware projection generator
-- ============================================================================

/-- Generate a random projection (subset of columns or star). -/
private partial def genProjection (schema : Array ColMeta) : Gen (List SelectItem) := do
  let useStar ← Gen.chooseAny Bool
  if useStar then pure [.star none]
  else do
    -- Pick each column with 50% probability
    let mut selected : List SelectItem := []
    for cm in schema do
      let pick ← Gen.chooseAny Bool
      if pick then
        selected := SelectItem.exprItem (.col ⟨some cm.qualifier, cm.name⟩) (some cm.name) :: selected
    let result := selected.reverse
    -- Fallback to * if nothing was selected
    pure (if result.isEmpty then [.star none] else result)

-- ============================================================================
-- Full query generator
-- ============================================================================

/-- A randomly generated query with valid schema references. -/
structure RandomQuery where
  stmt : SelectStmt
  deriving Repr

/-- Generate a random query against the users table. -/
private partial def genRandomQuery : Gen RandomQuery := do
  let items ← genProjection usersSchema
  let where_ ← Gen.frequency #[
    (3, some <$> genWherePred usersSchema 2),
    (1, pure none)
  ] (pure none)
  let orderBy ← Gen.frequency #[
    (2, pure []),
    (1, do
      let cm ← Gen.elements usersSchema
      let dir ← Gen.elements #[OrderDir.asc, .desc]
      pure [OrderByItem.mk (.col ⟨some cm.qualifier, cm.name⟩) dir])
  ] (pure [])
  let limit ← Gen.frequency #[
    (2, pure none),
    (1, some <$> Gen.choose Nat 0 10)
  ] (pure none)
  let offset ← Gen.frequency #[
    (3, pure none),
    (1, some <$> Gen.choose Nat 0 5)
  ] (pure none)
  let distinct ← Gen.chooseAny Bool
  pure ⟨.mk distinct items (some (.table ⟨"users", none⟩)) where_ [] none orderBy limit offset⟩

instance : Shrinkable RandomQuery where
  shrink _ := []

instance : SampleableExt RandomQuery :=
  SampleableExt.mkSelfContained genRandomQuery

-- ============================================================================
-- Property tests
-- ============================================================================

/-- Core property: random query + optimizer preserves semantics on testDb. -/
private def randomQueryOptOk (q : RandomQuery) : Bool :=
  selectOptOkDb testDb q.stmt

/-- Cross-product: random query × random database. -/
private def randomQueryRandomDbOk (q : RandomQuery) (rdb : RandomDb.RandomDb) : Bool :=
  selectOptOkDb rdb.toDb q.stmt

/-- Idempotence of optimizer on random queries. -/
private def randomQueryIdempotent (q : RandomQuery) : Bool :=
  optimizeSelectStmt (optimizeSelectStmt q.stmt) == optimizeSelectStmt q.stmt

/-- Column preservation on random queries. -/
private def randomQueryColPreserved (q : RandomQuery) : Bool :=
  let orig := evalSelect testDb q.stmt
  let opt := evalSelect testDb (optimizeSelectStmt q.stmt)
  match orig.head?, opt.head? with
  | some origRow, some optRow => origRow.map (·.1) == optRow.map (·.1)
  | none, none => true  -- both empty, column names trivially equal
  | _, _ => true  -- cardinality mismatches are checked by randomQueryOptOk

-- ============================================================================
-- Anti-vacuity
-- ============================================================================

/-- Verify the infrastructure works with a known query. -/
def antiVacuityTests : TestSeq :=
  test "random query infrastructure: SELECT * returns rows" (
    let q : RandomQuery := ⟨mkSelectWhere "users" none⟩
    (evalSelect testDb q.stmt).length > 0)

-- ============================================================================
-- All schema-aware query tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Anti-Vacuity" antiVacuityTests $
  group "Random Queries" (
    check (cfg := cfg) "random query preserves semantics (testDb)" (∀ q : RandomQuery, randomQueryOptOk q) $
    check (cfg := cfg) "random query preserves semantics (random db)" (∀ q : RandomQuery, ∀ rdb : RandomDb.RandomDb, randomQueryRandomDbOk q rdb) $
    check (cfg := cfg) "random query optimizer is idempotent" (∀ q : RandomQuery, randomQueryIdempotent q) $
    check (cfg := cfg) "random query preserves column names" (∀ q : RandomQuery, randomQueryColPreserved q)
  )

end QueryGen
