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

/-- Structural shrinking: drop WHERE, simplify projection, remove ORDER BY/LIMIT/OFFSET. -/
private def shrinkRandomQuery (q : RandomQuery) : List RandomQuery :=
  match q.stmt with
  | .mk distinct items from_ where_ groupBy having orderBy limit offset =>
    let mk := fun d i w ob l o => RandomQuery.mk (.mk d i from_ w groupBy having ob l o)
    -- Drop WHERE clause
    (if where_.isSome then [mk distinct items none orderBy limit offset] else []) ++
    -- Replace projection with SELECT *
    (match items with | [.star none] => [] | _ => [mk distinct [.star none] where_ orderBy limit offset]) ++
    -- Drop ORDER BY
    (if !orderBy.isEmpty then [mk distinct items where_ [] limit offset] else []) ++
    -- Drop LIMIT
    (if limit.isSome then [mk distinct items where_ orderBy none offset] else []) ++
    -- Drop OFFSET
    (if offset.isSome then [mk distinct items where_ orderBy limit none] else []) ++
    -- Drop DISTINCT
    (if distinct then [mk false items where_ orderBy limit offset] else [])

instance : Shrinkable RandomQuery where
  shrink q := shrinkRandomQuery q

instance : SampleableExt RandomQuery :=
  SampleableExt.mkSelfContained genRandomQuery

-- ============================================================================
-- Random JOIN query generator
-- ============================================================================

/-- A randomly generated JOIN query over users × orders. -/
structure RandomJoinQuery where
  stmt : SelectStmt
  deriving Repr

/-- Combined schema for JOIN queries. -/
private def joinSchema : Array ColMeta := usersSchema ++ ordersSchema

/-- Generate a random JOIN query over users × orders. -/
private partial def genRandomJoinQuery : Gen RandomJoinQuery := do
  let jt ← Gen.elements #[JoinType.inner, .left, .right, .full, .cross]
  let items ← genProjection joinSchema
  let fkCond := Expr.binOp .eq (qcol "users" "id") (qcol "orders" "user_id")
  let onCond ← if jt == .cross then
      pure none
    else
      Gen.frequency #[
        (3, pure (some fkCond)),
        (1, some <$> genWherePred joinSchema 0)
      ] (pure (some fkCond))
  let where_ ← Gen.frequency #[
    (3, some <$> genWherePred joinSchema 2),
    (1, pure none)
  ] (pure none)
  let usersFrom := FromClause.table ⟨"users", none⟩
  let ordersFrom := FromClause.table ⟨"orders", none⟩
  let joinFrom := FromClause.join usersFrom jt ordersFrom onCond
  pure ⟨.mk false items (some joinFrom) where_ [] none [] none none⟩

/-- Structural shrinking for JOIN queries. -/
private def shrinkRandomJoinQuery (q : RandomJoinQuery) : List RandomJoinQuery :=
  match q.stmt with
  | .mk distinct items from_ where_ groupBy having orderBy limit offset =>
    let mk := fun d i f w => RandomJoinQuery.mk (.mk d i f w groupBy having orderBy limit offset)
    -- Drop WHERE clause
    (if where_.isSome then [mk distinct items from_ none] else []) ++
    -- Replace projection with SELECT *
    (match items with | [.star none] => [] | _ => [mk distinct [.star none] from_ where_]) ++
    -- Downgrade to INNER JOIN (simplest join type)
    (match from_ with
     | some (.join l jt r on_) =>
       if jt != .inner then
         [mk distinct items (some (.join l .inner r on_)) where_]
       else []
     | _ => []) ++
    -- Drop DISTINCT
    (if distinct then [mk false items from_ where_] else [])

instance : Shrinkable RandomJoinQuery where
  shrink q := shrinkRandomJoinQuery q

instance : SampleableExt RandomJoinQuery :=
  SampleableExt.mkSelfContained genRandomJoinQuery

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

/-- Core property: random JOIN query + optimizer preserves semantics on testDb. -/
private def randomJoinQueryOptOk (q : RandomJoinQuery) : Bool :=
  selectOptOkDb testDb q.stmt

/-- Cross-product: random JOIN query × random database. -/
private def randomJoinQueryRandomDbOk (q : RandomJoinQuery) (rdb : RandomDb.RandomDb) : Bool :=
  selectOptOkDb rdb.toDb q.stmt

/-- Idempotence of optimizer on random JOIN queries. -/
private def randomJoinQueryIdempotent (q : RandomJoinQuery) : Bool :=
  optimizeSelectStmt (optimizeSelectStmt q.stmt) == optimizeSelectStmt q.stmt

-- ============================================================================
-- Anti-vacuity
-- ============================================================================

/-- Verify the infrastructure works with known queries. -/
def antiVacuityTests : TestSeq :=
  test "random query infrastructure: SELECT * returns rows" (
    let q : RandomQuery := ⟨mkSelectWhere "users" none⟩
    (evalSelect testDb q.stmt).length > 0) $
  test "random JOIN query infrastructure: INNER JOIN returns rows" (
    let joinStmt := (mkJoinQuery .inner 20)
    (evalSelect testDb joinStmt).length > 0)

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
  ) $
  group "Random JOIN Queries" (
    check (cfg := cfg) "random JOIN query preserves semantics (testDb)" (∀ q : RandomJoinQuery, randomJoinQueryOptOk q) $
    check (cfg := cfg) "random JOIN query preserves semantics (random db)" (∀ q : RandomJoinQuery, ∀ rdb : RandomDb.RandomDb, randomJoinQueryRandomDbOk q rdb) $
    check (cfg := cfg) "random JOIN query optimizer is idempotent" (∀ q : RandomJoinQuery, randomJoinQueryIdempotent q)
  )

end QueryGen
