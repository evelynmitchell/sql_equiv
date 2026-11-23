/-
  SlimCheck generators for SQL types.

  Provides SampleableExt + Shrinkable instances for Value, BinOp, UnaryOp,
  and depth-bounded ground Expr types used in property-based testing.
-/
import LSpec
import SqlEquiv

open LSpec SlimCheck
open SqlEquiv

/-- Default sample count per property: 10,000 (100× SlimCheck's default of 100).
    Override at runtime via the `LSPEC_SAMPLES` environment variable.
    CI sets LSPEC_SAMPLES=100000 for thorough coverage. -/
def defaultNumSamples : Nat := 10000

/-- Run seed used when `LSPEC_SEED` is not set. Pull-request CI uses it, so a PR is tested on
    the same samples every time; the scheduled workflow passes a fresh seed (#395). -/
def defaultSeed : Nat := 0

/-- Build a SlimCheck configuration with the given sample count and run seed. -/
def mkSlimCfg (numSamples : Nat := defaultNumSamples) (seed : Nat := defaultSeed) : Configuration :=
  { numInst := numSamples, randomSeed := some seed }

/-- The seed of one property: the run seed mixed with the property's name, so that properties
    do not share a sample stream. (`String`'s hash is a fixed function, not salted per run;
    a toolchain that changed it would change which samples each seed draws.) -/
def propertySeed (runSeed : Nat) (descr : String) : Nat :=
  (mixHash (hash runSeed) (hash descr)).toNat

/-- Run a property's samples from its seed. Returns the result and the number of samples that
    passed before it. LSpec's own `check` ignores `cfg.randomSeed` and always starts from
    `mkStdGen`, so every run used to draw the same samples. -/
def seededResult (p : Prop) [Checkable p] (cfg : Configuration) (descr : String) :
    TestResult p × Nat :=
  let runSeed := cfg.randomSeed.getD defaultSeed
  (ReaderT.run (Checkable.runSuite p cfg) (.up (mkStdGen (propertySeed runSeed descr)))).1

abbrev instTestableSeeded (p : Prop) (cfg : Configuration) (descr : String) [Checkable p] :
    Testable p :=
  let runSeed := cfg.randomSeed.getD defaultSeed
  match seededResult p cfg descr with
  | (.success (.inr h), _) => .isTrue h
  | (.success (.inl _), numSamples) => .isPassed numSamples
  | (.gaveUp n, _) => .isFailure 0 cfg.numInst s!"Gave up {n} times"
  | (.failure h xs n, numSamples) =>
    .isFalse h (numSamples + 1) cfg.numInst <| Checkable.formatFailure
      s!"Found problems at sample {numSamples + 1}! Replay: LSPEC_SEED={runSeed} LSPEC_SAMPLES={cfg.numInst} lake exe sql_equiv_lspec"
      xs n

open SlimCheck Decorations in
/-- `LSpec.check` with the samples drawn from `cfg.randomSeed` and the property's name (#395).
    Every property test in this suite uses it. -/
def checkS (descr : String) (p : Prop) (next : TestSeq := .done) (cfg : Configuration := {})
    (propString : Option String := none)
    (p' : DecorationsOf p := by mk_decorations) [Checkable p'] : TestSeq :=
  haveI : Testable p' := instTestableSeeded p' cfg descr
  .individual descr p' propString inferInstance next

-- ============================================================================
-- Simple enum generators
-- ============================================================================

instance : Shrinkable BinOp where shrink _ := []

instance : SampleableExt BinOp :=
  SampleableExt.mkSelfContained $
    Gen.elements #[.add, .sub, .mul, .div, .mod, .eq, .ne, .lt, .le, .gt, .ge, .and, .or, .concat, .like, .likeCI]

instance : Shrinkable UnaryOp where shrink _ := []

instance : SampleableExt UnaryOp :=
  SampleableExt.mkSelfContained $
    Gen.elements #[.not, .neg, .isNull, .isNotNull]

-- ============================================================================
-- Value generator
-- ============================================================================

instance : Shrinkable Value where
  shrink
    | .int n => (Shrinkable.shrink n).map Value.int
    | .decimal u s => (Shrinkable.shrink u).map (Value.mkDecimal · s)
    | .string s => if s.isEmpty then [] else [.string ""]
    | .bool _ => [.bool true, .bool false]
    | .null _ => []

instance : SampleableExt Value :=
  SampleableExt.mkSelfContained do
    let choice ← Gen.choose Nat 0 4
    match choice with
    | 0 => pure (.null none)
    | 1 => pure (.bool (← Gen.chooseAny Bool))
    | 2 => pure (.int (← SampleableExt.interpSample Int))
    | 3 => do
      -- Canonical decimals (mkDecimal) over small unscaled values/scales,
      -- so generated data matches the system invariant (#201)
      let u ← SampleableExt.interpSample Int
      let sc ← Gen.choose Nat 0 3
      pure (Value.mkDecimal u sc)
    | _ => do
      let n ← Gen.choose Nat 0 5
      pure (.string s!"s{n}")

-- ============================================================================
-- SqlType generator (for typed NULLs in three-valued logic tests)
-- ============================================================================

instance : Shrinkable SqlType where shrink _ := []

instance : SampleableExt SqlType :=
  SampleableExt.mkSelfContained $
    Gen.elements #[.int, .string, .bool, .decimal, .unknown]

instance : Shrinkable (Option SqlType) where
  shrink _ := []

instance : SampleableExt (Option SqlType) :=
  SampleableExt.mkSelfContained do
    let choice ← Gen.choose Nat 0 4
    match choice with
    | 0 => pure none
    | 1 => pure (some SqlType.int)
    | 2 => pure (some SqlType.string)
    | 3 => pure (some SqlType.bool)
    | _ => pure (some SqlType.unknown)

-- ============================================================================
-- Ground expression generators (no column references)
-- ============================================================================

/-- A ground expression bounded to depth ~3 for property testing. -/
structure BoundedGroundExpr where
  expr : Expr
  deriving Repr

instance : Shrinkable BoundedGroundExpr where
  shrink bge := match bge.expr with
    | .binOp _ l r => [⟨l⟩, ⟨r⟩]
    | .unaryOp _ e => [⟨e⟩]
    | _ => []

private partial def genLitExpr : Gen Expr := do
  let v ← SampleableExt.interpSample Value
  pure (.lit v)

private partial def genGroundExpr (depth : Nat) : Gen Expr :=
  if depth == 0 then genLitExpr
  else Gen.frequency #[
    (4, genLitExpr),
    (3, do
      let op ← Gen.elements #[BinOp.and, .or, .add, .sub, .mul, .eq, .ne, .lt]
      let l ← genGroundExpr (depth - 1)
      let r ← genGroundExpr (depth - 1)
      pure (.binOp op l r)),
    (2, do
      let op ← Gen.elements #[UnaryOp.not, .neg, .isNull, .isNotNull]
      let e ← genGroundExpr (depth - 1)
      pure (.unaryOp op e)),
    (1, do
      let cond ← genGroundExpr (depth - 1)
      let thn ← genGroundExpr (depth - 1)
      let els ← genGroundExpr (depth - 1)
      pure (.case [(cond, thn)] (some els)))
  ] genLitExpr

instance : SampleableExt BoundedGroundExpr :=
  SampleableExt.mkSelfContained (BoundedGroundExpr.mk <$> genGroundExpr 3)

/-- Integer-valued ground expression for arithmetic identity properties. -/
structure IntGroundExpr where
  expr : Expr
  deriving Repr

instance : Shrinkable IntGroundExpr where
  shrink ige := match ige.expr with
    | .binOp _ l r => [⟨l⟩, ⟨r⟩]
    | _ => []

private partial def genIntGroundExpr (depth : Nat) : Gen Expr := do
  let genIntLit : Gen Expr := do
    let n ← SampleableExt.interpSample Int
    pure (Expr.lit (.int n))
  if depth == 0 then
    genIntLit
  else
    let d := depth - 1
    Gen.frequency #[
      (4, genIntLit),
      (2, do
        let l ← genIntGroundExpr d
        let r ← genIntGroundExpr d
        pure (Expr.binOp .add l r)),
      (2, do
        let l ← genIntGroundExpr d
        let r ← genIntGroundExpr d
        pure (Expr.binOp .mul l r)),
      (1, do
        let l ← genIntGroundExpr d
        let r ← genIntGroundExpr d
        pure (Expr.binOp .sub l r))
    ] genIntLit

instance : SampleableExt IntGroundExpr :=
  SampleableExt.mkSelfContained (IntGroundExpr.mk <$> genIntGroundExpr 2)

/-- Boolean-valued ground expression for boolean algebra properties. -/
structure BoolGroundExpr where
  expr : Expr
  deriving Repr

instance : Shrinkable BoolGroundExpr where
  shrink bge := match bge.expr with
    | .binOp _ l r => [⟨l⟩, ⟨r⟩]
    | .unaryOp _ e => [⟨e⟩]
    | _ => []

private partial def genBoolGroundExpr (depth : Nat) : Gen Expr := do
  let genBoolLit : Gen Expr := do
    let b ← Gen.chooseAny Bool
    pure (Expr.lit (.bool b))
  if depth == 0 then
    genBoolLit
  else
    let d := depth - 1
    Gen.frequency #[
      (3, genBoolLit),
      (2, do
        let l ← genBoolGroundExpr d
        let r ← genBoolGroundExpr d
        pure (Expr.binOp .and l r)),
      (2, do
        let l ← genBoolGroundExpr d
        let r ← genBoolGroundExpr d
        pure (Expr.binOp .or l r)),
      (1, do
        let e ← genBoolGroundExpr d
        pure (Expr.unaryOp .not e)),
      (1, do
        let l ← genIntGroundExpr d
        let r ← genIntGroundExpr d
        pure (Expr.binOp .eq l r))
    ] genBoolLit

instance : SampleableExt BoolGroundExpr :=
  SampleableExt.mkSelfContained (BoolGroundExpr.mk <$> genBoolGroundExpr 2)

-- ============================================================================
-- Column-aware expression generator
-- ============================================================================

/-- Ground expression that may reference columns from a fixed 3-column schema. -/
structure ColumnGroundExpr where
  expr : Expr
  deriving Repr

instance : Shrinkable ColumnGroundExpr where
  shrink cge := match cge.expr with
    | .binOp _ l r => [⟨l⟩, ⟨r⟩]
    | .unaryOp _ e => [⟨e⟩]
    | _ => []

private partial def genColumnExpr (depth : Nat) : Gen Expr :=
  if depth == 0 then
    Gen.frequency #[
      (3, genLitExpr),
      (1, pure (.col ⟨none, "x"⟩)),
      (1, pure (.col ⟨none, "y"⟩)),
      (1, pure (.col ⟨none, "z"⟩))
    ] genLitExpr
  else Gen.frequency #[
    (3, genLitExpr),
    (2, do
      let idx ← Gen.choose Nat 0 2
      let col := ["x", "y", "z"].getD idx "x"
      pure (.col ⟨none, col⟩)),
    (2, do
      let op ← Gen.elements #[BinOp.and, .or, .add, .sub, .eq, .lt]
      let l ← genColumnExpr (depth - 1)
      let r ← genColumnExpr (depth - 1)
      pure (.binOp op l r)),
    (1, do
      let op ← Gen.elements #[UnaryOp.not, .neg, .isNull]
      let e ← genColumnExpr (depth - 1)
      pure (.unaryOp op e))
  ] genLitExpr

instance : SampleableExt ColumnGroundExpr :=
  SampleableExt.mkSelfContained (ColumnGroundExpr.mk <$> genColumnExpr 2)

-- ============================================================================
-- Query-level test generators
-- ============================================================================

/-- Comparison operators for WHERE clauses. -/
structure CmpOp where
  op : BinOp
  deriving Repr

instance : Shrinkable CmpOp where shrink _ := []

instance : Inhabited CmpOp := ⟨⟨.eq⟩⟩

instance : SampleableExt CmpOp :=
  SampleableExt.mkSelfContained $
    Gen.elements #[⟨.eq⟩, ⟨.ne⟩, ⟨.lt⟩, ⟨.le⟩, ⟨.gt⟩, ⟨.ge⟩]

/-- Small Nat (0..10) for LIMIT/OFFSET. -/
structure SmallNat where
  val : Nat
  deriving Repr

instance : Shrinkable SmallNat where
  shrink sn := (Shrinkable.shrink sn.val).map SmallNat.mk

instance : SampleableExt SmallNat :=
  SampleableExt.mkSelfContained (SmallNat.mk <$> Gen.choose Nat 0 10)

/-- Bounded Int (20..40) matching users.age range for meaningful filtering. -/
structure AgeInt where
  val : Int
  deriving Repr

instance : Shrinkable AgeInt where shrink _ := []

instance : SampleableExt AgeInt :=
  -- a `Nat` offset: `Gen.choose Int` does not keep to its bounds
  SampleableExt.mkSelfContained (do pure (AgeInt.mk (20 + Int.ofNat (← Gen.choose Nat 0 20))))

/-- JoinType generator for query-level property tests. -/
instance : Shrinkable JoinType where shrink _ := []

instance : SampleableExt JoinType :=
  SampleableExt.mkSelfContained $
    Gen.elements #[JoinType.inner, .left, .right, .full, .cross]

-- ============================================================================
-- Random databases (#245)
-- ============================================================================

/-- Contents of the fixed test schema, generated at random (#245):
    `users(id, name, age, department)`, `orders(id, user_id, amount, product)`,
    `products(id, name, price)` (the `QueryHelpers.testDb` schema) and the rewriter sweep's
    `t(a)`. Schema-driven: random contents, not random schemas, so queries stay meaningful. -/
structure GenDb where
  users : Table
  orders : Table
  products : Table
  t : Table
  deriving Repr

/-- The database a `GenDb` stands for; any other table is empty. -/
def GenDb.db (g : GenDb) : Database := fun n =>
  if n == "users" then g.users
  else if n == "orders" then g.orders
  else if n == "products" then g.products
  else if n == "t" then g.t
  else []

/-- Smaller versions of a table, most aggressive first: empty, each half, then each way of
    dropping one row. -/
private def dropOneRow (rs : Table) : List Table :=
  (if rs.length ≥ 2 then [[], rs.take (rs.length / 2), rs.drop (rs.length / 2)] else []) ++
  (List.range rs.length).map rs.eraseIdx

/-- Each way of making one non-NULL cell NULL. -/
private def nullOneCell (rs : Table) : List Table :=
  (List.range rs.length).flatMap fun i =>
    let row := rs.getD i []
    (List.range row.length).filterMap fun j =>
      match row.getD j ("", .null none) with
      | (_, .null _) => none
      | (k, _) => some (rs.set i (row.set j (k, .null none)))

/-- Shrink by dropping rows first, then by replacing values with NULL. LSpec takes a single
    shrink step (the recursive call in `SlimCheck.minimizeAux` is commented out), choosing the
    first candidate that still fails, so the candidates come most aggressive first. -/
instance : Shrinkable GenDb where
  shrink g :=
    (dropOneRow g.users).map ({ g with users := · }) ++
    (dropOneRow g.orders).map ({ g with orders := · }) ++
    (dropOneRow g.products).map ({ g with products := · }) ++
    (dropOneRow g.t).map ({ g with t := · }) ++
    (nullOneCell g.users).map ({ g with users := · }) ++
    (nullOneCell g.orders).map ({ g with orders := · }) ++
    (nullOneCell g.t).map ({ g with t := · })

/-- A row count of 0 to 6; 0 and 1 are common. -/
private def genRowCount : Gen Nat :=
  Gen.frequency #[(2, pure 0), (2, pure 1), (5, Gen.choose Nat 2 6)] (pure 0)

/-- NULL (typed `ty` or untyped) with probability `pct`%, else a value from `g`. -/
private def genNullOr (pct : Nat) (ty : SqlType) (g : Gen Value) : Gen Value := do
  if (← Gen.choose Nat 0 99) < pct then
    pure (.null (if ← Gen.chooseAny Bool then some ty else none))
  else g

/-- An integer in `lo..hi` (drawn as a `Nat` offset: `Gen.choose Int` does not keep to its
    bounds). -/
private def genSmallInt (lo hi : Int) : Gen Value := do
  pure (.int (lo + Int.ofNat (← Gen.choose Nat 0 (hi - lo).toNat)))

/-- An amount or price: usually an integer, sometimes an exact decimal. -/
private def genMoney : Gen Value :=
  Gen.frequency #[
    (3, genSmallInt 0 300),
    (1, do pure (Value.mkDecimal (Int.ofNat (← Gen.choose Nat 0 3000)) 1))] (genSmallInt 0 300)

private def genFrom (xs : Array String) : Gen Value := do
  pure (.string (← Gen.elements xs))

/-- Ids `1..n`, unique, or drawn from a small range so that duplicates are common. -/
private def genIds (n : Nat) : Gen (List Value) := do
  if ← Gen.chooseAny Bool then pure ((List.range n).map fun i => .int (Int.ofNat i + 1))
  else (List.range n).mapM fun _ => genSmallInt 1 3

/-- With probability 1/3, `rs` plus a copy of one of its rows. -/
private def withDuplicate (rs : Table) : Gen Table := do
  if rs.isEmpty || (← Gen.choose Nat 0 2) != 0 then pure rs
  else pure (rs ++ [rs.getD (← Gen.choose Nat 0 (rs.length - 1)) []])

def genGenDb : Gen GenDb := do
  -- users: ids sometimes duplicated, rarely NULL
  let nu ← genRowCount
  let uids ← genIds nu
  let users ← uids.mapM fun id => do
    let id ← genNullOr 5 .int (pure id)
    let name ← genNullOr 10 .string (genFrom #["Alice", "Bob", "Carol", "Dave"])
    let age ← genNullOr 15 .int (genSmallInt 18 40)
    let dept ← genNullOr 10 .string (genFrom #["Engineering", "Sales", "Marketing"])
    pure [("id", id), ("name", name), ("age", age), ("department", dept)]
  -- orders: user_id mostly an existing user id, sometimes dangling or NULL
  let no ← genRowCount
  let oids ← genIds no
  let orders ← oids.mapM fun id => do
    let uid ← Gen.frequency #[
      (7, if uids.isEmpty then pure (.int 99) else Gen.elements uids.toArray),
      (2, pure (.int 99)),
      (1, pure (.null (some .int)))] (pure (.int 99))
    let amount ← genNullOr 10 .int genMoney
    let product ← genNullOr 10 .string (genFrom #["Widget", "Gadget", "Gizmo"])
    pure [("id", id), ("user_id", uid), ("amount", amount), ("product", product)]
  -- products
  let np ← genRowCount
  let products ← (List.range np).mapM fun i => do
    let name ← genFrom #["Widget", "Gadget", "Gizmo"]
    let price ← genNullOr 10 .int genMoney
    pure [("id", .int (Int.ofNat i + 1)), ("name", name), ("price", price)]
  -- t(a): the rewriter sweep's subquery table
  let nt ← genRowCount
  let t ← (List.range nt).mapM fun _ => do
    pure [("a", ← genNullOr 15 .int (genSmallInt 0 6))]
  -- sometimes an exact copy of a row, so DISTINCT and bag semantics have something to do
  let users ← withDuplicate users
  let orders ← withDuplicate orders
  let t ← withDuplicate t
  pure { users, orders, products, t }

instance : SampleableExt GenDb := SampleableExt.mkSelfContained genGenDb

/-- `n` databases drawn from a fixed seed: the batch the vacuity guards and mutant checks of the
    database properties run over (#245). -/
def genDbBatch (n : Nat) (seed : Nat := 245) : List GenDb :=
  (ReaderT.run ((List.range n).mapM fun _ => genGenDb) (ULift.up 10)).run' (ULift.up (mkStdGen seed))
