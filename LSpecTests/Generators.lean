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

/-- Build a SlimCheck configuration with the given sample count. -/
def mkSlimCfg (numSamples : Nat := defaultNumSamples) : Configuration :=
  { numInst := numSamples }

-- ============================================================================
-- Simple enum generators
-- ============================================================================

instance : Shrinkable BinOp where shrink _ := []

instance : SampleableExt BinOp :=
  SampleableExt.mkSelfContained $
    Gen.elements #[.add, .sub, .mul, .div, .mod, .eq, .ne, .lt, .le, .gt, .ge, .and, .or, .concat, .like]

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
    | .string s => if s.isEmpty then [] else [.string ""]
    | .bool _ => [.bool true, .bool false]
    | .null _ => []

instance : SampleableExt Value :=
  SampleableExt.mkSelfContained do
    let choice ← Gen.choose Nat 0 3
    match choice with
    | 0 => pure (.null none)
    | 1 => pure (.bool (← Gen.chooseAny Bool))
    | 2 => pure (.int (← SampleableExt.interpSample Int))
    | _ => do
      let n ← Gen.choose Nat 0 5
      pure (.string s!"s{n}")

-- ============================================================================
-- SqlType generator (for typed NULLs in three-valued logic tests)
-- ============================================================================

instance : Shrinkable SqlType where shrink _ := []

instance : SampleableExt SqlType :=
  SampleableExt.mkSelfContained $
    Gen.elements #[.int, .string, .bool, .unknown]

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
  SampleableExt.mkSelfContained (AgeInt.mk <$> Gen.choose Int 20 40)

/-- JoinType generator for query-level property tests. -/
instance : Shrinkable JoinType where shrink _ := []

instance : SampleableExt JoinType :=
  SampleableExt.mkSelfContained $
    Gen.elements #[JoinType.inner, .left, .right, .full, .cross]
