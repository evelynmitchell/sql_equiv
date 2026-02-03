# Integrating LSpec Property-Based Testing into sql_equiv

This document describes how to incorporate LSpec property-based testing alongside the existing test suite, with a workflow for capturing shrunk counterexamples as permanent unit tests.

## Overview

### Goals

1. **Run LSpec separately** from the existing test suite (`lake exe sql_equiv_test`)
2. **Discover edge cases** through randomized property testing
3. **Capture shrunk counterexamples** as permanent regression tests in the regular unit test suite
4. **Maintain two complementary testing approaches**:
   - Fast, deterministic unit tests for CI (existing suite)
   - Longer-running property tests for deeper exploration (LSpec)

### Why This Approach?

Property-based testing excels at finding unexpected edge cases, but:
- It's non-deterministic (different runs may find different issues)
- It can be slow (running thousands of test cases)
- Shrinking takes time but produces minimal failing examples

By capturing shrunk counterexamples as unit tests, we get:
- **Reproducibility**: The exact failing case is preserved
- **Speed**: Unit tests run instantly in CI
- **Documentation**: Each captured test documents a discovered edge case
- **Regression prevention**: The bug can never silently return

## Setup

### 1. Add LSpec Dependency

Update `lakefile.toml`. Pin dependencies to immutable commit SHAs rather than
mutable branch names to ensure reproducible builds and avoid supply-chain risks:

```toml
name = "sql_equiv"
version = "0.1.0"
defaultTargets = ["sql_equiv"]

[[require]]
name = "batteries"
git = "https://github.com/leanprover-community/batteries"
rev = "45926c76c3e0d876e39b3e9e5e77080fef0b10ba"

[[require]]
name = "LSpec"
git = "https://github.com/argumentcomputer/LSpec"
rev = "1e6da63a9c92473747e816d07d5c6f6bc7c8a59e"

[[lean_lib]]
name = "SqlEquiv"

[[lean_lib]]
name = "Test"
globs = ["Test.*"]

[[lean_lib]]
name = "LSpecTests"
globs = ["LSpecTests.*"]

[[lean_exe]]
name = "sql_equiv"
root = "Main"

[[lean_exe]]
name = "sql_equiv_test"
root = "Test.Main"

# Separate executable for LSpec property tests
[[lean_exe]]
name = "sql_equiv_lspec"
root = "LSpecTests.Main"
```

> **Dependency pinning**: Always use full commit SHAs in `rev` fields, not branch
> names like `"main"`. Branch references are mutable — a force push or compromised
> upstream could silently change what you build. To update a dependency, run
> `lake update <dep>` and commit the new SHA from `lake-manifest.json`.

### 2. Fetch Dependencies

```bash
lake update LSpec
lake build
```

## Project Structure

```
sql_equiv/
├── SqlEquiv/                    # Main library (unchanged)
├── Test/                        # Existing unit test suite (unchanged)
│   ├── Main.lean
│   ├── Common.lean
│   ├── ParserTest.lean
│   ├── SemanticsTest.lean
│   ├── EquivTest.lean
│   ├── PropertyTest.lean        # Existing custom property tests
│   ├── OptimizerTest.lean
│   ├── ExprNormalizationTest.lean
│   ├── PredicatePushdownTest.lean
│   └── RegressionTest.lean      # NEW: Captured counterexamples go here
│
├── LSpecTests/                  # NEW: LSpec property test suite
│   ├── Main.lean                # LSpec test runner (uses lspecIO)
│   ├── Generators.lean          # SampleableExt / Shrinkable instances
│   ├── ExprProperties.lean      # Expression properties
│   ├── ParserProperties.lean    # Parser round-trip properties
│   ├── SemanticsProperties.lean # Semantic equivalence properties
│   └── OptimizerProperties.lean # Optimizer correctness properties
│
└── docs/
    └── LSPEC_INTEGRATION.md     # This document
```

## Implementation Guide

### Step 1: Create SampleableExt and Shrinkable Instances

LSpec uses SlimCheck for property-based testing. To generate random instances of
your types, implement the `SampleableExt` and `Shrinkable` typeclasses.

`SampleableExt` provides random generation; `Shrinkable` enables counterexample
minimization. Together they give you `Checkable` instances for universally
quantified propositions like `∀ (x : MyType), prop x`.

Create `LSpecTests/Generators.lean`:

```lean
-- LSpecTests/Generators.lean
import LSpec
import SqlEquiv

open SqlEquiv  -- All types (Value, Expr, Row, etc.) are in SqlEquiv namespace
open LSpec.SlimCheck

namespace LSpecTests.Generators

-- ============================================================================
-- Value: Generation and Shrinking
-- ============================================================================

-- Value has constructors: int, string, bool, null (no float).
-- The null constructor takes `Option SqlType` — `none` means unknown type.
instance : Repr Value where
  reprPrec v _ := match v with
    | .int n => s!"Value.int {repr n}"
    | .string s => s!"Value.string {repr s}"
    | .bool b => s!"Value.bool {repr b}"
    | .null t => s!"Value.null {repr t}"

instance : Shrinkable Value where
  shrink v := match v with
    | .int n => (Shrinkable.shrink n).map .int
    | .string s => (Shrinkable.shrink s).map .string
    | .bool _ => [.null none]
    | .null _ => []

instance : SampleableExt Value :=
  SampleableExt.mkSelfContained do
    let choice ← Gen.chooseAny Bool
    if choice then
      -- Generate non-null values
      let kind ← Gen.choose Int 0 2
      match kind with
      | 0 => return .bool (← Gen.chooseAny Bool)
      | 1 => return .int (← Gen.chooseAny Int)
      | _ => return .string (← Gen.chooseAny String)
    else
      -- Generate NULL (~50% of the time to stress NULL handling)
      return .null none

-- ============================================================================
-- ColumnRef: Generation and Shrinking
-- ============================================================================

instance : Repr ColumnRef where
  reprPrec c _ := s!"⟨{repr c.table}, {repr c.column}⟩"

instance : Shrinkable ColumnRef where
  shrink _ := []

def genColumnName : Gen String :=
  Gen.elements #["id", "name", "value", "count", "flag", "col"]

def genColumnRef : Gen ColumnRef := do
  let colName ← genColumnName
  return { table := none, column := colName }

-- ============================================================================
-- Row: Generation and Shrinking
-- ============================================================================

-- A Row is List (String × Value). We generate small rows with known columns.
instance : SampleableExt Row :=
  SampleableExt.mkSelfContained do
    let numCols ← Gen.choose Nat 0 3
    let mut row : Row := []
    for _ in List.range numCols do
      let col ← genColumnName
      let v ← SampleableExt.sample (α := Value)
      row := (col, v) :: row
    return row

-- ============================================================================
-- Expr: Generation and Shrinking
-- ============================================================================

-- IMPORTANT: NULL semantics in this codebase
--
-- There are TWO representations of NULL in `Option Value`:
--   1. `some (.null _)` — an explicit NULL literal (e.g., from `Expr.lit (.null none)`)
--   2. `none` — evaluation failure or NULL propagation through operators
--
-- When evalExpr evaluates `.lit (.null none)`, it returns `some (.null none)`.
-- But when that value flows into a binary/unary operator (e.g., AND, NOT),
-- the operator may not match it and returns `none` instead.
--
-- This means: `evalExpr row (NOT (lit NULL))` = `none`
--             `evalExpr row (lit NULL)` = `some (.null none)`
-- These are NOT equal, even though both represent "null" conceptually.
--
-- Properties must account for this. See ExprProperties.lean for strategies.

instance : Repr Expr where
  reprPrec e _ := match e with
    | .lit v => s!"Expr.lit {repr v}"
    | .col c => s!"Expr.col {repr c}"
    | .binOp op l r => s!"Expr.binOp {repr op} ({repr l}) ({repr r})"
    | .unaryOp op e => s!"Expr.unaryOp {repr op} ({repr e})"
    | _ => "Expr.«complex»"

instance : Shrinkable Expr where
  shrink e := match e with
    | .binOp _ l r => [l, r]
    | .unaryOp _ inner => [inner]
    | .«case» branches _ =>
      branches.filterMap (fun (_, r) => some r)
    | .lit (.int n) => (Shrinkable.shrink n).map (fun n => .lit (.int n))
    | .lit (.string s) => (Shrinkable.shrink s).map (fun s => .lit (.string s))
    | _ => []

-- Generate boolean-valued expressions (for boolean property testing).
-- This avoids type mismatches where AND/OR/NOT receive non-boolean operands
-- and fall through to `none`.
partial def genBoolExpr (depth : Nat := 3) : Gen Expr := do
  if depth == 0 then
    -- Base case: boolean literal or boolean-producing comparison
    let choice ← Gen.choose Nat 0 1
    match choice with
    | 0 => return .lit (.bool (← Gen.chooseAny Bool))
    | _ =>
      -- Generate a comparison that produces a Bool result
      let a ← Gen.chooseAny Int
      let b ← Gen.chooseAny Int
      return .binOp .eq (.lit (.int a)) (.lit (.int b))
  else
    let choice ← Gen.choose Nat 0 4
    match choice with
    | 0 => return .lit (.bool (← Gen.chooseAny Bool))
    | 1 => do
        let op ← Gen.elements #[BinOp.and, .or]
        let left ← genBoolExpr (depth - 1)
        let right ← genBoolExpr (depth - 1)
        return .binOp op left right
    | 2 => do
        let inner ← genBoolExpr (depth - 1)
        return .unaryOp .not inner
    | 3 => do
        -- Comparison of two int literals (always produces a Bool)
        let a ← Gen.chooseAny Int
        let b ← Gen.chooseAny Int
        let op ← Gen.elements #[BinOp.eq, .ne, .lt, .le, .gt, .ge]
        return .binOp op (.lit (.int a)) (.lit (.int b))
    | _ => return .lit (.bool (← Gen.chooseAny Bool))

-- Generate arbitrary expressions (may include NULLs and type mismatches).
-- Use this for properties that are expected to hold for ALL inputs.
partial def genExpr (depth : Nat := 3) : Gen Expr := do
  if depth == 0 then
    let choice ← Gen.choose Nat 0 2
    match choice with
    | 0 => return .lit (← SampleableExt.sample (α := Value))
    | 1 => return .col (← genColumnRef)
    | _ => return .lit (.null none)
  else
    let choice ← Gen.choose Nat 0 5
    match choice with
    | 0 => return .lit (← SampleableExt.sample (α := Value))
    | 1 => return .col (← genColumnRef)
    | 2 => do
        let op ← Gen.elements #[BinOp.and, .or, .eq, .ne, .lt, .gt, .le, .ge, .add, .sub, .mul]
        let left ← genExpr (depth - 1)
        let right ← genExpr (depth - 1)
        return .binOp op left right
    | 3 => do
        let op ← Gen.elements #[UnaryOp.not, .neg, .isNull, .isNotNull]
        let inner ← genExpr (depth - 1)
        return .unaryOp op inner
    | 4 => do
        let cond ← genBoolExpr (depth - 1)
        let thenE ← genExpr (depth - 1)
        let elseE ← genExpr (depth - 1)
        return .«case» [(cond, thenE)] (some elseE)
    | _ => return .lit (.null none)

instance : SampleableExt Expr :=
  SampleableExt.mkSelfContained (genExpr 3)

-- A wrapper type for boolean-only expressions, used in properties
-- that require boolean-valued inputs (identity laws, De Morgan's, etc.)
structure BoolExpr where
  expr : Expr
  deriving Repr

instance : Shrinkable BoolExpr where
  shrink be := (Shrinkable.shrink be.expr).map BoolExpr.mk

instance : SampleableExt BoolExpr :=
  SampleableExt.mkSelfContained do
    let e ← genBoolExpr 3
    return ⟨e⟩

end LSpecTests.Generators
```

### Step 2: Define Properties

Create property modules for different areas. Example `LSpecTests/ExprProperties.lean`:

```lean
-- LSpecTests/ExprProperties.lean
import LSpec
import SqlEquiv
import LSpecTests.Generators

open SqlEquiv  -- evalExpr, Expr, Value, Row, BinOp, UnaryOp, etc.
open LSpecTests.Generators

namespace LSpecTests.ExprProperties

/-!
## NULL handling strategy for properties

`evalExpr` returns `Option Value`. There are two null representations:
- `none`: operator couldn't evaluate (type mismatch, NULL propagation)
- `some (.null _)`: explicit NULL literal

When `Expr.lit (.null none)` is evaluated, it returns `some (.null none)`.
But passing that through operators (AND, NOT, etc.) typically yields `none`
because the operator's pattern match doesn't handle `.null`.

### Consequence for properties

Properties like `x AND true == x` FAIL when `x` evaluates to `some (.null _)`:
  - LHS: `evalBinOp .and (some (.null none)) (some (.bool true))` → `none`
  - RHS: `some (.null none)`
  - `none ≠ some (.null none)` → property fails

### Strategies used here

1. **Commutativity / annihilator properties**: Hold for ALL inputs because
   both sides go through the same operator and produce the same `none`/value.

2. **Identity / De Morgan's / double negation**: Only hold when operands
   evaluate to actual booleans. We use `BoolExpr` (from Generators.lean) to
   restrict inputs to boolean-valued expressions.

3. **NULL-specific properties**: Explicitly test NULL behavior to document
   the semantics (e.g., "NULL AND TRUE produces none").
-/

-- Helper: normalize the dual NULL representation for comparison.
-- Treats `some (.null _)` as `none` so both null forms are equal.
def normalizeNull : Option Value → Option Value
  | some (.null _) => none
  | other => other

-- ============================================================================
-- Properties that hold for ALL inputs (including NULLs)
-- ============================================================================

-- AND is commutative (holds universally: both sides produce the same result)
def prop_and_commutative (a b : Expr) (row : Row) : Bool :=
  evalExpr row (.binOp .and a b) == evalExpr row (.binOp .and b a)

-- OR is commutative
def prop_or_commutative (a b : Expr) (row : Row) : Bool :=
  evalExpr row (.binOp .or a b) == evalExpr row (.binOp .or b a)

-- x AND false == false (short-circuit matches `_, some (.bool false)`)
def prop_and_annihilator (a : Expr) (row : Row) : Bool :=
  evalExpr row (.binOp .and a (.lit (.bool false))) == some (.bool false)

-- x OR true == true (short-circuit matches `_, some (.bool true)`)
def prop_or_annihilator (a : Expr) (row : Row) : Bool :=
  evalExpr row (.binOp .or a (.lit (.bool true))) == some (.bool true)

-- EQ is commutative (Value.eq is symmetric)
def prop_eq_commutative (a b : Expr) (row : Row) : Bool :=
  evalExpr row (.binOp .eq a b) == evalExpr row (.binOp .eq b a)

-- ============================================================================
-- Properties restricted to boolean-valued expressions
-- These use BoolExpr to avoid NULL/type-mismatch false positives
-- ============================================================================

-- x AND true == x (only holds when x evaluates to a Bool, not NULL)
def prop_and_identity (a : BoolExpr) (row : Row) : Bool :=
  evalExpr row (.binOp .and a.expr (.lit (.bool true))) == evalExpr row a.expr

-- x OR false == x
def prop_or_identity (a : BoolExpr) (row : Row) : Bool :=
  evalExpr row (.binOp .or a.expr (.lit (.bool false))) == evalExpr row a.expr

-- Double negation: NOT (NOT x) == x
def prop_double_negation (a : BoolExpr) (row : Row) : Bool :=
  evalExpr row (.unaryOp .not (.unaryOp .not a.expr)) == evalExpr row a.expr

-- De Morgan's: NOT (a AND b) == (NOT a) OR (NOT b)
def prop_demorgan_and (a b : BoolExpr) (row : Row) : Bool :=
  evalExpr row (.unaryOp .not (.binOp .and a.expr b.expr)) ==
  evalExpr row (.binOp .or (.unaryOp .not a.expr) (.unaryOp .not b.expr))

-- De Morgan's: NOT (a OR b) == (NOT a) AND (NOT b)
def prop_demorgan_or (a b : BoolExpr) (row : Row) : Bool :=
  evalExpr row (.unaryOp .not (.binOp .or a.expr b.expr)) ==
  evalExpr row (.binOp .and (.unaryOp .not a.expr) (.unaryOp .not b.expr))

-- ============================================================================
-- NULL-specific properties (document actual semantics)
-- ============================================================================

-- NULL propagation: operations on NULL produce none, not some(.null _)
def prop_null_and_produces_none (a : Expr) (row : Row) : Bool :=
  let result := evalExpr row (.binOp .and (.lit (.null none)) a)
  -- Result is either none (NULL propagated) or some (.bool false) (short-circuit)
  result == none || result == some (.bool false)

-- IS NULL correctly identifies both null representations
def prop_is_null_detects_null_lit (row : Row) : Bool :=
  evalExpr row (.unaryOp .isNull (.lit (.null none))) == some (.bool true)

end LSpecTests.ExprProperties
```

### Step 3: Create the LSpec Test Runner

LSpec provides `lspecIO` as the main entry point for compiled test executables.
Tests are built as `TestSeq` chains using `test` (for decidable propositions)
and `checkIO` (for property-based tests evaluated at runtime).

Create `LSpecTests/Main.lean`:

```lean
-- LSpecTests/Main.lean
import LSpec
import SqlEquiv
import LSpecTests.Generators
import LSpecTests.ExprProperties

open LSpec
open SqlEquiv
open LSpecTests.Generators
open LSpecTests.ExprProperties

/-!
# LSpec Property-Based Test Suite

This suite runs randomized property tests to discover edge cases.
When a test fails, LSpec/SlimCheck will shrink the counterexample to
a minimal reproducing case.

## Running

```
lake exe sql_equiv_lspec                    # run all suites
lake exe sql_equiv_lspec -- expr            # run only "expr" suite
```

## Capturing Counterexamples

When you find a failing case, add it to `Test/RegressionTest.lean`
using the shrunk counterexample. See the "Counterexample Workflow"
section in docs/LSPEC_INTEGRATION.md.
-/

-- Build test sequences using LSpec's TestSeq API.
-- `group` nests tests; `checkIO` runs SlimCheck at runtime.
-- Each `checkIO` call generates random inputs, checks the property,
-- and shrinks any counterexample found.

def commutativityTests : TestSeq :=
  group "Commutativity" $
    checkIO "AND is commutative"
      (∀ (a b : Expr) (row : Row), prop_and_commutative a b row = true) $
    checkIO "OR is commutative"
      (∀ (a b : Expr) (row : Row), prop_or_commutative a b row = true) $
    checkIO "EQ is commutative"
      (∀ (a b : Expr) (row : Row), prop_eq_commutative a b row = true)
      .done

def identityTests : TestSeq :=
  group "Identity Laws (bool inputs only)" $
    checkIO "x AND true == x"
      (∀ (a : BoolExpr) (row : Row), prop_and_identity a row = true) $
    checkIO "x OR false == x"
      (∀ (a : BoolExpr) (row : Row), prop_or_identity a row = true)
      .done

def annihilatorTests : TestSeq :=
  group "Annihilator Laws" $
    checkIO "x AND false == false"
      (∀ (a : Expr) (row : Row), prop_and_annihilator a row = true) $
    checkIO "x OR true == true"
      (∀ (a : Expr) (row : Row), prop_or_annihilator a row = true)
      .done

def demorganTests : TestSeq :=
  group "De Morgan's Laws (bool inputs only)" $
    checkIO "NOT (a AND b) == (NOT a) OR (NOT b)"
      (∀ (a b : BoolExpr) (row : Row), prop_demorgan_and a b row = true) $
    checkIO "NOT (a OR b) == (NOT a) AND (NOT b)"
      (∀ (a b : BoolExpr) (row : Row), prop_demorgan_or a b row = true)
      .done

def doubleNegationTests : TestSeq :=
  group "Double Negation (bool inputs only)" $
    checkIO "NOT (NOT x) == x"
      (∀ (a : BoolExpr) (row : Row), prop_double_negation a row = true)
      .done

def nullTests : TestSeq :=
  group "NULL Semantics" $
    checkIO "NULL AND x produces none or false"
      (∀ (a : Expr) (row : Row), prop_null_and_produces_none a row = true) $
    test "IS NULL detects null literal"
      (prop_is_null_detects_null_lit [] = true)
      .done

-- lspecIO takes a HashMap of suite name → test list, plus CLI args for filtering.
-- Use @[test_driver] to register with `lake test`.
def main (args : List String) : IO UInt32 := do
  lspecIO
    (Std.HashMap.ofList [
      ("expr", [
        commutativityTests,
        identityTests,
        annihilatorTests,
        demorganTests,
        doubleNegationTests,
        nullTests
      ])
    ])
    args
```

### Step 4: Create the Regression Test File

Create `Test/RegressionTest.lean` to hold captured counterexamples:

```lean
-- Test/RegressionTest.lean
import SqlEquiv
import Test.Common

open SqlEquiv  -- All types and functions are in SqlEquiv namespace
open Test      -- Test.Common defines namespace Test with TestResult, runTests, etc.

/-!
# Regression Tests from LSpec Counterexamples

This file contains minimal test cases discovered by LSpec property testing.
Each test represents a shrunk counterexample that revealed a bug or edge case.

## Adding New Tests

When LSpec finds a failing property and shrinks it, add the counterexample here:

1. Copy the shrunk expression/values from LSpec output
2. Create a new test function with a descriptive name
3. Include a comment noting which property failed and when

Example:
```
-- Found 2024-01-15: prop_double_negation failed with NULL handling
def test_double_neg_null : TestResult :=
  let nullExpr := Expr.lit (.null none)  -- NULL literal
  let expr := Expr.unaryOp .not (.unaryOp .not nullExpr)
  let row := []
  let result := evalExpr row expr
  let expected := evalExpr row nullExpr
  if result == expected then .pass "double_neg_null"
  else .fail "double_neg_null" s!"Expected {expected}, got {result}"
```
-/

-- Following the pattern of other test modules (ParserTest, SemanticsTest, etc.)
namespace RegressionTest

-- ============================================================================
-- NULL Handling Edge Cases
-- ============================================================================

-- Placeholder: Add NULL-related counterexamples here
-- Example discovered edge case:
-- def test_null_and_true : TestResult :=
--   let nullExpr := Expr.lit (.null none)
--   let trueExpr := Expr.lit (.bool true)
--   let expr := Expr.binOp .and nullExpr trueExpr
--   let result := evalExpr [] expr
--   -- NULL AND TRUE → none (not some (.null _))
--   -- This is because evalBinOp .and doesn't match (.null _) as a boolean
--   match result with
--   | none => .pass "null_and_true"
--   | other => .fail "null_and_true" s!"Expected none, got {other}"

-- ============================================================================
-- Arithmetic Edge Cases
-- ============================================================================

-- Placeholder: Add arithmetic counterexamples here

-- ============================================================================
-- String Handling Edge Cases
-- ============================================================================

-- Placeholder: Add string counterexamples here

-- ============================================================================
-- Test Runner
-- ============================================================================

def regressionTests : List TestResult := [
  -- Add tests here as they are discovered
  -- test_null_and_true,
  -- test_division_by_zero,
  -- etc.
]

-- Use the existing runTests helper from Test.Common instead of reimplementing
def runRegressionTests : IO (Nat × Nat) := do
  Test.runTests "Regression Tests (LSpec Counterexamples)" regressionTests

end RegressionTest
```

### Step 5: Wire Regression Tests into Main Suite

Update `Test/Main.lean` to include regression tests:

```lean
-- Add import
import Test.RegressionTest

-- Add to main function, after other test suites:
let _ ← RegressionTest.runRegressionTests
```

## Workflow: Capturing Counterexamples

### The Process

```
┌─────────────────────────────────────────────────────────────────┐
│                    LSpec Discovery Workflow                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. Run LSpec        lake exe sql_equiv_lspec                   │
│         │                                                        │
│         ▼                                                        │
│  2. Property fails   "prop_and_identity failed"                 │
│         │                                                        │
│         ▼                                                        │
│  3. LSpec shrinks    Finds minimal counterexample:              │
│         │            a = Expr.lit (.null none)                   │
│         │            row = []                                    │
│         ▼                                                        │
│  4. Investigate      Is this a bug or expected behavior?        │
│         │                                                        │
│         ├─── Bug ───► Fix the code, then add regression test    │
│         │                                                        │
│         └─ Expected ► Update property preconditions or document │
│                                                                  │
│  5. Add to           Test/RegressionTest.lean                   │
│     unit tests       (prevents regression)                       │
│                                                                  │
│  6. CI runs fast     lake exe sql_equiv_test                    │
│     deterministic    (includes captured counterexamples)         │
│     tests                                                        │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Example: From Failure to Regression Test

**Step 1**: Run LSpec and observe failure

```bash
$ lake exe sql_equiv_lspec

  ✗ Identity Laws (bool inputs only) > x AND true == x
    Found a counter-example!
    a := BoolExpr.mk (Expr.lit (Value.null none))
    row := []
    issue: true ≠ false
```

**Step 2**: Investigate

This reveals that when `x` evaluates to `some (.null none)`, the expression
`x AND true` evaluates to `none` (because `evalBinOp .and` doesn't match
`(.null _)` as a boolean operand). Meanwhile `x` itself evaluates to
`some (.null none)`. The two are not equal.

This is expected SQL three-valued logic behavior — but it means our property
needs a precondition. We restrict to `BoolExpr` inputs (see Step 2 above).

If instead this revealed an actual bug (e.g., `NOT NULL` returning `false`
instead of `NULL`):

**Step 3**: Fix the bug in `SqlEquiv/Semantics.lean`

**Step 4**: Add regression test to `Test/RegressionTest.lean`

```lean
-- Found 2024-01-15: NOT NULL was returning false instead of NULL
-- Bug was in evalUnaryOp .not — it fell through to none for NULL
-- but we expected some (.null none) per SQL standard
def test_not_null_returns_null : TestResult :=
  let nullExpr := Expr.lit (.null none)
  let expr := Expr.unaryOp .not nullExpr
  let result := evalExpr [] expr
  -- In current implementation, NOT NULL → none (operator doesn't match)
  -- If we wanted SQL-standard behavior, it should be some (.null none)
  match result with
  | none => .pass "not_null_returns_null"
  | other => .fail "not_null_returns_null"
      s!"NOT NULL should be none, got {other}"
```

**Step 5**: Verify both suites pass

```bash
$ lake exe sql_equiv_test      # Fast, deterministic (includes new regression tests)
$ lake exe sql_equiv_lspec     # Randomized (should now pass)
```

## Running the Test Suites

### Commands

```bash
# Build everything
lake build

# Run fast deterministic tests (CI)
lake exe sql_equiv_test

# Run LSpec property tests (exploratory)
lake exe sql_equiv_lspec

# Run only a specific test suite (e.g., "expr")
lake exe sql_equiv_lspec -- expr
```

### CI Configuration

Keep the existing CI workflow for fast tests. Add a separate workflow for LSpec:

```yaml
# .github/workflows/lspec.yml
name: LSpec Property Tests

on:
  schedule:
    - cron: '0 0 * * 0'  # Weekly on Sundays
  workflow_dispatch:      # Manual trigger

jobs:
  lspec:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install elan
        run: |
          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
          echo "$HOME/.elan/bin" >> $GITHUB_PATH

      - name: Cache Lake packages
        uses: actions/cache@v4
        with:
          path: .lake
          key: lake-lspec-${{ hashFiles('lakefile.toml') }}-${{ hashFiles('lean-toolchain') }}

      - name: Build LSpec tests
        run: lake build sql_equiv_lspec

      - name: Run LSpec property tests
        run: lake exe sql_equiv_lspec
```

## Best Practices

### 1. Property Design

Write properties that test **semantic invariants**, not implementation details:

```lean
-- Good: Tests a mathematical property
def prop_addition_commutative (a b : Expr) (row : Row) : Bool :=
  evalExpr row (.binOp .add a b) == evalExpr row (.binOp .add b a)

-- Bad: Tests implementation detail
def prop_uses_hashmap_internally : Bool := ...
```

### 2. NULL Awareness

The dual NULL representation (`none` vs `some (.null _)`) is a major source of
property failures. Apply these guidelines:

| Property type | NULL-safe? | Strategy |
|---|---|---|
| Commutativity (`f(a,b) == f(b,a)`) | Yes | Both sides use same operator → same result |
| Annihilators (`x AND false == false`) | Yes | Short-circuit patterns match regardless of LHS |
| Identity (`x AND true == x`) | **No** | Use `BoolExpr` to restrict to boolean inputs |
| Involution (`NOT (NOT x) == x`) | **No** | Use `BoolExpr` to restrict to boolean inputs |
| De Morgan's laws | **No** | Use `BoolExpr` to restrict to boolean inputs |

If you want to test a property across ALL inputs including NULLs, use the
`normalizeNull` helper to collapse both null representations:

```lean
def prop_with_null_normalization (a : Expr) (row : Row) : Bool :=
  normalizeNull (evalExpr row (transform a)) == normalizeNull (evalExpr row a)
```

### 3. Generator Quality

Use `SampleableExt.mkSelfContained` with weighted generation to cover edge cases:

```lean
-- Good: Weighted toward edge cases, uses actual Gen combinators
instance : SampleableExt Value :=
  SampleableExt.mkSelfContained do
    let choice ← Gen.choose Nat 0 10
    match choice with
    | 0 => return .null none           -- NULL (important edge case)
    | 1 => return .int 0               -- Zero (edge case)
    | 2 => return .string ""           -- Empty string (edge case)
    | 3 | 4 | 5 => return .bool (← Gen.chooseAny Bool)
    | 6 | 7 | 8 => return .int (← Gen.chooseAny Int)
    | _ => return .string (← Gen.chooseAny String)
```

### 4. Shrinking

LSpec's shrinking works best when types have `Shrinkable` instances that
produce structurally smaller values:

```lean
instance : Shrinkable Value where
  shrink v := match v with
    | .int n => (Shrinkable.shrink n).map .int
    | .string s => (Shrinkable.shrink s).map .string
    | .bool _ => [.null none]
    | .null _ => []  -- Can't shrink further
```

For `Expr`, shrink by extracting subexpressions:

```lean
instance : Shrinkable Expr where
  shrink e := match e with
    | .binOp _ l r => [l, r]         -- Try each operand alone
    | .unaryOp _ inner => [inner]    -- Try the inner expression
    | _ => []
```

### 5. Regression Test Naming

Use descriptive names that indicate the origin:

```lean
-- Good: Clear origin and purpose
def test_lspec_null_and_true_three_valued_logic : TestResult := ...
def test_lspec_empty_string_comparison : TestResult := ...

-- Bad: Unclear
def test1 : TestResult := ...
def test_bug_fix : TestResult := ...
```

### 6. Documentation

Document each regression test with:
- Date discovered
- Which property failed
- Brief explanation of the edge case

```lean
/--
Found: 2024-01-15
Property: prop_demorgan_and
Issue: De Morgan's law doesn't hold when operands are NULL
       because NOT NULL → none, but we compared against some (.null _)
Fix: Restricted property to BoolExpr inputs
-/
def test_demorgan_with_nulls : TestResult := ...
```

## Appendix: LSpec API Reference

> **Note**: Based on LSpec commit `1e6da63` (Jan 2026). Consult the
> [LSpec repository](https://github.com/argumentcomputer/LSpec) if the
> API has changed.

### Core Types

```lean
-- Test sequence (the fundamental test structure)
inductive TestSeq
  | individual : String → (prop : Prop) → Testable prop → TestSeq → TestSeq
  | individualIO : String → IO (Bool × Option String) → TestSeq → TestSeq
  | group : String → TestSeq → TestSeq → TestSeq
  | done

-- Testable: resolves a Prop to pass/fail
class inductive Testable (p : Prop) where
  | isTrue (h : p)
  | isPassed (msg : Option String := none)
  | isMaybe (msg : Option String := none)
  | isFalse (h : ¬ p) (msg : Option String := none)
  | isFailure (msg : Option String := none)
```

### Key Functions

```lean
-- Compile-time test (proposition must be Decidable)
def test (descr : String) (p : Prop) [Testable p]
    (next : TestSeq := .done) : TestSeq

-- Property-based test via SlimCheck (compile-time, fixed seed)
def check (descr : String) (p : Prop) (next : TestSeq := .done)
    (cfg : Configuration := {}) [Checkable p'] : TestSeq

-- Property-based test via SlimCheck (runtime, random seed)
def checkIO (descr : String) (p : Prop) (next : TestSeq := .done)
    (cfg : Configuration := {}) [Checkable p'] : TestSeq

-- Grouping
def group (descr : String) (groupTests : TestSeq)
    (next : TestSeq := .done) : TestSeq

-- Main entry point for compiled test executables
def lspecIO (map : HashMap String (List TestSeq))
    (args : List String) : IO UInt32

-- Generator monad (ReaderT over Rand with a size parameter)
abbrev Gen (α : Type u) := ReaderT (ULift Nat) Rand α

-- Basic generator combinators
def Gen.chooseAny (α : Type u) [Random α] [DefaultRange α] : Gen α
def Gen.choose (α : Type u) [Random α] (lo hi : α) : Gen α
def Gen.elements [Inhabited α] (xs : Array α) : Gen α
def Gen.frequency (weighted : Array (Nat × Gen α)) (fallback : Gen α) : Gen α
def Gen.oneOf [Inhabited α] (xs : Array (Gen α)) : Gen α
def Gen.listOf (x : Gen α) : Gen (List α)
def Gen.arrayOf (x : Gen α) : Gen (Array α)

-- SampleableExt: how to generate random instances for property testing
class SampleableExt (α : Sort u) where
  proxy : Type v
  sample : Gen proxy
  interp : proxy → α

-- Shrinkable: how to minimize counterexamples
class Shrinkable (α : Type u) where
  shrink : (x : α) → List α := fun _ => []
```

### Adapting to API Changes

LSpec's `test`, `check`, `checkIO`, and `group` all take an optional `next`
parameter (defaulting to `.done`) for chaining. Use `$` to chain:

```lean
-- Chaining tests:
def myTests : TestSeq :=
  test "basic check" (1 + 1 = 2) $
  checkIO "property" (∀ n : Nat, n + 0 = n) $
  .done

-- Nesting groups:
def allTests : TestSeq :=
  group "Arithmetic" myTests $
  group "Other" otherTests $
  .done
```

## Summary

| Aspect | Existing Suite | LSpec Suite |
|--------|---------------|-------------|
| **Purpose** | Fast CI validation | Edge case discovery |
| **Determinism** | Deterministic | Randomized |
| **Speed** | Fast (~seconds) | Slower (~minutes) |
| **When to run** | Every commit | Weekly / on-demand |
| **Failure handling** | Fix immediately | Shrink → capture → fix |
| **Location** | `Test/` | `LSpecTests/` |
| **Command** | `lake exe sql_equiv_test` | `lake exe sql_equiv_lspec` |

The two approaches complement each other: LSpec discovers new edge cases through randomization, and the captured counterexamples become permanent regression tests that run quickly in CI.
