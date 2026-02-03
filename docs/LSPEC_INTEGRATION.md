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

Update `lakefile.toml`:

```toml
name = "sql_equiv"
version = "0.1.0"
defaultTargets = ["sql_equiv"]

[[require]]
name = "batteries"
git = "https://github.com/leanprover-community/batteries"
rev = "main"

[[require]]
name = "LSpec"
git = "https://github.com/argumentcomputer/LSpec"
rev = "main"

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
│   ├── Main.lean                # LSpec test runner
│   ├── Generators.lean          # Gen instances for SqlEquiv types
│   ├── ExprProperties.lean      # Expression properties
│   ├── ParserProperties.lean    # Parser round-trip properties
│   ├── SemanticsProperties.lean # Semantic equivalence properties
│   └── OptimizerProperties.lean # Optimizer correctness properties
│
└── docs/
    └── LSPEC_INTEGRATION.md     # This document
```

## Implementation Guide

### Step 1: Create Generator Instances

Create `LSpecTests/Generators.lean` with `Gen` instances for your types:

```lean
-- LSpecTests/Generators.lean
import LSpec
import SqlEquiv

open LSpec
open SqlEquiv  -- Note: SqlEquiv is the main namespace (not SqlEquiv.Ast)

namespace LSpecTests.Generators

-- Generate random SQL values
-- Note: Value has constructors: int, string, bool, null (no float)
instance : Gen Value where
  gen := do
    let choice ← Gen.chooseNat 0 3
    match choice with
    | 0 => return .null none          -- NULL with unknown type
    | 1 => return .bool (← Gen.bool)  -- Boolean
    | 2 => return .int (← Gen.int)    -- Integer
    | _ => return .string (← Gen.string)  -- String

-- Generate random column names
def genColumnName : Gen String := do
  let prefixes := #["id", "name", "value", "count", "flag", "col"]
  let idx ← Gen.chooseNat 0 (prefixes.size - 1)
  let suffix ← Gen.chooseNat 0 9
  return s!"{prefixes[idx]!}{suffix}"

-- Generate a ColumnRef (table qualifier is optional)
def genColumnRef : Gen ColumnRef := do
  let colName ← genColumnName
  return { table := none, column := colName }

-- Generate random expressions (with bounded depth to avoid infinite recursion)
-- Note: Expr constructors are: lit, col, binOp, unaryOp, func, agg, countStar, «case», etc.
-- The case constructor uses «» because 'case' is a Lean keyword
partial def genExpr (depth : Nat := 3) : Gen Expr := do
  if depth == 0 then
    -- Base cases only at depth 0
    let choice ← Gen.chooseNat 0 2
    match choice with
    | 0 => return .lit (← Gen.gen)           -- Literal value
    | 1 => return .col (← genColumnRef)      -- Column reference
    | _ => return .lit (.null none)          -- NULL literal
  else
    let choice ← Gen.chooseNat 0 6
    match choice with
    | 0 => return .lit (← Gen.gen)
    | 1 => return .col (← genColumnRef)
    | 2 => return .lit (.null none)
    | 3 => do
        -- BinOp: ne (not neq), and other operators
        let op ← Gen.elements #[BinOp.and, .or, .eq, .ne, .lt, .gt, .le, .ge, .add, .sub, .mul]
        let left ← genExpr (depth - 1)
        let right ← genExpr (depth - 1)
        return .binOp op left right
    | 4 => do
        let op ← Gen.elements #[UnaryOp.not, .neg, .isNull, .isNotNull]
        let inner ← genExpr (depth - 1)
        return .unaryOp op inner
    | 5 => do
        let cond ← genExpr (depth - 1)
        let thenE ← genExpr (depth - 1)
        let elseE ← genExpr (depth - 1)
        return .«case» [(cond, thenE)] (some elseE)  -- CASE expression
    | _ => return .lit (.null none)

instance : Gen Expr where
  gen := genExpr 3

-- Generate a row (list of column name/value pairs)
def genRow (columns : List String) : Gen Row := do
  let values ← columns.mapM fun col => do
    let v ← Gen.gen
    return (col, v)
  return values

-- Generate a simple table schema and data
def genTable (numRows : Nat := 5) : Gen (List String × List Row) := do
  let numCols ← Gen.chooseNat 1 5
  let cols ← (List.range numCols).mapM fun _ => genColumnName
  let rows ← (List.range numRows).mapM fun _ => genRow cols
  return (cols, rows)

end LSpecTests.Generators
```

### Step 2: Define Properties

Create property modules for different areas. Example `LSpecTests/ExprProperties.lean`:

```lean
-- LSpecTests/ExprProperties.lean
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec
open SqlEquiv  -- All types (Expr, Value, Row, etc.) and functions (evalExpr) are in SqlEquiv namespace

namespace LSpecTests.ExprProperties

/-!
Note: evalExpr returns `Option Value`, not `Value` directly.

For logical laws (AND, OR, NOT), the evaluator only returns boolean
results when both operands evaluate to `some (.bool _)`. If either
operand is non-boolean or `none`, the result is `none`. To avoid
noisy counterexamples from type mismatches, we use helper functions
that skip the comparison when operands aren't boolean.
-/

/-- Compare two evaluated expressions as booleans.
    Returns true iff both are `some (.bool v)` and the `Bool`s are equal.
    If either side is non-boolean or `none`, we treat the property
    as not applicable and return `true` to avoid noisy failures. -/
def boolEq (x y : Option Value) : Bool :=
  match x, y with
  | some (.bool vx), some (.bool vy) => vx == vy
  | _, _ => true

/-- Check that an evaluated expression is a given boolean value.
    Returns true iff the result is `some (.bool v)` with `v == b`.
    If evaluation fails or yields a non-boolean, we return `true`
    so that the property only constrains genuinely boolean cases. -/
def isBoolVal (b : Bool) (x : Option Value) : Bool :=
  match x with
  | some (.bool v) => v == b
  | _ => true

-- Property: AND is commutative (when both sides are boolean)
def prop_and_commutative (a b : Expr) (row : Row) : Bool :=
  boolEq
    (evalExpr row (.binOp .and a b))
    (evalExpr row (.binOp .and b a))

-- Property: OR is commutative (when both sides are boolean)
def prop_or_commutative (a b : Expr) (row : Row) : Bool :=
  boolEq
    (evalExpr row (.binOp .or a b))
    (evalExpr row (.binOp .or b a))

-- Property: Double negation elimination
-- Note: Only checked when the expression evaluates to a boolean.
-- Does not hold for NULL or non-boolean expressions (NOT returns none for those).
def prop_double_negation (a : Expr) (row : Row) : Bool :=
  boolEq
    (evalExpr row (.unaryOp .not (.unaryOp .not a)))
    (evalExpr row a)

-- Property: x AND true == x (for boolean-typed x)
def prop_and_identity (a : Expr) (row : Row) : Bool :=
  boolEq
    (evalExpr row (.binOp .and a (.lit (.bool true))))
    (evalExpr row a)

-- Property: x OR false == x (for boolean-typed x)
def prop_or_identity (a : Expr) (row : Row) : Bool :=
  boolEq
    (evalExpr row (.binOp .or a (.lit (.bool false))))
    (evalExpr row a)

-- Property: x AND false == false (for boolean-typed x)
def prop_and_annihilator (a : Expr) (row : Row) : Bool :=
  isBoolVal false
    (evalExpr row (.binOp .and a (.lit (.bool false))))

-- Property: x OR true == true (for boolean-typed x)
def prop_or_annihilator (a : Expr) (row : Row) : Bool :=
  isBoolVal true
    (evalExpr row (.binOp .or a (.lit (.bool true))))

-- Property: De Morgan's law: NOT (a AND b) == (NOT a) OR (NOT b)
-- Checked only when both sides evaluate to booleans.
def prop_demorgan_and (a b : Expr) (row : Row) : Bool :=
  boolEq
    (evalExpr row (.unaryOp .not (.binOp .and a b)))
    (evalExpr row (.binOp .or (.unaryOp .not a) (.unaryOp .not b)))

-- Property: De Morgan's law: NOT (a OR b) == (NOT a) AND (NOT b)
-- Checked only when both sides evaluate to booleans.
def prop_demorgan_or (a b : Expr) (row : Row) : Bool :=
  boolEq
    (evalExpr row (.unaryOp .not (.binOp .or a b)))
    (evalExpr row (.binOp .and (.unaryOp .not a) (.unaryOp .not b)))

end LSpecTests.ExprProperties
```

### Step 3: Create the LSpec Test Runner

Create `LSpecTests/Main.lean`:

```lean
-- LSpecTests/Main.lean
import LSpec
import SqlEquiv
import LSpecTests.Generators
import LSpecTests.ExprProperties

open LSpec
open SqlEquiv  -- All types are in SqlEquiv namespace
open LSpecTests.Generators
open LSpecTests.ExprProperties

/-!
# LSpec Property-Based Test Suite

This suite runs randomized property tests to discover edge cases.
When a test fails, LSpec will shrink the counterexample to a minimal
reproducing case.

## Capturing Counterexamples

When you find a failing case, add it to `Test/RegressionTest.lean`
using the shrunk counterexample. See the "Counterexample Workflow"
section in docs/LSPEC_INTEGRATION.md.
-/

-- Default configuration for property tests
def defaultConfig : LSpec.Config := {
  numTests := 1000      -- Number of random tests per property
  maxShrinks := 100     -- Maximum shrinking iterations
  seed := none          -- Use random seed (or set for reproducibility)
}

/-- Read test configuration from environment variables, falling back to defaults.
    Supports LSPEC_NUM_TESTS and LSPEC_SEED for CLI overrides. -/
def readConfig : IO LSpec.Config := do
  let mut config := defaultConfig
  if let some numTests ← IO.getEnv "LSPEC_NUM_TESTS" then
    if let some n := numTests.toNat? then
      config := { config with numTests := n }
  if let some seed ← IO.getEnv "LSPEC_SEED" then
    if let some s := seed.toNat? then
      config := { config with seed := some s }
  return config

def main : IO UInt32 := do
  let testConfig ← readConfig
  IO.println "╔═══════════════════════════════════════════╗"
  IO.println "║   SQL Equiv LSpec Property Test Suite     ║"
  IO.println "╠═══════════════════════════════════════════╣"
  IO.println "║  Running randomized property tests...     ║"
  IO.println "║  Failures will be shrunk automatically.   ║"
  IO.println "╚═══════════════════════════════════════════╝"
  IO.println ""

  -- Run property tests
  -- Note: Actual LSpec API may vary; adapt to current version
  -- Groups are nested within lists, not concatenated with ++
  let suite := LSpec.group "Expression Properties" [
    LSpec.group "Commutativity" [
      LSpec.check "AND is commutative" (∀ a b row, prop_and_commutative a b row),
      LSpec.check "OR is commutative" (∀ a b row, prop_or_commutative a b row)
    ],
    LSpec.group "Identity Laws" [
      LSpec.check "x AND true == x" (∀ a row, prop_and_identity a row),
      LSpec.check "x OR false == x" (∀ a row, prop_or_identity a row)
    ],
    LSpec.group "Annihilator Laws" [
      LSpec.check "x AND false == false" (∀ a row, prop_and_annihilator a row),
      LSpec.check "x OR true == true" (∀ a row, prop_or_annihilator a row)
    ],
    LSpec.group "De Morgan's Laws" [
      LSpec.check "NOT (a AND b) == (NOT a) OR (NOT b)" (∀ a b row, prop_demorgan_and a b row),
      LSpec.check "NOT (a OR b) == (NOT a) AND (NOT b)" (∀ a b row, prop_demorgan_or a b row)
    ],
    LSpec.group "Double Negation" [
      LSpec.check "NOT (NOT x) == x" (∀ a row, prop_double_negation a row)
    ]
  ]

  let result ← LSpec.runWith testConfig suite

  if result.failures.isEmpty then
    IO.println "\n✓ All property tests passed!"
    return 0
  else
    IO.println "\n✗ Some tests failed. Shrunk counterexamples:"
    for (name, counterexample) in result.failures do
      IO.println s!"  - {name}:"
      IO.println s!"    {counterexample}"
      IO.println ""
    IO.println "Add these counterexamples to Test/RegressionTest.lean"
    return 1
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
--   -- NULL AND TRUE should be NULL (three-valued logic)
--   -- evalExpr returns Option Value, so compare with some/none
--   match result with
--   | some (.null _) => .pass "null_and_true"
--   | _ => .fail "null_and_true" s!"Expected null, got {result}"

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
│  2. Property fails   "prop_and_commutative failed"              │
│         │                                                        │
│         ▼                                                        │
│  3. LSpec shrinks    Finds minimal counterexample:              │
│         │            a = .lit (.null none), b = .lit (.bool true)│
│         │            row = []                                    │
│         ▼                                                        │
│  4. Investigate      Is this a bug or expected behavior?        │
│         │                                                        │
│         ├─── Bug ───► Fix the code, then add regression test    │
│         │                                                        │
│         └─ Expected ► Update property or document behavior      │
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

╔═══════════════════════════════════════════╗
║   SQL Equiv LSpec Property Test Suite     ║
╚═══════════════════════════════════════════╝

✗ Double Negation: NOT (NOT x) == x
  Counterexample after 47 shrinks:
    a   = Expr.lit (.null none)
    row = []

  evalExpr [] (NOT (NOT NULL)) = none
  evalExpr [] NULL             = some (.null none)
```

**Step 2**: Investigate

In the current implementation, `evalUnaryOp .not` only handles `some (.bool _)` and
returns `none` for all other inputs (including NULL). So `NOT NULL` evaluates to `none`,
and `NOT (NOT NULL)` is `NOT none` which is also `none`. This doesn't match the input
`some (.null none)`, revealing that double negation doesn't hold for non-boolean values.

**Step 3**: Decide how to handle this

This is actually expected behavior in the current evaluator: `NOT` only operates
on booleans and returns `none` otherwise. Two options:
- **Fix the evaluator** to propagate NULL through NOT (SQL three-valued logic), or
- **Update the property** to only test boolean expressions (using `boolEq`).

If the property was already using `boolEq` (as recommended above), this case would
be skipped rather than reported as a failure.

**Step 4**: Add regression test to `Test/RegressionTest.lean`

```lean
-- Found 2024-01-15: prop_double_negation
-- NOT NULL returns none (not null) in current evaluator
-- This documents current behavior; fix evalUnaryOp if SQL NULL propagation is desired
def test_not_null_returns_none : TestResult :=
  let nullExpr := Expr.lit (.null none)
  let expr := Expr.unaryOp .not nullExpr
  let result := evalExpr [] expr
  -- Current behavior: NOT on non-boolean returns none
  match result with
  | none => .pass "not_null_returns_none"
  | other => .fail "not_null_returns_none"
      s!"NOT NULL expected none, got {other}"

def test_double_not_null : TestResult :=
  let nullExpr := Expr.lit (.null none)
  let expr := Expr.unaryOp .not (.unaryOp .not nullExpr)
  let result := evalExpr [] expr
  -- NOT (NOT NULL) = NOT none = none
  match result with
  | none => .pass "double_not_null"
  | other => .fail "double_not_null"
      s!"NOT (NOT NULL) expected none, got {other}"
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

# Run LSpec with specific seed (reproducible)
LSPEC_SEED=12345 lake exe sql_equiv_lspec

# Run LSpec with more iterations (thorough)
LSPEC_NUM_TESTS=10000 lake exe sql_equiv_lspec
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
        env:
          LSPEC_NUM_TESTS: 5000
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

### 2. Generator Quality

Ensure generators produce good coverage:

```lean
-- Good: Covers edge cases
instance : Gen Value where
  gen := Gen.frequency [
    (1, pure (.null none)),           -- NULL (important edge case)
    (3, .bool <$> Gen.bool),          -- Booleans
    (3, .int <$> Gen.int),            -- Integers
    (2, .string <$> Gen.string),      -- Strings
    (1, pure (.int 0)),               -- Zero (edge case)
    (1, pure (.string "")),           -- Empty string (edge case)
  ]
```

### 3. Shrinking

LSpec's shrinking works best when types have `Shrink` instances:

```lean
instance : Shrink Value where
  shrink v := match v with
    | .int n => (.int <$> Shrink.shrink n) ++ [.null none]
    | .string s => (.string <$> Shrink.shrink s) ++ [.null none]
    | .bool b => [.null none]
    | .null _ => []
    | _ => [.null none]
```

### 4. Regression Test Naming

Use descriptive names that indicate the origin:

```lean
-- Good: Clear origin and purpose
def test_lspec_null_and_true_three_valued_logic : TestResult := ...
def test_lspec_empty_string_comparison : TestResult := ...

-- Bad: Unclear
def test1 : TestResult := ...
def test_bug_fix : TestResult := ...
```

### 5. Documentation

Document each regression test with:
- Date discovered
- Which property failed
- Brief explanation of the edge case

```lean
/--
Found: 2024-01-15
Property: prop_demorgan_and
Issue: De Morgan's law doesn't hold when operands are NULL
       because NULL AND NULL ≠ NULL (should be NULL)
Fix: Updated evalBinOp to propagate NULL correctly
-/
def test_demorgan_with_nulls : TestResult := ...
```

## Appendix: LSpec API Reference

> **Note**: The LSpec API may vary between versions. The examples in this document
> are illustrative; consult the [LSpec repository](https://github.com/argumentcomputer/LSpec)
> for the current API. Adapt the code patterns to match your installed version.

### Core Types

```lean
-- Generator monad
def Gen (α : Type) : Type

-- Property type (varies by LSpec version)
def Property : Type := ...

-- Test configuration (if supported)
structure Config where
  numTests : Nat := 100
  maxShrinks : Nat := 100
  seed : Option Nat := none
```

### Key Functions

```lean
-- Run a test suite (basic version)
def LSpec.run (suite : TestSuite) : IO TestResult

-- Run with configuration (if available in your LSpec version)
def LSpec.runWith (config : Config) (suite : TestSuite) : IO TestResult

-- Check a property
def LSpec.check (name : String) (prop : Property) : Test

-- Group tests
def LSpec.group (name : String) (tests : List Test) : TestSuite

-- Basic generators
def Gen.bool : Gen Bool
def Gen.int : Gen Int
def Gen.nat : Gen Nat
def Gen.string : Gen String
def Gen.list (g : Gen α) : Gen (List α)
def Gen.choose (lo hi : Int) : Gen Int
def Gen.chooseNat (lo hi : Nat) : Gen Nat
def Gen.elements (xs : Array α) : Gen α
def Gen.frequency (weighted : List (Nat × Gen α)) : Gen α
```

### Adapting to API Changes

If `LSpec.runWith` is not available, use `LSpec.run` instead:

```lean
-- If runWith is available:
let result ← LSpec.runWith testConfig suite

-- If only run is available:
let result ← LSpec.run suite
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
