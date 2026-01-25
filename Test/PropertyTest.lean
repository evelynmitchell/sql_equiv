/-
  Property-Based Testing for SQL Equivalence

  Implements a simple QuickCheck-style property testing framework for Lean 4.
  Tests algebraic properties of SQL expressions using random generation.
-/
import SqlEquiv
import Test.Common

namespace PropertyTest

open SqlEquiv
open Test

-- ============================================================================
-- Simple Pseudo-Random Number Generator
-- ============================================================================

/-- Linear congruential generator state -/
structure RngState where
  seed : UInt64
  deriving Repr

/-- Create initial RNG state from seed -/
def RngState.init (seed : Nat) : RngState :=
  { seed := UInt64.ofNat seed }

/-- Generate next random value and return new state -/
def RngState.next (rng : RngState) : UInt64 × RngState :=
  -- LCG parameters (same as glibc)
  let a : UInt64 := 1103515245
  let c : UInt64 := 12345
  let m : UInt64 := 2147483648  -- 2^31
  let newSeed := (a * rng.seed + c) % m
  (newSeed, { seed := newSeed })

/-- Generate random Nat in range [0, max) -/
def RngState.nextNat (rng : RngState) (max : Nat) : Nat × RngState :=
  if max == 0 then (0, rng)
  else
    let (val, rng') := rng.next
    (val.toNat % max, rng')

/-- Generate random Bool -/
def RngState.nextBool (rng : RngState) : Bool × RngState :=
  let (n, rng') := rng.nextNat 2
  (n == 1, rng')

/-- Generate random Int in range [-bound, bound] -/
def RngState.nextInt (rng : RngState) (bound : Nat) : Int × RngState :=
  let range := 2 * bound + 1
  let (n, rng') := rng.nextNat range
  (Int.ofNat n - Int.ofNat bound, rng')

-- ============================================================================
-- Random Value Generator
-- ============================================================================

/-- Generate random SQL Value -/
def genValue (rng : RngState) : Value × RngState :=
  let (choice, rng1) := rng.nextNat 4
  match choice with
  | 0 =>
    let (n, rng2) := rng1.nextInt 100
    (.int n, rng2)
  | 1 =>
    let (idx, rng2) := rng1.nextNat 5
    let strings := #["alice", "bob", "test", "foo", "bar"]
    (.string (strings[idx]!), rng2)
  | 2 =>
    let (b, rng2) := rng1.nextBool
    (.bool b, rng2)
  | _ =>
    (.null none, rng1)

-- ============================================================================
-- Random Row Generator
-- ============================================================================

/-- Column names for generated rows -/
def columnNames : Array String := #["x", "y", "z", "a", "b"]

/-- Generate random Row with 3-5 columns -/
def genRow (rng : RngState) : Row × RngState :=
  let (numCols, rng1) := rng.nextNat 3  -- 0, 1, or 2 -> 3, 4, or 5 columns
  let numCols := numCols + 3
  go rng1 numCols []
where
  go (rng : RngState) (remaining : Nat) (acc : Row) : Row × RngState :=
    match remaining with
    | 0 => (acc.reverse, rng)
    | n + 1 =>
      let colIdx := columnNames.size - n - 1
      if h : colIdx < columnNames.size then
        let colName := columnNames[colIdx]
        let (val, rng') := genValue rng
        go rng' n ((colName, val) :: acc)
      else
        go rng n acc

-- ============================================================================
-- Random Expression Generator (Depth-Limited)
-- ============================================================================

/-- Generate random column reference from available columns -/
def genColRef (rng : RngState) : ColumnRef × RngState :=
  let (idx, rng') := rng.nextNat columnNames.size
  ({ table := none, column := columnNames[idx]! }, rng')

/-- Generate random expression with depth limit -/
partial def genExpr (rng : RngState) (maxDepth : Nat) : Expr × RngState :=
  if maxDepth == 0 then
    -- At max depth, only generate leaves
    let (choice, rng1) := rng.nextNat 2
    match choice with
    | 0 =>
      let (val, rng2) := genValue rng1
      (.lit val, rng2)
    | _ =>
      let (colRef, rng2) := genColRef rng1
      (.col colRef, rng2)
  else
    let (choice, rng1) := rng.nextNat 8
    match choice with
    | 0 =>  -- Literal
      let (val, rng2) := genValue rng1
      (.lit val, rng2)
    | 1 =>  -- Column reference
      let (colRef, rng2) := genColRef rng1
      (.col colRef, rng2)
    | 2 =>  -- AND
      let (left, rng2) := genExpr rng1 (maxDepth - 1)
      let (right, rng3) := genExpr rng2 (maxDepth - 1)
      (.binOp .and left right, rng3)
    | 3 =>  -- OR
      let (left, rng2) := genExpr rng1 (maxDepth - 1)
      let (right, rng3) := genExpr rng2 (maxDepth - 1)
      (.binOp .or left right, rng3)
    | 4 =>  -- NOT
      let (e, rng2) := genExpr rng1 (maxDepth - 1)
      (.unaryOp .not e, rng2)
    | 5 =>  -- Equality
      let (left, rng2) := genExpr rng1 (maxDepth - 1)
      let (right, rng3) := genExpr rng2 (maxDepth - 1)
      (.binOp .eq left right, rng3)
    | 6 =>  -- Addition
      let (left, rng2) := genExpr rng1 (maxDepth - 1)
      let (right, rng3) := genExpr rng2 (maxDepth - 1)
      (.binOp .add left right, rng3)
    | _ =>  -- Comparison (less than)
      let (left, rng2) := genExpr rng1 (maxDepth - 1)
      let (right, rng3) := genExpr rng2 (maxDepth - 1)
      (.binOp .lt left right, rng3)

/-- Generate a boolean expression (for AND/OR testing) -/
partial def genBoolExpr (rng : RngState) (maxDepth : Nat) : Expr × RngState :=
  if maxDepth == 0 then
    let (b, rng') := rng.nextBool
    (.lit (.bool b), rng')
  else
    let (choice, rng1) := rng.nextNat 5
    match choice with
    | 0 =>  -- Boolean literal
      let (b, rng2) := rng1.nextBool
      (.lit (.bool b), rng2)
    | 1 =>  -- AND
      let (left, rng2) := genBoolExpr rng1 (maxDepth - 1)
      let (right, rng3) := genBoolExpr rng2 (maxDepth - 1)
      (.binOp .and left right, rng3)
    | 2 =>  -- OR
      let (left, rng2) := genBoolExpr rng1 (maxDepth - 1)
      let (right, rng3) := genBoolExpr rng2 (maxDepth - 1)
      (.binOp .or left right, rng3)
    | 3 =>  -- NOT
      let (e, rng2) := genBoolExpr rng1 (maxDepth - 1)
      (.unaryOp .not e, rng2)
    | _ =>  -- Comparison that produces boolean
      let (left, rng2) := genExpr rng1 (maxDepth - 1)
      let (right, rng3) := genExpr rng2 (maxDepth - 1)
      (.binOp .eq left right, rng3)

-- ============================================================================
-- Property Definitions
-- ============================================================================

/-- Property type: takes RNG state and returns (passed, counterexample, new RNG) -/
def Property := RngState → (Bool × Option String × RngState)

/-- Format an expression for error reporting -/
def formatExpr (e : Expr) : String :=
  toString (repr e)

/-- Format a row for error reporting -/
def formatRow (row : Row) : String :=
  let pairs := row.map fun (k, v) => s!"{k}={repr v}"
  "[" ++ ", ".intercalate pairs ++ "]"

/-- Format an optional value -/
def formatOptValue (v : Option Value) : String :=
  match v with
  | some val => toString (repr val)
  | none => "none"

-- ============================================================================
-- Property: AND is commutative
-- ============================================================================

/-- Helper to run expression through semantics -/
def runExpr (row : Row) (e : Expr) : Option Value :=
  SqlEquiv.evalExpr row e

/-- For all expressions a, b and rows r: (a AND b) evaluates same as (b AND a) -/
def prop_and_comm : Property := fun rng =>
  let (a, rng1) := genBoolExpr rng 2
  let (b, rng2) := genBoolExpr rng1 2
  let (row, rng3) := genRow rng2

  let e1 := Expr.binOp .and a b
  let e2 := Expr.binOp .and b a
  let v1 := runExpr row e1
  let v2 := runExpr row e2

  if v1 == v2 then
    (true, none, rng3)
  else
    let msg := s!"a = {formatExpr a}\nb = {formatExpr b}\nrow = {formatRow row}\n" ++
               s!"(a AND b) = {formatOptValue v1}\n(b AND a) = {formatOptValue v2}"
    (false, some msg, rng3)

-- ============================================================================
-- Property: OR is commutative
-- ============================================================================

/-- For all expressions a, b and rows r: (a OR b) evaluates same as (b OR a) -/
def prop_or_comm : Property := fun rng =>
  let (a, rng1) := genBoolExpr rng 2
  let (b, rng2) := genBoolExpr rng1 2
  let (row, rng3) := genRow rng2

  let e1 := Expr.binOp .or a b
  let e2 := Expr.binOp .or b a
  let v1 := runExpr row e1
  let v2 := runExpr row e2

  if v1 == v2 then
    (true, none, rng3)
  else
    let msg := s!"a = {formatExpr a}\nb = {formatExpr b}\nrow = {formatRow row}\n" ++
               s!"(a OR b) = {formatOptValue v1}\n(b OR a) = {formatOptValue v2}"
    (false, some msg, rng3)

-- ============================================================================
-- Property: Double negation elimination
-- ============================================================================

/-- For all expressions e and rows r: (NOT NOT e) evaluates same as e -/
def prop_double_neg : Property := fun rng =>
  let (e, rng1) := genBoolExpr rng 2
  let (row, rng2) := genRow rng1

  let e_not_not := Expr.unaryOp .not (Expr.unaryOp .not e)
  let v1 := runExpr row e_not_not
  let v2 := runExpr row e

  if v1 == v2 then
    (true, none, rng2)
  else
    let msg := s!"e = {formatExpr e}\nrow = {formatRow row}\n" ++
               s!"(NOT NOT e) = {formatOptValue v1}\ne = {formatOptValue v2}"
    (false, some msg, rng2)

-- ============================================================================
-- Property: Normalization is idempotent
-- ============================================================================

/-- normalizeExpr(normalizeExpr(e)) = normalizeExpr(e) -/
def prop_normalize_idempotent : Property := fun rng =>
  let (e, rng1) := genExpr rng 3

  let normalized := normalizeExpr e
  let double_normalized := normalizeExpr normalized

  if normalized == double_normalized then
    (true, none, rng1)
  else
    let msg := s!"e = {formatExpr e}\n" ++
               s!"normalizeExpr(e) = {formatExpr normalized}\n" ++
               s!"normalizeExpr(normalizeExpr(e)) = {formatExpr double_normalized}"
    (false, some msg, rng1)

-- ============================================================================
-- Test Runner
-- ============================================================================

/-- Run a property N times with different random inputs -/
def runProperty (name : String) (prop : Property) (numTests : Nat) (seed : Nat) : IO TestResult := do
  let mut rng := RngState.init seed
  let mut passed := 0

  for _ in [:numTests] do
    let (success, counterexample, rng') := prop rng
    rng := rng'
    if success then
      passed := passed + 1
    else
      match counterexample with
      | some msg =>
        return TestResult.fail name s!"Counterexample found after {passed} tests:\n{msg}"
      | none =>
        return TestResult.fail name s!"Failed after {passed} tests (no counterexample)"

  return TestResult.pass s!"{name} ({numTests} tests)"

/-- Run all property tests -/
def runPropertyTests : IO (Nat × Nat) := do
  IO.println "═══════════════════════════════════"
  IO.println "Property-Based Tests"
  IO.println "═══════════════════════════════════"

  let numTests := 100
  let baseSeed := 42

  let results ← [
    runProperty "prop_and_comm" prop_and_comm numTests baseSeed,
    runProperty "prop_or_comm" prop_or_comm numTests (baseSeed + 1000),
    runProperty "prop_double_neg" prop_double_neg numTests (baseSeed + 2000),
    runProperty "prop_normalize_idempotent" prop_normalize_idempotent numTests (baseSeed + 3000)
  ].mapM id

  let mut passed := 0
  let mut failed := 0

  for result in results do
    match result with
    | .pass name =>
      IO.println s!"  PASS: {name}"
      passed := passed + 1
    | .fail name msg =>
      IO.println s!"  FAIL: {name}"
      IO.println s!"    {msg.replace "\n" "\n    "}"
      failed := failed + 1

  IO.println "-----------------------------------"
  IO.println s!"Property Tests: {passed} passed, {failed} failed"

  if failed == 0 then
    IO.println "ALL PROPERTY TESTS PASSED"
  else
    IO.println "SOME PROPERTY TESTS FAILED"

  return (passed, failed)

end PropertyTest
