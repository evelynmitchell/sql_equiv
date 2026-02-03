-- LSpec Hello World for sql_equiv
import LSpec
import SqlEquiv

open LSpec
open SlimCheck
open SqlEquiv

-- Shrinkable instance for Value (required for SampleableExt)
instance : Shrinkable Value where
  shrink _ := []  -- No shrinking for now

-- Generator for Value type using mkSelfContained
instance : SampleableExt Value :=
  SampleableExt.mkSelfContained do
    let choice ← Gen.choose Nat 0 3
    match choice with
    | 0 => pure (.null none)
    | 1 => do
        let b ← Gen.choose Nat 0 1
        pure (.bool (b == 1))
    | 2 => do
        let n ← Gen.choose Nat 0 100
        pure (.int n)
    | _ => do
        let n ← Gen.choose Nat 0 10
        pure (.string s!"s{n}")

-- Basic Lean tests
def basicTests : TestSeq :=
  test "2 + 2 = 4" (2 + 2 = 4) $
  check "addition is commutative" (∀ n m : Nat, n + m = m + n)

-- Value type decidable tests
def valueTests : TestSeq :=
  test "int equality reflexive" (Value.int 42 == Value.int 42) $
  test "null equals null" (Value.null none == Value.null none)

-- Property tests on Value (using our generator)
def valuePropertyTests : TestSeq :=
  check "Value BEq is reflexive" (∀ v : Value, v == v)

def main : IO UInt32 :=
  lspecIO (.ofList [
    ("Basic Nat Properties", [basicTests]),
    ("Value Decidable Tests", [valueTests]),
    ("Value Property Tests", [valuePropertyTests])
  ]) []
