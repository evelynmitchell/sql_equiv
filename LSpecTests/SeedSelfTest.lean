/-
  Self-tests for the seeded property runner (#395).

  A property test whose seed is silently ignored still passes, so the seed needs its own
  checks: different run seeds must draw different samples, and a false property must fail.
  The end-to-end check (the `LSPEC_SEED` variable, the exit code and replay) is
  `tools/lspec_seed_selftest.py`, which runs `sql_equiv_lspec --must-fail`.
-/
import LSpec
import LSpecTests.Generators

open LSpec SlimCheck

namespace SeedSelfTest

def mustFailName : String := "deliberately false property (seed self-test)"

open SlimCheck Decorations in
/-- The sample at which a property first fails under `cfg` (`none` if it passes). -/
def firstFailureOf (descr : String) (p : Prop) (cfg : Configuration)
    (p' : DecorationsOf p := by mk_decorations) [Checkable p'] : Option Nat :=
  match seededResult p' cfg descr with
  | (.failure .., n) => some (n + 1)
  | _ => none

/-- The same for the deliberately false property: it is false only on some samples, so its
    first failing sample depends on the seed. -/
def firstFailure (runSeed : Nat) (descr : String := mustFailName) : Option Nat :=
  firstFailureOf descr (∀ a b : Int, a ≠ b + 3) (mkSlimCfg 2000 runSeed)

def seeds : List Nat := List.range 20

def allTests : TestSeq :=
  test "a false property fails under every run seed tried" (seeds.all fun s => (firstFailure s).isSome) $
  test "different run seeds draw different samples"
    ((seeds.map (firstFailure ·)).eraseDups.length ≥ 5) $
  test "different property names draw different samples under one run seed"
    ((seeds.map fun i => firstFailure 0 s!"property {i}").eraseDups.length ≥ 5) $
  test "property seeds differ across names and across run seeds"
    (propertySeed 0 "a" ≠ propertySeed 0 "b" ∧ propertySeed 0 "a" ≠ propertySeed 1 "a")

/-- Run only by `sql_equiv_lspec --must-fail`: the suite must report a failure. -/
def mustFail (cfg : Configuration) : TestSeq :=
  checkS (cfg := cfg) mustFailName (∀ a b : Int, a ≠ b + 3)

end SeedSelfTest
