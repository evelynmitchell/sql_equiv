/-
  LSpec property-based test suite for sql_equiv.

  Runs SlimCheck-powered property tests that exercise the evaluator
  against algebraic identities, NULL propagation rules,
  and semantic-preserving transformations.

  Sample count is configurable via the LSPEC_SAMPLES environment variable
  (defaults to 10,000). CI sets LSPEC_SAMPLES=100000 for thorough coverage.

  The samples are drawn from a run seed, LSPEC_SEED (default 0, which pull-request CI uses).
  Each property mixes the run seed with its own name. A failure prints the command that
  replays it (#395).
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators
import LSpecTests.ExprAlgebra
import LSpecTests.NullSemantics
import LSpecTests.QueryHelpers
import LSpecTests.EdgeCaseDb
import LSpecTests.DiffSqlite
import LSpecTests.DiffDuckdb
import LSpecTests.DiffPostgres
import LSpecTests.RewriterProperties
import LSpecTests.SeedSelfTest

open LSpec SlimCheck

/-- The run seed: `LSPEC_SEED`, or `defaultSeed` when unset. A value that is not a natural
    number is an error, not a silent fallback to the default. -/
def readSeed : IO Nat := do
  match ← IO.getEnv "LSPEC_SEED" with
  | none | some "" => pure defaultSeed
  | some s =>
    match s.toNat? with
    | some n => pure n
    | none => throw <| IO.userError s!"LSPEC_SEED must be a natural number, got '{s}'"

def main (args : List String) : IO UInt32 := do
  let numSamples ← do
    let env ← IO.getEnv "LSPEC_SAMPLES"
    pure (env.bind String.toNat? |>.getD defaultNumSamples)
  let seed ← readSeed
  let cfg := mkSlimCfg numSamples seed
  IO.println s!"Running LSpec with {numSamples} samples per property, seed {seed}"
  -- `--must-fail`: only the deliberately false property (tools/lspec_seed_selftest.py)
  if args == ["--must-fail"] then
    return ← lspecIO (.ofList [("Seed Self-Test (must fail)", [SeedSelfTest.mustFail cfg])]) []
  unless args.isEmpty do
    throw <| IO.userError s!"unknown arguments {args}; the only one accepted is --must-fail"
  -- IO-based tests (SQLite differential)
  let sqliteTests ← DiffSqlite.runAllTests
  let duckdbTests ← DiffDuckdb.runAllTests
  let postgresTests ← DiffPostgres.runAllTests
  let rc ← lspecIO (.ofList [
    ("Expression Algebra", [ExprAlgebra.allTests cfg]),
    ("NULL Semantics", [NullSemantics.allTests cfg]),
    ("Edge-Case Databases", [EdgeCaseDb.allTests cfg]),
    ("SQLite Differential", [sqliteTests]),
    ("DuckDB Differential", [duckdbTests]),
    ("Postgres Differential", [postgresTests]),
    ("Rewriter Properties", [RewriterProperties.allTests cfg]),
    ("Seed Self-Test", [SeedSelfTest.allTests])
  ]) []
  if rc != 0 then
    IO.eprintln s!"Replay this run: LSPEC_SEED={seed} LSPEC_SAMPLES={numSamples} lake exe sql_equiv_lspec"
  return rc
