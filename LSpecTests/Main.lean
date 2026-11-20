/-
  LSpec property-based test suite for sql_equiv.

  Runs SlimCheck-powered property tests that exercise the evaluator
  against algebraic identities, NULL propagation rules,
  and semantic-preserving transformations.

  Sample count is configurable via the LSPEC_SAMPLES environment variable
  (defaults to 10,000). CI sets LSPEC_SAMPLES=100000 for thorough coverage.
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

open LSpec SlimCheck

def main : IO UInt32 := do
  let numSamples ← do
    let env ← IO.getEnv "LSPEC_SAMPLES"
    pure (env.bind String.toNat? |>.getD defaultNumSamples)
  let cfg := mkSlimCfg numSamples
  IO.println s!"Running LSpec with {numSamples} samples per property"
  -- IO-based tests (SQLite differential)
  let sqliteTests ← DiffSqlite.runAllTests
  let duckdbTests ← DiffDuckdb.runAllTests
  let postgresTests ← DiffPostgres.runAllTests
  lspecIO (.ofList [
    ("Expression Algebra", [ExprAlgebra.allTests cfg]),
    ("NULL Semantics", [NullSemantics.allTests cfg]),
    ("Edge-Case Databases", [EdgeCaseDb.allTests cfg]),
    ("SQLite Differential", [sqliteTests]),
    ("DuckDB Differential", [duckdbTests]),
    ("Postgres Differential", [postgresTests]),
    ("Rewriter Properties", [RewriterProperties.allTests cfg])
  ]) []
