/-
  LSpec property-based test suite for sql_equiv.

  Runs SlimCheck-powered property tests that exercise the evaluator
  and optimizer against algebraic identities, NULL propagation rules,
  and semantic-preserving transformations.

  Sample count is configurable via the LSPEC_SAMPLES environment variable
  (defaults to 1000). CI can set LSPEC_SAMPLES=100 for faster runs.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators
import LSpecTests.ExprAlgebra
import LSpecTests.NullSemantics
import LSpecTests.OptimizerEquiv
import LSpecTests.ConstantFolding
import LSpecTests.FlattenRoundtrip
import LSpecTests.ExprOrdering
import LSpecTests.PredicatePushdown
import LSpecTests.QueryOptimizer

open LSpec SlimCheck

def main : IO UInt32 := do
  let numSamples ← do
    let env ← IO.getEnv "LSPEC_SAMPLES"
    pure (env.bind String.toNat? |>.getD defaultNumSamples)
  let cfg := mkSlimCfg numSamples
  IO.println s!"Running LSpec with {numSamples} samples per property"
  lspecIO (.ofList [
    ("Expression Algebra", [ExprAlgebra.allTests cfg]),
    ("NULL Semantics", [NullSemantics.allTests cfg]),
    ("Optimizer Equivalence", [OptimizerEquiv.allTests cfg]),
    ("Constant Folding", [ConstantFolding.allTests cfg]),
    ("Flatten Roundtrip", [FlattenRoundtrip.allTests cfg]),
    ("Expression Ordering", [ExprOrdering.allTests cfg]),
    ("Predicate Pushdown", [PredicatePushdown.allTests cfg]),
    ("Query Optimizer", [QueryOptimizer.allTests cfg])
  ]) []
