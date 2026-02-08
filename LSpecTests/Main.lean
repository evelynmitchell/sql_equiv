/-
  LSpec property-based test suite for sql_equiv.

  Runs SlimCheck-powered property tests that exercise the evaluator
  and optimizer against algebraic identities, NULL propagation rules,
  and semantic-preserving transformations.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators
import LSpecTests.ExprAlgebra
import LSpecTests.NullSemantics
import LSpecTests.OptimizerEquiv

open LSpec

def main : IO UInt32 :=
  lspecIO (.ofList [
    ("Expression Algebra", [ExprAlgebra.allTests]),
    ("NULL Semantics", [NullSemantics.allTests]),
    ("Optimizer Equivalence", [OptimizerEquiv.allTests])
  ]) []
