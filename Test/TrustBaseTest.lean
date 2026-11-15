/-
  Trust-base guard (#212, #237): every theorem, definition and opaque
  constant in the `SqlEquiv` namespace, including private declarations,
  auxiliary proofs and proof-carrying definitions such as `certifiedRewrite`
  and `checkEquivFull`, must depend only on Lean's standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`). A `sorry` (`sorryAx`),
  `native_decide` (`Lean.ofReduceBool`) or project `axiom` fails the build of
  `sql_equiv_test`, which is what CI builds. Plain `lake build` (default
  target `sql_equiv`) does not import this file. `unsafe` constants are
  skipped by the axiom walk; `#assert_no_runtime_overrides` (below) instead
  fails if any hand-written `unsafe`, `@[implemented_by]` or `@[extern]`
  declaration appears in the namespace (#278). The compiler's own pairs are
  allowed: a `partial def f` implemented by `f._unsafe_rec`, and (Lean ≥ 4.36)
  an inductive's `ctorIdx` implemented by `ctorIdx._impl`.

  The commands live in `Test/TrustBaseCommands.lean`.
-/
import SqlEquiv
import Test.TrustBaseCommands

#assert_trust_base SqlEquiv

#assert_no_runtime_overrides SqlEquiv
