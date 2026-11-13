/-
  rewrite-audit: whole-library trust-base guard.

  `#assert_trust_base NS` collects, in one shared traversal, the axioms used
  by every theorem whose name lies under the namespace `NS`, and fails if
  any is outside Lean's standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`). A `sorry` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`,
  `Lean.trustCompiler`) or a project `axiom` anywhere in a proof cone is
  reported.

  Use: copy this file into the project's test sources (or run
  `check_trust_base.sh`), then in a module the CI build imports:

      import MyProject
      import TrustBase
      #assert_trust_base MyProject

  Tested with Lean 4.27 (`Lean.CollectAxioms`). If that API moves, fall back
  to `#print axioms` on key theorems (`print_axioms.sh`).
-/
import Lean

open Lean Elab Command

/-- Fails unless every theorem under namespace `ns` uses only Lean's standard
    axioms. Reports the theorem count and the axioms found. -/
elab "#assert_trust_base " ns:ident : command => do
  let root := ns.getId
  let env ← getEnv
  let thms := env.constants.toList.filterMap fun (n, ci) =>
    if root.isPrefixOf n && !n.isInternal then
      match ci with
      | .thmInfo _ => some n
      | _ => none
    else none
  if thms.isEmpty then
    throwError m!"no theorems found under namespace {root}"
  let act : CollectAxioms.M Unit := thms.forM CollectAxioms.collect
  let ((), st) := (act.run env).run {}
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let extra := st.axioms.filter (fun a => !allowed.contains a)
  if extra.isEmpty then
    logInfo m!"trust base OK: {thms.length} theorems under {root}, axioms {st.axioms.toList}"
  else
    throwError m!"theorems under {root} depend on non-standard axioms: {extra.toList}"
