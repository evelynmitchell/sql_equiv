/-
  Trust-base guard (#212, #237): every theorem in the `SqlEquiv` namespace
  must depend only on Lean's standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`). A `sorry` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`)
  or a project `axiom` anywhere in a theorem's proof cone fails the build.
  Runs in about 2 seconds: one axiom traversal shared by all theorems.
-/
import SqlEquiv
open Lean Elab Command

/-- Fails unless every theorem in the `SqlEquiv` namespace depends only on
    Lean's standard axioms. -/
elab "#assert_sqlequiv_trust_base" : command => do
  let env ← getEnv
  let thms := env.constants.toList.filterMap fun (n, ci) =>
    if n.getRoot == `SqlEquiv && !n.isInternal then
      match ci with
      | .thmInfo _ => some n
      | _ => none
    else none
  let act : CollectAxioms.M Unit := thms.forM CollectAxioms.collect
  let ((), st) := (act.run env).run {}
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let extra := st.axioms.filter (fun a => !allowed.contains a)
  if extra.isEmpty then
    logInfo m!"trust base OK: {thms.length} theorems, axioms {st.axioms.toList}"
  else
    throwError m!"theorems depend on non-standard axioms: {extra.toList}"

#assert_sqlequiv_trust_base
