/-
  rewrite-audit: whole-library trust-base guard.

  `#assert_trust_base NS` collects, in one shared traversal, the axioms used
  by every theorem, definition and opaque constant whose name lies under the
  namespace `NS`, including private declarations and auxiliary proofs. It
  fails if any is outside Lean's standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`), and names the offending constants. A
  `sorry` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`,
  `Lean.trustCompiler`) or a project `axiom` anywhere is reported, including
  inside proof-carrying definitions such as rewriters returning
  `{ e' // R e e' }`.

  Use: copy this file into the project's test sources (or run
  `check_trust_base.sh`), then in a module the CI build imports:

      import MyProject
      import TrustBase
      #assert_trust_base MyProject

  Tested with Lean 4.36 (`Lean.collectAxioms`, `Lean.privateToUserName?`). If
  that API moves, fall back to `#print axioms` on key theorems
  (`print_axioms.sh`).
-/
import Lean

open Lean Elab Command

/-- Is `n` a declaration of namespace `root`, including private declarations
    (`_private.<module>.<n>.<user name>`) and their auxiliary constants? -/
private def inTrustScope (root n : Name) : Bool :=
  match Lean.privateToUserName? n with
  | some u => root.isPrefixOf u
  | none => root.isPrefixOf n

/-- Fails unless every theorem, definition and opaque constant under namespace
    `ns` depends only on Lean's standard axioms (`propext`, `Classical.choice`,
    `Quot.sound`). This includes private declarations, auxiliary proofs and
    proof-carrying definitions such as functions returning `{ e' // R e e' }`.
    `unsafe` constants are skipped: the kernel forbids safe code from using
    them, and runtime-only code is the separate runtime/proof-divergence
    check. On failure, the offending constants are listed. -/
elab "#assert_trust_base " ns:ident : command => do
  let root := ns.getId
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut nThm : Nat := 0
  let mut nDef : Nat := 0
  let mut nOpaque : Nat := 0
  for (n, ci) in env.constants.toList do
    if !inTrustScope root n || ci.isUnsafe then continue
    match ci with
    | .thmInfo _ => nThm := nThm + 1; names := names.push n
    | .defnInfo _ => nDef := nDef + 1; names := names.push n
    | .opaqueInfo _ => nOpaque := nOpaque + 1; names := names.push n
    | _ => pure ()
  if nThm == 0 then
    throwError m!"no theorems found under namespace {root}"
  -- Lean 4.36 made the `Lean.CollectAxioms` internals private (module
  -- system); the public `Lean.collectAxioms` looks up imported constants'
  -- axioms precomputed at export time, so one call per constant is cheap.
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut all : Array Name := #[]
  let mut offenders : Array (Name × List Name) := #[]
  for n in names do
    let axs ← collectAxioms n
    for a in axs do
      if !all.contains a then all := all.push a
    let bad := axs.toList.filter (fun a => !allowed.contains a)
    if !bad.isEmpty then offenders := offenders.push (n, bad)
  if offenders.isEmpty then
    logInfo m!"trust base OK under {root}: {nThm} theorems, {nDef} definitions, {nOpaque} opaque constants; axioms {all.toList}"
  else
    let extra := (offenders.toList.flatMap (·.2)).eraseDups
    throwError m!"constants under {root} depend on non-standard axioms {extra}; offenders ({offenders.size}): {(offenders.toList.take 25)}"
