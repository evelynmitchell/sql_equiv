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

  Tested with Lean 4.27 (`Lean.CollectAxioms`, `Lean.privateToUserName?`). If
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

/-- Non-standard axioms reachable from `n`, memoised across calls. A node is
    marked visited before its dependencies are explored, so cycles (possible
    among compiler-generated helpers) terminate. -/
private partial def badAxiomsOf (env : Environment) (allowed : List Name) (n : Name) :
    StateM (Std.HashMap Name (Array Name)) (Array Name) := do
  if let some r := (← get)[n]? then return r
  modify (·.insert n #[])
  let r ← match env.find? n with
    | some (.axiomInfo _) => pure (if allowed.contains n then #[] else #[n])
    | some ci => do
      let mut acc : Array Name := #[]
      for d in ci.getUsedConstantsAsSet.toList do
        for a in (← badAxiomsOf env allowed d) do
          if !acc.contains a then acc := acc.push a
      pure acc
    | none => pure #[]
  modify (·.insert n r)
  return r

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
  let mut nThm := 0
  let mut nDef := 0
  let mut nOpaque := 0
  for (n, ci) in env.constants.toList do
    if !inTrustScope root n || ci.isUnsafe then continue
    match ci with
    | .thmInfo _ => nThm := nThm + 1; names := names.push n
    | .defnInfo _ => nDef := nDef + 1; names := names.push n
    | .opaqueInfo _ => nOpaque := nOpaque + 1; names := names.push n
    | _ => pure ()
  if nThm == 0 then
    throwError m!"no theorems found under namespace {root}"
  let act : CollectAxioms.M Unit := names.toList.forM CollectAxioms.collect
  let ((), st) := (act.run env).run {}
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let extra := st.axioms.filter (fun a => !allowed.contains a)
  if extra.isEmpty then
    logInfo m!"trust base OK under {root}: {nThm} theorems, {nDef} definitions, {nOpaque} opaque constants; axioms {st.axioms.toList}"
  else
    -- failure only: name the offending constants (memoised walk)
    let mut cache : Std.HashMap Name (Array Name) := {}
    let mut offenders : Array (Name × List Name) := #[]
    for n in names do
      let (bad, c) := (badAxiomsOf env allowed n).run cache
      cache := c
      if !bad.isEmpty then offenders := offenders.push (n, bad.toList)
    throwError m!"constants under {root} depend on non-standard axioms {extra.toList}; offenders ({offenders.size}): {(offenders.toList.take 25)}"
