/-
  Trust-base commands, shared by `Test/TrustBaseTest.lean` (namespace
  `SqlEquiv`) and `SqlCoreTest/TrustBaseTest.lean` (namespace `SqlCore`, #287).

  - `#assert_trust_base NS`: every theorem, definition and opaque constant in
    `NS`, private ones included, depends only on `propext`,
    `Classical.choice` and `Quot.sound`; otherwise the offenders are named.
  - `#assert_no_runtime_overrides NS`: no hand-written `unsafe`,
    `@[implemented_by]` or `@[extern]` in `NS` (compiler-generated pairs are
    allowed).

  Same implementation as `tools/rewrite-audit/scripts/lean/TrustBase.lean`.
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

/-- Fails if namespace `ns` contains a hand-written runtime override: an
    `unsafe` declaration, an `@[implemented_by]` or an `@[extern]`. Each makes
    the compiled code differ from the code the kernel checked. Allowed: the
    compiler-generated pair for a `partial def f` (`f` implemented by the
    `unsafe` `f._unsafe_rec`). -/
elab "#assert_no_runtime_overrides " ns:ident : command => do
  let root := ns.getId
  let env ← getEnv
  let mut bad : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if !inTrustScope root n then continue
    -- compiler-generated pairs: `partial def f` is implemented by the unsafe
    -- `f._unsafe_rec`; since Lean 4.36 each inductive's `ctorIdx` is
    -- implemented by `ctorIdx._impl`
    let isCtorIdx (m : Name) := m.isStr && m.getString! == "ctorIdx"
    let isCompilerAux := n.isStr &&
      (n.getString! == "_unsafe_rec" || (n.getString! == "_impl" && isCtorIdx n.getPrefix))
    if ci.isUnsafe && !isCompilerAux then bad := bad.push n
    if let some impl := Compiler.implementedByAttr.getParam? env n then
      if impl != n ++ `_unsafe_rec && !(isCtorIdx n && impl == n ++ `_impl) then
        bad := bad.push n
    if isExtern env n && !isCompilerAux then bad := bad.push n
  if bad.isEmpty then
    logInfo m!"no runtime overrides under {root}"
  else
    throwError m!"runtime overrides under {root} ({bad.size}): {bad.toList.take 25}"
