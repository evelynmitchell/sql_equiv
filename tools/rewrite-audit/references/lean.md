# Lean layer

For Lean 4 projects. A rewriter that returns `{ e' // R e e' }`, or has a
correctness theorem, is checked by the kernel. The audit's job is what the
kernel does **not** check.

## 1. Trust base

- Run `#print axioms` on each rewriter's correctness theorem, using
  `scripts/lean/print_axioms.sh`. Expected:
  `[propext, Classical.choice, Quot.sound]`. Anything else is a finding:
  - `sorryAx` (a `sorry` somewhere in the proof cone);
  - `Lean.ofReduceBool` / `Lean.trustCompiler` (from `native_decide`; trusts
    the compiler);
  - a project `axiom`.
- **Whole-library guard.** `scripts/lean/TrustBase.lean` defines
  `#assert_trust_base <Namespace>`. In one shared traversal it collects the
  axioms of every **theorem, definition and opaque constant** in the
  namespace, and fails if any falls outside the allow-list, naming the
  offenders. It covers private declarations, auxiliary proofs and
  proof-carrying definitions; only `unsafe` constants are skipped.
  - A guard limited to public theorems misses a `sorry` inside a
    proof-carrying function, such as a rewriter returning
    `{ e' // R e e' }` or a checker returning a proof-carrying result, or
    inside a private lemma.
  - Recommend adding the guard to the project's test build (a module the CI
    target imports). Check which target that is: a guard in the test target
    does not run on a plain default build.
  - `scripts/lean/check_trust_base.sh` runs it ad hoc. Its vacuity check
    plants a public `sorry` theorem, a private `native_decide` theorem and a
    proof-carrying definition with `sorry`, and requires all three to be
    named.

## 2. Runtime/proof divergence

The compiled code is not the proved code when any of these sit on the
rewriter's or the evaluator's path:

- `@[implemented_by]`, `@[extern]`, `unsafe`: the runtime uses different code.
- `partial def`: opaque to proofs. Theorems can only treat it as an
  unspecified function, and runtime behaviour is unconstrained by them.
- `native_decide` in a proof: trusts the compiler (also caught by §1).

Search `grep -rn "implemented_by\|@\[extern\|unsafe\|partial def"`. Then
**check the path, per rewriter and decision procedure**: which of them can
reach the item at runtime? An override can be off-path for one (e.g. a
rewriter that never compares expressions) and on-path for another (e.g. a
checker deciding syntactic equality through it).
- **Off-path:** dead code, a pretty-printer, a parser. Report it as cleanup,
  not risk.
- **On-path:** say what the theorems cannot cover.

## 3. Relation scope

Unfold the relation the rewriter's proof concludes and list what it
quantifies over. Compare that with the guarantee the project documents.
Typical gaps:
- quantifying over rows but not over the database or environment (a proof
  "on the empty database" does not cover subqueries on real data);
- a weaker sibling relation kept for convenience, used by some proofs. List
  these in the config's `relation.weakerVariantsToReject`;
- a decision procedure that concludes the full relation from a check that is
  only valid for a restricted class of expressions (e.g. "ground" vs
  "closed").

## 4. Guard bridges

Each static guard used by an arm needs a theorem from the guard to the
semantic precondition the arm's proof uses. That theorem must quantify over
the same contexts as the relation. List each guard with its bridge, or flag
it as missing.
