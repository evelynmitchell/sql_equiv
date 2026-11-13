# Plan: extract `/audit` as a standalone tool

Status: **phases 1–5 and the §7 validation done**:
- `tools/rewrite-audit/` and the thin `/audit` adapter;
- the blind Python trial and the seeded-regression run
  (`tools/rewrite-audit/trials/README.md`).

Phase 6 (packaging) remains.

Decisions (13 Nov 2026):
- **Scope:** any expression rewriter, with the Lean layer loaded only for Lean
  projects.
- **Home:** `tools/rewrite-audit/` in this repository.
- **Name:** `rewrite-audit`.
- **Licence:** n/a while the tool lives in this repository.
- **Cached config:** the tool proposes `.claude/rewrite-audit.json` and writes
  it only with the user's agreement. This is the default; the user did not
  decide it.

## 1. Background

`/audit` (`.claude/commands/audit.md`) is a soundness-review command for this
repository's expression rewriters. It was added in February 2026 (`cce09c7`)
after Copilot found that `a AND TRUE → a` is wrong when `a` is not a boolean.
It was later updated for the all-database `≃ₑ` (#242) and the zero-`sorryAx`
trust base (#212).

It has two parts:

- **A general method.** For any program that rewrites expressions:
  - list each rule and its free variables;
  - list every runtime kind of value each variable can take, including NULLs
    and errors;
  - trace the evaluator before and after the rewrite, watching catch-all arms;
  - compare the results.

  It also checks a set of known high-risk patterns, checks that type guards
  are conservative and connected to the property the rule needs, and runs a
  differential probe whose non-vacuity is shown with a known-bad mutant. For
  Lean projects it audits what the kernel does not check:
  - the trust base;
  - runtime/proof divergence;
  - the scope of the proven relation.
- **Repository bindings.** These are the parts that only work here:
  - evaluator names: `evalBinOp`, `evalUnaryOp`, `evalFunc`;
  - the `Value` table;
  - `≃ₑ` vs `≃ₑ₀`, and `isGround` vs `isClosed`;
  - `certifiedRewrite` and `normalizeExpr`;
  - `sweepCases` in `LSpecTests/RewriterProperties.lean`;
  - `Test/TrustBaseTest.lean`.

The method is valuable anywhere: compilers, SQL optimizers, symbolic algebra,
lint autofixes, refactoring tools. Today it can only run here.

## 2. Goal

A Claude Code skill that:

1. **Finds the rewriter, evaluator and value domain itself** in an unfamiliar
   project. When it cannot, it asks one question.
2. **Applies the general protocol** and reports in a fixed format.
3. **Adds a proof-assistant layer** (Lean first) only when the project is one.
4. **Lets this repository keep identical behaviour** through a thin adapter.

### Non-goals

- Proving rewrites. The tool audits; it does not verify.
- Replacing a project's own test suite. The probe uses existing property or
  differential tests where they exist, and only proposes one when none does.
- Languages beyond those in §4.2 in the first release.

## 3. Shape of the tool

A skill, packaged so it can be installed per user or shared as a plugin:

```
rewrite-audit/
  SKILL.md                    # protocol + discovery + output format (always loaded)
  references/
    risk-patterns.md          # identity elimination, absorption, double negation,
                              # arithmetic identities, context/db-dependent rules
    value-domains.md          # how to derive the value table from a project
    probe-design.md           # differential probe + mutant vacuity check
    lean.md                   # trust base, runtime divergence, relation scope,
                              # guard bridges (loaded only for Lean projects)
    output-format.md          # report template and status markers
  scripts/
    lean/TrustBase.lean       # parameterised namespace guard (from TrustBaseTest)
    lean/print_axioms.sh      # #print axioms for a list of names
  examples/
    sql_equiv.md              # worked example: this repo's Nov 2026 audit
```

`SKILL.md` stays short and generic. Language- and prover-specific detail lives
in `references/` and is loaded on demand, so the skill's description and body
stay small.

## 4. Generalising each part

### 4.1 Discovery: replaces the hard-coded names

| Today (hard-coded) | Generic step |
|---|---|
| `certifiedRewrite`, `normalizeExpr` | Find functions with an AST → AST signature, plus rule tables (pattern → replacement). Heuristics per language (§4.2). |
| `evalBinOp` / `evalUnaryOp` / `evalFunc` | From each rewriter, find the evaluator it must preserve: an interpreter over the same AST, or the target language's semantics. |
| The `Value` table | Read the project's value type (enum, inductive, union) and its error/null representations. Build the table from it: one row per constructor, plus NULL kinds and the error result. |
| `≃ₑ` / `≃ₑ₀` | Find the equivalence relation the rewriter is meant to preserve (Lean: the subtype or theorem it returns). Then ask: *what does it quantify over?* (rows, environments, databases, configurations) |
| `sweepCases` | Find existing property, fuzz or differential tests over the rewriter. |

Findings are cached in a small per-project file (e.g.
`.claude/rewrite-audit.json` with the rewriter list, evaluator entry points,
value type, equivalence relation and probe command). Later runs skip
discovery, and the user can correct the file. If discovery is ambiguous, the
skill asks **one** question listing the candidates.

### 4.2 Languages in the first release

- **Lean 4.** Rewriters returning `{ e' // R e e' }` or with an accompanying
  theorem; `#print axioms`; `partial` / `implemented_by` / `unsafe`.
- **Python and TypeScript.** Visitor or transformer classes, `match`
  statements, rule dictionaries.
- **Rust.** `fn(&Expr) -> Expr`, `match` rewrite arms.

Others work through the generic path: the user names the rewriter and the
evaluator.

### 4.3 The protocol (moves almost unchanged)

The seven steps carry over as-is:

1. identify the rule;
2. list free variables;
3. enumerate value kinds;
4. trace before;
5. trace after;
6. compare;
7. check guards.

Two edits:

- Step 3 reads the value table from discovery instead of a fixed list.
- Step 7 generalises "bridge theorem" to "bridge evidence": a proof (prover
  projects), or a test showing the guard implies the precondition (others).

### 4.4 Probe (generic version of the context sweep)

- **If the project has property or differential tests over the rewriter:** run
  them, report counts, and require a vacuity check. Make a temporary mutant that
  removes one guard (the `a AND TRUE → a` shape) and confirm the probe fails.
  Revert the mutant.
- **Otherwise:** generate a probe outline from `probe-design.md`. Enumerate
  operand kinds × contexts, compare evaluator(original) against
  evaluator(rewritten), and propose it as a file. Do not silently add it to the
  test suite.

### 4.5 Proof-assistant layer (Lean first)

Loaded only when the project is a Lean project:

- **Trust base.** Run `#print axioms` on the rewriter's top-level theorem. Ship
  `TrustBase.lean`, a generalisation of `Test/TrustBaseTest.lean` that takes a
  namespace and an allow-list and fails on anything else, with a vacuity
  check (a planted `sorry`).
- **Runtime/proof divergence.** `implemented_by`, `extern`, `unsafe`,
  `partial`, `native_decide` on the rewriter's or evaluator's path. Only the
  path counts: unused `partial` code is reported as cleanup, not risk.
- **Relation scope.** Is the proven relation as strong as the claim? For
  example, our `≃ₑ₀` covered the empty database only, while the claim was all
  databases. This is phrased generically as "list what the relation quantifies
  over; compare with the documented guarantee".

A Coq/Rocq or Isabelle layer can be added later behind the same interface
(`Print Assumptions`, `thm_deps`).

### 4.6 Output

The current report format carries over unchanged:

- trust base;
- per-function, per-arm tables with `ok` / `MISMATCH` / `GUARD`;
- empirical probe;
- summary.

It moves into `output-format.md` so reports stay comparable across projects.

## 5. This repository after extraction

`.claude/commands/audit.md` becomes a thin adapter. It:

- calls the generic skill;
- ships a pre-filled `.claude/rewrite-audit.json`:
  - rewriters: `certifiedRewrite`, `normalizeExpr`, `checkEquivFull`;
  - evaluator: `evalBinOp`, `evalUnaryOp`, `evalFunc`;
  - value type: `Value`;
  - relation: `≃ₑ`, which must not be `≃ₑ₀`;
  - probe: `lake exe sql_equiv_lspec`, Context Sweep;
  - trust guard: `Test/TrustBaseTest.lean`;
- keeps the repo-only checks that don't generalise: `isGround` vs `isClosed`,
  and the CLAUDE.md trigger list for when to suggest `/audit`.

**Acceptance for this repo:** a full-scan run of the adapter reproduces the
13 Nov 2026 audit. That means:

- 3 functions;
- 0 soundness issues;
- the same trust base;
- the same probe counts: 54,876 expressions, 7,850 rewritten, 0 mismatches;
- the same three minor observations.

## 6. Phases and deliverables

| Phase | Deliverable | Done when |
|---|---|---|
| 1. Extract | `SKILL.md` + `references/` + `output-format.md`, with repo names removed | A reviewer finds no repo-specific identifier outside `examples/` |
| 2. Discovery | Discovery steps, `.claude/rewrite-audit.json` schema, language heuristics | On this repo, discovery finds the three rewriters, the evaluator and `Value` without hints |
| 3. Lean layer | `references/lean.md`, `scripts/lean/TrustBase.lean` (namespace parameter, allow-list, vacuity check) | `TrustBase.lean` passes here and fails on a planted `sorry` |
| 4. Adapter | Thin `.claude/commands/audit.md` + config | Adapter run reproduces the §5 acceptance numbers |
| 5. Portability | One non-Lean trial: a small Python or TypeScript expression simplifier with a seeded `x * 1 → x` bug that ignores strings | The tool finds the seeded bug with a concrete counterexample |
| 6. Package | Plugin or user-level install, README, version tag | Fresh install in an empty project; `/rewrite-audit` loads and asks the discovery question |

Phases 1–4 landed together:
- the skill is in `tools/rewrite-audit/`;
- this repo's map is in `.claude/rewrite-audit.json`;
- `/audit` is now the adapter.

Results against the done-criteria:
- **Phase 1:** no repo identifier outside `examples/`.
- **Phase 2:** discovery finds `certifiedRewrite` and `normalizeExpr` by
  signature, and `checkEquivFull` by the proof-carrying-result heuristic.
  `Expr.beq` is dropped as a false positive.
- **Phase 3:** `check_trust_base.sh SqlEquiv SqlEquiv` reports 1258 theorems
  OK, and `--vacuity` detects a planted `sorry`.
- **Phase 4:** an adapter run reproduces the baseline: the same axioms,
  54,876 expressions with 7,850 rewritten and 0 mismatches, and the oracle
  self-check passes.

Phase 5 is done: a blind trial on a Python simplifier
(`tools/rewrite-audit/trials/`).
- It found the planted `x * 1 → x` with counterexamples, and had 0 false
  positives.
- It also found 3 real bugs the answer key had missed: patterns compared with
  Python equality, where `False == 0` and `True == 1`.
- The trial's feedback is folded into the skill: a new risk pattern,
  kind-strict probe comparison, vacuity check on a failing baseline, the
  driver vs root rules, and output-format gaps.

Phase 6 (packaging) is open.

## 7. Validation (beyond the acceptance checks)

- **Seeded regressions in this repo,** each on a throwaway branch and never
  merged:
  - an unguarded `a AND TRUE → a`;
  - a rule proven only under `≃ₑ₀`;
  - a `native_decide` in a rewriter proof;
  - a `partial def` on the evaluator path.

  Each must be reported.
- **False-positive check:** run the tool on the current clean master; it must
  report no soundness issues.
- **Cost check:** record the token and time cost of a full scan here. The
  rewriter has 34 arms, so cap per-arm hand-tracing for proven arms (§9).

## 8. Open decisions

1. **Scope.** Any expression rewriter, with Lean as an optional layer
   (recommended), or Lean-verified rewriters only (smaller, sharper)?
2. **Home.** A user-level skill (`~/.claude/skills/`), a plugin in a separate
   repository, or kept in this repository under `tools/`?
3. **Name.** `rewrite-audit` is a placeholder.
4. **Licence**, if published separately.
5. **Cached config.** Should the tool write `.claude/rewrite-audit.json`
   automatically, or only propose it?

## 9. Risks

- **Too generic to be useful.** The current command's value comes from naming
  exact functions. Mitigation: discovery plus the cached config give each
  project the same concreteness after the first run.
- **Discovery picks the wrong evaluator.** Mitigation: show the findings and
  ask before auditing; the config file is editable.
- **Cost on large rule sets.** Hand-tracing every arm is expensive. Mitigation:
  for arms with a proof, check only the proof's relation and guards (as now).
  Trace fully only unproven arms, and let the user target one function.
- **Lean API drift.** `TrustBase.lean` uses `Lean.CollectAxioms`. Mitigation:
  pin the tested Lean version in the script header and keep a `#print axioms`
  fallback.
- **Mutant edits left behind.** The vacuity check edits code. Mitigation: do it
  on a scratch branch or in a temporary copy, and verify the working tree is
  clean afterwards.
