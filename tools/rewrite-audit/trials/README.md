# rewrite-audit trials

Blind trials that check the skill works on projects it was not written for
(plan: `docs/AUDIT_EXTRACTION_PLAN.md`, phase 5). Each trial is a small
fixture with planted bugs. The answer key below was written before the run,
and kept out of the fixture.

## py_simplifier (13 Nov 2026)

A tiny Python expression language: AST, evaluator and rule-based simplifier.
Values are int, str, bool, NULL and ERROR. The simplifier has seven root
rules.

### Answer key (written before the run)

| Rule | Intended | Expected verdict |
|---|---|---|
| constant folding (binary), via the evaluator, never to ERROR | sound | SOUND |
| constant folding (`NOT` of a literal) | sound | SOUND |
| `x * 1 → x`, unguarded | **planted bug** | UNSOUND: str or bool `x` gives ERROR before, the value after |
| `x + 0 → x`, guarded by `is_definitely_int` | sound | SOUND |
| `x AND TRUE → x`, guarded by `is_definitely_bool` | sound | SOUND |
| `x AND FALSE → FALSE` (the evaluator's FALSE wins over everything) | sound | SOUND |
| `NOT NOT x → x`, guarded by `is_definitely_bool` | sound | SOUND |

### Run

A fresh subagent was given only `SKILL.md` + `references/` and the fixture
(no `examples/`, no `docs/`), and told the user was unavailable.

### Result

| Rule | Skill's verdict | Correct? |
|---|---|---|
| folding (binary, unary) | SOUND | yes |
| `x * 1 → x` | **UNSOUND**: counterexamples `x='s'` and `x=True` give `ERROR → value`. Also matches `x * TRUE` | yes, the planted bug was found |
| `x + 0 → x` | **UNSOUND**: the pattern `r == Lit(0)` also matches `Lit(False)`, because Python's `False == 0` makes the dataclasses compare equal. `5 + FALSE` gives `ERROR → 5` | **yes: a real bug the answer key missed** |
| `x AND TRUE → x` | **UNSOUND**: it also matches `Lit(1)`. `TRUE AND 1` gives `ERROR → True` | **yes: a real bug the answer key missed** |
| `x AND FALSE → FALSE` | **UNSOUND**: it also matches `Lit(0)`. `x AND 0` with `x=True` gives `ERROR → False` | **yes: a real bug the answer key missed** |
| `NOT NOT x → x` | SOUND (dead through `simplify`: folding fires first) | yes |

All counterexamples were reproduced independently after the run.

- **Planted bug:** found, with concrete counterexamples.
- **False positives:** 0.
- **Real bugs found beyond the key:** 3. All are host-language equality in
  pattern matching: Python's `bool` is a subclass of `int`.
- **Procedure:**
  - the config was proposed, not written;
  - the fixture was not modified;
  - a probe was proposed and run: 21,404 expressions, 7,538 rewritten,
    1,947,764 checks, 23,784 mismatches across 330 expressions;
  - the mutant vacuity check was run (guard removed from `x AND TRUE`):
    caught.

The fixture is left **as is** (bugs included): it is a test input, not code
to fix.

### Feedback applied to the skill

The subagent's "Skill feedback" led to these changes:
1. **`risk-patterns.md`:** a new row, "pattern match uses host-language
   equality". `SKILL.md` protocol step 3 now enumerates the kinds of the
   *matched constants* as well as of the free variables.
2. **`probe-design.md`:**
   - kind-strict result comparison;
   - change detection that does not rely on the same loose equality;
   - the vacuity check when the baseline already fails;
   - choosing a mutant whose effect is disjoint from known failures.
3. **`discovery.md`:**
   - the config gains `relation.equality` (how results are compared);
   - `"bridge": null` is defined to mean "no bridge evidence: report it";
   - the relation may come from the README when there are no tests.
4. **`SKILL.md`:** audit both the driver (fixed-point/traversal) and the root
   rules, and report arms that are unreachable through the driver.
5. **`output-format.md`:**
   - a discovery and proposed-config section;
   - a fallback when there's no commit;
   - flexible analysis tables;
   - a reachability line.

## Seeded regressions in this repository (§7, 13 Nov 2026)

Four bugs were planted on a local throwaway branch, which was never pushed
and was deleted afterwards. A fresh subagent then ran `/audit` as a full scan,
blind: no git history, no plan doc, no trial records.

### Seeds and results

| # | Seed | Caught? | How |
|---|---|---|---|
| 1 | `a AND TRUE → a` with its `isDefinitelyBool` guard removed and the proof replaced by `sorry` | **yes** | Concrete counterexamples (`42 AND TRUE` → `42`, typed NULLs); `sorryAx` traced to `simplifyBinOp`; the Context Sweep showed 168 mismatches |
| 2 | `foldGround`: a public rewriter returning `{ e' // e ≃ₑ₀ e' }`. It folds `isGround` expressions by evaluating them on the empty database | **yes** | Found by re-running discovery (it was not in the config). It concludes the rejected weaker relation. Executed counterexample: `EXISTS (SELECT 1 FROM t)` → `FALSE` |
| 3 | `theorem … := by native_decide` in `Comparison.lean` | **yes** | `Lean.ofReduceBool` / `trustCompiler` traced to the theorem |
| 4 | `minMaxAgg` made a `partial def` (on the aggregate evaluation path) | **yes** | Reported as a new on-path `partial`, absent from the baseline. Rightly classed as an observation: it hides code from proofs but is not unsound |

### Real weaknesses found, beyond the seeds (all fixed)

These are present on master, not only on the seeded branch.

- **The trust guard checked only public theorems.** It skipped:
  - private theorems: 755 of them were invisible;
  - proof-carrying definitions, e.g. a `sorry` inside `checkEquivFull` or
    inside a rewriter returning `{ e' // … }`;
  - instances.

  Both `Test/TrustBaseTest.lean` and the skill's `TrustBase.lean` now check
  every theorem, definition and opaque constant, private ones included, and
  skip only `unsafe` constants. On failure they name the offending
  constants, using a memoised dependency walk that takes seconds. Clean
  master passes: 2582 theorems, 2105 definitions, 71 opaque constants. The
  only `lcProof` use is the documented `unsafe` `Expr.decEqUnsafe`. The
  vacuity check now plants a public `sorry`, a private `native_decide` and a
  proof-carrying `sorry` definition, and requires all three to be named.
- **The trust guard does not run on plain `lake build`.** It runs only in
  `sql_equiv_test`, which is what CI builds. The README, `/audit` and the docs
  said "at build time". The wording is corrected, and `/audit` now always
  runs the script.
- **The probe's "oracle self-check" was not a mutant check.** It only showed
  that the evaluator distinguishes `42 AND TRUE` from `42`. It is replaced by
  a real mutant check: an unguarded `a AND TRUE → a` rewriter runs through the
  same `rewriteMismatchWith` function, cases, rows and databases, and is
  caught on 45 cases. `probe-design.md` now requires this.
- **The baseline was wrong about the `unsafe` `DecidableEq Expr`.** It called
  it "off-path", which is true only for `certifiedRewrite`. It is on-path for
  `checkEquivFull`'s syntactic branch and `sql_equiv!`. The example is
  corrected, and `lean.md` now asks "on-path for which rewriter or decision
  procedure?".
- **`/audit` told the auditor not to re-run discovery**, which would have hidden
  seed 2. Full scans now re-run discovery and report anything not in the
  config (`SKILL.md`, `/audit`).
- Smaller:
  - `value-domains.md` asks for one row per typed NULL;
  - the baseline records the guard and probe counts, so a tree can be
    compared without git history;
  - the README states that `≃ₑ` says nothing about aggregates or window
    functions, which evaluate to an error at expression level.
