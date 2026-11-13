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
