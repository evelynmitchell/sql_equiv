# rewrite-audit

A soundness audit for **expression rewriters**: optimizers, simplifiers,
query rewriters, lint autofixes. It ships as a Claude Code skill.

The question it answers is: *does every rewrite rule give the same result as
the original expression, for every runtime kind of value (including NULLs and
errors), in every context the evaluator depends on?*
- For unproven rules it traces the evaluator by hand and runs a differential
  probe whose non-vacuity is checked with a known-bad mutant.
- For Lean projects with kernel-checked rewriters, it audits what the kernel
  does not check:
  - the trust base;
  - runtime/proof divergence;
  - the scope of the proven relation;
  - guard bridges.

It was extracted from this repository's `/audit` command (plan:
`docs/AUDIT_EXTRACTION_PLAN.md`). `examples/sql_equiv.md` is a real report.

## Layout

```
SKILL.md                  protocol, procedure, after-audit steps
references/
  discovery.md            finding the rewriter, evaluator, value domain; config schema
  value-domains.md        building the per-operand enumeration table
  risk-patterns.md        rule shapes that most often fail, and what makes them sound
  probe-design.md         differential probe and mutant vacuity check
  lean.md                 Lean layer (trust base, divergence, relation scope, bridges)
  output-format.md        report template and status markers
scripts/lean/
  TrustBase.lean          `#assert_trust_base NS`: whole-library axiom guard
  check_trust_base.sh     run the guard ad hoc; `--vacuity` plants a sorry
  print_axioms.sh         `#print axioms` for named theorems
examples/sql_equiv.md     worked example
```

## Using it in another project

Copy the directory to `~/.claude/skills/rewrite-audit/`, or to the project's
`.claude/skills/rewrite-audit/`. Then ask for a rewrite audit or run
`/rewrite-audit`.

On the first run the skill finds the rewriter, evaluator and value domain,
asks you to confirm, and proposes a `.claude/rewrite-audit.json`. It writes
that file only with your agreement; later runs use it.

For a Lean project, add the whole-library guard to the test build:

```lean
-- in a module your CI target imports, with TrustBase.lean copied alongside
import MyProject
import TrustBase
#assert_trust_base MyProject
```

or run it ad hoc from the project root:

```bash
tools/rewrite-audit/scripts/lean/check_trust_base.sh MyProject MyProject
```

```bash
tools/rewrite-audit/scripts/lean/check_trust_base.sh MyProject MyProject --vacuity
```

## In this repository

`/audit` (`.claude/commands/audit.md`) is a thin adapter. It follows
`SKILL.md` using `.claude/rewrite-audit.json`, which pre-fills this repo's
rewriters, evaluator, value type, relation (`≃ₑ`, rejecting `≃ₑ₀`), guards,
probe and trust guard, plus repo-only checks.
