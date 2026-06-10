# Claude Notes for sql_equiv

## Build System (Lean 4 / Lake)

- **Never run `lake clean` unless absolutely necessary** - it wipes the entire build cache and forces a full recompile (~20+ minutes). Incremental builds after small changes take only seconds.
- Use `lake build` for building, `lake exe sql_equiv_test` for running tests.
- Linter warnings about unused variables can be fixed by prefixing with `_` (e.g., `h1` → `_h1`).

## Soundness Audit Reminder

After editing any of these files, suggest running `/audit` before committing:
- `SqlEquiv/Semantics.lean` — `evalBinOp`, `evalUnaryOp`, `evalFunc` dispatch
- `SqlEquiv/Ast.lean` — `Value`, `BinOp`, `UnaryOp` type definitions
- `SqlEquiv/Equiv.lean` — equivalence module root
- `SqlEquiv/Equiv/` — axioms, lemmas, and equivalence definitions

## Workflow

- **Always open a PR for anything substantial** (semantics, proofs, new features,
  CI changes). Small follow-up fixes can ride on the open PR's branch.
- **Critical self-review heuristic — review when a bug would be quiet, skip
  when it would be loud.** Run `/critical-self-review` before merging:
  semantics changes (evalBinOp, aggregates, NULL paths, SELECT pipeline), new
  Value types or parser changes, new external surfaces (CI steps, oracles,
  dependency installs), and any change where the tests were written in the
  same pass as the code. Skip for docs, lint cleanup, test-only additions,
  and proof repairs where theorem statements are unchanged (the kernel is a
  stricter reviewer). Verify findings empirically (probe, don't speculate)
  before acting on them.
- **Docs ship with behavior.** Update README/plan checkboxes/TESTING_STRATEGY
  in the same PR as the change they describe, and run `/doc-freshness` before
  closing any tracking issue. When adding a Value type, the coverage tool
  (`tools/definition_coverage_matrix.py`) and the LSpec generators must learn
  it in the same batch — a coverage tool that doesn't know a type reports
  vacuous green.
- **Operating loop for autonomous sessions:** pick/confirm an issue → fresh
  branch → implement (code + proofs + tests + docs together) → push → PR
  linking the issue → critical self-review per the heuristic above → fix
  findings → green CI → hand off for merge. Two human gates only: merges,
  and design decisions (present options with trade-offs, wait for a pick).
  Issues are the memory between sessions — write them so a cold session can
  execute them. Goal generation: the Spider parse-rate baseline
  (`tools/spider_parse_baseline.py`) is the north-star metric; failure
  classes in its report become issues.
