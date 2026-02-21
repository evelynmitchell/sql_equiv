# Theorem Coverage Audit Plan

## Status
- Branch: `master` (current)
- **0 axioms** across tracked `.lean` files (0 in `Equiv/`, 0 in infrastructure)
- **562 theorems** proved (100.0%)
- Axiom ratchet: 0 (`tools/axiom_count_minimum.txt`)
- Live counts: `python3 tools/count_axioms_theorems.py -v`
- Coverage validator: `uv run python tools/axiom_coverage_validator.py --runtime`

## Goal
Identify which axioms have no test coverage. An axiom with no coverage can be
removed (or replaced with `sorry`) without any test failing, meaning there's
no runtime or compile-time check that it's correct.

## Approach: Automated Validator

The `tools/axiom_coverage_validator.py` script performs static analysis:

1. Scans all axiom declarations in `SqlEquiv/**/*.lean` (Equiv/ and infrastructure files)
2. Scans all test names in `Test/*.lean`
3. Matches test names to axiom names (test must START with axiom name
   followed by a non-word character)
4. Reports covered vs uncovered axioms

Run with `--runtime` flag for full analysis. No build required.

## Axiom Breakdown by File

### Equivalence Axioms (`SqlEquiv/Equiv/`)

| File | Axioms | Theorems | Description |
|------|--------|----------|-------------|
| `Comparison.lean` | 0 | 193 | Comparison, boolean, arithmetic equivalences |
| `Decidable.lean` | 0 | 26 | Decidable equivalence helpers |
| `Defs.lean` | 0 | 20 | Core definitions (ExprEquiv, StmtEquiv) |
| `ExprAxioms.lean` | 0 | 51 | Expression-level axioms and theorems |
| `SetBagLemmas.lean` | 0 | 6 | Set/bag equivalence lemmas |
| `StatementAxioms.lean` | 0 | 94 | Statement-level axioms (joins, subqueries, set ops) |
| `ValueLemmas.lean` | 0 | 43 | Value-level helper lemmas |
| **Subtotal** | **0** | **433** | |

### Infrastructure Axioms

| File | Axioms | Theorems | Description |
|------|--------|----------|-------------|
| `Semantics.lean` | 0 | 60 | Evaluator unfolding (evalExprWithDb_lit, _binOp, etc.) |
| `SemanticsBase.lean` | 0 | 1 |  |
| `SemanticsCore.lean` | 0 | 68 |  |
| **Subtotal** | **0** | **129** | |

### Grand Total: 0 axioms, 562 theorems (100.0% proved)

> **Note:** `Semantics_test.lean` is an untracked scratch file (7 axioms, 38
> theorems) not included in these counts. The ratchet tracks only committed files.

## Key Constraints
- NEVER run `lake clean` (20+ min full rebuild)
- Test names must START with the axiom name followed by a non-word character
  (e.g., `"flattenAnd_nonempty (simple AND)"` covers `flattenAnd_nonempty`)
- Beware: `"join_comm_full"` does NOT cover `join_comm` (next char is `_`, a word char)

## Expected Categories of Results
- **Compile-time covered**: Axiom used in a theorem proof or another declaration
  that's part of the build
- **Runtime covered**: Axiom tested via runtime evaluation in `Test/*.lean`
- **Uncovered**: Axiom exists but nothing tests it
