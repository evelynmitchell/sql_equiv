# Theorem Coverage Audit Plan

## Status
- Branch: `master` (current)
- **47 axioms** across 9 `.lean` files (34 in `Equiv/`, 13 in infrastructure)
- **418 theorems** proved (89.9%)
- Axiom ratchet: 47 (`tools/axiom_count_minimum.txt`)
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
| `Comparison.lean` | 11 | 182 | Comparison, boolean, arithmetic equivalences |
| `Decidable.lean` | 3 | 2 | Decidable equivalence helpers |
| `Defs.lean` | 0 | 20 | Core definitions (ExprEquiv, StmtEquiv) |
| `ExprAxioms.lean` | 1 | 42 | Expression-level axioms and theorems |
| `SetBagLemmas.lean` | 0 | 6 | Set/bag equivalence lemmas |
| `StatementAxioms.lean` | 19 | 67 | Statement-level axioms (joins, subqueries, set ops) |
| `ValueLemmas.lean` | 0 | 37 | Value-level helper lemmas |
| **Subtotal** | **34** | **356** | |

### Infrastructure Axioms

| File | Axioms | Theorems | Description |
|------|--------|----------|-------------|
| `ExprNormalization.lean` | 2 | 0 | Normalization preserves semantics |
| `JoinReordering.lean` | 2 | 1 | Join reorder forward/backward |
| `Optimizer.lean` | 3 | 6 | Optimizer correctness (pushdown, join reorder) |
| `OptimizerUtils.lean` | 0 | 5 | Optimizer utility lemmas |
| `PredicatePushdown.lean` | 1 | 0 | Predicate pushdown preserves semantics |
| `Semantics.lean` | 5 | 22 | Evaluator unfolding (evalExprWithDb_lit, _binOp, etc.) |
| `SemanticsCore.lean` | 0 | 28 |  |
| **Subtotal** | **13** | **62** | |

### Grand Total: 47 axioms, 418 theorems (89.9% proved)

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
