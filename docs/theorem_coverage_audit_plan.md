# Theorem Coverage Audit Plan

## Status
- Branch: `master` (current)
- **85 axioms** across 10 `.lean` files (56 in `Equiv/`, 29 in infrastructure)
- **331 theorems** proved (79.6%)
- Axiom ratchet: 85 (`tools/axiom_count_minimum.txt`)
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
| `Comparison.lean` | 18 | 167 | Comparison, boolean, arithmetic equivalences |
| `Decidable.lean` | 3 | 2 | Decidable equivalence helpers |
| `Defs.lean` | 0 | 20 | Core definitions (ExprEquiv, StmtEquiv) |
| `ExprAxioms.lean` | 5 | 38 | Expression-level axioms and theorems |
| `SetBagLemmas.lean` | 0 | 6 | Set/bag equivalence lemmas |
| `StatementAxioms.lean` | 26 | 63 | Statement-level axioms (joins, subqueries, set ops) |
| `ValueLemmas.lean` | 4 | 23 | Value-level helper lemmas |
| **Subtotal** | **56** | **319** | |

### Infrastructure Axioms

| File | Axioms | Theorems | Description |
|------|--------|----------|-------------|
| `ExprNormalization.lean` | 2 | 0 | Normalization preserves semantics |
| `JoinReordering.lean` | 2 | 1 | Join reorder forward/backward |
| `Optimizer.lean` | 3 | 6 | Optimizer correctness (pushdown, join reorder) |
| `OptimizerUtils.lean` | 0 | 5 | Optimizer utility lemmas |
| `PredicatePushdown.lean` | 1 | 0 | Predicate pushdown preserves semantics |
| `Semantics.lean` | 21 | 0 | Evaluator unfolding (evalExprWithDb_lit, _binOp, etc.) |
| **Subtotal** | **29** | **12** | |

### Grand Total: 85 axioms, 331 theorems (79.6% proved)

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
