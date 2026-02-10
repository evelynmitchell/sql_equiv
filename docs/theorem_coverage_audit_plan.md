# Theorem Coverage Audit Plan

## Status
- Branch: `master` (current)
- **107 axioms** across 9 `.lean` files (86 in `Equiv/`, 21 in infrastructure)
- **232 theorems** proved
- Axiom ratchet: 107 (`tools/axiom_count_minimum.txt`)
- Coverage validator: `uv run python tools/axiom_coverage_validator.py --runtime`

## Goal
Identify which axioms have no test coverage. An axiom with no coverage can be
removed (or replaced with `sorry`) without any test failing, meaning there's
no runtime or compile-time check that it's correct.

## Approach: Automated Validator

The `tools/axiom_coverage_validator.py` script performs static analysis:

1. Scans all axiom declarations in `SqlEquiv/Equiv/*.lean`
2. Scans all test names in `Test/*.lean`
3. Matches test names to axiom names (test must START with axiom name
   followed by a non-word character)
4. Reports covered vs uncovered axioms

Run with `--runtime` flag for full analysis. No build required.

## Axiom Breakdown by File

### Equivalence Axioms (`SqlEquiv/Equiv/`)

| File | Axioms | Theorems | Description |
|------|--------|----------|-------------|
| `Comparison.lean` | 23 | 119 | Comparison, boolean, arithmetic equivalences |
| `StatementAxioms.lean` | 75 | 0 | Statement-level axioms (joins, subqueries, set ops) |
| `ExprAxioms.lean` | 3 | 42 | Expression-level axioms and theorems |
| `Decidable.lean` | 3 | 2 | Decidable equivalence helpers |
| `Defs.lean` | 0 | 12 | Core definitions (ExprEquiv, StmtEquiv) |
| `ValueLemmas.lean` | 0 | 27 | Value-level helper lemmas |
| **Subtotal** | **104** | **202** | |

### Infrastructure Axioms

| File | Axioms | Description |
|------|--------|-------------|
| `Semantics.lean` | 11 | Evaluator unfolding (evalExprWithDb_lit, _binOp, etc.) |
| `Optimizer.lean` | 3 | Optimizer correctness (pushdown, join reorder) |
| `ExprNormalization.lean` | 2 | Normalization preserves semantics |
| `JoinReordering.lean` | 2 | Join reorder forward/backward |
| `PredicatePushdown.lean` | 1 | Predicate pushdown preserves semantics |
| **Subtotal** | **19** | |

### Grand Total: 107 axioms, 232 theorems

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
