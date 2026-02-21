# /coverage

Run the axiom coverage validator and report gaps.

## Usage

- `/coverage` — Run static analysis and report uncovered theorems
- `/coverage runtime` — Run with runtime validation (requires build)

## Instructions

### Steps

1. **Run the coverage validator:**
   ```bash
   uv run python tools/axiom_coverage_validator.py --runtime 2>&1
   ```
   If `--runtime` fails (build required), fall back to static:
   ```bash
   uv run python tools/axiom_coverage_validator.py 2>&1
   ```

2. **Parse the output.** The tool reports:
   - Axioms/theorems with test coverage
   - Axioms/theorems WITHOUT test coverage
   - Test names that don't map to any axiom/theorem

3. **For uncovered theorems**, check if they are:
   - Infrastructure lemmas (internal helpers, not user-facing) — these are OK to skip
   - Public theorems in `Equiv/` — these SHOULD have coverage
   - Bridge theorems (`*_eq_*Core`) — these are OK to skip

4. **Report the coverage gap** with specific theorem names and which test file should contain them.

### Test Name Convention

Test names must START with the axiom/theorem name followed by a **non-word character** (space, paren, etc.):
- `"flattenAnd_nonempty (simple AND)"` — covers `flattenAnd_nonempty`
- `"join_comm_full"` — does NOT cover `join_comm` (next char is `_`, a word character)

### Output Format

```
Coverage Report
===============
Covered: 45/52 theorems (86.5%)

Uncovered theorems needing tests:
  SqlEquiv/Equiv/StatementAxioms.lean:
    - filter_join_right (public, needs test in SubqueryTest.lean)
    - join_assoc (public, needs test in SubqueryTest.lean)

  SqlEquiv/Equiv/ExprAxioms.lean:
    (all covered)

Uncovered but OK to skip:
  - evalSelect_eq_evalSelectCore (bridge theorem)
  - list_filter_and_eq (internal helper)

Orphan tests (no matching theorem):
  - "old_optimizer_test" in Test/EquivTest.lean (stale?)
```

### Related Commands

- `/count` — Count axioms and theorems
- `/test` — Run the test suite
