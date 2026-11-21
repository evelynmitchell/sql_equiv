# /coverage

Run the axiom/theorem coverage validator and report gaps.

## Usage

- `/coverage` — Run full coverage validation (comments out axioms and runs `lake build`/tests; requires build)
- `/coverage runtime` — Run static runtime coverage (no build, test-name matching only)
- `/coverage theorems` — Run static coverage including theorems and LSpec annotations

## Instructions

### Steps

1. **Run the coverage validator in static runtime mode (no build):**
   ```bash
   uv run python tools/axiom_coverage_validator.py --runtime 2>&1
   ```

   This mode does **not** build or run tests; it matches test names to axiom/theorem names to compute "static runtime coverage".

   To include theorems from `Equiv/` and LSpec `-- covers:` annotations:
   ```bash
   uv run python tools/axiom_coverage_validator.py --runtime --theorems 2>&1
   ```

   CI runs this command as a ratchet (#181): an uncovered public theorem must be listed in
   `tools/theorem_coverage_uncovered.txt`, and a listed name that is now covered must be
   removed. After adding tests, regenerate the list with `--runtime --theorems --update-ratchet`
   and review the diff.

   The build-based mode below edits source files in place and takes hours with `--theorems`;
   never edit the tree while it runs.

   To run the full build-based coverage validation (which comments out axioms and runs `lake build`/tests), use:
   ```bash
   uv run python tools/axiom_coverage_validator.py 2>&1
   ```

2. **Parse the output.** The tool reports:
   - Axioms/theorems with test coverage (from Test/ name matching AND/OR LSpec `-- covers:` annotations)
   - Axioms/theorems WITHOUT test coverage
   - Coverage source breakdown: Test/ only, LSpec only, both

3. **For uncovered axioms/theorems**, check if they are:
   - Infrastructure lemmas (internal helpers, not user-facing) — these are OK to skip
   - Public theorems in `Equiv/` — these SHOULD have coverage
   - Bridge theorems (`*_eq_*Core`) — these are OK to skip

4. **Report the coverage gap** with specific axiom/theorem names and which test file should contain them.

### Coverage Sources

**Test/ name matching:** Test names must START with the axiom/theorem name followed by a **non-word character** (space, paren, etc.):
- `"flattenAnd_nonempty (simple AND)"` — covers `flattenAnd_nonempty`
- `"join_comm_full"` — does NOT cover `join_comm` (next char is `_`, a word character)

**LSpec `-- covers:` annotations:** Comment above each `check` statement in `LSpecTests/` files:
```lean
-- covers: and_comm, evalBinOp_and_comm
check (cfg := cfg) "AND commutes" (∀ a b : BoundedGroundExpr, ...)
```
- Multiple theorem names separated by commas
- Exact match against theorem names (not prefix matching)

### Output Format

```
Coverage Report
===============
Covered: 200/339 declarations (59.0%)
  Test/ only:  157
  LSpec only:   35
  Both:          8

Uncovered items needing tests:
  SqlEquiv/Equiv/StatementAxioms.lean:
    - join_assoc [theorem] (public, needs test)
    - filter_join_right [theorem] (public, needs test)

  SqlEquiv/Equiv/ExprAxioms.lean:
    (all covered)

Uncovered but OK to skip:
  - evalSelect_eq_evalSelectCore (bridge theorem)
  - list_filter_and_eq (internal helper)
```

### Related Commands

- `/count` — Count axioms and theorems
- `/test` — Run the test suite
- `/lspec-test` — Add new LSpec property tests
