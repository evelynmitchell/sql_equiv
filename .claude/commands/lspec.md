# /lspec

Run LSpec property-based tests for sql_equiv.

## Usage

- `/lspec` - Run all LSpec property tests
- `/lspec build` - Build only (don't run)
- `/lspec verbose` - Run with full output

## Instructions

When the user runs `/lspec`, execute the LSpec test suite and report results.

### Steps

1. **Build the LSpec tests:**
   ```bash
   source ~/.elan/env && lake build sql_equiv_lspec
   ```

2. **Run the tests:**
   ```bash
   source ~/.elan/env && lake exe sql_equiv_lspec
   ```

   The samples come from a run seed, `LSPEC_SEED` (default 0; the run prints it). To explore
   other samples or replay a failure, set it:
   ```bash
   source ~/.elan/env && LSPEC_SEED=12345 LSPEC_SAMPLES=100000 lake exe sql_equiv_lspec
   ```
   A failing property prints its replay command. New properties must use `checkS` (not
   LSpec's `check`, which ignores the seed); `python3 tools/lspec_seed_selftest.py` checks this.

3. **Report results:**
   - List passing tests with their status (✓ = proven, ✓* = property test passed)
   - For any failures, show the counterexample clearly
   - If counterexamples are found, suggest adding them to `Test/RegressionTest.lean`

### Counterexample Handling

When a test fails, LSpec outputs something like:
```
× property_name
  Counterexample after N shrinks:
    var1 := value1
    var2 := value2
```

Extract and present this clearly to the user. Offer to help add it as a regression test.

### Example Output Format

```
LSpec Property Tests
====================
✓  2 + 2 = 4
✓* addition is commutative (100 samples)
✓* Value BEq is reflexive (100 samples)

All tests passed!
```

Or on failure:
```
LSpec Property Tests
====================
✓  2 + 2 = 4
✗  subtraction is commutative
   Counterexample: n = 1, m = 0
   (1 - 0 = 1, but 0 - 1 = 0)

1 failure. Consider adding counterexample to Test/RegressionTest.lean
```
