# /counterexample

Add a counterexample to the regression test suite.

## Usage

- `/counterexample` - Add a counterexample found by LSpec
- `/counterexample show` - Show existing regression tests

## Instructions

When LSpec finds a counterexample, help add it as a permanent regression test.

### Steps

1. **Get the counterexample details:**
   - Which property failed?
   - What were the concrete values?

2. **Find the regression test file:**
   ```
   Look for Test/RegressionTest.lean or similar
   ```

3. **Add the test:**
   - Create a concrete test case using the counterexample values
   - Add a comment explaining where it came from
   - Ensure the test fails (demonstrating the bug) or passes (if bug was fixed)

### Format

```lean
-- Counterexample from LSpec: property_name
-- Found: 2024-01-15
example : ¬ (some_claim counterexample_values) := by
  native_decide
```

Or if it should now pass (bug fixed):

```lean
-- Regression test: previously failed with counterexample_values
example : some_claim counterexample_values := by
  native_decide
```

### After Adding

Run `/lspec` and `/test` to verify the new test behaves as expected.
