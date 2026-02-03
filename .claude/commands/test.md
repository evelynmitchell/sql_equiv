# /test

Run the main sql_equiv test suite.

## Usage

- `/test` - Run all tests
- `/test verbose` - Run with detailed output

## Instructions

Build and run the main test executable.

### Steps

1. **Build the test executable:**
   ```bash
   source ~/.elan/env && lake build sql_equiv_test 2>&1
   ```

2. **Run the tests:**
   ```bash
   source ~/.elan/env && lake exe sql_equiv_test 2>&1
   ```

3. **Report results:**
   - Show pass/fail summary
   - For failures, show the test name and what went wrong
   - Suggest fixes if the failure pattern is recognizable

### Related Commands

- `/lspec` - Run property-based tests (LSpec)
- `/build` - Build without running tests
