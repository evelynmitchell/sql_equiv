# /build

Build the sql_equiv project using Lake.

## Usage

- `/build` - Incremental build (fast, recommended)
- `/build full` - Build all targets
- `/build <target>` - Build specific target

## Instructions

Run an incremental build using Lake. This is the most common operation.

### Steps

1. **Run the build:**
   ```bash
   source ~/.elan/env && lake build 2>&1
   ```

2. **Report results:**
   - On success: Show "Build successful" with job count
   - On failure: Show the error clearly, focusing on the first error message
   - For type errors: Show the file, line, and expected vs actual types

### Important Notes

- **Never run `lake clean`** unless explicitly requested - it wipes the build cache and forces a 20+ minute rebuild
- Incremental builds after small changes take only seconds
- Unused variable warnings can be fixed by prefixing with `_` (e.g., `h1` -> `_h1`)

### Example Output

```
Build successful (12 jobs)
```

Or on failure:
```
Build failed

Error in SQLEquiv/Expr.lean:42:
  type mismatch
    expected: List Value
    actual:   Array Value
```
