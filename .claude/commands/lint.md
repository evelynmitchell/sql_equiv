# /lint

Check for linter warnings in the sql_equiv project.

## Usage

- `/lint` - Check all files for warnings
- `/lint <file>` - Check specific file

## Instructions

Build the project and collect linter warnings.

### Steps

1. **Run a build to collect warnings:**
   ```bash
   source ~/.elan/env && lake build 2>&1 | grep -E "(warning|unused)"
   ```

2. **Report findings:**
   - List each warning with file and line number
   - Group by warning type (unused variables, unused imports, etc.)
   - Suggest fixes

### Common Warnings and Fixes

| Warning | Fix |
|---------|-----|
| unused variable `x` | Rename to `_x` |
| unused import | Remove the import |
| unused have | Remove or use the hypothesis |

### Example Output

```
Linter Warnings
===============
SQLEquiv/Expr.lean:42: unused variable `h1` (rename to `_h1`)
SQLEquiv/Expr.lean:58: unused variable `ctx` (rename to `_ctx`)

2 warnings found. Run `/lint fix` to auto-fix.
```
