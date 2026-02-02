# /deps

Manage Lake dependencies for sql_equiv.

## Usage

- `/deps` - Show current dependencies
- `/deps update` - Update all dependencies
- `/deps add <package>` - Add a new dependency

## Instructions

Help manage the project's Lake dependencies.

### Show Dependencies

1. **Read lakefile.toml:**
   ```bash
   cat lakefile.toml
   ```

2. **Read lake-manifest.json for versions:**
   ```bash
   cat lake-manifest.json
   ```

3. **Present cleanly:**
   - List each dependency with its current version/commit
   - Note any that might be outdated

### Update Dependencies

```bash
source ~/.elan/env && lake update 2>&1
```

**Warning:** After updating, you may need to rebuild. If builds fail after update, the dependency versions may be incompatible.

### Common Dependencies for Lean 4

- `mathlib` - Mathematics library
- `std` - Standard library (now part of core in recent Lean)
- `lspec` - Property-based testing
- `aesop` - Automated theorem prover
