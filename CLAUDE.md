# Claude Notes for sql_equiv

## Build System (Lean 4 / Lake)

- **Never run `lake clean` unless absolutely necessary** - it wipes the entire build cache and forces a full recompile (~20+ minutes). Incremental builds after small changes take only seconds.
- Use `lake build` for building, `lake exe sql_equiv_test` for running tests.
- Linter warnings about unused variables can be fixed by prefixing with `_` (e.g., `h1` → `_h1`).
