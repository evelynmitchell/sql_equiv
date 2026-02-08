# Claude Notes for sql_equiv

## Build System (Lean 4 / Lake)

- **Never run `lake clean` unless absolutely necessary** - it wipes the entire build cache and forces a full recompile (~20+ minutes). Incremental builds after small changes take only seconds.
- Use `lake build` for building, `lake exe sql_equiv_test` for running tests.
- Linter warnings about unused variables can be fixed by prefixing with `_` (e.g., `h1` → `_h1`).

## Soundness Audit Reminder

After editing any of these files, suggest running `/audit` before committing:
- `SqlEquiv/Optimizer.lean` — rewrite functions
- `SqlEquiv/ExprNormalization.lean` — normalization rewrites
- `SqlEquiv/PredicatePushdown.lean` — predicate pushdown rewrites
- `SqlEquiv/OptimizerUtils.lean` — utility rewrites
- `SqlEquiv/Semantics.lean` — `evalBinOp`, `evalUnaryOp`, `evalFunc` dispatch
- `SqlEquiv/Ast.lean` — `Value`, `BinOp`, `UnaryOp` type definitions
- `SqlEquiv/Equiv.lean` — equivalence module root
- `SqlEquiv/Equiv/` — axioms, lemmas, and equivalence definitions
