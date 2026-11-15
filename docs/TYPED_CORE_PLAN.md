# Typed core plan

This tracks #287. The decisions are in [`TYPED_CORE_DECISIONS.md`](TYPED_CORE_DECISIONS.md).

## Goal

Rebuild the semantic core in the typed style of cslib-frontier's SQL development
(`CslibFrontier/Languages/SQL`, pinned at `e78796a1`):

- rows are positional (`Fin n → Datum`);
- NULL is `none` of `Datum := Option Value`;
- errors have their own type and are strict;
- schemas are separate data that instances conform to;
- typing is static, with a soundness theorem;
- laws have decidable side conditions.

The core is learned by re-deriving its foundations, and the work moves into
CSLib through the frontier.

## Layout

| Path | What |
|---|---|
| `SqlCore.lean`, `SqlCore/` | the typed core library (may import Mathlib) |
| `SqlCoreTest/` | its tests; `lake exe sqlcore_test` |
| `SqlCoreTest/TrustBaseTest.lean` | trust base and runtime-override guard for namespace `SqlCore` |
| `Test/TrustBaseCommands.lean` | the guard commands, shared with `Test/TrustBaseTest.lean` (`SqlEquiv`) |

`SqlEquiv` stays on Batteries and never imports Mathlib. Mathlib and cslib-frontier
are both on Lean `v4.36.0-rc2`, and Mathlib is pinned to the frontier's commit
(`69552756`) in `lakefile.toml`. Mathlib is listed last there, so its dependency pins
win. Use `lake exe cache get` for prebuilt Mathlib, and never run `lake clean`.

## Phases

- [x] **Decisions** (#288)
- [x] **Phase 0: groundwork** (#289): toolchain (#299), Mathlib, `SqlCore` scaffold,
  trust guard for `SqlCore`, CI
- [ ] Phase 1: values, three-valued logic, scalar operators (#290), *re-derive*
- [ ] Phase 2: rows, columns, schemas (#291), *re-derive*
- [ ] Phase 3: resolved expressions, typing, type soundness (#292), *re-derive*
- [ ] Correlated-subquery prototype (in #297), alongside phases 3–4
- [ ] Phase 4: core queries with bag semantics (#293), *from cslib-frontier*
- [ ] Phase 5: equivalence and rewrite laws (#294), *from cslib-frontier*; the inventory of
  `SqlEquiv` theorems still applies
- [ ] Phase 6: bridge from the parsed AST, differential tests against Postgres and DuckDB (#295)
- [ ] Phase 7: certified simplifier, decision procedure, tactics (#296)
- [ ] Phase 8: features beyond the frontier (#297), *offered upstream*
- [ ] Phase 9: retire the untyped semantics (#298)

## Rules for every phase

- No `sorry`, no project axioms and no `native_decide` in `SqlCore`. CI enforces this through
  `#assert_trust_base SqlCore` and `#assert_no_runtime_overrides SqlCore`.
- Design decisions are human gates.
- Docs ship with behaviour, so each phase ticks its box above.
