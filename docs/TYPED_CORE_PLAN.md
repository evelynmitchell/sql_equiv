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
| `SqlCoreTest/ScalarExamples.lean` | kernel-checked (`decide`) examples of the operators |
| `SqlCoreTest/ScalarDiffTest.lean` | differential test against `SqlEquiv.evalBinOp`/`evalUnaryOp` |
| `SqlCoreTest/SchemaExamples.lean` | column resolution examples; `SemanticsTest.testDb` as a `DbSchema` and a conforming instance |
| `SqlCoreTest/SchemaDiffTest.lean` | the typed test database has exactly the original rows |
| `Test/TrustBaseCommands.lean` | the guard commands, shared with `Test/TrustBaseTest.lean` (`SqlEquiv`) |

`SqlEquiv` stays on Batteries and never imports Mathlib. Mathlib and cslib-frontier
are both on Lean `v4.36.0-rc2`, and Mathlib is pinned to the frontier's commit
(`69552756`) in `lakefile.toml`. Mathlib is listed last there, so its dependency pins
win. Use `lake exe cache get` for prebuilt Mathlib, and never run `lake clean`.

## Phases

- [x] **Decisions** (#288)
- [x] **Phase 0: groundwork** (#289): toolchain (#299), Mathlib, `SqlCore` scaffold,
  trust guard for `SqlCore`, CI
- [x] **Phase 1: values, three-valued logic, scalar operators** (#290), *re-derive*
  - [x] `int`/`text`/`bool`: `SqlCore/Value.lean`, `Truth.lean`, `Scalar.lean` (#301)
  - [x] exact `decimal` as `ℚ`, with int↔decimal promotion (decisions 4 and 6)
- [x] **Phase 2: rows, columns, schemas** (#291), *re-derive*: `SqlCore/Row.lean`, `Column.lean`,
  `Schema.lean`
- [ ] Phase 3: resolved expressions, typing, type soundness (#292), *re-derive*
- [ ] Correlated-subquery prototype (in #297), alongside phases 3–4
- [ ] Phase 4: core queries with bag semantics (#293), *from cslib-frontier*
- [ ] Phase 5: equivalence and rewrite laws (#294), *from cslib-frontier*; the inventory of
  `SqlEquiv` theorems still applies
- [ ] Phase 6: bridge from the parsed AST, differential tests against Postgres and DuckDB (#295)
- [ ] Phase 7: certified simplifier, decision procedure, tactics (#296)
- [ ] Phase 8: features beyond the frontier (#297), *offered upstream*
- [ ] Phase 9: retire the untyped semantics (#298)

## Phase 1 differences

The scalar operators were re-derived from the frontier's `Value`, `Truth` and `Scalar`, and
compared against `SqlEquiv`, Postgres 16 and DuckDB (decisions 8 and 9).

| Case | `SqlCore` | `SqlEquiv` | Postgres | DuckDB |
|---|---|---|---|---|
| `false < true` | `TRUE` | error (no boolean order) | `t` | `true` |
| `1 / 0` | `divisionByZero` | error (`none`) | `ERROR: division by zero` | `1 // 0` is `NULL` |
| `FALSE AND 1` (ill-typed) | `typeMismatch` | `FALSE` (short-circuit) | error (type) | `false` (casts `1` to boolean) |
| `1 = 1.0` | `TRUE` (promotion) | `TRUE` (promotion) | `t` | `true` |
| `7.5 % -2` | `1.5` (exact, dividend's sign) | error (#201) | `1.5` | `1.5` |
| `1.0 / 4` | `unsupported` | error (#201) | `0.25000000000000000000` | `0.25` (a `DOUBLE`) |
| `1.0 / 0` | `divisionByZero` | error | `ERROR: division by zero` | `inf` |
| `1 IN (2, NULL)` | `unknown` | (IN is in the expression evaluator) | `NULL` | `NULL` |

`SqlCoreTest/ScalarDiffTest.lean` checks every well-typed operand pair over a small domain,
with integers and decimals mixed (3668 cases). The only disagreements are the 16 boolean
orderings and the 168 decimal remainders; any other one fails the test.

Decimal division is `unsupported` because the engines disagree on its result type and scale.
Equality of values (`=` on `Value`) is structural, so `int 1 ≠ decimal 1` although `1 = 1.0` is
`TRUE` in SQL. The laws over a common type (`inList_eq_ok`, `eval_eq_ok_true_iff`) are unaffected.
Mixed-type membership such as `1 IN (1.0)` still evaluates correctly; only its closed form is
stated for a common type.

## Phase 2 differences

| Case | `SqlCore` | `SqlEquiv` |
|---|---|---|
| Column reference | a position `Fin n`, resolved once by `resolveColumn` | a name, looked up in each row |
| Name case | exact (decision 7); the parser normalises | case-insensitive (`Row.lookupCI`) |
| Unqualified name in two tables | `ambiguousColumn` | the first match |
| Columns and types of a table | the schema, so an empty table has them | read off the rows, so an empty table has none |
| Type of a `NULL` cell | the column's declared type | `.null (some τ)` on the value |

Phase 2 is done in the sense of #291: `SqlCoreTest/SchemaExamples.lean` writes `SemanticsTest.testDb`
(six tables) as a `DbSchema` and an instance, and `decide` proves that it conforms.
`SqlCoreTest/SchemaDiffTest.lean` checks at run time that every row matches the original.
`deriving Fintype` fails at the current Mathlib pin, so the test writes the instance out.

## Rules for every phase

- No `sorry`, no project axioms and no `native_decide` in `SqlCore`. CI enforces this through
  `#assert_trust_base SqlCore` and `#assert_no_runtime_overrides SqlCore`.
- Design decisions are human gates.
- Docs ship with behaviour, so each phase ticks its box above.
