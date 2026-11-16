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
| `SqlCoreTest/ExprExamples.lean` | evaluation, typing, safety and lowering examples; soundness on the typed test database |
| `SqlCoreTest/ExprDiffTest.lean` | generated well-typed expressions evaluated against `SqlEquiv.evalExpr` |
| `SqlCoreTest/QueryExamples.lean` | the frontier's query examples, decimals in queries, and queries over the typed test database |
| `SqlCoreTest/LawExamples.lean` | the laws applied, and for every side condition an instance where the law fails without it |
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
- [x] **Phase 3: resolved expressions, typing, type soundness** (#292), *re-derive*:
  `SqlCore/Expr.lean`, `Typing.lean`, `Preconditions.lean`
- [ ] Correlated-subquery prototype (in #297), alongside phases 3–4
- [x] **Phase 4: core queries with bag semantics** (#293), *re-derived* (decision 0, revised):
  `SqlCore/Query.lean`, `SqlCore/Except.lean`
- [x] **Phase 5: equivalence and rewrite laws** (#294), *re-derived* like phase 4: `SqlCore/Equiv.lean`,
  `QueryEquiv.lean`, `QueryLaws.lean`, `Foundations/`. The inventory of `SqlEquiv` theorems is
  [`TYPED_CORE_INVENTORY.md`](TYPED_CORE_INVENTORY.md)
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

## Phase 3 differences

| Case | `SqlCore` | `SqlEquiv` | Postgres 16 | DuckDB |
|---|---|---|---|---|
| Column reference | `col (i : Fin n)`, resolved | a name, looked up per row | | |
| Error in a `CASE` condition | the error | swallowed; takes `ELSE` | the error | the error |
| `CASE WHEN … THEN 1 ELSE 1.5 END` | ill-typed (branches of one type) | `1` | `1` (`numeric`) | `1.0` (`DECIMAL`) |
| `1.0 / 2` | ill-typed | error (#201) | `0.5000…` | `0.5` (`DOUBLE`) |
| `x IN (1, 2.5, NULL)` with `x` an integer | well-typed (comparable elements) | evaluates | evaluates | evaluates |
| Aggregates, subqueries, windows | not in the fragment | in `Expr` | | |

Accepting mixed int/decimal `CASE` branches would need evaluation to convert the int branch
(soundness promises a datum of the declared type). It is left to the phase 6 bridge, which can insert
the conversion, or to a later `CAST` expression.

Type soundness (`Expr.eval_ok_or_divisionByZero`) is proved for every constructor. A well-typed
expression never raises `typeMismatch` or `unsupported`, and a safe one (`Expr.IsSafe`, decidable)
always succeeds. `SqlCore/Preconditions.lean` gives the typed counterpart of each precondition in
`SqlEquiv/Equiv/Defs.lean`.

`SqlCoreTest/ExprDiffTest.lean` evaluates every generated well-typed expression on the rows of `users`
and `items` (17848 cases). The only disagreements are the 36 boolean orderings. Swapping the
`CASE` branches in the translation makes 4536 cases disagree.

Extension candidates that are already in `SqlEquiv` and not ported: `BETWEEN` (expressible as
`AND` of two comparisons), `LIKE`/`ILIKE` (dialect-dependent, #262), string functions (`UPPER`,
`LOWER`, `LENGTH`, `SUBSTR`, `TRIM`, …), `COALESCE`/`NULLIF`, `ABS`, and `CAST`. Port them when
phases 4–6 need them.

## Phase 4 notes

`Query S n` (table, `WHERE`, `SELECT` list, inner join `ON θ`, `UNION ALL`, `DISTINCT`) has
evaluation, typing and type soundness for every constructor (`Query.eval_ok_or_divisionByZero`).
A safe query (`Query.IsSafe`, decidable) succeeds on every conforming instance.

Changes from the frontier, all because of decimals:

- `Expr.evalTruth_eqCols_eq_ok_true_iff` takes a common-type hypothesis, since `1 = 1.0` is `TRUE`
  although the values differ.
- `Expr.isSafePredicate_eqCols_iff` asks for comparable key types, not equal ones.
- `SqlCore/Except.lean` is the frontier's `Foundations/Control/Except.lean` in namespace
  `SqlCore.Except`. It also has a local `map_error`, which lives in a Mathlib module this library
  does not import.

`SqlCoreTest/QueryExamples.lean` checks queries over the typed `SemanticsTest.testDb` by `decide`:
a filter, an equijoin, `DISTINCT`, and a decimal filter that drops a `NULL` price.

## Phase 5 notes

- `Expr.Equiv Γ` holds when two expressions have equal observations (`Except.toOption`) on every row
  conforming to `Γ`. It is a setoid and a congruence for every constructor, and it is compatible
  with renaming and substitution.
- `Query.Equiv ℓ` has three levels, `ordered`, `bag` (`List.Perm`, decision 5) and `set`, over
  conforming instances. It comes with `mono` and with congruence in every query and expression
  argument.
- The laws are the frontier's. The arithmetic identities (`add_zero`, `zero_add`, `sub_zero`,
  `mul_one`, `one_mul`, `neg_neg`) are generalised from integers to any numeric type, so they also
  hold for decimals.
- Ten expression laws were added beyond the frontier: De Morgan (`not_and`, `not_or`),
  associativity (`and_assoc`, `or_assoc`), distributivity (`and_or_distrib_left`,
  `or_and_distrib_left`), idempotence (`and_self`, `or_self`, for a boolean operand) and absorption
  (`and_or_absorb`, `or_and_absorb`, which also need a safe dropped operand). Each is lifted from the
  `Truth` lattice through the operands' observed truth values.
- Every side condition is a decidable check: `typeOf … = some τ`, `IsSafe` or `IsSafePredicate`.
  No law takes a hypothesis quantified over databases or rows. The exceptions are the congruence
  rules, whose hypothesis is itself an equivalence, and `binary_comm`, which asks for a property of
  the operator on datums.
- `SqlCoreTest/LawExamples.lean` shows, for each side condition, a concrete row or instance on which
  the law fails without it. The query cases are the frontier's; the expression cases are ours.
- `SqlCore/Foundations/` holds four small lemma files from the frontier's `Foundations`. They stay in
  their root namespaces (`Option.Rel`, `List`, `Fin`) so that dot notation finds them, and they are
  candidates for Mathlib and Batteries. The trust guard scans only `SqlCore`, but it collects axioms
  transitively, so these lemmas are still covered through the theorems that use them.

## Rules for every phase

- No `sorry`, no project axioms and no `native_decide` in `SqlCore`. CI enforces this through
  `#assert_trust_base SqlCore` and `#assert_no_runtime_overrides SqlCore`.
- Design decisions are human gates.
- Docs ship with behaviour, so each phase ticks its box above.
