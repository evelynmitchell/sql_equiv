# Typed core: design decisions

These are the picks recorded on #288 (15 Nov 2026) for the typed core (`SqlCore`, #287).
Changing one is a design decision: propose it on an issue and wait for a pick
(`CLAUDE.md`).

| # | Question | Pick |
|---|---|---|
| 0 | Build on cslib-frontier, or re-derive it? | **Hybrid.** Re-derive phases 1–3 (values, rows, typed expressions) by hand, to learn the design. Then depend on [cslib-frontier](https://github.com/cslib-community/cslib-frontier) for queries and laws (phases 4–5). Phases 6 (bridge, oracles, Spider) and 8 (features beyond the frontier) are built on it and offered upstream. *Revised at #293: phase 4 is re-derived onto `SqlCore`'s types as well, so queries see decimals (the frontier has none), and the decimal extension is offered upstream ([cslib-community/cslib-frontier#5915](https://github.com/cslib-community/cslib-frontier/issues/5915)). Phase 5's laws are stated over these queries, so they follow the same path.* |
| 1 | Mathlib | **Yes, in `SqlCore` only, from phase 1.** It arrives through the frontier from phase 4 anyway. `SqlEquiv` does not import it. |
| 2 | Error behaviour | **Strict, as in the frontier.** A predicate or projection that fails on any row fails the whole query. Laws that move, duplicate or drop an expression carry a decidable safety condition. (This contrasts with `SqlEquiv`'s quiet errors, #270.) |
| 3 | Library name and location | **`SqlCore`, a Lake library in this repo** (namespace `SqlCore`, tests in `SqlCoreTest`). cslib-frontier is added later as a `require`. |
| 4 | Types in the first cut | **`int`, `text`, `bool`**, then exact `decimal` at the end of the values phase. Float stays deferred (#202). *Decimal storage (picked at #290 part 2): Mathlib `ℚ`, so `2.50 = 2.5` structurally and the order is Mathlib's; kernel evaluation needs `decide +kernel`.* |
| 5 | Bags | **`List` with `List.Perm`**, as in the frontier. |
| 6 | Comparison across types | **Both operands of a comparison have one type** (the frontier's rule), *except int↔decimal, which promotes (picked at #290 part 2): `1 = 1.0` is `TRUE` and `1 + 0.5` is `1.5`, as in Postgres, DuckDB and `SqlEquiv`. The typing relation is `SqlType.Comparable`.* #254 is the precedent in `SqlEquiv`. |
| 7 | Name case and resolution | **Exact match; an ambiguous reference is an elaboration error.** Names are normalised before resolution. |
| 8 | Dialects | **A single semantics, with no dialect modes in the typed core.** Engine differences are listed as known divergences in the oracle tests and in `docs/IMPLEMENTATION_DEFINED.md`. |
| 9 | Reference engines | **Postgres and DuckDB.** sqlite is kept only for Spider fidelity. |

## Phase 9 decisions (#298, #458; 24 Nov 2026)

| # | Question | Pick |
|---|---|---|
| D1 | Dialects in phase 9, given decision 8 | **Elaboration time only.** A dialect's choice is made by the elaborator from `DialectConfig`, as bare columns (`bareColumns`), NULL ordering and LIKE case already are; the typed semantics takes no dialect parameter. Decision 8 stands. |
| D2 | sqlite's quiet errors (`ErrorMode.quiet`, registry row 23) | **Dropped.** The typed core is strict (decision 2). After the switch (#466) the sqlite dialect has no quiet mode; it is recorded as a divergence from sqlite in the registry then. |
| D3 | `SqlEquiv`'s 714 theorems | **Inventory first, decided by group.** The inventory and a proposed fate per group are in `docs/TYPED_CORE_PLAN.md` ("D3 inventory"); each group's fate is confirmed when #466 reaches it. |
| D4 | The oracle for features ported in phase 9 | **The engines.** Each is validated against DuckDB and Postgres through the typed core (`SqlCoreTest.DuckdbDiff`, `SqlCoreTest.PostgresDiff`); no bridge proof against `SqlEquiv` is required, and `SqlEquiv`'s divergences there (outer-join padding, UPDATE assignment order, INSERT column names) are not fixed. |
| D5 | Spider after the switch: the evaluate ratchet falls from 559 to at most 520 (44 type-affinity queries do not elaborate) | **Accept and re-base** (24 Nov 2026). At the switch (#466) the Spider ratchets are re-based on the typed core and `CLAUDE.md`'s north-star text updated; the 44 queries are recorded as rejected by design (they rely on sqlite's type affinity, the same looseness D2 drops). No fallback evaluator. |
| D6 | Correlated subqueries and `EXISTS` (9.4, #462) | **Two additive constructors, `Query.outer` and `Query.lateral`** (24 Nov 2026, after the 9.4a spike). The core query type keeps its single arity index. See "D6: correlated subqueries" below. |

### D6: correlated subqueries

**Design.** `Query.outer Γ : Query S n` is the outer row of a correlated body, with its column
types; outside a body it is ill-typed. `Query.lateral body q : Query S (n + k)` is
`q CROSS JOIN LATERAL body`: for each row `r` of `q`, `body` is evaluated with `r` as its outer
row, and each of its rows is appended to `r`. Evaluation and typing take an optional outer row:
`Query.evalIn D env` and `Query.typeOfIn Γo`, with `Query.eval D := evalIn D none` and
`Query.typeOf := typeOfIn none`, so every existing statement keeps its meaning and the
equation lemmas stay `rfl`. Type soundness is stated for any conforming outer row
(`evalIn_spec`); `eval_spec` is its instance with none.

The elaborator turns a correlated subquery into a `lateral` column of the query it filters, as
`attach` does for an uncorrelated one. The body joins `outer` in front of its own `FROM`;
a column resolves in the body's own scope first, then in the outer row (#253). `EXISTS` counts
the body's rows and does not evaluate its select list. A body nested inside a body sees every
enclosing column, because each body's rows carry the outer columns.

**Why.** The body runs once per outer row, as in the engines, so `LIMIT` inside a body and an
error that only some outer rows raise behave as DuckDB and Postgres do. The spike measured the
cost (numbers in #462):

| Design | Cost | Faithful to the engines |
|---|---|---|
| **Outer-context index, `Query S o n`** (the plan's first idea) | 428 of the 1910 `SqlCore`/`SqlBridge` theorems change type; 161 proofs unfold `Query.eval`/`typeOf` or induct on `Query` and break; predicates become `Expr (o + n)` | yes |
| **`outer` + `lateral`** (chosen) | about the cost of `Query.one` (#473): new match arms, `In` versions of the equation and typing lemmas, 3 bridge proof edits; two theorems about the `WHERE` shape (`elabWhere_one_inSub`, `elabWhere_one_scalar`) need a hypothesis that the body is uncorrelated | yes: 14 correlated queries agreed with SqlEquiv, DuckDB and Postgres in the spike |
| **Decorrelation at elaboration** (semijoin, or an aggregate per outer row) | a new constructor all the same | no: per-row `LIMIT` and per-row errors cannot be expressed (`AggCall.first` evaluates every row); covers a subset of `lateral` |

**Accepted limits.** Query equivalence (`Query.Equiv`) is defined with no outer row, so the
simplifier and the laws leave `lateral` bodies alone; laws about bodies (decorrelation, pushing a
predicate into a body) need an equivalence under an outer row and are not planned. The outer row's
types are checked against the `outer` leaf's annotation when the query is typed, and
`evalIn_spec` covers it.

Still to agree before phase 6 (#295): the Spider elaboration-rate target for
retiring the untyped semantics (#298).
