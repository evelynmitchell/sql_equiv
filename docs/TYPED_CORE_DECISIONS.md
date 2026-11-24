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
| D5 | Spider after the switch: the evaluate ratchet falls from 559 to at most 520 (44 type-affinity queries do not elaborate) | **Open.** Accept and re-base the ratchets, or keep `SqlEquiv`'s evaluator as a fallback for those queries. |

Still to agree before phase 6 (#295): the Spider elaboration-rate target for
retiring the untyped semantics (#298).
