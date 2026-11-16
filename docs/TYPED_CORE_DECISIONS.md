# Typed core: design decisions

These are the picks recorded on #288 (15 Nov 2026) for the typed core (`SqlCore`, #287).
Changing one is a design decision: propose it on an issue and wait for a pick
(`CLAUDE.md`).

| # | Question | Pick |
|---|---|---|
| 0 | Build on cslib-frontier, or re-derive it? | **Hybrid.** Re-derive phases 1–3 (values, rows, typed expressions) by hand, to learn the design. Then depend on [cslib-frontier](https://github.com/cslib-community/cslib-frontier) for queries and laws (phases 4–5). Phases 6 (bridge, oracles, Spider) and 8 (features beyond the frontier) are built on it and offered upstream. |
| 1 | Mathlib | **Yes, in `SqlCore` only, from phase 1.** It arrives through the frontier from phase 4 anyway. `SqlEquiv` does not import it. |
| 2 | Error behaviour | **Strict, as in the frontier.** A predicate or projection that fails on any row fails the whole query. Laws that move, duplicate or drop an expression carry a decidable safety condition. (This contrasts with `SqlEquiv`'s quiet errors, #270.) |
| 3 | Library name and location | **`SqlCore`, a Lake library in this repo** (namespace `SqlCore`, tests in `SqlCoreTest`). cslib-frontier is added later as a `require`. |
| 4 | Types in the first cut | **`int`, `text`, `bool`**, then exact `decimal` at the end of the values phase. Float stays deferred (#202). *Decimal storage (picked at #290 part 2): Mathlib `ℚ`, so `2.50 = 2.5` structurally and the order is Mathlib's; kernel evaluation needs `decide +kernel`.* |
| 5 | Bags | **`List` with `List.Perm`**, as in the frontier. |
| 6 | Comparison across types | **Both operands of a comparison have one type** (the frontier's rule), *except int↔decimal, which promotes (picked at #290 part 2): `1 = 1.0` is `TRUE` and `1 + 0.5` is `1.5`, as in Postgres, DuckDB and `SqlEquiv`. The typing relation is `SqlType.Comparable`.* #254 is the precedent in `SqlEquiv`. |
| 7 | Name case and resolution | **Exact match; an ambiguous reference is an elaboration error.** Names are normalised before resolution. |
| 8 | Dialects | **A single semantics, with no dialect modes in the typed core.** Engine differences are listed as known divergences in the oracle tests and in `docs/IMPLEMENTATION_DEFINED.md`. |
| 9 | Reference engines | **Postgres and DuckDB.** sqlite is kept only for Spider fidelity. |

Still to agree before phase 6 (#295): the Spider elaboration-rate target for
retiring the untyped semantics (#298).
