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
| `SqlBridge/Elab.lean` | elaborator from parsed SQL to typed queries (library `SqlBridge`) |
| `SqlBridge/Spider.lean`, `SqlBridge/SpiderMain.lean` | Spider schemas; `lake exe spider_elab`, driven by `tools/spider_elab_baseline.py` |
| `SqlCoreTest/BridgeDiffTest.lean` | parsed SQL through `SqlBridge` and through `SqlEquiv`, compared as bags |
| `SqlCoreTest/DuckdbDiffTest.lean` | parsed SQL through `SqlBridge` + `SqlCore` vs the `duckdb` CLI |
| `SqlCore/Simplify.lean`, `SqlCore/Check.lean` | certified simplifier and checkers |
| `SqlCore/Canon.lean` | canonical forms modulo AC, with strong-equivalence certificates |
| `SqlBridge/CliMain.lean` | `lake exe sqlcore check …`: parse, elaborate, check |
| `SqlCoreTest/SimplifyExamples.lean` | the frontier's simplifier tests, and checker examples |
| `SqlCore/Aggregate.lean` | aggregate calls: evaluation over a group, typing, soundness |
| `SqlCoreTest/AggregateExamples.lean` | `GROUP BY` and aggregates checked by `decide` |
| `SqlCoreTest/OrderByExamples.lean` | `ORDER BY`, `LIMIT` and `OFFSET` checked by `decide` |
| `SqlCoreTest/SetOpExamples.lean` | `INTERSECT`, `EXCEPT` and `LIKE` checked by `decide` |
| `SqlCoreTest/SqliteDiffTest.lean` | sqlite-dialect bare columns and multi-row scalar subqueries through the bridge, against sqlite |
| `SqlCoreTest/SubqueryExamples.lean` | uncorrelated subqueries (`Query.attach`) checked by `decide` |
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
- [x] **Phase 6: bridge from the parsed AST, differential tests** (#295)
  - [x] Elaborator `SqlBridge/Elab.lean`: parsed `SqlEquiv.Query` to `SqlCore.Query S n`
  - [x] Schema from the test database; differential test against `SqlEquiv` on parsed SQL
  - [x] Schema from Spider's `tables.json`, and the Spider elaboration rate: **129/564 (22.9%)**,
    [`elab_report.md`](../benchmarks/spider/elab_report.md), ratcheted in CI
  - [x] Differential test against DuckDB; differences registered (`IMPLEMENTATION_DEFINED.md`, rows T1–T8)
  - [x] Elaborator correctness for single-table `WHERE` and column lists (#309):
    `SqlBridge/Correct.lean`, `elabStmt_correct`. For `SELECT e₁, …, eₖ FROM t [AS a] [WHERE p]`
    with literals, columns, comparisons, `AND`, `OR` and `NOT`: when the statement elaborates,
    the typed query evaluates, and its rows relate, in order, to `SqlEquiv`'s (values by `ValRel`:
    a typed decimal is the rational of an untyped scaled integer; a typed `NULL` is an untyped
    `NULL` of any tag; column names are dropped). Hypotheses: the untyped database relates to
    the typed one (`DbRel`), the schema's fold keeps names equal ignoring case (`id`, or
    `String.toLower` as Spider's schemas use, since #351), column names have no dots and
    are distinct ignoring case (`WellNamed`), and no ordering comparison has two boolean
    operands (`QNoBoolOrder`: the typed core orders `false < true`, `SqlEquiv` does not order
    booleans). `SqlCoreTest/CorrectExamples.lean` checks the hypotheses on the bridge test schema
  - [ ] Elaborator correctness roadmap (#352), below
    - [x] Step 0: case-folding schemas (#351)
    - [x] Step 1: `ORDER BY` column keys, `LIMIT`, `OFFSET`: `SqlBridge/CorrectOrder.lean`,
      `elabStmt_correct_ordered`. Spider coverage **113**, up from 64
    - [x] Step 2: inner and cross joins: `SqlBridge/CorrectJoin.lean`, `elabStmt_correct_join`.
      Spider coverage **165**, up from 113
    - [x] Step 3a: aggregates without `GROUP BY` (`COUNT`, `COUNT(DISTINCT)`, `SUM`, `MIN`,
      `MAX`; not `AVG`): `SqlBridge/CorrectAgg.lean`, `elabStmt_correct_agg`. Spider coverage
      **258**, up from 165
    - [x] Step 3b-1: `GROUP BY` columns, items keys or aggregates: `SqlBridge/CorrectGroup.lean`,
      `elabStmt_correct_group`. Spider coverage **288**, up from 258
    - [x] Step 3b-2: `HAVING`: `elabStmt_correct_having`. Spider coverage **303**, up from 288
    - [x] Step 3b-3: ordering by aggregates, `LIMIT`/`OFFSET`: `SqlBridge/CorrectGroupOrder.lean`,
      `elabStmt_correct_group_ordered`. Spider coverage **333**, up from 303
    - [x] Step 3b-4: bare columns read on the group's first row (registry T9), and every
      combination of `HAVING`, `ORDER BY` aggregates and `LIMIT`: one statement,
      `SqlBridge/CorrectGrouped.lean`, `elabStmt_correct_grouped`, of which 3b-1 to 3b-3 are
      instances. Spider coverage **380**, up from 333
    - [x] Step 3b-5: bare columns next to one `MIN`/`MAX`, read on the row where its argument is
      extreme (`AggCall.atExtreme`, `SqlBridge/CorrectExtreme.lean`), in the same statement.
      Spider coverage **381**, up from 380
    - [x] Step 3b-6: the same without `GROUP BY` (`SqlBridge/CorrectAggBare.lean`,
      `elabStmt_correct_aggBare`), and ordering a grouped query by a key column (`OrderKeyOk`, in
      `elabStmt_correct_grouped`). Spider coverage **384**, up from 381
    - [ ] `AVG`, after the decision on its rounding (registry rows 7 and T10)
    - [ ] Step 4: `IS NULL`, negation, arithmetic, `IN (list)`, `BETWEEN`
    - [ ] Step 5: `DISTINCT`
- [x] **Phase 7: certified simplifier, decision procedure, tactics** (#296)
  - [x] Simplifier `SqlCore/Simplify.lean` (`Expr.simplify`, `Query.simplify`, with certificates)
  - [x] Certified checkers `SqlCore/Check.lean` (`Expr.checkEquiv`, `Query.checkEquiv`)
  - [x] CLI `lake exe sqlcore check TABLES.json DB "SQL1" "SQL2"` (`SqlBridge/CliMain.lean`)
  - [x] Canonical forms `SqlCore/Canon.lean` (AC-sorted `AND`/`OR` chains, ordered operands of
    `=`, `<>`, `+`, `*`, `>`/`>=` turned into `<`/`<=`); the checkers compare canonical forms
  - [x] Tactics `sql_expr_equiv`, `sql_query_equiv` (`decide +kernel`)
  - [x] Comparison with `SqlEquiv`'s certified rewriter (below)
- [x] Phase 8: features beyond the frontier (#297), *offered upstream*. Done when the Spider
  elaboration rate matches `SqlEquiv` except for schema-typing defects. The bar was first
  "about 553/564" (#297); it was revised on 2026-11-17 to exclude the sqlite type-affinity
  queries, which a typed core rejects by design (see "Phase 8 result" below). **520/564 (92.2%)**
  - [x] 8a GROUP BY, HAVING, aggregates (#313)
    - [x] Core: `AggCall`, `Query.aggregate`, typing, type soundness, simplifier and checker
    - [x] Elaboration from SQL, differential tests, Spider rate: **268/564 (47.5%)**, up from 129
  - [x] 8b ORDER BY, LIMIT, OFFSET (#318)
    - [x] Core: `SortKey`, `Query.orderBy`, `Query.limit`, typing, type soundness, congruences,
      simplifier and checker
    - [x] Elaboration from SQL, differential tests, Spider rate: **364/564 (64.5%)**, up from 268
  - [x] 8c INTERSECT, EXCEPT, LIKE (#322)
    - [x] Core: `Query.intersect`, `Query.difference`, `BinOp.like`, typing, type soundness,
      congruences at every level, laws, simplifier and checker
    - [x] Elaboration from SQL, differential tests, Spider rate: **405/564 (71.8%)**, up from 364
  - [x] 8d AVG and decimal `/`, exact (#326; decides #201 for the typed core)
    - [x] Core: exact `divDec`, `AggFn.avg`, typing and type soundness
    - [x] Elaboration, differential tests, Spider rate: **426/564 (75.5%)**, up from 405
  - [x] 8e Bare columns per dialect (registry T9)
    - [x] Core: `AggCall.atExtreme`, typing and type soundness
    - [x] Bridge (`DialectConfig.bareColumns`), sqlite differential, Spider rate: **479/564
      (84.9%)**, up from 426
  - [x] 8f Uncorrelated subqueries in `WHERE` (#329), and derived tables
    - [x] Core: `Query.attach`, `SubKind`, `EvalError.cardinality`; soundness generalised to runtime
      errors (`Query.eval_ok_or_runtimeError`); congruence; simplifier and checker
    - [x] Bridge (nested, compound bodies, correlated rejected), differential tests, Spider rate:
      **519/564 (92.0%)**, up from 479
- [ ] Phase 9: retire the untyped semantics (#298)

## Elaborator correctness roadmap (#352)

`elabStmt_correct` is what connects the two evaluators: whenever the elaborator accepts a query,
the typed query's result rows match `SqlEquiv`'s, which the differential tests check against
sqlite, DuckDB and Postgres. It is also the precondition for retiring the untyped semantics
(phase 9, #298). Its fragment today (steps 1 to 3b-6 done) is
`SELECT e₁, …, eₖ FROM f [WHERE p] [ORDER BY c₁, …] [LIMIT n] [OFFSET m]`
(`elabStmt_correct_join`), where `f` nests tables (optionally aliased) under inner joins and
cross joins without `ON`, with literals, columns, comparisons, `AND`, `OR` and `NOT` (in `ON`
too), where the `ORDER BY` keys are column references and, when there is an `ORDER BY`, every
item is a column or has an alias; and `SELECT agg₁, …, aggₖ FROM f [WHERE p]`
(`elabStmt_correct_agg`) with `COUNT(*)`, `COUNT([DISTINCT] e)`, `SUM(e)`, `MIN(e)`, `MAX(e)`;
and the same with `GROUP BY c₁, …` columns, each item a key column, such an aggregate or a bare
column read on the group's first row (no `MIN`/`MAX` written) or on the row where the one
`MIN`/`MAX` argument is extreme, with an optional `HAVING` of key
columns, such aggregates, literals, comparisons, `AND`, `OR` and `NOT`, ordered by such
aggregates or by key columns no other item's name captures, with `LIMIT`/`OFFSET`
(`elabStmt_correct_grouped`); and aggregates next to bare columns without `GROUP BY`
(`elabStmt_correct_aggBare`).

**Measured coverage.** `lake exe spider_elab` lists, for every Spider query that elaborates, the
features that put it outside the fragment (`SqlBridge/Coverage.lean`, `outsideFragment`; checked
against the theorem's own shape, `stmtShape`, in `SqlCoreTest/CorrectExamples.lean`).
`tools/spider_elab_baseline.py` turns them into the coverage table of
[`elab_report.md`](../benchmarks/spider/elab_report.md): the queries in the fragment today and
after each step below. At the time of writing (20 Nov 2026, 520 queries elaborate):

| Step | Spider queries in the fragment |
|------|-------------------------------:|
| Before step 1 | 64 |
| 1. `ORDER BY` / `LIMIT` (done) | 113 |
| 2. Joins (inner, cross) (done) | 165 |
| 3a. Aggregates without `GROUP BY`, not `AVG` (done) | 258 |
| 3b-1. `GROUP BY` columns, items keys or aggregates (done) | 288 |
| 3b-2. `HAVING` (done) | 303 |
| 3b-3. Ordered by aggregates, `LIMIT` (done) | 333 |
| 3b-4. Bare columns on the first row, all combinations (done) | 380 |
| 3b-5. Bare columns at a `MIN`/`MAX` under `GROUP BY` (done) | 381 |
| Today: 3b-6. Bare columns without `GROUP BY`, ordering by a key column (done) | 384 |
| 4. `IS NULL`, negation, arithmetic, `IN (list)`, `BETWEEN` | 388 |
| 5. `DISTINCT` | 410 |

Still outside after step 5: subqueries, set operations and CTEs (80), `AVG` (24, pending the
rounding decision), `LIKE` (8), `*` (2). (With `AVG`, the rows after steps 3b–5 were 405, 409
and 431.)

**Step 0, a prerequisite: case folding (#351), done.** The theorem used to assume the schema
does not fold names (`fold = id`), while Spider's schemas lowercase them, as sqlite's names are
case-insensitive; so it applied to none of the Spider queries above. It now takes any fold that
keeps names equal ignoring case (`(fold s).toLower = s.toLower`), and `DbRel` asks the untyped
database to answer every spelling the fold maps to a table's key (the `Database` decides how
names match, registry row 20, #372). `CorrectExamples` checks the hypotheses on a Spider-shaped
schema and that mixed-case Spider references (`SELECT T1.name FROM SINGER AS T1 WHERE t1.AGE …`)
elaborate into the fragment. So the "Today" row is now queries the theorem covers.

**Order, and why.** #352 first listed the steps by proof cost: unary operators, arithmetic,
`IN`/`BETWEEN`, `DISTINCT`, joins. Measured on Spider, those first four steps add almost
nothing: the queries that use them also use aggregates, joins or `ORDER BY`. The order above
follows coverage instead (decided 20 Nov 2026):

1. **`ORDER BY` / `LIMIT`, done.** The cheapest large step. Both evaluators sort stably, keep
   input order on ties (registry rows 2 and T14) and carry an explicit NULL position on every
   key, so the in-order output relation (`List.Forall₂ OutRel`) stays as it is.
   `SqlBridge/CorrectOrder.lean` proves `elabStmt_correct_ordered` in layers:
   - `SqlEquiv` sorts with `List.mergeSort`, the typed core with an insertion sort
     (`sortKeyed`). Both are stable, so they agree whenever the comparator is total and
     transitive on the list (`mergeSort_eq_insertionSort_of_mem`; ties allowed).
   - Per key, `SqlEquiv`'s `orderKeyCmp` and the typed `SortKey.cmpDatum` agree on related
     values (`cmpDatum_agree`), and so do the lexicographic comparators (`compareBy_agree`).
   - The typed comparator is a total preorder on rows that conform to the context
     (`transCmp_cmpKeyRows`, `keyed_total_trans`).
   - An elaborated key resolves to the same value in both evaluators (`orderKey_rel`):
     `SqlEquiv` sorts the projected row followed by the source row and looks the key up by
     name, the elaborator looks it up among the output names first, then in scope.

   New hypotheses, each checked satisfiable on a Spider-shaped schema in `CorrectExamples`:
   keys are column references (`hcols`); with an `ORDER BY`, items are columns or aliased and
   output names have no dot (`itemsNamed`, since `SqlEquiv` names an unaliased expression
   `expr`, the elaborator `?column?`); the fold identifies exactly the names equal ignoring
   case (`hfoldCI`, `String.toLower` does; `id` does not, so the bridge test schema is out for
   `ORDER BY`); and `QNoBoolOrder` also rules out boolean keys. On Spider, every query ordered
   by something other than a column, and every unaliased item next to an `ORDER BY`, is an
   aggregate query (`ORDER BY count(*)`), so step 3 takes those on.
2. **Joins (inner and cross), done.** `SqlBridge/CorrectJoin.lean` proves
   `elabStmt_correct_join` for a `FROM` tree of tables (optionally aliased) under inner joins
   (`ON` a fragment condition, or none) and cross joins without `ON`, nested as Spider writes
   them (`FROM a AS T1 JOIN b AS T2 ON … JOIN c AS T3 ON …`):
   - Both evaluators build a join as the cross product, left row outermost, filtered by `ON`
     (`evalFrom_join_filter`; the typed `Query.join` is `Row.product` then `filterRows`), so
     the `WHERE` argument of #309 carries over (`product_rel`, `filter_rel_of`).
   - `RowRel` ("every resolved reference finds its value") does not compose under `++`: a
     reference resolved in the right table could match a key of the left one. `KeyedRow`
     records the keys `SqlEquiv`'s `FROM` builds (`Q.name` per column, `Q` the table name or
     alias as written), composes under joins, and implies `RowRel` (`rowRel_of_keyed`).
   - The projection, `WHERE`, `ORDER BY` and `LIMIT`/`OFFSET` reuse step 1 unchanged, as they
     only see the column list.

   New hypotheses, each checked on a Spider-shaped schema in `CorrectExamples`: the fold
   identifies exactly the names equal ignoring case (`hfoldCI`, now for every statement, since
   two tables may spell a qualifier alike up to case), and the schema's column names are their
   own folds (`hfix`: Spider lowercases them), so a name the elaborator resolves unambiguously
   in the joined columns is the one `SqlEquiv`'s first-match lookup finds; `QNoBoolOrder` also
   covers `ON`. An unqualified column that two tables share is ambiguous: the elaborator
   rejects it, so the theorem does not speak of it. Outer joins (`LEFT`/`RIGHT`/`FULL`), which
   the elaborator rejects, stay out.
3. **Aggregates and `GROUP BY` / `HAVING`.** The largest blocker, and the hardest step, split
   in two (decided 20 Nov 2026):
   - **3a. Aggregates without `GROUP BY`, done.** `SqlBridge/CorrectAgg.lean` proves
     `elabStmt_correct_agg` for `SELECT agg₁, …, aggₖ FROM f [WHERE p]`: one row on each side
     (the typed `Query.aggregate` with no keys has one group even for no rows), related item by
     item. Per aggregate, on related lists of one type: `COUNT` and `COUNT(DISTINCT)` count
     the same (`SqlEquiv` deduplicates by `Value.setKey`, which identifies exactly the equal
     typed values, via the decimal normal form of `mkDecimal`); `SUM` is the same number
     (`sumScaled` computes the rational sum; integers stay integers); `MIN`/`MAX` pick related
     values (both keep the first of ties). Every dialect mode agrees, as the typed columns
     hold no booleans or mixed types. No new hypotheses beyond step 2's. Out of 3a, and
     reported as such: `AVG` (below), `DISTINCT` in `SUM`/`MIN`/`MAX` (no Spider query),
     bare columns next to an aggregate (registry T9; 2 Spider queries), and aggregates with
     `ORDER BY`/`LIMIT` (step 3b).
   - **3b. `GROUP BY` / `HAVING`**, in four sub-steps by Spider coverage (decided 20 Nov 2026):
     - **3b-1, done.** `SqlBridge/CorrectGroup.lean` proves `elabStmt_correct_group` for
       `SELECT … FROM f [WHERE p] GROUP BY c₁, …`, column keys, each item a key column or an
       aggregate of 3a. Both evaluators group in order of first appearance and append rows to
       their group; `SqlEquiv` keys a group by the `setKey`s of its key values, which identify
       exactly the equal typed keys (as for `COUNT(DISTINCT)`), so the groups correspond one to
       one, in order (`groupAux_rel`). Per group, aggregates relate by 3a's `agg_rel`, and a key
       column, which `SqlEquiv` reads on a sample row of the group, holds the group's key. No
       new hypotheses.
     - **3b-2, `HAVING`, done** (15 queries). `elabStmt_correct_having`: the elaborator builds
       `select p` over the aggregate, `p` over its output scope; `SqlEquiv` evaluates the
       predicate per group, over the group's rows and sample row, and drops the group unless it
       is `TRUE`. `TranslatesH` relates the two predicates (aggregates read their output column,
       key columns their key column, as the elaborator's hook resolves them), and its
       evaluation lemma (`TranslatesH.eval_rel`) gives the same decision per group
       (`isTrue_iff_where`), so both keep the same groups, in order (`grouped_rel`).
     - **3b-3, ordering by aggregates, `LIMIT`, done** (30 queries, mostly
       `ORDER BY count(*) DESC LIMIT 1`). `elabStmt_correct_group_ordered`, without `HAVING`
       (no Spider query combines the two): the elaborator adds the sort keys' aggregates to the
       aggregate and sorts its output by their columns, below the projection; `SqlEquiv` builds a
       key row per group (`groupOrderKeyRow`, columns `__group_orderkey_k`) and sorts the
       projected rows together with the key rows, reading the keys back by name. The keys are
       found when no output name is dotted or a key name ignoring case (`keyRow_lookup`; a new
       hypothesis, `hnm`, which the coverage report checks); they relate by 3a's `agg_rel`, so
       the two comparators agree on related pairs and step 1's sorting argument applies to any
       such pair relation (`sorted_gen`). The one Spider query ordered by a key column is left
       to 3b-6.
     - **3b-4, bare columns, done** (47 queries, registry T9). One statement for the whole
       grouped fragment, `elabStmt_correct_grouped` (`SqlBridge/CorrectGrouped.lean`): an
       optional `HAVING`, `ORDER BY` aggregates, `LIMIT`/`OFFSET`, in any combination (filter,
       then sort), and items that are aggregates, key columns or bare columns; 3b-1 to 3b-3 are
       its instances, and their separate proofs are gone. A bare column becomes the aggregate
       `AggCall.first`; `SqlEquiv` reads it on its sample row, which is the group's first row
       when no `MIN`/`MAX` is written (`BareOk`, the one hypothesis bare columns bring).
       The elaborator used to resolve an ambiguous name against the aggregate's output, where
       only the keys keep their names: it accepted
       `SELECT name FROM singer a JOIN singer b ON … GROUP BY b.name` (sqlite: "ambiguous column
       name") and read `b.name`, where `SqlEquiv` reads the row's first `name`. It now checks
       that every item and `HAVING` column resolves in the `FROM` scope (#384). Building the
       proof also found a `SqlEquiv` bug: a `MIN`/`MAX` written twice (`SELECT b, max(a) …
       HAVING max(a) > 1`) counted as two calls, so bare columns read the first row; sqlite and
       the bridge count it once (fixed, registry T9).
     - **3b-5, the extreme row, done** (1 query under `GROUP BY`). Next to one `MIN`/`MAX`, a
       bare column reads the first row where the argument is extreme: `AggCall.atExtreme` in the
       typed core, `bareSampleRow` in `SqlEquiv`, which takes `minMaxAgg`'s value and searches
       for the first row whose argument is structurally that value. `SqlBridge/CorrectExtreme.lean`
       proves both are one fold, the first strictly best entry over a linear order (`fbest`), and
       that the search finds its pick (`atExtreme_rel`): every earlier row's typed key is `NULL`
       or strictly worse, so its untyped value differs (an untyped value relates to one typed
       value, `valRel_inj`). Decimals `1.0` and `1.00`, structurally different and equal in the
       typed core, are no obstacle: ties after the pick are never searched. `BareOk` gains a
       third case: the sqlite dialect, exactly one `MIN`/`MAX` call in the items and `HAVING`
       (counted once, not DISTINCT, in a mode that picks the row), and no other in `ORDER BY`.
       Still outside: a `MIN`/`MAX` only in `ORDER BY` picks the row in sqlite and the bridge,
       not in `SqlEquiv` (registry T9, pending a decision).
     - **3b-6, done** (3 queries). *Bare columns without `GROUP BY`* (`select max(capacity),
       average from stadium`): the elaborator builds the grouped query with no keys, so
       `elab_grouped_shape` covers it once an aggregate item rules out its plain branch
       (`groupBy ≠ [] ∨` an aggregate item). With no keys there is one group even for no rows;
       `SqlEquiv` then reads the bare columns on the empty sample row, `NULL`, as `first` and
       `atExtreme` are over no rows (`bare_eval_nil`, `col_on_empty`). The statement is
       `elabStmt_correct_aggBare` (`SqlBridge/CorrectAggBare.lean`), and `SqliteDiffTest` checks
       the empty case against sqlite. *Ordering by a key column* (`… GROUP BY document_id ORDER
       BY document_id`): a sort key may be a `GROUP BY` column that every item named like it (in
       either evaluator) is (`OrderKeyOk`). The elaborator then sorts on the key's column,
       whether the name matches an output column or not; `SqlEquiv` reads the matching output
       value or, past the output names, the sample row's column, both the group's key
       (`keyCol_lookup`). The unified proof now relates each sort key through its output
       column (`idx`), an aggregate's or a key's. The key is matched as written: `ORDER BY Age`
       after `GROUP BY age` stays outside.
   - **`AVG`, a design decision.** `AVG` is an exact rational in the typed core (T10) and
     rounded to 16 places in `SqlEquiv` when it does not terminate (row 7): the theorem can
     leave it out, assume the averages terminate, or relate values up to rounding. Left out
     for now (24 Spider queries).
4. **Unary operators, arithmetic, `IN (list)`, `BETWEEN`.** As in #352's first steps: division
   by zero (a typed error, an untyped NULL) and decimal `%` need a hypothesis or a design
   decision. These come in wherever an earlier step's queries need them.
5. **`DISTINCT`.** The output relation becomes a bag or set relation, since dedup keeps the first
   occurrence and NULL tags differ.

Each step lands with its theorem, `CorrectExamples` checks that its new hypotheses are
satisfiable, and an update of this table (the report regenerates it).

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

Decimal division was `unsupported` in phase 1, because the engines disagree on its result type and
scale. Phase 8d (#326) made it exact.
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
evaluation, typing and type soundness for every constructor (`Query.eval_ok_or_divisionByZero`,
renamed `Query.eval_ok_or_runtimeError` in phase 8f).
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

## Phase 6 notes

`SqlBridge.elabStmt` translates a parsed statement in the fragment and reports one of five
distinct failures: `unknownTable`, `unknownColumn`, `ambiguousColumn`, `unsupported` (naming
the construct) or `typeError`. The fragment is `SELECT [DISTINCT] … FROM` tables, inner and
cross joins, `WHERE`, `UNION ALL`, and `UNION`. The elaborator makes these choices:

- `UNION` is `DISTINCT (… UNION ALL …)`.
- `BETWEEN a AND b` is `≥ a AND ≤ b`.
- `NOT IN` is `NOT (… IN …)`.
- A multi-branch `CASE` is nested `caseWhen`, and a missing `ELSE` is `NULL`.
- An untyped `NULL` takes the type of the operand it meets, or the other branch of a `CASE`.
- Names match exactly (decision 7): `SELECT NAME FROM users` is `unknownColumn`.

Spider: `tools/spider_elab_baseline.py` elaborates the 564 dev queries against their schemas.
129 elaborate (22.9%). The count is ratcheted in `tools/spider_elab_minimum.txt`, and CI checks
it. The failure classes are phase 8's work list: GROUP BY 149, aggregates 122, ORDER BY 67,
subqueries 46, INTERSECT 21, EXCEPT 16, LIKE 8, derived tables 1. 5 more queries are ill-typed
under Spider's declared column types, for example a `text` age compared with `32`; sqlite
accepts these through type affinity.

Names are lowercased for Spider (`NamedSchema.fold`), because sqlite is case-insensitive. The
lookup is still exact after that normalisation, as decision 7 asks.

`SqlBridge` lives in its own library, because it imports both `SqlEquiv` and `SqlCore`. The trust
guard covers it.

`SqlCoreTest/BridgeDiffTest.lean` runs a corpus of 53 queries. 36 are in the fragment and agree
with `SqlEquiv` as bags of rows; they cover NULL, decimals, joins, `IN`/`NOT IN` with NULL,
`CASE` and set operations. 17 must be rejected with a specific failure. A seeded `BETWEEN` bug
(`>` for `>=`) is caught.

DuckDB: `SqlCoreTest/DuckdbDiffTest.lean` generates DuckDB's tables from the typed test database
(`CREATE TABLE` with the declared types, then its rows), and runs the 36 in-fragment corpus
queries through both. Results are compared as bags, with numbers as exact rationals. All 36 agree
except `age / 7`, where DuckDB's `/` returns a DOUBLE (registry T1, documented). Removing that
entry from the expected list makes the test fail. The typed core's differences from the engines
are registry rows T1–T8.

sqlite is dynamically typed, so a differential test against it is meaningful only on queries
whose columns hold values of their declared types. Its type affinity accepts the 5 ill-typed
Spider queries above. The Spider harness (`tools/spider_eval_baseline.py`) remains the sqlite
comparison, for `SqlEquiv`.

## Phase 7 notes

- **Simplifier.** `SqlCore/Simplify.lean` is the frontier's simplifier: bottom-up expression
  rewrites guarded by decidable checks, plus `WHERE` pushdown and projection fusion for queries.
  Its certificates are `Expr.equiv_simplify` and `Query.equiv_simplify` (ordered level). The
  arithmetic identity rewrites are guarded by integer type, as in the frontier; the laws behind
  them also hold for decimals, so widening the guards is a small follow-up.
- **Checkers.** `Expr.checkEquiv` and `Query.checkEquiv` return `Check.proved` with a proof when
  the two simplifications are syntactically equal, and `unknown` otherwise.
- **`Query.beq`.** `Query` cannot derive `DecidableEq`: the arity index of `table` defeats the
  deriving handler. `Query.beq` is therefore written by hand, listing every pair of constructors,
  and `Query.eq_of_beq` proves it sound.
- **CLI.** `lake exe sqlcore check benchmarks/spider/dev_tables.json concert_singer "…" "…"`
  prints `equivalent (certified …)` (exit 0), `unknown` (1), or an elaboration error (2). It is a
  separate executable, so the `sql_equiv` CLI does not link Mathlib.
- **Canonical forms (part 2).** `SqlCore/Canon.lean` rebuilds every chain of `AND` and of `OR` in
  sorted order. It also orders the operands of `=`, `<>`, `+` and `*`, and turns `>`/`>=` into
  `<`/`<=` with the operands swapped.
  - Every step holds with no side condition, so its certificate is a *strong* equivalence
    (`Expr.SEquiv`): equivalence in every typing context, so agreement on every row, since a row
    conforms to its own context (`Row.ctxOf`).
  - Strong equivalence lifts into queries without typing hypotheses (`Query.select_sexpr`,
    `project_sexpr`, `join_sexpr`, `Query.equiv_canon`).
  - The checkers compare `normalize = canon ∘ simplify`. The sort is an insertion sort, because
    `List.mergeSort` is well-founded recursion and the kernel does not unfold it.
- **What the decision procedure decides.** `checkEquiv` proves two inputs equivalent when they
  have the same normal form. That means equal up to the simplifier's rewrites, constant folding
  (which also evaluates ground subexpressions), associativity and commutativity of
  `AND`/`OR`/`+`/`*`, symmetry of `=`/`<>`, and the comparison swap. It is sound and incomplete:
  `unknown` is not a refutation.
- **Tactics.** `sql_expr_equiv` closes `Expr.Equiv Γ e₁ e₂`, and `sql_query_equiv` closes
  `Query.Equiv ℓ q₁ q₂` at any level. Both run the checker in the kernel (`decide +kernel`, no
  `native_decide`).

### `SqlEquiv`'s certified rewriter (`SqlEquiv/Rewriter.lean`) against the typed simplifier

| `SqlEquiv` rewrite | Typed core |
|---|---|
| `p AND FALSE`, `FALSE AND p` → `FALSE` (no guard) | Performed when `p` is a safe predicate. Under strict errors a failing `p` must still fail (`and_false`). |
| `p OR TRUE`, `TRUE OR p` → `TRUE` (no guard) | Performed when `p` is a safe predicate, as above (`or_true`). |
| `p AND TRUE`, `TRUE AND p`, `p OR FALSE`, `FALSE OR p` → `p` (`isDefinitelyBool`) | Performed when `p.typeOf Γ = some .bool`, which is a decidable check in place of the syntactic guard. |
| `x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x` → `x` (`isDefinitelyInt`) | Performed when `x` is an integer. The laws also hold for decimals; widening the guard is a follow-up. |
| `NOT (a op b)` → `a (negate op) b`, for the six comparisons | Performed (`not_cmp`). |
| `NOT (NOT p)` → `p` (`isDefinitelyBool`) | Performed when `p` is boolean. |
| `NOT EXISTS` flag flip | Not performed: `EXISTS` is outside the fragment. Phase 8f added uncorrelated `IN` and scalar subqueries only. |
| `x LIKE ''` → `x = ''` | Not performed by the simplifier. Since phase 8c the law is `likeText_empty_iff`. |
| `e IN ()` → `FALSE` | Performed when `e` is safe. Strict errors: a failing `e` must still fail. |
| `e NOT IN ()` → `TRUE` | Performed: `NOT (e IN ())` → `NOT FALSE` → `TRUE` (constant folding), when `e` is safe. |
| `e IN (v)` → `e = v` | Performed (`inList_singleton`). |
| `e NOT IN (v)` → `e <> v` | Performed: `NOT (e = v)` → `e <> v` (`not_cmp`). |
| `CASE WHEN TRUE THEN x ELSE y` → `x`; `WHEN FALSE` → `y`, or `NULL` without `ELSE` | Performed (`caseWhen_true`, `caseWhen_false`, `caseWhen_null`). The elaborator makes a missing `ELSE` a typed `NULL`. |
| `CASE` with no branches | Not applicable: a `CASE` always has a branch in the typed syntax. |
| `BETWEEN` → `AND(>=, <=)` | Done by the elaborator (`SqlBridge`), which desugars `BETWEEN`. |
| `normalizeExpr`: AC ordering (`Equiv/Decidable.lean`) | Performed by `Expr.canon` for `AND`, `OR`, `=`, `<>`, `+`, `*`, and comparison direction. |
| Ground evaluation (`Equiv/Decidable.lean`) | Performed by constant folding in `Expr.simplify`. An error is never folded. |

Every rewrite of `SqlEquiv`'s certified rewriter on the core fragment is performed. Rewrites
outside the fragment (`EXISTS`, `LIKE`) are left for phase 8. The typed simplifier also rewrites
queries (pushdown, projection fusion), which `SqlEquiv`'s rewriter does not.

## Phase 8 notes

Decisions (#297): GROUP BY and aggregates come first. The phase 9 bar was matching `SqlEquiv` on
Spider; it was revised on 2026-11-17 to exclude schema-typing defects (see "Phase 8 result"). `AVG`
and decimal `/` are exact rationals (#326, decided 2026-11-17; see 8d below).

**8a, core (#313).**

- `AggCall n` covers `COUNT(*)`, `COUNT/SUM([DISTINCT] e)`, `MIN(e)` and `MAX(e)`.
  - `NULL` arguments are ignored. `SUM`/`MIN`/`MAX` over no value give `NULL`; `COUNT` gives `0`.
  - `SUM` keeps `int`/`decimal`. `MIN`/`MAX` take int, decimal or text; booleans are ill-typed,
    following Postgres (registry row 14).
- `Query.aggregate keys aggs q : Query S (g + a)` groups by key tuple, in order of first
  appearance, with `NULL` keys grouping together. With no keys there is one group even for no
  rows. `HAVING` is a `select` over it.
- Type soundness (`Query.eval_ok_or_runtimeError` since 8f) covers it, as do `divSafe` and `IsSafe`.
- Congruence is proved at the ordered level only (`Equiv.aggregate`). At the bag level it needs
  grouping to be insensitive to input order. At the set level it fails, since counts change.
- The simplifier keeps a `WHERE` above an aggregate. Pushing it below is valid only for
  predicates on the keys, and would be a new law.
- Every behaviour was checked against Postgres 16 and DuckDB.

**8a, elaboration (#313).** `SqlBridge` elaborates `GROUP BY`, aggregates and `HAVING`:

- The aggregate calls of the `SELECT` list and `HAVING` are collected (`aggsOf`) and elaborated over
  the input. The query becomes `aggregate keys aggs q`.
- The `SELECT` list and `HAVING` are elaborated over the aggregate's output. A hook maps each
  aggregate call to its column, and each expression equal to a key to the key's column.
- A column that is neither grouped nor aggregated is rejected (registry T9), as the standard,
  Postgres and DuckDB do; sqlite accepts it.

The parsed-SQL corpus gained 15 aggregate queries. They agree with `SqlEquiv` and with DuckDB,
except `GROUP BY staff` over two typed NULLs, where `SqlEquiv` split the NULL group (#315). That
query was checked against DuckDB instead, until #315 was fixed (grouping keys, and since then `DISTINCT`, erase the NULL
type tag) and it agrees with `SqlEquiv` again.

Spider: 268/564 now elaborate. The largest remaining classes are ORDER BY (125), subqueries
(47), bare columns (37, a sqlite extension), AVG (27), and INTERSECT/EXCEPT (37).

**8b, core (#318).**

- `SortKey n` is an expression with a direction (`desc`) and a NULL position (`nullsFirst`).
  The NULL position is explicit. The parser fills it from the dialect when the SQL leaves it out
  (registry row 1).
- `Query.orderBy keys q` evaluates the key tuple of every row, then sorts by it with Mathlib's
  stable `List.insertionSort`. Tied rows keep their input order. Engines leave that order
  unspecified (registry T14).
  - A failing key fails the query. A key may be any well-typed expression of the input.
  - Values compare by `Value.cmp`, so `int` and `decimal` are promoted.
- `Query.limit count offset q` drops `offset` rows, then keeps `count` rows if there is a count.
- Type soundness, `divSafe` and `IsSafe` cover both.
- Congruence:
  - `Equiv.orderBy` holds at every level: sorting only permutes the rows, and bag and set
    equivalence are insensitive to permutations (`EquivLevel.Rel.perm_congr`).
  - `Equiv.limit` holds at the ordered level only: a prefix of a bag is not determined by the bag.
- The simplifier and canonical forms recurse below both nodes, and the checker compares them
  structurally. A `WHERE` above a `LIMIT` cannot move below it.

**8b, elaboration (#318).**

- Without DISTINCT, `ORDER BY` goes below the projection. A key may be any expression of the
  input, including columns that are not selected.
- Under GROUP BY, keys go over the aggregate output. Aggregates in `ORDER BY` are collected with
  those of the `SELECT` list and `HAVING`.
- A bare name is first looked up among the output names (aliases and selected columns). An
  integer literal is a 1-based position, as in Postgres, sqlite and DuckDB.
- Under DISTINCT with every key selected, the sort is above the `DISTINCT`, over the output
  columns.
- A key that is not selected under DISTINCT is a dialect choice (registry row 5, decided on #319):
  the parser rejects it in `standard` and `postgres`, as Postgres does. In `sqlite` and `duckdb`,
  each distinct row sorts by the key of its first source row, as both engines do. The bridge builds
  `aggregate` by the selected expressions with the new `AggCall.first` of each key (the first
  row's value, `NULL` included, evaluated strictly on every row), sorts on those columns and
  projects the selected ones (T13).
- `spider_elab` parses in the `sqlite` dialect, like the SqlEquiv Spider harness.
- `LIMIT`/`OFFSET` wrap the result.
- ORDER BY or LIMIT on a compound query used to be rejected, because the parser bound them to
  the last branch. Since #317 the parser builds `Query.ordered` over the whole compound. The
  bridge elaborates its keys against the compound's output columns and wraps `orderBy` and
  `limit` around it. A tail on an inner branch is a parse error, as in sqlite and Postgres.

The parsed-SQL corpus gained 28 queries (one pins the dialect's default NULL position, a documented DuckDB difference); queries with `ORDER BY` are compared as ordered lists on
tie-free keys. They agree with DuckDB. They agree with `SqlEquiv` except two positional
`ORDER BY` queries, where `SqlEquiv` sorted by a constant (#316). Since the #316 fix, which resolves
positions at parse time, they agree too; only positions after a `*` item still differ.

Spider: 364/564 now elaborate. The largest remaining classes:

| Class | Queries | Notes |
|---|---:|---|
| Bare columns (T9) | 64 | Now including queries that also sort |
| Subqueries | 47 | |
| `AVG` | 27 | |
| `INTERSECT`/`EXCEPT` | 37 | |
| Type errors | 16 | sqlite affinity |
| `LIKE` | 8 | |

**8c, core (#322).**

- `Query.intersect q₁ q₂` and `Query.difference q₁ q₂` (`EXCEPT`) are the standard set operations.
  They keep one copy of each row of `q₁` that is (or is not) a row of `q₂`. Rows compare
  positionally as wholes, so `NULL`s in the same places are equal. The parser has no `ALL`
  variants.
- Both are congruences at every level (`EquivLevel.Rel.setOp`): the right input matters only
  through which rows it contains.
- Laws:
  - `eval_difference_self` and `eval_intersect_of_eval_eq_nil`.
  - `intersect_self` (`q INTERSECT q` is `DISTINCT q`).
  - `intersect_assoc` (ordered) and `intersect_comm` (bag).
- `BinOp.like ci` is `text LIKE text → bool`, with `NULL` from `NULL`.
  - `%` matches any sequence and `_` exactly one character; there is no `ESCAPE`.
  - With `ci`, ASCII letters match regardless of case: the sqlite dialect (registry row 8, T16).
  - The matcher (`likeText`) simulates the pattern's automaton by structural recursion, so
    `decide` evaluates it.
  - It agrees with DuckDB (case-sensitive) and sqlite (`ci`) on all 676 pairs of a 26-string
    sample. The scalar differential against `SqlEquiv` checks it with an independent backtracking
    reference.
  - Laws: `likeText_pct`, `likeText_empty_iff` and `likeText_self` (every text matches itself).

**8c, elaboration (#322).** `INTERSECT` and `EXCEPT` branches elaborate like `UNION`. `LIKE` and
sqlite's `likeCI` map to `BinOp.like false` and `BinOp.like true`. The corpus gained:

- 19 queries in the default dialect;
- 4 in the sqlite dialect, compared against `SqlEquiv` and non-empty only when the match ignores
  case.

They found three `SqlEquiv` bugs, all confirmed by DuckDB, and the affected queries are checked
against DuckDB instead:

- #323: `LIKE` treats `_` and interior `%` as literals (fixed: `SqlEquiv` now uses a port of
  the typed matcher).
- #324: `INTERSECT`/`EXCEPT` compare column names (fixed).
- #324: `INTERSECT`/`EXCEPT` keep typed `NULL`s apart (fixed).

Spider: 405/564 now elaborate. The largest remaining classes are bare columns (64, T9),
subqueries (47), `AVG` (27, #201) and type errors under sqlite's affinity (20).

**8d, AVG and decimal `/` (#326).** The decision, made in session on 2026-11-17, is exact
rationals.

- Decimal `/`:
  - `1.0 / 3` is `1/3`, and a zero divisor is still `divisionByZero`.
  - Integer `/` keeps truncating (T1).
  - Decimal `/` is now well-typed, so it no longer raises the `unsupported` error.
- `AVG`:
  - It is the exact mean of an int or decimal argument, as a decimal: `SUM / COUNT`, with `DISTINCT`
    as for `SUM`.
  - It is `NULL` over no values and ill-typed over text.
- The engines all round, and each does it differently:
  - Postgres uses a scale that varies with the input, so `AVG(i) * 3` over 1, 1, 2 is
    `3.9999999999999999`.
  - sqlite and DuckDB return doubles.

  The exact value agrees with every engine whenever it is a finite decimal (T3, T10). The Spider
  harness compares numbers to 10 significant digits.
- Tests:
  - The DuckDB differential rounds both sides to 12 decimal places.
  - The scalar differential accepts a decimal `/` difference from `SqlEquiv` only if the quotient
    multiplies back exactly.
  - `SqlEquiv` still truncates `AVG` (registry row 7) and leaves decimal `/` unimplemented, so
    fractional results are checked against DuckDB.
- Spider: 426/564. The remaining classes:

  | Class | Queries | Note |
  |---|---:|---|
  | Bare columns | 64 | T9 |
  | Subqueries | 47 | |
  | Type errors | 26 | sqlite affinity, now including six `AVG`s of text columns |

**8e, bare columns (registry T9).** `SELECT max(a), b FROM t`: an error in the standard,
Postgres and DuckDB, accepted by sqlite. It is a dialect choice, `DialectConfig.bareColumns`, which
the bridge reads from `NamedSchema.config`. `spider_elab` uses the sqlite dialect.

Rules for sqlite (3.45.1), all observed:

- With one `MIN`/`MAX` call (in the select list, `HAVING` or `ORDER BY`), a bare column comes from
  the first row where that call's argument is extreme. Ties keep the first row.
- Otherwise it comes from the group's first row.
- The bridge turns each bare column into an aggregate of its own: `AggCall.atExtreme pick key e`
  (new, with typing and soundness) or `AggCall.first`.
- Two cases stay `unsupported`, because sqlite's row is arbitrary there:
  - several `MIN`/`MAX` calls;
  - `MIN`/`MAX(DISTINCT …)`, which takes the last tie.
- When every argument is NULL, the model takes the last row. sqlite's choice there depends on the
  query plan: it takes the first row when its MAX optimisation answers `WHERE a IS NULL`. That case
  is a documented divergence.

`SqlCoreTest/SqliteDiffTest.lean` checks 15 queries against the `sqlite3` CLI and checks the
rejections in both dialects. A mutation that swaps `MIN` and `MAX` fails 7 of them.

Spider: 479/564 now elaborate. What remains:

| Class | Queries | Note |
|---|---:|---|
| Subqueries | 47 | |
| Type errors | 37 | sqlite affinity: text columns compared with numbers, `AVG` of text, … |
| Derived table | 1 | |

**8f, uncorrelated subqueries (#329; design approved in session).** All 47 remaining Spider subquery
failures were in `WHERE`:

| Form | Queries |
|---|---:|
| `NOT IN (SELECT …)` | 25 |
| Scalar | 20 |
| `IN (SELECT …)` | 2 |

**Core.** A subquery adds a column. `Query.attach kind sub q : Query S (n + 1)` evaluates `sub`
(one column) once, first, then appends a column to every row of `q`:

- `SubKind.scalar firstRow`: the subquery's value.
  - No rows give `NULL`.
  - Several rows give `EvalError.cardinality`, or the first row in the sqlite dialect (T17).
- `SubKind.inSub neg e`: the truth of `e [NOT] IN (sub)`, through the three-valued `inList`.

`Expr` and `Query` stay separate. The extra column is an `Expr.evalRow` of `col`s and one computed
expression, so congruence reuses the projection lemmas:

- every level in `q`;
- the ordered level in `sub`.

**Soundness.** A well-typed query now fails only with a *runtime* error (`EvalError.IsRuntime`:
`divisionByZero` or `cardinality`), and only if it is not `divSafe`. An error-mode scalar subquery
is never `divSafe`.

**Bridge.**

- The subqueries of a `WHERE` predicate are collected (`subsOf`), elaborated recursively and
  attached. A hook maps each one to its column, and the extra columns are projected away.
- Nesting is bounded by fuel (16 levels), so elaboration stays a total function.
- Compound subquery bodies elaborate like compound queries.
- A subquery that reads the outer row is `unsupported: correlated subquery`.

**Tests.**

- Corpus: 14 queries, against `SqlEquiv` and DuckDB.
- sqlite: 2 multi-row scalar queries.
- Kernel examples, including the `NOT IN (…, NULL)` rule and the strict multi-row error.
- A mutation that swaps `IN` and `NOT IN` fails 7 queries against each oracle.

The tests found a quiet `SqlEquiv` bug, #330: `NOT IN (subquery)` ignores NULLs. It is fixed:
`SqlEquiv` now evaluates `[NOT] IN (subquery)` three-valued too.

Spider: 519/564 now elaborate. The remaining classes are type errors under sqlite's affinity (44)
and one derived table.

**Derived tables (8f).** `FROM (SELECT …) AS t` elaborates the body as a subquery, with fuel. Its
output columns are requalified by the alias, as in `SqlEquiv` (#257). The corpus gained 4 queries.
They agree with DuckDB. They agree with `SqlEquiv` except a `UNION ALL` body whose branches name a
column differently: `SqlEquiv` reads it by the first branch's name, which is the #324 root cause.
Since the #324 fix, the later branch's rows take the first branch's names, and it agrees.

**Phase 8 result.** 520/564 Spider dev queries elaborate, up from 129 after phase 6. All 44 that
remain are type errors that sqlite accepts through *type affinity*. The Spider schemas declare a
column's type inconsistently with how queries use it:

| Kind | Queries | Example |
|---|---:|---|
| A `text` column compared with a number literal | ≈22 | `year = 2014` |
| Join keys declared `text` on one side and `number` on the other | ≈15 | |
| An aggregate over a `text` column | ≈6 | `avg(age)` |
| A double-quoted string compared with a number | 1 | |

On 2026-11-17 these were classified as schema defects that a typed core rejects by design. The
phase 8 bar became "`SqlEquiv`'s coverage minus these", and it is met: every Spider query
`SqlEquiv` handles either elaborates or is one of these 44.

The two options not taken are recorded for later:

- **Literal coercion in the bridge** for the sqlite dialect (`year = 2014` read as
  `year = '2014'`, which is exactly what sqlite does): about 22 queries, with no core change.
- **A text-to-number conversion in the core:** all 44, but a semantics change.

## Rules for every phase

- No `sorry`, no project axioms and no `native_decide` in `SqlCore`. CI enforces this through
  `#assert_trust_base SqlCore` and `#assert_no_runtime_overrides SqlCore`.
- Design decisions are human gates.
- Docs ship with behaviour, so each phase ticks its box above.
