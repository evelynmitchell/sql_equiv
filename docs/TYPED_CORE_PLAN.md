# Typed core plan

This tracks #287. The decisions are in [`TYPED_CORE_DECISIONS.md`](TYPED_CORE_DECISIONS.md).

## Goal

Rebuild the semantic core in the typed style of cslib-frontier's SQL development
(`CslibFrontier/Languages/SQL`, pinned at `e78796a1`; its one SQL commit since, the proof
refactor `841a64b4e`, is ported too, #415; re-diffed against upstream `d619c680e` on
2026-11-22, which adds no SQL feature):

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
| `SqlCoreTest/SubqueryExamples.lean` | uncorrelated subqueries (`Query.attach`) and correlated bodies (`Query.lateral`) checked by `decide` |
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
  - [x] Elaborator correctness roadmap (#352, closed 2026-11-22 at 512 of the 520 elaborated
    Spider queries), below. The eight left continue in #407 and #409 to #413 (#407 and #409
    to #412 done, 2026-11-22: 519; #413 closed as not planned, 2026-11-23)
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
    - [x] Step 3c: `AVG` as an item, grouped or not, its value related up to `SqlEquiv`'s rounding
      (`SqlBridge/CorrectAvg.lean`, `AvgRel`; decided 2026-11-21). Spider coverage **403**, up
      from 384. `AVG` in `ORDER BY` stays outside; in `HAVING` see step 6c
    - [x] Step 4: `BETWEEN`, in expressions and in `HAVING` (`Translates.between`,
      `TranslatesH.between`). Spider coverage **407**, up from 403
    - [x] `LIKE` in the expression fragment (`Translates.like`, 2026-11-22), case-sensitive or,
      as the sqlite dialect parses it, ignoring ASCII case. Both evaluators simulate the same
      pattern automaton; `SqlBridge/CorrectLike.lean` shows the matchers equal
      (`likeMatch_eq`) and that `SqlEquiv`'s lowercase-then-match is the typed core's
      match-ignoring-case (`likeMatchCI_eq`: lowercasing keeps `%` and `_` and makes no other
      character one of them). Not in `HAVING`. Spider coverage **512**, up from 504
    - [ ] Step 4's other operators (`IS NULL`, negation, arithmetic, `IN (list)`): no Spider
      query needs them; left until the bar for phase 9 is set (decided 2026-11-21)
    - [x] Step 5: plain `SELECT DISTINCT`, up to the order of the rows
      (`SqlBridge/CorrectDistinct.lean`, `elabStmt_correct_distinct`; registry T18). Spider
      coverage **428**, up from 407
    - [x] Step 6a: set operations, `UNION [ALL]`, `INTERSECT`, `EXCEPT`, nested, up to the order
      of the rows (`SqlBridge/CorrectSetOp.lean`, `elabStmt_correct_setOp`; registry T18;
      decided 2026-11-21). Spider coverage **466**, up from 428
    - [ ] Step 6b: `IN` / `NOT IN` with an uncorrelated subquery (23 Spider queries)
      - [x] A plain outer query, `WHERE e [NOT] IN (plain subquery)`
        (`SqlBridge/CorrectSub.lean`, `elabStmt_correct_inSub`). Spider coverage **475**, up
        from 466
      - [x] The same under aggregates without `GROUP BY` (`elabStmt_correct_agg_inSub`; the
        aggregate theorem now takes its `WHERE` abstractly, `elabStmt_correct_agg_w`). Spider
        coverage **483**, up from 475
      - [x] The same next to an `AVG` or a bare column (`elabStmt_correct_aggBare_inSub`; the
        grouped and bare-column theorems take their `WHERE` abstractly too). Spider coverage
        **486**, up from 483
      - [x] Under `a AND …` and under plain `DISTINCT` (`InSubWhere`,
        `elabStmt_correct_distinct_inSub`). Spider coverage **488**, up from 486
      - [ ] With a grouped or set-operation body (2 queries): needs those theorems under an
        outer row, and the membership test up to the order of the body's rows
    - [ ] Step 6c: an uncorrelated scalar subquery in a comparison (16 Spider queries)
      - [x] `a op (SELECT …)` over a plain body or one of aggregates other than `AVG`, alone
        or under `AND`, in a dialect that takes the first row of several (sqlite); the `IN`
        clauses get the same forms (`SubWhere`, replacing `InSubWhere`). Spider coverage
        **497**, up from 488
      - [x] Bodies that are an `AVG` (5 queries; **decided 2026-11-21:** under a size bound).
        `AvgWhere`: the compared expression is not a decimal (`NonDecimalIn`; true of any
        column in a schema without decimal columns, `nonDecimalIn_col`) and the average's
        denominator is at most `10¹⁶` (`AvgBound`; true when `FROM` has at most that many
        rows, `avgBound_of_rows`). `SqlEquiv` rounds the quotient to 16 places; against an
        integer that cannot change the comparison under the bound (`cmp_agree_avg`). Also under
        `GROUP BY` (`elabStmt_correct_grouped_inSub`, for every `AnySubWhere` clause). Spider
        coverage **502**, up from 497
      - [x] `HAVING AVG(c) op k`, by the same argument per group (`HavingAvgOk`,
        `TranslatesH.cmpAvg`; 2 queries). Spider coverage **504**, up from 502
      - [ ] Bodies with `ORDER BY … LIMIT 1` (2 queries, one grouped)
    - [ ] `DISTINCT` with `ORDER BY` (1 Spider query, an unselected sort key with `LIMIT`).
      **Left outside, decided 2026-11-21:** a full step (the `AggCall.first` shape has no
      correctness lemma) for one query that Postgres rejects (registry row 5). Both
      evaluators already agree on it in the differential tests; it can be proved later
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
- [ ] Phase 9: retire the untyped semantics (#298), option B (port every feature first; plan
  below, chosen 24 Nov 2026)
  - [ ] 9.0 Decisions and the typed-coverage metric (#458): metric, Postgres harness, D1–D4
    done (24 Nov 2026); D5 decided (accept and re-base)
  - [x] 9.4a Spike for EXISTS and correlated subqueries (24 Nov 2026): go, with `Query.outer` and
    `Query.lateral` (decision D6 in `docs/TYPED_CORE_DECISIONS.md`; report in #462)
  - [x] 9.1a `SELECT` without `FROM` (24 Nov 2026): `Query.one`, a source of one row with no
    columns; typed corpus 504 → 553. Follow-ups: set operations across INT/DECIMAL and untyped
    NULL branches (#472); the parser rejects `WHERE`/`ORDER BY` after a FROM-less `SELECT`
  - [x] 9.1 scalar functions, `IN` over non-literals (#459): `UnOp.round d`, `lower`, `upper`,
    `length` in the typed core (typing, soundness, canonical order); COALESCE, NULLIF, ABS and
    CONCAT written with `CASE` by the elaborator, `IN` over non-literals with `OR`. Corpus
    597 → 630. SqlEquiv's CONCAT (two arguments, NULL propagates) differs from the engines (any
    number, NULLs skipped); left as is (D4)
  - [x] Set operations across INT/DECIMAL and untyped NULL branches, `CASE`/`COALESCE` promotion
    (#472): `UnOp.toDecimal`; branches aligned when one has no `FROM` (the bridge theorems'
    branches all have one). Corpus 630 → 647
  - [x] 9.2 Non-recursive CTEs, by inlining (#460): `SqlBridge.Inline` substitutes each CTE as a
    derived table (`FROM c AS x` → `FROM (body) AS x`) wherever a table can occur, the bodies in
    order (a CTE sees the earlier ones; a body naming its own CTE reads the base table), in
    `elabQuery`, so `elabQueryRaw` and the bridge theorems are unchanged (`elabQuery_of_raw`).
    Every body must elaborate, used or not (registry T23); a name defined twice is an error. 22
    `WITH` queries agree with SqlEquiv, DuckDB and Postgres or are rejections; one is a SqlEquiv
    bug (#482). Corpus 874 → 879: every non-recursive `WITH` over the test schema. Not done: an
    `EXISTS` body over a CTE (a body over a derived table, 9.4b "richer bodies"); a CTE body with
    `ORDER BY`/`LIMIT` over a set operation; `WITH` before DML
  - [x] 9.3 Outer joins (#461): `Query.outerJoin kind θ q₁ q₂` with `JoinKind` left, right or full
    (`Row.outerRows`): `θ` evaluated on every pair, as for an inner join; each left row's matches,
    or the row padded with `NULL` (left, full), then each right row that matches nothing, padded
    (right, full). A `NULL` has every type, so the typing rule is the inner join's and soundness
    is `Row.outerRows_spec`. Laws: `outerRows_left_nil`, `outerRows_full_nil_left`,
    `eval_outerJoin_left_of_nil` (an empty side); the row counts of inner, left, right and full
    joins with `NULL` keys on both sides, and the padded rows, are kernel examples
    (`OuterJoinExamples`); inner ⊆ outer and right = left with the sides swapped are not general
    theorems yet. Simplifier, canon and
    checker: opaque. Elaborator: `joinOf` in `elabFrom`'s join case (`ON` required); the bridge
    theorems are unchanged (their fragment has inner and cross joins only). 14 queries agree with
    DuckDB and Postgres, 13 with SqlEquiv; the empty-side case is a SqlEquiv divergence (registry
    T26). Corpus 884 → 889: every outer join in the corpus
  - [ ] 9.4b EXISTS and correlated subqueries, design D6 (#462):
    - [x] core: `outer`, `lateral`, `evalIn`/`typeOfIn`, `evalIn_spec`, `Equiv.lateral`, the law
      `lateral_closed` (a body that reads no outer row, and cannot fail, is a cross join)
    - [x] correlated subqueries and `EXISTS` in `WHERE` (`elabCorrBody`: `SELECT items FROM f
      [WHERE w] [LIMIT n]`, aggregates without `GROUP BY`); the 6b/6c theorems ask for an
      `uncorrelated` body (`CorrectSub.uncorrelated`); 14 queries agree with SqlEquiv, DuckDB and
      Postgres
    - [x] subqueries in other positions, correlated or not (`attachSubs`): the SELECT list,
      `HAVING`, and items over the groups (the probe of an `IN` may be an aggregate); FROM-less
      outer queries; `EXISTS` over a set operation; with window functions as the probe of an `IN`
      (9.5). Not done: JOIN ON, ORDER BY, a `CASE` branch (rejected: the typed core evaluates an attached subquery
      whether or not the branch is taken), bare columns next to a subquery. Corpus 560 → 597
    - [ ] richer bodies (GROUP BY or set operations in a correlated body), if the corpus asks
  - [x] 9.5 Window functions (#463): `Query.window` with a `WinCall` (partition expressions,
    sort keys, and ROW_NUMBER, RANK, DENSE_RANK or an aggregate over the partition's rows that do
    not sort after the row, the SQL default frame `RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT
    ROW`), one column per window, appended to the row; typing, `evalIn_spec`, `Equiv.window`,
    simplifier, canonicaliser and checker arms. The elaborator attaches a `window` per distinct
    window node of the items and `ORDER BY`, over the `FROM` rows or over the groups after
    `HAVING` (aggregates in the window's argument and keys read their columns), before the
    subqueries of the SELECT list, so the probe of an `IN (subquery)` may be a window. `SELECT
    DISTINCT` applies after the windows. The bridge theorems are unchanged: their fragments have
    no window functions, and the elaborator takes the old path when there are none
    (`selectHasWindowFn_frag`, `orderExprs_noWindow`). 44 window queries agree with SqlEquiv,
    DuckDB and Postgres (one documented DuckDB difference: NULLs last under `DESC`, registry row
    1). Corpus 647 → 834; the one window statement left has its window in a subquery in a join's
    `ON`, where no subquery elaborates yet. Not done: a subquery inside a window's argument
    (`subsOf` does not look inside a window); explicit frames (`ROWS`, `RANGE … PRECEDING`), rejected by the parser; a window as the
    probe of an `IN (subquery)` under `GROUP BY` (the subqueries attach before `HAVING`)
  - [x] 9.6 Recursive CTEs (#464). Decided 25 Nov 2026: the engines' working-table iteration;
    an error (`EvalError.recursionLimit`) after 1000 rounds that still add rows (registry T25);
    Postgres's rules for the recursive step in every dialect, DuckDB's extras recorded as a
    known divergence (T24, #485).
    - [x] linear recursion, Postgres's rules, in every dialect: `Query.recurse distinct rounds
      base step`, the step evaluated once per row of the previous round's new rows, that row
      being its outer row (`outer`); `UNION` removes duplicates against every row so far; typing
      (the step keeps the base's types), soundness (`recurseRounds_spec`), simplifier, canon and
      checker arms (opaque); kernel examples mirroring the engine probes (`RecurseExamples`).
      Elaborator (`elabWith`): one recursive CTE per `WITH`, its body `base UNION [ALL] step`, the
      step naming the CTE once as a source of its `FROM` and without aggregates, `DISTINCT`,
      `GROUP BY`, `ORDER BY` or `LIMIT`; the step and everything after the CTE are elaborated with
      the CTE as one more table (`NamedSchema.withView`), which `bindView` replaces by `outer` and
      by the `recurse` query; the bridge theorems are unchanged. 22 queries agree with SqlEquiv,
      DuckDB and Postgres or are Postgres's rejections. Corpus 879 → 884
    - not done, by decision (#485): the duckdb dialect's extras (the CTE twice, aggregates,
      subqueries, `DISTINCT` or windows in the step, a type cast back), which read the whole
      working table; recorded in registry T24
  - [x] 9.7 INSERT, UPDATE, DELETE (#465): `SqlCore.Stmt` (`insert t q`, `update t set w`,
    `delete t w`) and `Stmt.exec : Database S → Except EvalError (Database S)`, atomic; type
    soundness `Stmt.exec_spec` (a well-typed statement on a conforming instance gives a conforming
    instance or a runtime error). `UPDATE` holds every column's new value as an expression over the
    old row, so `SET a = b, b = a` swaps (T21), and evaluates it only on rows `WHERE` keeps.
    `SqlBridge.elabDml`: `INSERT … VALUES` as a `UNION ALL` of one-row projections, `INSERT …
    SELECT` as a projection of the `SELECT`, by position or column list (others `NULL`); fewer
    values than columns per dialect (T19); only values of the column's type, `NULL` or an integer
    into `DECIMAL` (T20). 47 statements checked against DuckDB and Postgres, statement then
    `SELECT *` (`DmlDiffTest`, 76 comparisons). Corpus 834 → 874. Not done: subqueries in
    `UPDATE`/`DELETE` and in `VALUES`; `INSERT … SELECT` over a set operation (the parser takes one
    `SELECT`); `RETURNING`
  - [ ] 9.8 Switch over and retire `SqlEquiv`'s evaluator (#466). Final form decided: D7 (a
    labelled reference oracle, with the bridge theorems).
    - [x] Spider evaluate harness on the typed core (`spider_elab --eval`,
      `SqlBridge.SpiderEval`), `SqlEquiv` beside it; ratchets re-based (D5): exact 520 → 489,
      evaluate-agreement 559 → 520; the 44 queries the typed core does not elaborate are the only
      disagreements between the two (report section "Typed core vs SqlEquiv")
    - [x] the CLI (REPL `eval` and `equiv`, and `--file`) on the typed core (`SqlBridge.Cli`):
      `eval` elaborates and evaluates (DML: the written table), `equiv` asks `Query.checkEquiv`
      for a proof, else compares on the sample database; the reference oracle's answer is shown,
      labelled, where the typed core does not elaborate or disagrees. `normalize` waits for the
      rewriter swap
    - [x] D3 decided (25 Nov 2026): the 714 theorems stay as the oracle's theory; nothing is
      ported or deleted. `certifiedRewrite`, `checkEquivFull`, the statement checkers, the
      `sql_equiv` tactic and `Strict.lean` stay as oracle-level tools (D7 amended);
      `SqlCore.simplify` / `checkEquiv` are the project's rewriter and checker
    - [x] the evaluator and its tools labelled as the reference oracle (module docs); README
      overview, trust and CSLib sections; `/audit` config; `TESTING_STRATEGY.md`
  - [ ] 9.9 Upstream conversation with cslib-frontier (#467)

## Phase 9 plan (#298, option B)

Chosen on 24 Nov 2026 over the alternatives:
- (A) retire `SqlEquiv` now, at Spider parity, dropping what only it evaluates;
- (C) make the typed core the default and keep `SqlEquiv` as a labelled oracle.

Option B ports every feature `SqlEquiv` evaluates to the typed core first, then switches over.
Revised the same day after a review (probes on sqlite and DuckDB).

**Done when** (#298): `lake build` and the full test suite pass with the typed core as the only
semantics on the proof path, and `/doc-freshness` is clean.

**The engines are the oracle (decided 24 Nov 2026).** A feature ported in phase 9 is validated
against DuckDB and Postgres by differential tests through the typed core (the harness in
`SqlCoreTest`, today DuckDB only: #458 adds Postgres). No bridge proof against `SqlEquiv` is
required for it. The reason: `SqlEquiv` is wrong in exactly these features, and is being retired.
Confirmed on sqlite and DuckDB:

| Statement | `SqlEquiv` | Engines |
|---|---|---|
| `t LEFT JOIN e`, `e` empty | the left row, with no right columns (padding comes from `rightRows.head?`) | right columns padded with NULL |
| `UPDATE t SET a = b, b = a` on (1, 2) | (2, 2): each SET sees the earlier ones | (2, 1): every SET reads the old row |
| `INSERT INTO t VALUES (5, 6)` | a row with columns `col0`, `col1` | columns `a`, `b`, by position |

These are not fixed in `SqlEquiv`; the typed core follows the engines. The existing bridge proofs
(`SqlBridge/Correct*.lean`) stay as they are until 9.8. Each step still proves what is internal
to the typed core: typing, soundness, laws, simplifier and checker congruence.

**Measuring progress.** Spider cannot measure this phase: by a pattern search, none of its 564 dev
queries uses an outer join, EXISTS, a CTE, a window function, DML or a scalar function.
Progress is measured by #458's metric: the share of the SQL in the unit tests and the
differential suites that elaborates into the typed core, ratcheted in CI. The PR counts below are
guesses made before that metric exists: its first report also shows what the elaborator rejects
inside areas listed as supported, and the plan is re-estimated then.

| Step | Feature | Typed-core work | Decisions | PRs (guess) | Issue |
|---|---|---|---|---|---|
| 9.0 | Decisions, metric | D1 dialects (elaboration time only, or reopen decision 8); D2 sqlite's quiet errors (drop, or keep as oracle); D3 the fate of `SqlEquiv`'s 714 theorems; D5 Spider after the switch (below); the corpus metric; Postgres in the typed differential harness | D1, D2, D3, D5 | 1–2 | #458 |
| 9.4a | **Spike** for EXISTS and correlated subqueries, on a throwaway branch | prototype queries over an outer context (`Query S o n`); alternatives: a `correlate` constructor, decorrelation at elaboration; count the theorems that break | **go/no-go**, and which design | 0 | #462 |
| 9.1a | `SELECT` without `FROM` | a one-row source in `Query` (80 corpus statements); done, `Query.one` | | 1 | #459 |
| 9.1 | COALESCE, NULLIF, ABS, ROUND, LENGTH, UPPER/LOWER, CONCAT; `IN` over non-literals | `Expr` constructors, typing, soundness, simplifier congruence | | 1–2 | #459 |
| 9.2 | `WITH` (non-recursive) | none: inlined at elaboration | | 1 | #460 |
| 9.3 | LEFT / RIGHT / FULL joins | one `Query.outerJoin` with a kind (left, right, full), NULL padding from the schema, laws | | 2 | #461 |
| 9.4b | EXISTS, correlated subqueries | D6: `Query.outer` and `Query.lateral` | | 3–4 | #462 |
| 9.5 | Window functions | `Query.window` (partition, sort, function per row), composing with `aggregate` | | 3–4 | #463 |
| 9.6 | `WITH RECURSIVE` | `Query.fix`, fuel-bounded | stop on bag equality as engines do, or on list equality; what running out of fuel is (an error, in a strict core, or the rows so far as `SqlEquiv`) | 2 | #464 |
| 9.7 | INSERT / UPDATE / DELETE | `Stmt.exec : Instance → Except Error Instance`, conformance preserved; UPDATE reads the old row; INSERT fills columns by position | | 2–3 | #465 |
| 9.8 | Switch over | CLI, Spider harness and differential suites on the typed core, both semantics compared during the transition (the three divergences above are expected); typed simplifier and checker become the project's (the old ones and `SqlEquiv/Strict.lean` stay as oracle-level tools, D7 amended); D3 and D5 carried out; README trust sections | the final form (decided: D7, a labelled reference oracle) | 3–5 | #466 |
| 9.9 | Upstream | inventory of upstreamable modules, proposed order; the user opens the conversation | | | #467 |

**First report of the metric (24 Nov 2026, `benchmarks/typed_corpus/report.md`).** 504 of 983
test statements (51.3%) elaborate; 180 more strings are left out (parser rejections, tables or
columns outside the test schema). What does not elaborate, by class:

| Statements | Class | Step |
|--:|---|---|
| 171 | window functions | 9.5 |
| 80 | `SELECT` without `FROM` (`SELECT 1`, `SELECT 0.1 + 0.2`) | **9.1a, new** |
| 61 | subqueries the fragment lacks (EXISTS, correlated, other positions) | 9.4 |
| 61 | type errors | none: mostly tests of ill-typed queries (aggregates over booleans or strings, mixed-type MIN/MAX, a number against a string literal), which the typed core rejects by design; to be sorted in 9.8 into kept rejections and sqlite-only behaviour (D2) |
| 45 | DML | 9.7 |
| 32 | scalar functions (ROUND 14, ABS 9, LOWER 6, UPPER 2, COALESCE 1) | 9.1 |
| 12 | `WITH` | 9.2, 9.6 |
| 7 | `IN` over non-literals (`a IN (b)`) | **9.1, added** |
| 5 | outer joins | 9.3 |
| 5 | bare columns outside the decided cases | none (rejections) |

So the plan changes in two ways. A step 9.1a is added: `SELECT` without `FROM`, a one-row source
(a `Query` constructor for the empty-arity single row, or `VALUES`), which is small and worth 80
statements. And the order within 9.5–9.7 follows the corpus: windows (171) first, then DML (45).
Outer joins matter least here (5 statements). The ceiling is about 920 of 983, since the
type-error tests stay rejected.

**D3 inventory** (theorem counts by `grep`, 714 in all). The fates below were proposed; decided on
25 Nov 2026 instead: every group stays, relabelled as the reference oracle's theory (D3, D7), and
nothing is ported or deleted.

| Module | Theorems | What they are | Proposed fate |
|---|--:|---|---|
| `Equiv/Comparison.lean` | 200 | comparison and three-valued-logic laws for `≃ₑ` | port what `SqlCore`'s scalar and expression laws lack; delete the rest |
| `Equiv/StatementAxioms.lean` | 102 | statement-level laws: set operations, joins, subquery unnesting, pagination facts | port the laws that hold in the typed core (`QueryLaws`), delete facts tied to `SqlEquiv`'s row representation |
| `SemanticsCore.lean`, `Semantics.lean`, `SemanticsBase.lean` | 193 | unfolding and congruence lemmas of the evaluator | delete with the evaluator (or keep with it, if it stays as an oracle) |
| `Equiv/ValueLemmas.lean`, `Equiv/ExprAxioms.lean` | 102 | value-level and algebraic laws, `normalizeExpr` | port what `SqlCore.Simplify`/`Canon` lack; delete the rest |
| `Equiv/Decidable.lean`, `Rewriter.lean` | 52 | `checkEquivFull`, `certifiedRewrite` and their soundness | replaced by `SqlCore.Check` and `SqlCore.Simplify`; delete |
| `Equiv/Defs.lean`, `Equiv/SetBagLemmas.lean` | 52 | the relations `≃ₑ`, `≃ₛ`, `≃ᵩ`, bag and set lemmas | delete with the relations; list lemmas of general use move to `SqlCore` |
| `AstSize.lean` | 10 | size lemmas for termination | stay if anything total over the AST stays (parser side) |
| `Strict.lean` | 3 | strict-layer transfer | delete (the typed core is strict) |

**D5, Spider after the switch (decided 24 Nov 2026: accept and re-base).** 44 Spider queries do not elaborate (sqlite type
affinity, left out by decision on 23 Nov). `SqlEquiv` evaluates them, so retiring its evaluator
takes the Spider evaluate-agreement ratchet from 559 to at most 520. Either accept that (the
ratchets are re-based on the typed core and `CLAUDE.md`'s north-star text updated), or keep
`SqlEquiv`'s evaluator as a fallback for those queries. Picked: accept; the 44 queries are
recorded as rejected by design when #466 re-bases the ratchets.

**Order:**
1. 9.0.
2. The 9.4a spike (done: D6 keeps the core query type, so nothing after it waits on 9.4b).
3. 9.1–9.3.
4. 9.4b.
5. 9.5–9.7, in any order (9.6 builds on 9.2).
6. 9.8 last.

9.9 can run at any time. Each PR goes through the operating loop: code, proofs, tests and docs
together, `/critical-self-review`, `/audit`, engine differential cases.

**Human gates:** D1, D2, D3, D5; the 9.4 go/no-go (decided: D6); the recursive-CTE stopping rule; the final
form of the retirement.

**Main risk (retired 24 Nov 2026):** 9.4 might have changed the core query type every typed-core
proof is built on. The spike found a design that does not (D6).

## Elaborator correctness roadmap (#352)

`elabStmt_correct` is what connects the two evaluators: whenever the elaborator accepts a query,
the typed query's result rows match `SqlEquiv`'s, which the differential tests check against
sqlite, DuckDB and Postgres. It is also the precondition for retiring the untyped semantics
(phase 9, #298). Its fragment today (steps 1 to 3b-6 done) is
`SELECT e₁, …, eₖ FROM f [WHERE p] [ORDER BY c₁, …] [LIMIT n] [OFFSET m]`
(`elabStmt_correct_join`), where `f` nests tables (optionally aliased) under inner joins and
cross joins without `ON`, with literals, columns, comparisons, `BETWEEN`, `AND`, `OR` and `NOT` (in `ON`
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
| 3b-6. Bare columns without `GROUP BY`, ordering by a key column (done) | 384 |
| 3c. `AVG` items, up to rounding (done) | 403 |
| 4. `BETWEEN` (done) | 407 |
| 5. Plain `DISTINCT`, up to row order (done) | 428 |
| 6a. Set operations, up to row order (done) | 466 |
| 6b (part). `WHERE e [NOT] IN (plain subquery)`, plain outer query (done) | 475 |
| 6b (part). The same under aggregates without `GROUP BY` (done) | 483 |
| 6b (part). The same next to `AVG` or bare columns (done) | 486 |
| 6b (part). The clause under `AND`, and under `DISTINCT` (done) | 488 |
| 6c (part). Scalar subqueries over plain, `MIN`, `MAX`, `COUNT`, `SUM` bodies (done) | 497 |
| 6c (part). Scalar subqueries over an `AVG` body, under a size bound (done) | 502 |
| `HAVING AVG(c) op k`, under the same bound (done) | 504 |
| `LIKE` (done) | 512 |
| `IN` / `NOT IN` and scalar subqueries with a grouped body (#409, done) | 513 |
| `IN` / `NOT IN` with a set-operation body (#410, done) | 514 |
| Subquery bodies with `ORDER BY … LIMIT`, plain and grouped (#411, done) | 516 |
| `COUNT(*)` over a derived table, set-operation bodies included (#412, done) | 517 |
| Today: `SELECT *` (#407, done) | 519 |
| `DISTINCT` with an unselected sort key and `LIMIT` | 520 |

Nothing else is outside after that.

#352 was closed on 2026-11-22 with eight queries outside. Each has an issue:

| Issue | Queries | What |
|---|---:|---|
| #407 (done) | 2 | `SELECT *`. `itemsStar` admits fragment items and `*` (not `t.*`) anywhere in the list; `elabStmt_correct_star` relates `SELECT … FROM f [WHERE p] [LIMIT n] [OFFSET m]` with such items: the elaborator expands `*` to the `FROM` scope's columns in order, `SqlEquiv` returns the source row, which has exactly those columns in that order (`KeyedRow`), and `OutRel` compares by position (`star_items_rel`). `elabStmt_correct_join` takes `itemsStar` (with `ORDER BY` its items must be named, so star-free), and so does `Leaf.plain`, which brings in the `UNION` query. The other theorems keep `itemsFragment`: under an outer row `SqlEquiv`'s `*` returns the outer columns too, so `*` stays outside subquery bodies (and `DISTINCT`, `GROUP BY`, `ORDER BY`, a subquery `WHERE`) |
| #409 (done) | 1 | `IN` / `NOT IN` with a grouped body. The grouped theorem now concludes under every outer row (`elabStmt_correct_grouped_ctx`: `SqlEquiv`'s grouped path has the same closed form on source rows `row ++ ctx`, for any `ORDER BY`), and `BodyOk.grouped` admits a body whose item columns are all keys, without an `AVG` item or an `AVG` comparison in `HAVING`; no `ORDER BY` or `LIMIT` in the body |
| #410 (done) | 1 | `IN` / `NOT IN` with a set-operation body. `SubBodyOk` takes `UNION [ALL]`, `INTERSECT` and `EXCEPT` over `BodyOk` bodies, nested; `subBody_ctx` relates such a body under every outer row up to row order (`CorrectSetOp.setOpQuery_rel`), and `inExpr_eval_perm` shows membership does not see the order. A set operation as a scalar subquery stays outside: its value is the first row |
| #411 (done) | 2 | A scalar subquery with an `ORDER BY … LIMIT 1` body (one plain, one grouped). Under an outer row `SqlEquiv` sorts each projected row next to its source row with the outer row stripped (`evalSelectCore_project_ordered_ctx`); since every column the typed row resolves is found before the outer row (`Found`), lookups and projections read the same (`rowRel_strip`, `projRow_append`), and `elabStmt_correct_join_ctx` now concludes under every outer row with `ORDER BY` and `LIMIT` (`finish_rel_ctx`). The grouped theorem already did (#409). `BodyOk.plain` and `BodyOk.grouped` take `ORDER BY` and `LIMIT` / `OFFSET`, for `IN` bodies too. Ties: both evaluators sort stably over rows related in order, so the row `LIMIT 1` picks is the same |
| #412 (done) | 1 | A subquery in `FROM` (over a set operation). `elabStmt_correct_countDerived` (`SqlBridge/CorrectDerived.lean`): `SELECT COUNT(*), … FROM (sq) [AS al]`, no `WHERE`, over a `SubBodyOk` body (`subBody_ctx`, fuel 15 = 14 + 1). The body's rows are related only up to order; `COUNT(*)` reads only their number, so the outer row is related exactly. Left out: other aggregates, `WHERE` or plain items over a derived table, and a derived table under a join: they read its columns, which needs the keys of `SqlEquiv`'s output rows (the statement theorems relate values by position, `OutRel`); and order-dependent outer queries over a set-operation body |
| #413 | 1 | `DISTINCT` with an unselected sort key and `LIMIT`; left outside by decision, confirmed and closed as not planned (2026-11-23) |

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
   - **3c, `AVG` up to rounding, done** (19 queries; decided 2026-11-21). `AVG` is an exact
     rational in the typed core (T10) and rounded half away from zero to `max 16 s` places in
     `SqlEquiv` when it does not terminate (row 7); the engines differ too (sqlite and DuckDB a
     float, Postgres a numeric of about 16 digits), the standard leaving it to the
     implementation. Of the options (leave it out; assume the averages terminate, a condition on
     the data; make one evaluator round like the other; relate the values up to rounding) the
     theorem takes the last and changes neither evaluator: an `AVG` item's untyped value is the
     typed quotient rounded half away from zero to some `p ≥ 16` places (`CorrectAvg.AvgRel`;
     equal when the quotient terminates within them). `divRoundHalfAway_eq` shows `SqlEquiv`'s
     integer rounding is `roundHalfAway` of the rational quotient, and `avg_agree` that the
     scaled sums agree (as for `SUM`). The output relation becomes per item (`ItemRel`,
     `OutRelI`): exact for every column but `AVG` items, so 3b-1 to 3b-3 keep their exact
     statements (`outRel_of_outRelI`). `AVG` in `HAVING` or `ORDER BY` stays outside: rounding
     can flip a comparison when the compared value is the rounded one (`1.3333333333333333 <
     avg` with the average 4/3); a bound on the row count (rows × 10^scale below about 10^16)
     would rule that out, a later step if wanted.
4. **`BETWEEN`, done** (4 queries; the other operators of this step add none). Both evaluators
   read `e BETWEEN lo AND hi` as `e >= lo AND e <= hi`: the elaborator desugars it, `SqlEquiv`
   evaluates it so, with or without an aggregate inside. So the proof is the comparison and
   `AND` cases composed (`Translates.between`), and in `HAVING` the same over the aggregate's
   output (`TranslatesH.between`; without an aggregate inside, `SqlEquiv` hands the predicate
   to its row evaluator, `evalWithAgg_of_noAgg`). No new hypothesis.
   **Left out, decided 2026-11-21:** `IS NULL`, unary minus, `+ - *` and `IN (list)` have no
   known divergence but add no Spider query; integer `/` and `%` would ride on the existing
   nonzero-literal-divisor condition (division by zero is a typed error and a quiet `none` in
   `SqlEquiv`, registry T2); decimal `/` and `%` cannot be related, `SqlEquiv` not implementing
   them (#201). They wait for the phase 9 bar (#298).
5. **Plain `DISTINCT`, done up to row order** (21 queries; decided 2026-11-21, registry T18).
   The two evaluators remove the same duplicates (rows equal column by column, `NULL` tags
   erased, numbers by value: `row_eq_iff_valueKey`, from `COUNT(DISTINCT)`'s `trel_iff`) and
   keep different copies: the typed core the last (`List.dedup`, as in cslib-frontier),
   `SqlEquiv` the first (`dedupByKey`, as sqlite); DuckDB and Postgres hash. SQL fixes no order
   without `ORDER BY`, so the theorem relates the typed rows to `SqlEquiv`'s up to a
   permutation and changes neither evaluator: the elaborated query is `Query.distinct` of the
   plain statement's (`elab_distinct_shape`), `SqlEquiv`'s result is `dedupByKey` of the plain
   statement's (`evalSelectCore_distinct`), and `elabStmt_correct_join` relates the two plain
   results in order (`distinct_rel`). The options not taken: elaborating `DISTINCT` as a
   grouping (first-copy order, but the core's `DISTINCT` operator would go unused) and changing
   the core's `DISTINCT` (diverges from the frontier). `DISTINCT … LIMIT` without `ORDER BY`
   can keep a different row in each evaluator and stays outside, as does the one Spider query
   with an unselected sort key. `QNoBoolOrder` now looks through `Query.distinct` (it was
   vacuously true there).

6. **Subqueries and set operations** (80 queries; none uses a CTE, `EXISTS` or a correlated
   subquery). Three parts, in this order (decided 2026-11-21):
   - **6a. Set operations, done up to row order** (38 queries). Both evaluators compare rows the
     same way (`row_eq_iff_valueKey`) and, as for `DISTINCT`, keep different copies of a
     duplicate: `SqlEquiv` the first (`dedupByKey`), the typed core the last (`List.dedup`, in
     `Query.distinct` and `Row.setOp`). So `UNION`, `INTERSECT` and `EXCEPT` return the same rows
     in a different order, and the theorem relates the two up to a permutation, changing
     neither evaluator (registry T18 extended). The proof is compositional: `PermRel` (related
     up to order) is preserved by concatenation, deduplication and filtering by membership in
     the other branch (`permRel_append`, `permRel_dedup`, `permRel_filter_mem`); a compound
     query that elaborates has branches that elaborate to one type (`elab_compound_shape`); so
     related branches give a related compound query (`compound_rel`), and by induction any
     tree of set operations over related leaves is related (`setOpTree_rel`).
     `elabStmt_correct_setOp` instantiates the leaves (`Leaf`) with the statements of
     `elabStmt_correct_join`, `_distinct`, `_agg` and `_grouped` that have no `ORDER BY` or
     `LIMIT`. Left out: branches with an `AVG` item (related only up to rounding, which a row
     comparison could tell apart), bare columns without `GROUP BY`, and a trailing
     `ORDER BY`/`LIMIT` over the set operation (with `LIMIT` the kept rows can differ; no Spider
     query has one). `QNoBoolOrder` now descends into set operations (it was vacuously true
     there).
   - **6b. `IN` / `NOT IN` subqueries** (23 queries), **the plain case done** (9 queries):
     `SELECT … FROM f WHERE e [NOT] IN (SELECT e' FROM f' [WHERE p']) [ORDER BY …] [LIMIT n]`,
     rows related in order (`elabStmt_correct_inSub`). The pieces, in `SqlBridge/CorrectSub.lean`
     unless noted:
     - *The body ignores the outer row.* `SqlEquiv` evaluates the body on rows `inner ++ outer`,
       once per outer row. Lookups take the first match, so a row related to a typed row stays
       related with columns appended (`rowRel_append`), and the body's result under any outer
       row relates to the typed rows (`elabStmt_correct_join_ctx`, in `CorrectJoin.lean`; without
       `ORDER BY`, where `SqlEquiv` aligns the sort on rows without the outer row).
     - *The value.* The typed three-valued membership (`Datum.inList`) is TRUE exactly when
       `SqlEquiv` finds a match and unknown exactly when it finds none and a `NULL` takes part
       (`inList_agree`, `inSub_agree`), whatever the order of the body's rows.
     - *The clause.* The elaborator attaches the membership test as a last column, filters on
       it and projects it away (`elabWhere_inSub`); that pipeline keeps the rows `SqlEquiv`'s
       filter keeps (`attachFilter_rel`).
     - *The statement theorems take the `WHERE` abstractly.* `WhereOk` (in `CorrectJoin.lean`)
       says what a statement theorem needs of the clause's elaboration; a fragment predicate
       provides it (`whereOk_frag`) and so does the subquery clause (`whereOk_inSub`).
       `elabStmt_correct_join` is unchanged, now a corollary. The elaborator's inline `WHERE`
       handling became the named function `elabWhere` for this (no behaviour change).
     - `QNoBoolOrder` now constrains attached subqueries (it was vacuously true there).

     The aggregate theorem takes `WhereOk` too (`elabStmt_correct_agg_w`), which gives the
     clause under aggregates without `GROUP BY` (`elabStmt_correct_agg_inSub`, 8 queries).

     So do the grouped and bare-column theorems (`elabStmt_correct_grouped_w`,
     `elabStmt_correct_aggBare_w`; `elabStmt_correct_aggBare_inSub`, 3 queries).

     *The clause under `AND`.* The elaborator elaborates the whole predicate among the columns
     with the attached one appended (named `?subquery?`), a hook replacing the subquery node by
     that column. A fragment expression elaborated there is its elaboration among the original
     columns, re-indexed (`elabExpr_weaken`), provided it does not refer to that name
     (`noRefTo`; the parser has no quoted identifiers, so SQL text cannot, but a hand-built AST
     could, and would read the attached column in the typed core and an unknown column in
     `SqlEquiv`). The pipeline lemma takes any predicate over the extended row
     (`attachFilter_rel`), and `whereOk_attach` turns "the predicate relates to the clause,
     given the attached column relates to the subquery node" into `WhereOk`. The `DISTINCT`
     theorem takes `WhereOk` too (`elabStmt_correct_distinct_w`).

     Still to do in 6b: bodies that are grouped or set operations (2 queries).
   - **6c. Scalar subqueries** (16 queries), **the first part done** (9 queries). A clause is
     now a context around one subquery node (`HoleCtx`: the node, `a op node` for a comparison,
     either under `AND` on either side), and `holeCtx_elab` relates the elaborated clause to
     the untyped one given only that the attached column relates to the node's value. So the
     two node kinds differ in one lemma each (`NodeOk`, inside `whereOk_of_subWhere`): an `IN`
     node attaches the membership test, a scalar node the body's first value, `NULL` for an
     empty body, as `SqlEquiv` reads it. The typed core's safety check wants the dialect to
     take the first of several rows (`scalarSubqueryRows = firstRow`, sqlite), so the theorem
     assumes it; in Postgres or DuckDB a body with two rows is an error there and a value in
     `SqlEquiv`. Bodies (`BodyOk`): a plain statement or one of aggregates
     (`elabStmt_correct_agg_w`, which now also holds under every outer row), both without
     `ORDER BY`/`LIMIT`; the `IN` clauses gain the aggregate body and the other `AND` order.

     *`AVG` bodies* (5 queries, done). The typed core keeps the exact quotient, `SqlEquiv`
     rounds it to at least 16 places, so the attached column relates to the node's value only
     up to rounding (`AvgRel`). `holeCtx_elab` therefore takes the relation at the attached
     column as a parameter: it must decide a comparison (`hRcmp`) and be exact on what an `AND`
     accepts (`hRbool`). For an integer `z` and a quotient `q` with denominator at most `10ᵖ`,
     `z ≠ q` puts them at least `10⁻ᵖ` apart, and rounding to `p` places moves `q` by at most
     half of that (`compare_int_round`), so both evaluators order `z` and the average alike.
     The two hypotheses this adds are not syntactic, and each has a lemma that discharges it.
     `NonDecimalIn`: the compared expression does not have type decimal (a decimal could sit
     between the average and its rounding). It holds for integer literals (`nonDecimalIn_lit`)
     and, in a schema without decimal columns, for every column among the columns of any
     `FROM` tree (`nonDecimalIn_col`, by `from_noDecimal`); Spider's typing has no decimal
     column. `AvgBound`: the denominator bound. It holds when the `AVG` argument is not a
     decimal and `FROM` has at most `10¹⁶` rows (`avgBound_of_rows`: an average of integers
     has a denominator at most the number of rows averaged, `avg_den_le`, and a `WHERE` only
     removes rows); for a single table that is a bound on the table (`fromRows_table`). What
     the coverage count still assumes is that data bound. `CorrectExamples` instantiates both
     lemmas on the Spider-shaped test schema. The body theorem is
     `elabStmt_correct_aggBare_ctx`, the bare-column aggregate theorem under an outer row.

     *`AVG` in `HAVING`* (2 queries, done 2026-11-22). The same argument per group:
     `HAVING AVG(c) op k`, the average of a column against an integer literal
     (`CorrectGroup.cmpAvgForm`), is a new case of the `HAVING` translation
     (`TranslatesH.cmpAvg`), related by `cmp_agree_avg_left`. The grouped theorem takes
     `HavingAvgOk`, which asks nothing of a `HAVING` without such a comparison and otherwise
     that no column of the schema is a decimal and that `FROM` has at most `10¹⁶` rows: the
     average is then one of integers over a group, its denominator at most the group's size
     (`avg_den_le`, `Row.length_le_of_mem_groups`). Other uses of `AVG` in `HAVING` (the
     literal on the left, against another aggregate, `AVG(DISTINCT …)`, a decimal literal)
     and `AVG` in `ORDER BY` stay outside, as does such a `HAVING` in a branch of a set
     operation.

     Still to do: `ORDER BY … LIMIT 1` bodies (2 queries).

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
- **The `Spec` refactor (upstream #5583, `841a64b4e`; here #415).** Type soundness is stated as
  a postcondition, `Except.Spec x P E` (`x` succeeds with a result satisfying `P` or fails with
  an error satisfying `E`), which composes along `>>=` by `Spec.bind`: `Expr.eval_spec`,
  `Expr.evalTruth_spec`, `Expr.filterRows_spec`, `Expr.evalRow_spec`, and for this repo's
  extensions `AggCall.eval_spec`, `AggCall.evalAll_spec` and `Query.eval_spec` (whose error side
  is `EvalError.IsRuntime`, wider than upstream's division by zero). The older statements
  (`eval_ok_or_divisionByZero`, `evalAll_ok_or_divisionByZero`, `eval_ok_or_runtimeError`,
  `conforms_of_eval_eq_ok`) are corollaries, so `SqlBridge` is unchanged. `Except.ok` is the simp
  normal form of `pure`; `bind_comm_of_eq_error` replaces the per-operator commutation lemmas;
  `EquivLevel.Rel.lift` derives the unary `Rel` lemmas. Differences from upstream: the lemmas
  live in `SqlCore.Except`, so the predicate is written `Spec x P E` where upstream writes
  `x.Spec P E`; `Spec.imp_right`, `Spec.ok_or_error` and `Spec.of_ok_or_error` are added (the
  first for the wider error class, the others so the `attach` case of `Query.eval_spec` keeps
  its proof); upstream's shortened proofs in `QueryLaws` and `Simplify` are not ported (they
  change no statement).

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
