# Implementation-Defined SQL Behaviour

Some SQL behaviour is left to each engine by the standard (or is standardised
but implemented differently in practice). Engines then disagree, and "correct"
depends on which engine you compare against. This document is the single place
that records, for each such behaviour, what the standard says, what the engines
we test against actually do, what **we** do, why, and how it is tested.

It has two parts: the **policy** for deciding and testing these behaviours, and
the **registry** of known cases.

---

## Policy

### 1. Choosing a behaviour

Queries are checked against a target **dialect**: `standard` (the default),
`sqlite`, `duckdb` or `postgres` (`Dialect` in `SqlEquiv/Ast.lean`). Users pick
it with `parse sql (dialect := .postgres)`, the CLI's `--dialect <name>`, or the
REPL's `dialect <name>`. A dialect is a profile, `Dialect.config : DialectConfig`,
with one field per configurable registry row.

In order of preference:

1. **The standard defines it** → follow the standard, in every dialect.
2. **Implementation-defined, and it has an AST node to carry the choice** →
   add a field to `DialectConfig`, give each dialect its engine's observed
   behaviour, and have the parser write the choice into the AST. Evaluation
   and proofs never see the dialect, so theorems that quantify over statements
   cover every dialect automatically. Examples: NULL ordering (row 1, the
   `NullsOrder` of each ORDER BY item) and MIN/MAX over mixed types and
   booleans (rows 13–14, the `MinMaxMode` of each MIN/MAX).
3. **Implementation-defined with no AST node** (e.g. how `=` coerces mixed
   types, rows 10–12) → choose one behaviour and record it here. If per-dialect
   behaviour is wanted later, this is where an *evaluation-time* dialect
   parameter would come in (a larger change: equivalences become per-dialect).

The **`standard` dialect** follows the standard; where the standard itself
leaves the choice to the implementation, it takes the Postgres behaviour (the
standards tiebreaker), e.g. NULL largest. The Spider harness runs in the
`sqlite` dialect because Spider's gold results come from sqlite.

Choosing or changing a behaviour is a **design decision**: per CLAUDE.md, present
the options with trade-offs and wait for a pick. Record the decision here, with
the issue or PR.

### 2. Testing requirements (every registry row)

- **Pin our choice**: a unit test in `Test/` that asserts our behaviour, so it
  cannot change silently.
- **Agreeing engines**: a differential case in `LSpecTests/DiffSqlite.lean` /
  `DiffDuckdb.lean` for each engine that agrees with us. Each harness parses in
  its engine's dialect (`parse sql (dialect := .duckdb)`), so configurable rows
  are checked against the engine's own choice.
- **Disagreeing engines**: either an explicit *disagreement* test that asserts
  the engine's different answer, or an entry in that harness's KNOWN
  DIVERGENCES header pointing back to this registry. Never just avoid the case.
- **Verify by running, not by memory**: engine behaviour in this document was
  observed on the versions below. Re-run when adding or changing a row.

### 3. The Spider harness never hides a divergence

`tools/spider_eval_baseline.py` compares against sqlite. Where we tolerate or
emulate an implementation-defined difference, the harness counts it in its own
labelled category with a self-test (as with **tie-valid** answers), never as a
silent pass.

### 4. Changing a row

Same PR: update this registry, the harness KNOWN DIVERGENCES headers, the
unit/differential tests, and (if the default changes) the Spider ratchet.

---

## Engines and their roles

Observed with **sqlite 3.45.1**, **DuckDB 1.5.3** and **PostgreSQL 16.15**
(all installed in the dev environment; Postgres is started on demand with
`pg_ctlcluster 16 main start`).

| Engine | Role (from #225) | Harness |
|---|---|---|
| sqlite | Spider-fidelity target: Spider's gold results were computed on it | `LSpecTests/DiffSqlite.lean`, `tools/spider_eval_baseline.py` |
| DuckDB | Standards and DECIMAL cross-check (strict types, real DECIMAL) | `LSpecTests/DiffDuckdb.lean` |
| PostgreSQL | Standards tiebreaker | none yet (#224) |

**Cross-cutting difference:** where DuckDB and Postgres raise a *query error*,
our evaluator returns `none` for the expression. In a WHERE clause that silently
drops the row; in a SELECT list it shows as NULL. So our "error" is quieter than
theirs. Rows below say "ours: error (row dropped)" for this.

---

## Registry

Legend for **Status**: *decided* (deliberate, tested), *open* (divergence with an
open decision or issue), *gap* (behaviour matches no engine or is untested).

| # | Behaviour (example) | Standard | sqlite | DuckDB | Postgres | **Ours** | Status | Tests |
|---|---|---|---|---|---|---|---|---|
| 1 | NULL position in ORDER BY (`ORDER BY price` with a NULL) | Implementation-defined; `NULLS FIRST/LAST` syntax | NULL smallest (first ASC, last DESC) | NULLs last both ways | NULL largest (last ASC, first DESC) | **Per dialect** (`DialectConfig.nullOrdering`): standard and postgres NULL largest, sqlite NULL smallest, duckdb always last; `NULLS FIRST/LAST` supported | decided (#251; dialects #260) | `nulls_*` unit tests (all three rules); DiffSqlite and DiffDuckdb in each engine's dialect |
| 2 | Order of rows tied on every sort key | Unspecified | Arbitrary | Arbitrary | Arbitrary | Stable: input order | decided | Spider harness **tie-valid** category + self-test (#249) |
| 3 | Double-quoted text `SELECT "abc"` | Delimited identifier | String literal (fallback) | Identifier → error | Identifier → error | String literal | decided (#215; we have no quoted identifiers) | `Test/ParserTest.lean`; no differential (DuckDB/Postgres reject) |
| 4 | ON-less JOIN `A JOIN B WHERE …` | Join condition required | Cross product + WHERE | Syntax error | Syntax error | Cross product (sqlite) | decided | `ParserTest`, `DiffSqlite` case; DuckDB KNOWN DIVERGENCES |
| 5 | `SELECT DISTINCT name … ORDER BY price` (sort key not selected) | Not allowed | Sorts by the key of each value's **first** source row | Same (plans it as `first(price)`) | Error ("ORDER BY expressions must appear in select list") | **Per dialect** (`DialectConfig.distinctOrderBy`): standard, postgres → parse error (`reject`); sqlite, duckdb → accepted (`firstRow`). In the accepting dialects `SqlEquiv` still ties the key, so output keeps input order (gap, #320); `SqlCore` implements `firstRow` (T13) | decided (#319); SqlEquiv evaluation in sqlite/duckdb open (#320) | Unit pins `distinct_order_by_unselected_per_dialect`, `distinct_order_by_selected_accepted`, `distinct_order_by_unselected_keeps_input_order` (gap); `DuckdbDiffTest` (`SqlCore` vs DuckDB, first-row cases); DiffSqlite and DuckDB KNOWN DIVERGENCES (`SqlEquiv` gap) |
| 6 | Integer division `7 / 2`, `-7 / 2`, `-7 % 2` | Implementation-defined precision/scale | 3, -3, -1 (truncate toward zero) | 3.5 (`/` is float division); `//` gives 3, -3; `%` gives -1 | 3, -3, -1 | 3, -3, -1 (truncate toward zero; was Euclidean -4 / 1 before #262) | decided (#262) | Unit pins `int_division_*`, `int_mod_sign_of_dividend`; DiffSqlite agreement; DiffDuckdb `%` agreement + KNOWN DIVERGENCES for `/` |
| 7 | AVG over integers (`AVG` of 1, 2) | Implementation-defined precision/scale | 1.5 | 1.5 | 1.5 | **1** (truncates; no fractional result type for integer AVG) | **open**: diverges from all three; tied to #201 (decimal division policy) and #202 (floats). *Not* the main cause of the AVG-in-subquery Spider failures (see "Bugs found" below) | Unit pin `avg` (750/4 → 187); DuckDB KNOWN DIVERGENCES (AVG over decimals) |
| 8 | LIKE case sensitivity `'abc' LIKE 'ABC'` | Collation-dependent | true (ASCII case-insensitive by default) | false | false | **Per dialect** (`DialectConfig.likeCase`): sqlite → ASCII case-insensitive (`BinOp.likeCI`); standard, duckdb, postgres → case-sensitive (`BinOp.like`) | decided (#262) | Unit pins `like_*` (every dialect, non-ASCII, NULL, AST); DiffSqlite and DiffDuckdb cases in each dialect |
| 9 | String ordering `'a' < 'B'` | Collation-dependent | false (binary) | false | false (`C.UTF-8` here; an `en_US` collation gives true) | false (code point), every dialect | decided (#262) | Unit pins `string_order_code_point*`; DiffSqlite and DiffDuckdb agreement |
| 10 | Cross-type comparison `1 = 'a'` | Error (types not comparable) | false (numbers sort before text) | Error (conversion) | Error (conversion) | Error (row dropped / NULL) | **decided** (#127, closed): keep the error; matches DuckDB/Postgres | Unit drift guards for `mismatched_types_error` (`SemanticsTest`); lemma `mismatched_types_error`; DiffSqlite KNOWN DIVERGENCES |
| 11 | Numeric column vs string literal `price = '10'` | Error without CAST | Converts literal: matches | Converts: matches | Converts: matches | **Error (row dropped)**, in every dialect | **decided (#254): keep, documented divergence.** All three engines convert; we don't. No Spider query hits it. Options considered: convert numeric-looking strings in comparisons; convert string literals only (Postgres's untyped-literal model); per-dialect evaluation-time rule. Engine detail (14 Nov 2026): `'10.0'`, `'1e1'` convert in sqlite/DuckDB but error in Postgres; `'abc'` is 0 rows in sqlite, an error in DuckDB/Postgres; IN and BETWEEN with numeric strings convert in all three | Unit pins `int_vs_numeric_string_literal_drops_row`, `numeric_string_literal_vs_int_drops_row`, `int_in_numeric_string_list_drops_row`, `int_between_numeric_strings_drops_row`; KNOWN DIVERGENCES in DiffSqlite and DiffDuckdb |
| 12 | TEXT column vs number `tag >= 2014` | Error without CAST | Column affinity: compares as **text** | Error ("explicit cast required") | Error ("no operator") | Error (row dropped) | **decided** (#235, option A): the core keeps the type error; the **Spider harness** emulates sqlite by quoting the literal for our engine only (`year >= 2014` → `year >= '2014'`), reported as the "TEXT-affinity emulated" category | Unit pins `text_vs_number_is_type_error`, `text_vs_quoted_number_compares_as_text`; harness self-test; DiffSqlite KNOWN DIVERGENCES |
| 13 | MIN/MAX over mixed numbers and strings (`MAX` of `'abc'`, `5`) | Error (one declared type per column) | Type-class order (numbers < text): MAX `'abc'`, MIN `5` | Error ("explicit cast required") | Error (invalid input syntax) | **Per dialect** (`DialectConfig.mixedMinMax`): standard, duckdb, postgres → error (row dropped / NULL); sqlite → type-class order | decided (dialects #260). Reachable only through untyped data (CASE mixing types, Spider TEXT columns with numeric-looking cells) | Unit pins `minmax_mixed_*`, `max_mixed_sqlite_type_class`, `min_mixed_sqlite_type_class`, `minmax_mode_recorded_in_ast`; DiffSqlite type-class cases; DuckDB KNOWN DIVERGENCES (its error fails the query, ours is quieter) |
| 14 | MIN/MAX over booleans (`MAX(age > 26)`) | Boolean not orderable by MAX in the standard aggregate set | Integers: `1` / `0`; with numbers, as 1/0 | Boolean result (false < true); with numbers, as 1/0; with strings, error | Error (no `max(boolean)`) | **Per dialect** (`DialectConfig.boolMinMax`): standard, postgres → error (row dropped / NULL); sqlite → `asInt`; duckdb → `ordered` | decided (#261) | Unit pins `max_bool_*` / `min_bool_*` (every dialect, HAVING, window); DiffSqlite and DiffDuckdb boolean cases |

### Typed core (`SqlCore`, #287)

The registry rows above describe `SqlEquiv`. The typed core makes its choices statically: what
`SqlEquiv` drops as a row error is a type error at elaboration (`SqlBridge`) or an evaluation error.
`SqlCoreTest/DuckdbDiffTest.lean` checks it against DuckDB on parsed SQL; the decisions are in
`docs/TYPED_CORE_DECISIONS.md` and `docs/TYPED_CORE_PLAN.md`.

| # | Behaviour (example) | DuckDB | Postgres | **SqlCore** | Status | Tests |
|---|---|---|---|---|---|---|
| T1 | Integer `/` (`age / 7`), row 6 | DOUBLE | Truncates | Truncates (`Int.tdiv`) | decided | `DuckdbDiffTest` (documented difference), `ScalarExamples` |
| T2 | Integer division by zero `1 / 0` | `//` gives NULL | Error | `divisionByZero` error | decided | `ScalarExamples` |
| T3 | Decimal division `1.0 / 4`, `1.0 / 3` | DOUBLE `0.25`, `0.3333333333333333` | `0.25000000000000000000`, `0.33333333333333333333` (scale varies) | Exact rational: `1/4`, `1/3`; agrees with every engine whenever the quotient is a finite decimal | decided (#326, phase 8d; exact rational chosen over a fixed scale, Postgres's scale rule or a float type) | `ScalarExamples`, `ScalarDiffTest` (multiplied back), `BridgeDiffTest`/`DuckdbDiffTest` (rounded to 12 places) |
| T4 | Decimal `%` (`7.5 % -2`) | `1.5` | `1.5` | `1.5` (exact, dividend's sign) | decided | `ScalarDiffTest` (scaled `tmod` reference) |
| T5 | `1 = 1.0`, `1 + 0.5` | Promotes | Promotes | Promotes (decision 6) | decided | `ScalarExamples`, `BridgeDiffTest`, `DuckdbDiffTest` |
| T6 | `CASE WHEN … THEN 1 ELSE 1.5 END` | DECIMAL | numeric | Ill-typed: branches of one type | **gap**: matches neither; needs a conversion (phase 6 bridge or `CAST`) | `ExprExamples` |
| T7 | Cross-type comparison (rows 10–12) | Error | Error | Type error at elaboration | decided | `BridgeDiffTest` (rejections) |
| T8 | Boolean ordering `false < true` | true | true | true | decided (`SqlEquiv` has no boolean order) | `ScalarDiffTest` |
| T9 | Bare column with aggregates `SELECT max(a), b FROM t` | Error (binder) | Error | **Per dialect** (`DialectConfig.bareColumns`, applied by the bridge): standard, postgres, duckdb → `unsupported` at elaboration; sqlite → accepted. With one `MIN`/`MAX` call, `b` comes from the first row where its argument is extreme (`AggCall.atExtreme`; ties keep the first row); with none, from the group's first row (`AggCall.first`). Several `MIN`/`MAX` calls or `MIN`/`MAX(DISTINCT …)` stay `unsupported` (sqlite: arbitrary, and the last tie with `DISTINCT`). When every argument is NULL the last row is used. sqlite's choice there depends on the plan (last row with `GROUP BY` or a plain scan, first row when its MAX optimisation answers `WHERE a IS NULL`), so that case is a known divergence. `SqlEquiv`'s evaluator accepts bare columns in every dialect and reads the group's first row | decided (phase 8e) | `SqliteDiffTest` (15 queries vs sqlite, plus rejections in both dialects), `AggregateExamples`, `BridgeDiffTest` (standard-dialect rejection) |
| T10 | `AVG` over integers (`AVG` of 1, 2; of 1, 1, 2), row 7 | `1.5`, `1.3333333333333333` (DOUBLE) | `1.5000…`, `1.3333333333333333` (numeric; `AVG(i) * 3` is `3.9999999999999999`) | Exact rational decimal: `3/2`, `4/3` (`AVG(i) * 3` is exactly `4`); `NULL` over no values; ill-typed over text | decided (#326, phase 8d) | `AggregateExamples`, `DuckdbDiffTest` (rounded to 12 places), `BridgeDiffTest` |
| T11 | `MIN`/`MAX` over booleans, row 14 | Boolean result | Error | Ill-typed | decided (#313) | `AggregateExamples` |
| T12 | `NULL` keys in `GROUP BY` | One group | One group | One group (`NULL` is `none`) | decided; `SqlEquiv` agrees since #315 (grouping keys erase the NULL type tag; `DISTINCT` and set operations still compare tags, #324) | `AggregateExamples`, `DuckdbDiffTest`, `BridgeDiffTest`, unit pins `group_by_typed_nulls_*` |
| T13 | `SELECT DISTINCT a … ORDER BY b` with `b` not selected, row 5 | Sorts by the first source row's `b` | Error | Follows the parse (row 5): rejected in standard/postgres; in sqlite/duckdb, `aggregate` by the selected expressions with `AggCall.first b`, sorted, projected | decided (#319) | `OrderByExamples`; `DuckdbDiffTest` (duckdb-dialect corpus, ordered, agrees; also checked on sqlite) |
| T14 | Order of rows tied on every `ORDER BY` key | Unspecified | Unspecified | Input order (stable insertion sort) | decided (#318); the differential tests use tie-free keys | `OrderByExamples` |
| T15 | `ORDER BY 2` (integer literal) | Position | Position | Position; out of range is `unsupported` | decided (#318); `SqlEquiv` sorts by a constant (#316) | `BridgeDiffTest`, `DuckdbDiffTest` |
| T16 | `LIKE` letter case and wildcards, row 8 | Case-sensitive | Case-sensitive | Follows the parse: `BinOp.like false` (standard, duckdb, postgres) or `BinOp.like true` (sqlite: ASCII letters only). `%` any sequence, `_` one character, no `ESCAPE` | decided (#322); `SqlEquiv` ignores `_` and interior `%` (#323) | `SetOpExamples`, `ScalarDiffTest` (independent reference), engine sweep of 676 pairs (DuckDB and sqlite), `BridgeDiffTest` sqlite-dialect corpus |
| T17 | Scalar subquery with several rows `WHERE x > (SELECT a FROM t)` | Error ("More than one row returned by a subquery used as an expression") | Error (same) | **Per dialect** (`DialectConfig.scalarSubqueryRows`, recorded on each `SubKind.scalar` node): standard, postgres, duckdb → `EvalError.cardinality` at evaluation (so such a node is never `divSafe`); sqlite → the first row's value. No rows is `NULL` everywhere. The subquery is evaluated strictly, once, even when the outer query has no rows, so the error is raised there too; DuckDB agrees, but Postgres is lazy (no error when the value is never needed: an empty outer query or a short-circuited `AND`), a known divergence in the error mode | decided (#329, phase 8f) | `SubqueryExamples`, `SqliteDiffTest` (first row, against sqlite) |

### Notes on individual rows

- **Row 1** is the model for a configurable behaviour: one enum on the AST
  item, a `DialectConfig` field, and each differential harness running in its
  engine's dialect. Parsing the DuckDB cases with sqlite's rule makes the ASC case
  fail, which shows those tests check the NULL position.
- **Row 7**: changing AVG means choosing a fractional result type (DECIMAL with
  a scale rule, or floats). That is the #201 / #202 design decision, not a
  local fix.
- **Row 8**: the certified rewriter's LIKE rules (`x LIKE '%'`, `x LIKE ''`,
  `x LIKE x`) are stated for the case-sensitive `BinOp.like` only; the
  sqlite dialect's `BinOp.likeCI` is not rewritten, so those rules stay sound
  in every dialect.
- **Row 6**: integer `/` and `%` used Lean's Euclidean division (`-7 / 2 =
  -4`, `-7 % 2 = 1`), matching no engine; found while pinning (#262) and fixed
  to truncate toward zero, as all three engines do. Integer AVG's truncation
  (row 7) uses the same rounding.
- **Rows 10–12** are related: they are all about comparing values of different
  types. Rows 10 and 12 were decided together: keep the core's type error
  (matching DuckDB/Postgres), and emulate sqlite's TEXT affinity only in the
  Spider harness. The measured cost of the alternative for row 10: making
  `1 = 'a'` return FALSE makes the certified rewriter's `x LIKE '' → x = ''`
  rule unsound for non-string `x` unless it gets a type guard. Row 11 was
  decided in #254 the same way (keep the type error), though here all three
  engines convert: it is a documented divergence, pinned by unit tests.
- **Row 12 harness emulation** is conservative: it rewrites only comparisons
  with a column that, in every table of the database, has TEXT affinity and
  holds only non-numeric strings in the synthetic data. Each query runs as
  written first; the rewritten form is used only if the original fails, so the
  rewrite cannot turn an agreement into a failure. A self-test guards the
  rewrite on every invocation.

---

## Bugs found while compiling this registry (standard-defined, not implementation-defined)

- **Correlated-subquery name resolution was outer-first** (fixed, #253).
  Inside a subquery, an unqualified column was resolved against the *outer*
  query's row before the subquery's own tables; SQL scoping is the reverse.
  Over `singer(age) = 20, 30, 41`, `SELECT (SELECT avg(age) FROM singer) FROM
  singer` returned **20** (the outer row's `age`), and `WHERE age > (SELECT
  min(age) FROM singer)` returned no rows instead of two. Fixed by building
  subquery context rows inner-first (`row ++ outerRow`) and making unqualified
  lookup a single first-match pass, so an unqualified outer key (from a derived
  table) cannot beat a qualified inner one. This, not AVG
  truncation, was the main cause of the Spider "AVG" failure class (Spider
  539 → 549). Pinned by the `scope_*` unit tests and DiffSqlite/DiffDuckdb
  `scope:` cases.
- **MAX/MIN over strings returned NULL** (fixed, #256). All three engines
  order text, so `SELECT max(name) FROM t` is the greatest string; ours
  returned NULL because MIN/MAX looked at numerics only. Now MIN/MAX range over
  the string inputs when there are no numeric ones (code-point order, as row 9).
  Seen in Spider (`dog_kennels`, and `max` over TEXT columns in the "plain
  SELECT" class): 549 → 553. Pinned by the `max_string*` / `min_string` unit
  tests and DiffSqlite/DiffDuckdb `over strings` cases.

- **Derived-table alias** (fixed, #257). `FROM (SELECT name FROM users) AS d`
  now qualifies the derived columns by the alias: `d.name` resolves (as in
  sqlite, DuckDB and Postgres) and unqualified `name` still works. Keys are
  re-qualified by `requalifyRow` (`SemanticsBase.lean`): a key that already
  carries the alias is kept, otherwise its column part (after the last `.`)
  is prefixed with the alias. The inner table's qualifier is out of scope
  outside the derived table: `users.name` there finds no column (NULL, a quiet
  error under #270), where engines reject the query. The six filter theorems
  were restated beforehand in #269 so the fix needed no statement change.
  Spider is unchanged (553/564). Pinned by the `derived_*` unit tests and
  DiffSqlite/DiffDuckdb `derived:` cases.

---

## Backlog to meet the policy

Rows that do not yet meet the testing requirements in §2:

- **Row 5**: decided per dialect (#319), but `SqlEquiv`'s evaluator still
  ties an unselected key in the sqlite and duckdb dialects instead of using
  the first source row (#320); pinned in the meantime.
- **`SqlEquiv` `NOT IN (subquery)` with NULLs** (#330): standard behaviour that
  `SqlEquiv` gets wrong; the typed core is right (three-valued `inList`).
- **`SqlEquiv` LIKE wildcards** (#323) and **set operations** (#324): standard
  behaviour that `SqlEquiv` gets wrong (not implementation-defined); recorded
  in both harnesses' KNOWN DIVERGENCES, and the typed core is right.
- **Postgres harness** (#224): Postgres is installed in the dev environment,
  so its standards-tiebreaker role can be implemented.
