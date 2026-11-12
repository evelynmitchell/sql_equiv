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
| 5 | `SELECT DISTINCT name … ORDER BY price` (sort key not selected) | Not allowed | Sorts (by some source row) | Sorts | Error | Keys resolve against output columns only; key ties silently, so output stays in input order | **gap**: matches no engine; Postgres errors, the others sort | DuckDB KNOWN DIVERGENCES only; **no unit pin** |
| 6 | Integer division `7 / 2` | Implementation-defined precision/scale | 3 | 3.5 (`/` is float division; `//` is integer) | 3 | 3 | decided (implicitly) | **no dedicated unit pin** |
| 7 | AVG over integers (`AVG` of 1, 2) | Implementation-defined precision/scale | 1.5 | 1.5 | 1.5 | **1** (truncates; no fractional result type for integer AVG) | **open**: diverges from all three; tied to #201 (decimal division policy) and #202 (floats). *Not* the main cause of the AVG-in-subquery Spider failures (see "Bugs found" below) | Unit pin `avg` (750/4 → 187); DuckDB KNOWN DIVERGENCES (AVG over decimals) |
| 8 | LIKE case sensitivity `'abc' LIKE 'ABC'` | Collation-dependent | true (ASCII case-insensitive by default) | false | false | false | decided (implicitly; matches DuckDB/Postgres) | **no unit pin; no sqlite disagreement test** |
| 9 | String ordering `'a' < 'B'` | Collation-dependent | false (binary) | false | false (`C.UTF-8` here; an `en_US` collation gives true) | false (code point) | decided (implicitly) | **no unit pin** |
| 10 | Cross-type comparison `1 = 'a'` | Error (types not comparable) | false (numbers sort before text) | Error (conversion) | Error (conversion) | Error (row dropped / NULL) | **decided** (#127, closed): keep the error; matches DuckDB/Postgres | Unit drift guards for `mismatched_types_error` (`SemanticsTest`); lemma `mismatched_types_error`; DiffSqlite KNOWN DIVERGENCES |
| 11 | Numeric column vs string literal `price = '10'` | Error without CAST | Converts literal: matches | Converts: matches | Converts: matches | **Error (row dropped)** | **gap** (#254): diverges from all three; no Spider query hits it today | **none** |
| 12 | TEXT column vs number `tag >= 2014` | Error without CAST | Column affinity: compares as **text** | Error ("explicit cast required") | Error ("no operator") | Error (row dropped) | **decided** (#235, option A): the core keeps the type error; the **Spider harness** emulates sqlite by quoting the literal for our engine only (`year >= 2014` → `year >= '2014'`), reported as the "TEXT-affinity emulated" category | Unit pins `text_vs_number_is_type_error`, `text_vs_quoted_number_compares_as_text`; harness self-test; DiffSqlite KNOWN DIVERGENCES |
| 13 | MIN/MAX over mixed numbers and strings (`MAX` of `'abc'`, `5`) | Error (one declared type per column) | Type-class order (numbers < text): MAX `'abc'`, MIN `5` | Error ("explicit cast required") | Error (invalid input syntax) | **Per dialect** (`DialectConfig.mixedMinMax`): standard, duckdb, postgres → error (row dropped / NULL); sqlite → type-class order | decided (dialects #260). Reachable only through untyped data (CASE mixing types, Spider TEXT columns with numeric-looking cells) | Unit pins `minmax_mixed_*`, `max_mixed_sqlite_type_class`, `min_mixed_sqlite_type_class`, `minmax_mode_recorded_in_ast`; DiffSqlite type-class cases; DuckDB KNOWN DIVERGENCES (its error fails the query, ours is quieter) |
| 14 | MIN/MAX over booleans (`MAX(age > 26)`) | Boolean not orderable by MAX in the standard aggregate set | Integers: `1` / `0`; with numbers, as 1/0 | Boolean result (false < true); with numbers, as 1/0; with strings, error | Error (no `max(boolean)`) | **Per dialect** (`DialectConfig.boolMinMax`): standard, postgres → error (row dropped / NULL); sqlite → `asInt`; duckdb → `ordered` | decided (#261) | Unit pins `max_bool_*` / `min_bool_*` (every dialect, HAVING, window); DiffSqlite and DiffDuckdb boolean cases |

### Notes on individual rows

- **Row 1** is the model for a configurable behaviour: one enum on the AST
  item, a `DialectConfig` field, and each differential harness running in its
  engine's dialect. Parsing the DuckDB cases with sqlite's rule makes the ASC case
  fail, which shows those tests check the NULL position.
- **Row 7**: changing AVG means choosing a fractional result type (DECIMAL with
  a scale rule, or floats). That is the #201 / #202 design decision, not a
  local fix.
- **Rows 10–12** are related: they are all about comparing values of different
  types. Rows 10 and 12 were decided together: keep the core's type error
  (matching DuckDB/Postgres), and emulate sqlite's TEXT affinity only in the
  Spider harness. The measured cost of the alternative for row 10: making
  `1 = 'a'` return FALSE makes the certified rewriter's `x LIKE '' → x = ''`
  rule unsound for non-string `x` unless it gets a type guard. Row 11 is open
  as #254.
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

- **Derived-table alias is ignored** (open, #257, deferred by decision).
  `FROM (SELECT name FROM users) AS d` keeps the subquery's own keys, so
  `d.name` evaluates to NULL (all engines return the column) while `name`
  works; out-of-scope references such as `users.name` outside the derived table
  still resolve, where engines reject them. Fixing it with standard scoping
  makes six proven theorems false as stated (`filter_and`, `filter_commute`,
  `filter_idempotent`, `filter_pushdown_table`, `filter_join_left`,
  `filter_join_right`): they wrap a FROM in `(SELECT * …) AS inner` and depend
  on pass-through keys, and results compare column names. Deferred: Spider has
  no query that needs it. Pinned by the `derived_*` unit tests.

---

## Backlog to meet the policy

Rows that do not yet meet the testing requirements in §2:

- **Row 5**: add a unit pin for our DISTINCT + ORDER BY behaviour; decide
  whether to error (Postgres, standard) or sort (sqlite, DuckDB).
- **Rows 6, 8, 9**: add unit pins; add a sqlite *disagreement* test for row 8
  (sqlite's LIKE is case-insensitive).
- **Row 11**: decide via #254 (all three engines convert the literal); add a pin either way.
- **Postgres harness** (#224): Postgres is installed in the dev environment,
  so its standards-tiebreaker role can be implemented.
