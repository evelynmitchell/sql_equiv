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
silent pass. Disagreements where DuckDB also disagrees with sqlite (or rejects
the query) go to Postgres, the standards tiebreaker. If Postgres gives sqlite's
answer the query is a failure of ours (**tiebroken against ours**); otherwise it is
labelled **engine-divergent**: reported apart from failures of ours, but still not
counted as agreement.

### 4. Changing a row

Same PR: update this registry, the harness KNOWN DIVERGENCES headers, the
unit/differential tests, and (if the default changes) the Spider ratchet.

---

## Engines and their roles

Observed with **sqlite 3.45.1**, **DuckDB 1.5.3** and **PostgreSQL 16.15**
(all installed in the dev environment; Postgres is started on demand with
`pg_ctlcluster 16 main start`). CI uses the runner's preinstalled Postgres
(18.6 when the harness landed; the CI log prints the version).

| Engine | Role (from #225) | Harness |
|---|---|---|
| sqlite | Spider-fidelity target: Spider's gold results were computed on it | `LSpecTests/DiffSqlite.lean`, `tools/spider_eval_baseline.py` |
| DuckDB | Standards and DECIMAL cross-check (strict types, real DECIMAL) | `LSpecTests/DiffDuckdb.lean` |
| PostgreSQL | Standards tiebreaker | `LSpecTests/DiffPostgres.lean` (postgres dialect, #224); tiebreaker in `tools/spider_eval_baseline.py` |

**Cross-cutting difference:** where DuckDB and Postgres raise a *query error*,
our evaluator returns `none` for the expression. In a WHERE clause that silently
drops the row; in a SELECT list it shows as NULL. So our "error" is quieter than
theirs. Rows below say "ours: error (row dropped)" for this.

**What this means for proved equivalences (#270):** `SqlEquiv`'s equivalences compare these
quiet results. They transfer to DuckDB or Postgres only for queries that raise no error there:
two queries can be equivalent in the model while one aborts in the engine (a rewrite that drops
an always-false conjunct whose other operand would have raised). The typed core (`SqlCore`) is
strict, with errors as a separate result, so its equivalences do not carry this caveat.
`SqlEquiv` stays quiet; strictness is a layer per dialect on top (decided on #270, row 23):
`evalQueryIn (dialect.config.errors)` runs the quiet evaluation and a check (`checkQuery`,
`SqlEquiv/Strict.lean`) that fails the statement when a WHERE, join ON, GROUP BY key, aggregate
argument, HAVING, select item, window argument or key, or ORDER BY key yields an error on a row
the evaluator evaluates it on. It recurses into derived tables, set-operation branches, CTE bodies
(each working table of a recursive CTE), and the subqueries engines always evaluate with an
expression: scalar subqueries and `IN (subquery)`, checked with the row as outer row. `evalStmtIn`
checks INSERT values, UPDATE SET (on the rows WHERE keeps, on the row before the update) and
WHERE, and DELETE WHERE the same way. `evalQueryIn_transfer`:
two quiet-equivalent queries that both succeed give the same rows, so every theorem transfers
whenever neither side fails. That one side fails and the other does not is not excluded. The check
is a runtime approximation. Not seen, decided on #448: errors engines raise at bind or plan time
(a type mismatch behind `FALSE AND …` or over an empty table; Postgres folding a constant `1 / 0`
even where it is never evaluated), since `SqlEquiv`'s database has no schema; subqueries under
`AND`/`OR` (Postgres reorders and short-circuits the operands), past a CASE's first condition, or
in `EXISTS` (Postgres ignores its select list and stops at the first row, DuckDB scans its WHERE in
full); the select items of a window query under LIMIT without ORDER BY (Postgres evaluates them
only on the rows it returns, in the windows' order; window arguments and keys are checked on every
row); and ORDER BY keys of an aggregate query without GROUP BY (one row, never compared). Whatever is decided applies to every evaluation path alike: since #423 the aggregate and window paths combine an operand's error as the row evaluator does (`FALSE AND <error>` is FALSE, `<error> IS NULL` is TRUE), so an item's value no longer depends on whether another item has an aggregate or a window function.

---

## Registry

Legend for **Status**: *decided* (deliberate, tested), *open* (divergence with an
open decision or issue), *gap* (behaviour matches no engine or is untested).

| # | Behaviour (example) | Standard | sqlite | DuckDB | Postgres | **Ours** | Status | Tests |
|---|---|---|---|---|---|---|---|---|
| 1 | NULL position in ORDER BY (`ORDER BY price` with a NULL) | Implementation-defined; `NULLS FIRST/LAST` syntax | NULL smallest (first ASC, last DESC) | NULLs last both ways | NULL largest (last ASC, first DESC) | **Per dialect** (`DialectConfig.nullOrdering`): standard and postgres NULL largest, sqlite NULL smallest, duckdb always last; `NULLS FIRST/LAST` supported | decided (#251; dialects #260) | `nulls_*` unit tests (all three rules); DiffSqlite and DiffDuckdb in each engine's dialect; DiffPostgres (postgres rule, NULLS FIRST/LAST) |
| 2 | Order of rows tied on every sort key | Unspecified | Arbitrary | Arbitrary | Arbitrary | Stable: input order | decided | Spider harness **tie-valid** category + self-test (#249) |
| 3 | Double-quoted text `SELECT "abc"` | Delimited identifier | String literal (fallback) | Identifier → error | Identifier → error | String literal | decided (#215; we have no quoted identifiers) | `Test/ParserTest.lean`; no differential (DuckDB/Postgres reject) |
| 4 | ON-less JOIN `A JOIN B WHERE …` | Join condition required | Cross product + WHERE | Syntax error | Syntax error | Cross product (sqlite) | decided | `ParserTest`, `DiffSqlite` case; DuckDB KNOWN DIVERGENCES |
| 5 | `SELECT DISTINCT name … ORDER BY price` (sort key not selected) | Not allowed | Sorts by the key of each value's **first** source row | Same (plans it as `first(price)`) | Error ("ORDER BY expressions must appear in select list") | **Per dialect** (`DialectConfig.distinctOrderBy`): standard, postgres → parse error (`reject`); sqlite, duckdb → accepted (`firstRow`). Both evaluators implement `firstRow`: `SqlCore` with `AggCall.first` (T13), `SqlEquiv` by sorting each distinct row with its first source row (or, over GROUP BY, its first group's key row) as context (#320) | decided (#319); `SqlEquiv` since #320 | Unit pins `distinct_order_by_unselected_per_dialect`, `distinct_order_by_selected_accepted`, `distinct_order_by_unselected_first_row`, `distinct_order_by_first_row_not_min`, `distinct_group_by_order_by_first_group`; `DuckdbDiffTest` (SqlEquiv, `SqlCore` and DuckDB on the first-row cases, ordered); DiffPostgres (`diffRejects`: both reject in the postgres dialect) |
| 6 | Integer division `7 / 2`, `-7 / 2`, `-7 % 2` | Implementation-defined precision/scale | 3, -3, -1 (truncate toward zero) | 3.5 (`/` is float division); `//` gives 3, -3; `%` gives -1 | 3, -3, -1 | 3, -3, -1 (truncate toward zero; was Euclidean -4 / 1 before #262) | decided (#262) | Unit pins `int_division_*`, `int_mod_sign_of_dividend`; DiffSqlite agreement; DiffDuckdb `%` agreement + KNOWN DIVERGENCES for `/`; DiffPostgres (`/` and `%` agree) |
| 7 | AVG over integers (`AVG` of 1, 2) | Implementation-defined precision/scale | 1.5 | 1.5 | 1.5 | **1.5**: a decimal, the exact quotient when it terminates within `max(16, input scale)` places, otherwise rounded half away from zero to them (`AVG` of 1, 1, 2 is `1.3333333333333333`, as DuckDB and Postgres show it). Always a decimal (`AVG` of 10, 12 is decimal `11`), as Postgres and the typed core (T10) | decided (was truncation; found hiding 17 Spider queries by the `--stress` variants). Settles the scale rule for AVG only; general decimal `/` is still #201 | `SqlBridge/CorrectAvg.lean`: the elaborator theorems relate an `AVG` item up to this rounding (`AvgRel`, step 3c); `BridgeDiffTest` `.agreeRounded`. Unit pins `avg` (750/4 → 187.5), `avg_negative_exact`, `avg_rounded_16_places`, `window_avg_partition_by`; DiffDuckdb (terminating averages, plain, grouped and window); BridgeDiffTest (terminating averages agree with the typed core's rationals); DiffPostgres (terminating averages, plain, grouped and window) |
| 8 | LIKE case sensitivity `'abc' LIKE 'ABC'` | Collation-dependent | true (ASCII case-insensitive by default) | false | false | **Per dialect** (`DialectConfig.likeCase`): sqlite → ASCII case-insensitive (`BinOp.likeCI`); standard, duckdb, postgres → case-sensitive (`BinOp.like`) | decided (#262) | Unit pins `like_*` (every dialect, non-ASCII, NULL, AST); DiffSqlite and DiffDuckdb cases in each dialect; DiffPostgres (case-sensitive) |
| 9 | String ordering `'a' < 'B'` | Collation-dependent | false (binary) | false | false (`C.UTF-8` here; an `en_US` collation gives true) | false (code point), every dialect | decided (#262) | Unit pins `string_order_code_point*`; DiffSqlite and DiffDuckdb agreement; DiffPostgres (`COLLATE "C"` columns) |
| 10 | Cross-type comparison `1 = 'a'` | Error (types not comparable) | false (numbers sort before text) | Error (conversion) | Error (conversion) | Error (row dropped / NULL) | **decided** (#127, closed): keep the error; matches DuckDB/Postgres | Unit drift guards for `mismatched_types_error` (`SemanticsTest`); lemma `mismatched_types_error`; DiffSqlite KNOWN DIVERGENCES |
| 11 | Numeric column vs string literal `price = '10'` | Error without CAST | Converts literal: matches | Converts: matches | Converts: matches | **Error**, in every dialect: the row is dropped (sqlite), the statement fails (strict dialects, row 23) | **decided (#254): keep, documented divergence.** All three engines convert; we don't. One Spider query hits it (`cars_data.year = '1970'`, found by the #270 probe in the duckdb dialect). Options considered: convert numeric-looking strings in comparisons; convert string literals only (Postgres's untyped-literal model); per-dialect evaluation-time rule. Engine detail (14 Nov 2026): `'10.0'`, `'1e1'` convert in sqlite/DuckDB but error in Postgres; `'abc'` is 0 rows in sqlite, an error in DuckDB/Postgres; IN and BETWEEN with numeric strings convert in all three | Unit pins `int_vs_numeric_string_literal_drops_row`, `numeric_string_literal_vs_int_drops_row`, `int_in_numeric_string_list_drops_row`, `int_between_numeric_strings_drops_row`; KNOWN DIVERGENCES in DiffSqlite and DiffDuckdb |
| 12 | TEXT column vs number `tag >= 2014` | Error without CAST | Column affinity: compares as **text** | Error ("explicit cast required") | Error ("no operator") | Error (row dropped) | **decided** (#235, option A): the core keeps the type error; the **Spider harness** emulates sqlite by quoting the literal for our engine only (`year >= 2014` → `year >= '2014'`), reported as the "TEXT-affinity emulated" category | Unit pins `text_vs_number_is_type_error`, `text_vs_quoted_number_compares_as_text`; harness self-test; DiffSqlite KNOWN DIVERGENCES |
| 13 | MIN/MAX over mixed numbers and strings (`MAX` of `'abc'`, `5`) | Error (one declared type per column) | Type-class order (numbers < text): MAX `'abc'`, MIN `5` | Error ("explicit cast required") | Error (invalid input syntax) | **Per dialect** (`DialectConfig.mixedMinMax`): standard, duckdb, postgres → error (row dropped / NULL); sqlite → type-class order | decided (dialects #260). Reachable only through untyped data (CASE mixing types, Spider TEXT columns with numeric-looking cells) | Unit pins `minmax_mixed_*`, `max_mixed_sqlite_type_class`, `min_mixed_sqlite_type_class`, `minmax_mode_recorded_in_ast`; DiffSqlite type-class cases; DuckDB KNOWN DIVERGENCES (its error fails the query, ours is quieter) |
| 14 | MIN/MAX over booleans (`MAX(age > 26)`) | Boolean not orderable by MAX in the standard aggregate set | Integers: `1` / `0`; with numbers, as 1/0 | Boolean result (false < true); with numbers, as 1/0; with strings, error | Error (no `max(boolean)`) | **Per dialect** (`DialectConfig.boolMinMax`): standard, postgres → error (row dropped / NULL); sqlite → `asInt`; duckdb → `ordered` | decided (#261) | Unit pins `max_bool_*` / `min_bool_*` (every dialect, HAVING, window); DiffSqlite and DiffDuckdb boolean cases |
| 15 | Name of a set-operation result column whose branches name it differently, as a trailing `ORDER BY` sees it (`SELECT 'b' AS x UNION ALL SELECT 'a' AS y ORDER BY y`) | Implementation-dependent: the column takes its branches' common name; when they differ, the name is left to the implementation | Any branch's name: the column is labelled `x` but `ORDER BY y` also finds it | Any branch's name (same) | First branch's name only: the column is `x`, and `ORDER BY y` is an error ("column "y" does not exist") | First branch's name only, as Postgres, in every dialect: the parser resolves each key to an output name of the first branch, so a name only a later branch uses is a parse error. Keys that name no result column (qualified names, expressions) are errors in every engine and here | **Implementation-defined**; decided (#317). Per dialect is possible (policy option 2: the parser carries the choice), not done | Unit pin `compound_order_by_errors`; DiffPostgres (first branch's name sorts; a later branch's name is rejected by both) |
| 16 | Result type and rounding of `ROUND(x[, d])` (`ROUND(7)`, `ROUND(2.5)`, `ROUND(15, -1)`) | Not in the core standard (vendor function) | Always a float: `7.0`, `3.0`; negative `d` treated as 0 (`ROUND(15, -1)` is `15.0`) | Keeps the input type: `7`, `3` (decimal), `20`; half away from zero | `double precision` for an integer, `numeric` for a decimal (`5.00` at `d = 2`); `3`, `20`; half away from zero | **Keeps the input type** (DuckDB): an integer stays an integer, a decimal is rounded exactly at `d` places (`Value.mkDecimal`); half away from zero; negative `d` rounds to a multiple of `10^-d`; NULL in either argument gives NULL; a non-integer `d` is an error. `ABS` of a decimal keeps its scale | decided (#355; we have exact decimals, not floats, #202) | `round_*`, `abs_decimal` unit tests; DiffDuckdb (agrees on values and types); sqlite differs in type only for `d ≥ 0` (DiffSqlite KNOWN DIVERGENCES); DiffPostgres (values agree) |
| 17 | `AVG`/`SUM` over a TEXT column (Spider `avg(horsepower)`, `horsepower` declared `text`; dates stored as text, #211) | Type error: no AVG/SUM over character strings | Converts each string to a number: its numeric prefix, else 0 (`AVG` of `'130'`, `'abc'`, `'2020-01-02'` is `716.67`) | Binder error (`No function matches avg(VARCHAR)`) | Error (`function avg(text) does not exist`) | **Type error** (`none`), as DuckDB and Postgres: any string among the inputs (`hasNonNumeric`), also mixed with numbers. In a SELECT item it shows as NULL; `IS NULL` reads it as NULL, in HAVING as in WHERE (#423), and `IS NOT NULL` is false. Booleans: row 18 | decided: error, do not emulate sqlite | Unit pins `avg_text_column_error`, `sum_text_column_error` (the aggregate's value is an error), `avg_text_column_error_is_null_in_having`, `sum_text_column_error_not_a_value_in_having`, `avg_mixed_text_error_in_having`, `avg_numbers_in_having`; Spider harness reports these as their own labelled failure class, **known divergence: AVG/SUM over a TEXT column (registry row 17)**, with a self-test; DiffSqlite KNOWN DIVERGENCES |
| 18 | `SUM`/`AVG` over booleans (`SUM(age > 26)`) | No SUM/AVG over booleans | Integers 1/0: `SUM` counts the true rows, `AVG` is their fraction | `SUM` as 1/0; `AVG` is a binder error | Error (`function sum(boolean) does not exist`, likewise `avg`) | **Per dialect and per function** (`DialectConfig.boolSum`/`boolAvg`, recorded on each `AggFunc.sum`/`avg` and window `sum`/`avg` node as `BoolSumAvg`): sqlite → 1/0 for both; duckdb → 1/0 for SUM, error for AVG; standard, postgres → error for both. Previously booleans were skipped like NULLs, matching no engine | decided | Unit pins `sum_bool_sqlite`, `avg_bool_sqlite`, `sum_bool_duckdb`, `avg_bool_duckdb_error`, `sum_bool_standard_error`, `avg_bool_postgres_error`, `sum_bool_error_mode`, `avg_bool_error_mode`; DiffSqlite and DiffDuckdb (`SUM over booleans`) |
| 19 | `UPPER`/`LOWER` of non-ASCII letters (`LOWER('ÉCOLE')`) | Unicode case mapping (the standard's `LOWER` folds by the character set) | ASCII letters only: `lower('ÉCOLE')` is `École` | Unicode: `école` | Unicode: `école` | **ASCII letters only, in every dialect** (`String.toLower`/`toUpper`), as sqlite. sqlite's `LIKE` (row 8) folds the same letters | **decided**: keep ASCII. It matches sqlite, Spider's engine, needs no Unicode case table to carry and keep current, and keeps `LOWER(x) LIKE LOWER(p)` (#267) exact against a sqlite `LIKE`. A DuckDB or Postgres query applying `LOWER`/`UPPER` to non-ASCII text is a documented divergence. Found while checking #267. Related: unquoted identifiers fold ASCII only in all three engines (`Été` ≠ `été`), as ours do: row 20 | Unit pins `lower_non_ascii_ascii_only`, `upper_non_ascii_ascii_only`, `lower_ascii`; DiffSqlite agreement on non-ASCII; DiffDuckdb and DiffPostgres agree on ASCII and pin the divergence (`diffDiverges`); `to_sql_in_likeci_same_rows_*` |
| 20 | Unquoted identifiers: which characters, and how names match (`SELECT Élan FROM Été`; `été` vs `Été`) | Identifier characters by Unicode class; regular identifiers compare case-insensitively | Any character from U+0080 is an identifier character; names fold ASCII letters only (`été` is not `Été`) | Same, except U+00A0 (no-break space) is whitespace | Same as sqlite (U+00A0 is part of the name) | **Any character from U+0080 is an identifier character** (`isIdentStart`/`isIdentChar`, as sqlite and Postgres), **except typographic quotes (U+2018–U+201F) and non-ASCII spaces (U+00A0, U+2000–U+200B, U+3000, …)**, which are parse errors with a hint: the engines read them as identifier characters and then fail with "no such column", but an unknown column is a quiet NULL here, so accepting them would turn a pasted `‘Alice’` or no-break space into a silent empty result. An unquoted name containing one of them (`O’Brien`) is therefore rejected, where the engines accept it; keywords are ASCII, so a non-ASCII word is always an identifier. Column names fold ASCII letters only (`Row.lookupCI`, `String.toLower`), so `élan` does not find `Élan`. **Table names** are passed to the `Database` exactly as written, not folded: the engines fold ASCII letters, so with a `Database` that matches names exactly, `FROM tab` against a table named `Tab` reads an empty table here and the real one in the engines. **Decided (#372): documented, not changed.** A `Database` is a function from names to tables and decides its own matching rule; one that should behave like the engines folds ASCII letters itself (the Spider harness lowercases table names on both sides). Folding in the evaluator or the parser was considered: it would touch the FROM semantics or every output name for a difference no harness hits. Before #370 the tokenizer rejected every non-ASCII character | decided (#370); table-name matching left to the `Database` (#372) | Unit pins `non_ascii_column`, `non_ascii_cjk_column_and_alias`, `non_ascii_name_folds_ascii_only`, `non_ascii_ascii_letters_still_fold`, `table_name_matched_exactly`, `table_name_exact_spelling_found`; ParserTest `non_ascii_*` round trips, `typographic_*_rejected`, `no_break_space_rejected`, `ideographic_space_rejected`; DiffSqlite, DiffDuckdb, DiffPostgres `non-ASCII table, column and alias names`, `non-ASCII table alias as qualifier` |
| 21 | Grouping of a comparison followed by `IN` / `BETWEEN` / `LIKE` (`a = b IN (c)`), and chains (`a < b = c`, `a LIKE b IN (c)`) | `<predicate>`s do not nest without parentheses: `a = b IN (c)` and `a = b = c` are not in the grammar | A predicate applies to the whole comparison on its left, and comparisons chain: `a = b IN (c)` is `(a = b) IN (c)`, `1 < 2 = TRUE` is `(1 < 2) = TRUE`, `'a' LIKE 'a' IN (TRUE)` is `('a' LIKE 'a') IN (TRUE)` | `IN` / `BETWEEN` / `LIKE` bind tighter than the comparisons: `a = b IN (c)` is `a = (b IN (c))`. Comparisons do not chain (`1 < 2 = TRUE`, `1 = 1 = 1` are syntax errors), and neither does a predicate directly after `BETWEEN` or `LIKE` (`5 BETWEEN 1 AND 9 IN (TRUE)`, `'a' LIKE 'a' LIKE 'a'` are syntax errors; after `IN (…)` another may follow) | Same as DuckDB | **As DuckDB and Postgres, in every dialect** (`parsePredRest`, `parseCompRest` in `SqlEquiv/Parser.lean`): `a = b IN (c)` is `a = (b IN (c))`, and the chains they reject are parse errors here with a message asking for parentheses. Where the three engines agree there is no choice and we follow them (#400): `IN` / `BETWEEN` / `LIKE` / `IS [NOT] NULL` take the whole arithmetic expression on their left (`1 + 1 IN (2)` is true; before #400 it parsed as `1 + (1 IN (2))` and was NULL), `IS [NOT] NULL` takes a whole comparison (`a = b IS NULL` is `(a = b) IS NULL`), and `NOT` is looser than all of them and tighter than `AND` (`NOT a = b` is `NOT (a = b)`; before #400, `(NOT a) = b`). **In the `sqlite` dialect this differs from sqlite** for the shapes in this row: `a = b IN (c)` groups the other way, quietly, and sqlite accepts the chains we reject. **Decided (22 Nov 2026): documented, not changed.** The parse tree could carry sqlite's grouping (policy rule 2: a `DialectConfig` field), and the shape could be rejected in the `sqlite` dialect; neither is done, because no Spider query has these shapes and parentheses give the same reading in every engine | decided (#400); the `sqlite` dialect's difference is documented, not changed | ParserTest `prec_*` (grouping in every dialect by comparison with the parenthesised spelling, round trips, rejections, evaluation pins); DiffSqlite, DiffDuckdb, DiffPostgres `precedence: …` (agreed shapes); DiffDuckdb, DiffPostgres `precedence: comparison then LIKE (row 21)`; DiffSqlite KNOWN DIVERGENCES |
| 22 | A query without `GROUP BY` and without an aggregate in the select list (one inside a window function counts) that has a `HAVING`: `SELECT 1 FROM t HAVING COUNT(*) > 1`, `SELECT ROW_NUMBER() OVER () FROM t HAVING COUNT(*) > 1` | One group | Error ("HAVING clause on a non-aggregate query") | One group | One group | **Per dialect** (`DialectConfig.implicitGroup`, #440): standard, duckdb, postgres → one group (over no rows too: `WHERE FALSE HAVING 1 = 1` gives one row); sqlite → rejected at parse time, as sqlite does. Before #440 such a `HAVING` filtered the rows one by one, in every dialect. A window query also aggregates through an aggregate inside a window in the select list (`SUM(SUM(x)) OVER ()`, #438), in all four engines. Known divergence: an aggregate only in `ORDER BY` (`SELECT 1 FROM t ORDER BY COUNT(*)`; DuckDB and Postgres give one row, sqlite rejects it) is rejected in every dialect, because the evaluator decides grouping from the select list and `HAVING` only (#445). A bare column in such a query (`SELECT name FROM t HAVING age > 26`) reads the sample row, as registry T9 says for every aggregate query; DuckDB and Postgres reject it | decided (#438, #440, 23 Nov 2026: handle it as implementation-defined, per dialect) | `having_without_group_by_*`, `window_having_aggregate_*` (SemanticsTest); `implicitGroupDialectTests`, `aggregate_only_in_order_by_rejected` (ParserTest); DiffDuckdb, DiffPostgres `implicit group:` and `window over aggregate: having` |
| 23 | An evaluation error at run time: `SELECT id / (age - 30) FROM users` with an age of 30, `SELECT name + 1 FROM users`, `WHERE name > 1` | Exception: the statement fails | Quiet: division and modulo by zero are NULL, mixed types compare by type class | Statement fails, except division by zero (float infinity, row 6) and modulo by zero (NULL); type errors fail at bind time | Statement fails (type errors at bind time) | **Per dialect** (`DialectConfig.errors`, #270): the evaluator is quiet (`none`: row dropped in WHERE, NULL in the select list) in every dialect, and `evalQueryIn` layers the dialect's mode on top: sqlite → `quiet`; standard, postgres → `strict` (the statement fails when a clause yields an error on a row it is evaluated on); duckdb → `strictDivZeroNull` (`strict`, but division and modulo by zero are not errors). Covers every clause, window queries, scalar and `IN` subqueries, recursive CTEs and DML (#448). Not seen: bind/plan-time errors (no schema), subqueries under `AND`/`OR`, past a CASE's first condition or in `EXISTS` | decided (#270, #448) | `strictErrorTests`, `strictDmlTests` in `Test/SemanticsTest.lean`; `diffErrors` cases in DiffDuckdb and DiffPostgres, whose `diffTest` evaluate in the dialect's error mode |

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
| T9 | Bare column with aggregates `SELECT max(a), b FROM t` | Error (binder) | Error | **Per dialect** (`DialectConfig.bareColumns`, applied by the bridge): standard, postgres, duckdb → `unsupported` at elaboration; sqlite → accepted. With one `MIN`/`MAX` call, `b` comes from the first row where its argument is extreme (`AggCall.atExtreme`; ties keep the first row); with none, from the group's first row (`AggCall.first`). Several `MIN`/`MAX` calls or `MIN`/`MAX(DISTINCT …)` stay `unsupported` (sqlite: arbitrary, and the last tie with `DISTINCT`). When every argument is NULL the last row is used. sqlite's choice there depends on the plan (last row with `GROUP BY` or a plain scan, first row when its MAX optimisation answers `WHERE a IS NULL`), so that case is a known divergence. `SqlEquiv`'s evaluator accepts bare columns in every dialect. In the sqlite dialect it follows sqlite when the statement has one MIN/MAX (not DISTINCT), of any argument: the parser records `MinMaxMode.bareRow`, and the bare columns read the first row where the argument is extreme, or the last row when every value is NULL (`bareSampleRow`), as the bridge does. A call left of `IN (subquery)` counts, as in sqlite 3 (`SELECT name, MAX(age) IN (SELECT 35) FROM users` reads `name` on the max row, Carol; `MIN(age) IN (SELECT 1)` on the min row, Eve; #422). A call written more than once (`SELECT b, max(a) … HAVING max(a) > 1`) counts once, as in sqlite and the bridge; the comparison is syntactic, so `max(a)` and `max(t.a)` stay two calls in `SqlEquiv` (sqlite resolves both to one column and reads the max row; the bridge rejects the query as several `MIN`/`MAX`). Otherwise, in every dialect, they read the group's first row. That includes a bare column inside a window function over groups (#429): `MAX(age) - MIN(age) OVER (PARTITION BY COUNT(*))` under `GROUP BY department` reads `age` on each group's sample row, as sqlite does, where DuckDB and Postgres reject it. A `MIN`/`MAX` that occurs only inside a window function does not count for the sqlite rule in `SqlEquiv` (`SELECT department, name, RANK() OVER (ORDER BY MAX(age)) FROM users GROUP BY department` reads `name` on the group's first row; sqlite reads it on the max row): a known divergence, found in the #429 self-review (#446). Known divergence, pending a decision: sqlite (and the bridge) also count a `MIN`/`MAX` in `ORDER BY` (`SELECT b FROM t GROUP BY c ORDER BY max(a)` reads `b` on the max row); `SqlEquiv` does not, because following it would make the row count depend on `ORDER BY` under `DISTINCT`, against `evalSelect_orderBy_length` | decided (phase 8e; `SqlEquiv` sqlite rule from the Spider evaluate failures) | `elabStmt_correct_grouped` (proof: the bridge and `SqlEquiv` agree under `GROUP BY`, first and extreme row, `SqlBridge/CorrectExtreme.lean`; without `GROUP BY`, `elabStmt_correct_aggBare`), `SqliteDiffTest` (21 queries vs sqlite, plus rejections in both dialects), `AggregateExamples`, `BridgeDiffTest` (standard-dialect rejection); `SqlEquiv`: `bare_column_*` unit tests (column and expression arguments), DiffSqlite |
| T10 | `AVG` over integers (`AVG` of 1, 2; of 1, 1, 2), row 7 | `1.5`, `1.3333333333333333` (DOUBLE) | `1.5000…`, `1.3333333333333333` (numeric; `AVG(i) * 3` is `3.9999999999999999`) | Exact rational decimal: `3/2`, `4/3` (`AVG(i) * 3` is exactly `4`); `NULL` over no values; ill-typed over text | decided (#326, phase 8d) | `AggregateExamples`, `DuckdbDiffTest` (rounded to 12 places), `BridgeDiffTest`; related to row 7's rounding in the elaborator theorems (`CorrectAvg.AvgRel`) |
| T11 | `MIN`/`MAX` over booleans, row 14 | Boolean result | Error | Ill-typed | decided (#313) | `AggregateExamples` |
| T12 | `NULL` keys in `GROUP BY` | One group | One group | One group (`NULL` is `none`) | decided; `SqlEquiv` agrees since #315 (grouping keys erase the NULL type tag); set operations since #324 (rows compared by `Row.valueKey`); `DISTINCT` and aggregate `DISTINCT` too, and all of them compare by `Value.setKey` (NULLs equal, `1` = `1.0`) | `AggregateExamples`, `DuckdbDiffTest`, `BridgeDiffTest`, unit pins `group_by_typed_nulls_*`, `distinct_typed_nulls_one_row`, `*_numbers_by_value` |
| T13 | `SELECT DISTINCT a … ORDER BY b` with `b` not selected, row 5 | Sorts by the first source row's `b` | Error | Follows the parse (row 5): rejected in standard/postgres; in sqlite/duckdb, `aggregate` by the selected expressions with `AggCall.first b`, sorted, projected | decided (#319) | `OrderByExamples`; `DuckdbDiffTest` (duckdb-dialect corpus, ordered, agrees; also checked on sqlite) |
| T14 | Order of rows tied on every `ORDER BY` key | Unspecified | Unspecified | Input order (stable insertion sort) | decided (#318); the differential tests use tie-free keys | `OrderByExamples` |
| T15 | `ORDER BY 2` (integer literal) | Position | Position | Position; out of range is `unsupported` | decided (#318). `SqlEquiv` resolves positions at parse time since #316 (out of range is a parse error, as in sqlite, DuckDB and Postgres); after a `*` item it cannot count columns and still sorts by the constant | `BridgeDiffTest`, `DuckdbDiffTest`, unit pins `order_by_position*` |
| T16 | `LIKE` letter case and wildcards, row 8 | Case-sensitive | Case-sensitive | Follows the parse: `BinOp.like false` (standard, duckdb, postgres) or `BinOp.like true` (sqlite: ASCII letters only). `%` any sequence, `_` one character, no `ESCAPE` | decided (#322); `SqlEquiv` agrees since #323 (`likeMatch`, a port of the typed core's matcher) | `SetOpExamples`, `ScalarDiffTest` (independent reference), engine sweep of 676 pairs (DuckDB and sqlite), `BridgeDiffTest` sqlite-dialect corpus |
| T17 | Scalar subquery with several rows `WHERE x > (SELECT a FROM t)` | Error ("More than one row returned by a subquery used as an expression") | Error (same) | **Per dialect** (`DialectConfig.scalarSubqueryRows`, recorded on each `SubKind.scalar` node): standard, postgres, duckdb → `EvalError.cardinality` at evaluation (so such a node is never `divSafe`); sqlite → the first row's value. No rows is `NULL` everywhere. The subquery is evaluated strictly, once, even when the outer query has no rows, so the error is raised there too; DuckDB agrees, but Postgres is lazy (no error when the value is never needed: an empty outer query or a short-circuited `AND`), a known divergence in the error mode | decided (#329, phase 8f) | `SubqueryExamples`, `SqliteDiffTest` (first row, against sqlite) |
| T18 | Order of `SELECT DISTINCT` and set-operation rows without `ORDER BY`, and so which row `DISTINCT … LIMIT 1` keeps | Hash order (`Sales, Marketing, Engineering` for departments `Sales, Engineering, Marketing, Sales`) | Hash order (`Marketing, Engineering, Sales` on 16.15; depends on the plan and version) | Keeps the **last** copy of each row (`List.dedup`, as cslib-frontier): `Engineering, Marketing, Sales`. `SqlEquiv` keeps the **first** copy (`dedupByKey`), as sqlite does: `Sales, Engineering, Marketing`. The standard fixes no order without `ORDER BY`, so all four are conforming; the same rows come back, in a different order, and a `LIMIT` without `ORDER BY` can keep a different row (typed core `Engineering`, `SqlEquiv` and sqlite `Sales`, Postgres `Marketing`). Neither evaluator is changed: the elaborator theorem for plain `DISTINCT` relates the rows up to a permutation (`elabStmt_correct_distinct`), and `DISTINCT … LIMIT` without `ORDER BY` is outside it. **Set operations are the same case** (`UNION`, `INTERSECT`, `EXCEPT` deduplicate the same way in each evaluator): for departments `Sales, Engineering, Marketing, Sales`, `SELECT department … INTERSECT SELECT department …` is `Sales, Engineering, Marketing` in `SqlEquiv`, `Engineering, Marketing, Sales` in the typed core and in sqlite 3.45 (which sorts), `Sales, Engineering, Marketing` in DuckDB 1.5.3 and `Marketing, Engineering, Sales` in Postgres 16; `elabStmt_correct_setOp` relates the rows up to a permutation, and a set operation under `LIMIT` without a total `ORDER BY` is outside it | decided 2026-11-21 (keep both; relate up to order; extended to set operations the same day) | `BridgeDiffTest` (`.orderDiffers`, `.rowsDiffer`: fail if the two ever agree; plain `DISTINCT`, and `UNION`, `INTERSECT`, `EXCEPT`); `DiffPostgres` "DISTINCT order and LIMIT 1 (T18)" (same set; the `LIMIT 1` row is one of the distinct rows; logs the order Postgres chose) |

### Notes on individual rows

- **Printing (#267).** Choices are recorded in the AST, so printed SQL must carry
  them or say it cannot. `Stmt.toSqlIn d` prints for dialect `d`: NULLS clauses
  relative to `d`'s rule (row 1), and a sqlite case-insensitive LIKE as
  `LOWER(x) LIKE LOWER(p)` for case-sensitive dialects (row 8; exact in our
  evaluator and sqlite; see row 19 for DuckDB and Postgres). **Decision:** the MIN/MAX mode (rows 13, 14,
  T9) and the SUM/AVG boolean rule (row 18) have no SQL spelling, so `toSqlIn`
  refuses, with an error naming the choice, whenever `d` would record a different
  one on re-parsing. A case-sensitive LIKE printed for sqlite is refused for the
  same reason. Alternatives considered: documenting that printed SQL is
  dialect-bound (the loss stays quiet), or annotating printed SQL with a dialect
  comment that our parser reads (engines ignore it). The check re-parses the
  output and compares the two statements with these choices spelled out as
  comments (`PrintCfg.annotate`). Tests: per-dialect round trips of a corpus
  covering every recorded choice, and the 564 Spider queries in each dialect
  (checked once, all AST-identical); refusal and same-rows pins in
  `Test/ParserTest.lean` (`to_sql_in_*`).

- **Row 1** is the model for a configurable behaviour: one enum on the AST
  item, a `DialectConfig` field, and each differential harness running in its
  engine's dialect. Parsing the DuckDB cases with sqlite's rule makes the ASC case
  fail, which shows those tests check the NULL position.
- **Row 7**: AVG needed a fractional result type. The choice: an exact decimal
  when the quotient terminates, else rounded to 16 places (`avgNumeric`). No floats
  (#202), and the rule covers AVG only: decimal `/` stays unimplemented (#201). The
  typed core keeps exact rationals (T10), so a repeating average is the one place the
  two evaluators differ (BridgeDiffTest records it).
- **Row 8**: the certified rewriter's LIKE rules (`x LIKE '%'`, `x LIKE ''`,
  `x LIKE x`) are stated for the case-sensitive `BinOp.like` only; the
  sqlite dialect's `BinOp.likeCI` is not rewritten, so those rules stay sound
  in every dialect.
- **Row 6**: integer `/` and `%` used Lean's Euclidean division (`-7 / 2 =
  -4`, `-7 % 2 = 1`), matching no engine; found while pinning (#262) and fixed
  to truncate toward zero, as all three engines do.
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
- **LIKE ignored `_` and interior `%`** (fixed, #323). `simpleLike`
  handled only `%` at either end of the pattern, so `'ab' LIKE '_b'` and
  `'abc' LIKE 'a%c'` were FALSE. `likeMatch` is now a full matcher: `%` matches
  any sequence and `_` one character, anywhere in the pattern. It is the
  typed core's automaton over pattern suffixes, ported. The laws
  `like_match_all`, `like_empty_pattern` and `like_self` keep their statements,
  with their helper lemmas ported from `SqlCore` too. The scalar differential
  now checks every `LIKE` case against an independent backtracking matcher.
  Spider is unchanged. Pinned by the `like_*` unit tests, the `LIKE wildcard:`
  engine cases and the `BridgeDiffTest` corpus (both dialects).
- **DISTINCT and GROUP BY told equal values apart** (fixed, #315). `GROUP BY`
  split a typed and an untyped NULL into two groups. `SELECT DISTINCT` kept
  them as two rows, and both kept `1` and `1.0` apart, as did
  `COUNT(DISTINCT …)`. Every engine treats them as one value. Grouping keys,
  `SELECT DISTINCT` rows and aggregate `DISTINCT` values are now compared by
  `Value.setKey`, the comparison set operations use (#324): NULLs equal
  whatever their tag, and numbers by value. Each key is kept once, as its first
  row or value. `in_subquery_unnest_to_join` now holds on value keys (as a bag),
  since its two DISTINCT forms may meet rows with equal keys in different
  orders. Spider is unchanged. Pinned by `distinct_typed_nulls_one_row`,
  `*_numbers_by_value`, `group_by_typed_nulls_*` and the `distinct null:`
  engine cases.
- **`[NOT] IN (subquery)` ignored NULLs** (fixed, #330). It was two-valued: a
  match gave TRUE and anything else FALSE, so `5 NOT IN (SELECT NULL)` kept the
  row. It is now three-valued, as the standard and `IN (list)` define it
  (`inSubqueryResult`). A match gives TRUE. With no match, a NULL in the
  subquery, or a NULL probe against a non-empty subquery, gives unknown.
  Otherwise the result is FALSE, and an empty subquery gives FALSE even for a
  NULL probe. `NOT IN` negates, and unknown drops the row in a WHERE clause.
  `in_subquery_as_exists`, `not_in_subquery_as_not_exists` and
  `not_in_subquery_unnest_to_antijoin` now assume the probe and the subquery
  column are never NULL. That is the guard optimizers check before turning
  `NOT IN` into an anti-join. The theorems that use only "a match gives TRUE"
  keep their statements. Spider is unchanged (556): none of its `NOT IN`
  queries meet a NULL. Pinned by the `not_in_subquery_*`/`in_subquery_*` unit
  tests, the `NOT IN null:` engine cases and the `BridgeDiffTest` corpus.
- **Set operations compared column names and NULL type tags** (fixed,
  #324). `INTERSECT`, `EXCEPT` and `UNION` compared whole rows, names
  included, so `SELECT user_id FROM orders INTERSECT SELECT id FROM users`
  was empty. A typed and an untyped NULL were also two rows, and so were `1`
  and `1.0`. Rows are now compared by `Row.valueKey`: values in column
  order, NULL tags erased, numbers by value as `=` compares them (an integer
  as the equal decimal). Each value key is kept once, as its first row. That
  row keeps its own representation (`SELECT 1 UNION SELECT 1.0` gives `1`, as
  sqlite does). DuckDB types the column as the common supertype and prints
  `1.0`. The later branches' rows take the
  first branch's column names, which an `ORDER BY` over the compound relies
  on. Since #340 the names come from the first branch's SELECT list, so an
  empty first branch still names them (with a `*` there, from its first row).
  Laws that swap or merge branches now hold on values (`≃ᵇᵛ`, `≃ˢᵛ`), since
  the two sides name their columns differently. Spider evaluate 553 → 556:
  the EXCEPT, INTERSECT and UNION+EXCEPT failures. Pinned by the `set_op_*`
  unit tests and the `BridgeDiffTest` corpus.
- **ORDER BY/LIMIT after a compound query sorted only its last branch**
  (fixed, #317). The parser attached a trailing `ORDER BY`/`LIMIT`/`OFFSET` to
  the last `SELECT`, so `A UNION ALL B ORDER BY 1 LIMIT 1` returned all of `A`
  plus one row of `B`. The parser now builds `Query.ordered` over the whole
  compound query (sqlite, DuckDB and Postgres agree). A tail on an inner branch is
  a parse error, as in sqlite and Postgres. A position `k` resolves to the
  name of the leftmost branch's `k`-th column; an unaliased expression there is a
  parse error. Any other key must be an output name of the first branch;
  qualified names and expressions are errors, as in every engine, because
  evaluated on the compound's rows they would quietly sort by NULL (a name
  that only a later branch uses: registry row 15, the name of a result column
  whose branches name it differently). Since #324 the later branches' rows
  take the first branch's column names, so such a key finds them too, even
  when the first branch has no rows (#340). Spider is unchanged: none of its queries has a
  compound tail. Pinned by the `compound_order_by_*` unit tests and the
  `BridgeDiffTest` and `DuckdbDiffTest` corpus.

---

## Backlog to meet the policy

Rows that do not yet meet the testing requirements in §2:

- **`SqlEquiv` set operations whose first branch has a `*`**: the column names
  come from the first branch's first row, so if that branch is empty the
  later branches' rows keep their own names. Without a `*`, the names come
  from the SELECT list (#340). This is the same limit as positions after `*`
  (#316).
- **Postgres differential gaps**: `DiffPostgres` compares results and parse-time
  rejections only. Rows where Postgres raises a query error and we return a
  quieter `none` (10, 13, 14 in the postgres dialect, 17, 18) are pinned by unit
  tests, not by Postgres; an error-agreement mode would need the evaluator to
  surface expression errors.
