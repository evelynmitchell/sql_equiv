# Spider Benchmark

Text-to-SQL benchmark from Yale LILY Lab.

## Download

```bash
# Option 1: Google Drive (official)
# Download from: https://drive.google.com/uc?id=1iRDVHLr4mX2wQKSgA9J8Pire73Jahh0m

# Option 2: Direct link (may change)
wget https://yale-lily.github.io/spider/data/spider.zip
unzip spider.zip
```

## Contents

After extraction:
- `train_spider.json` - 7,000 training examples
- `train_others.json` - Additional training data
- `dev.json` - 1,034 development examples
- `tables.json` - Database schemas
- `database/` - SQLite database files

## Query Complexity Levels

| Level | Description | Example |
|-------|-------------|---------|
| easy | Single table, simple WHERE | `SELECT name FROM users WHERE age > 18` |
| medium | JOIN, GROUP BY | `SELECT dept, COUNT(*) FROM emp GROUP BY dept` |
| hard | Nested queries, multiple JOINs | Subqueries, 3+ table joins |
| extra | Complex nesting, set operations | UNION, nested subqueries, CTEs |

## Citation

```bibtex
@inproceedings{Yu&al.18,
  title     = {Spider: A Large-Scale Human-Labeled Dataset for Complex and Cross-Domain Semantic Parsing and Text-to-SQL Task},
  author    = {Tao Yu and Rui Zhang and Kai Yang and Michihiro Yasunaga and Dongxu Wang and Zifan Li and James Ma and Irene Li and Qingning Yao and Shanelle Roman and Zilin Zhang and Dragomir Radev},
  booktitle = {EMNLP},
  year      = {2018}
}
```

## License

CC BY-SA 4.0

## Parse-Rate Baseline (north-star metric)

`dev_queries.sql` contains the 563 unique queries from the Spider dev set
(extracted from [taoyds/spider](https://github.com/taoyds/spider)
`evaluation_examples/examples/dev.json`, CC BY-SA 4.0).

`python3 tools/spider_parse_baseline.py` parses all of them through our
parser and writes `parse_report.md` (rate + failure classes, each an issue
candidate). The passing count is ratcheted in `tools/spider_parse_minimum.txt`
and checked in CI. Next stages (evaluate-rate, oracle-agreement-rate) need the
Spider databases — see Download above.

## Evaluate-Rate Baseline (north-star metric, stage 2)

`python3 tools/spider_eval_baseline.py` builds every dev schema
(`dev_tables.json`) with deterministic FK-aware synthetic data, evaluates all
564 `dev_queries.jsonl` pairs with our engine (`sql_equiv --spider-eval`) and
with in-process sqlite3 (the Spider-fidelity oracle), and compares result
multisets. Report: `eval_report.md`; ratchet: `tools/spider_eval_minimum.txt`
(CI-checked). Failure classes are issue candidates, per the operating loop.
A failure that is a decided implementation-defined difference stays a failure
but is reported under its own label naming the registry row (e.g. **known
divergence: AVG/SUM over a TEXT column (registry row 17)**), so the remaining
unlabelled classes are the ones still to investigate.

**DuckDB cross-check** (#225 stage 2). Each disagreement with sqlite is re-run on
DuckDB (the `duckdb` CLI, loaded with the same synthetic data: `number`/`boolean`
columns as BIGINT, the rest as VARCHAR). If DuckDB rejects the query or answers
differently from sqlite, the class gains an **engine-divergent** prefix saying
which, and whether our answer is DuckDB's. sqlite's answer is then not the only
defensible one, so the report counts these apart from "failures of ours" (queries
where sqlite and DuckDB agree and we do not). The headline rate and the ratchet
are unchanged: an engine-divergent query still does not count as agreement. Only
disagreements are cross-checked, so CI stays fast; without the CLI the report says
the cross-check was not run. A self-test guards the classification.

**Postgres tiebreaker.** For an engine-divergent query, the harness also runs
Postgres (`psql`, the same data in a throwaway schema: BIGINT/TEXT columns, table
and column names lowercased so Spider's unquoted identifiers resolve). If Postgres
gives sqlite's answer, two of the three oracles agree against ours and the query
is counted as a failure of ours under **tiebroken against ours**. Otherwise the
engine-divergent label records what Postgres did (rejects the query, matches ours,
matches DuckDB, or differs from all three). Without a reachable Postgres (`psql -c
'select 1'` fails) the tiebreaker is skipped and the report says so. Locally:
`pg_ctlcluster 16 main start`, then a superuser role and database for your user
(`su postgres -c "createuser -s $USER && createdb $USER"`). Self-tested on every
run when Postgres is reachable.

**Stress variants** (`--stress=K`). The fixed data (5 rows per table, NULLs only on
row 3, foreign keys cycling 1–5) can hide bugs: the grouped-aggregate bug of #353
passed most queries by luck of the data. `python3 tools/spider_eval_baseline.py
--stress=40` re-runs the corpus on 40 seeded variants (0–8 rows per table; NULLs
anywhere outside primary keys; duplicate, zero and negative numbers; dangling or
NULL foreign keys) and writes `stress_report.md`: the queries that agree with
sqlite on the fixed data but not on some variant. It is not ratcheted; its classes
are issue candidates. The variants are deterministic (seeded by database, table and
variant number). Known noise: a query whose *subquery* sorts with `LIMIT` on a tie
(e.g. `ORDER BY count(*) LIMIT 1` with equal counts) can pick a different row in
any engine; the tie-valid check covers only a top-level `ORDER BY … LIMIT`.
