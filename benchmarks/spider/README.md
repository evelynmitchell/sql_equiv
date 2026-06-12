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
