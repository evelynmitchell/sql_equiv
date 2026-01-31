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
