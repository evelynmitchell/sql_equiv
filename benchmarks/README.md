# SQL Benchmarks and Test Corpora

This directory contains real-world SQL queries for testing sql_equiv's parser, semantics, and optimizer.

---

## Directory Structure

```
benchmarks/
├── spider/           # Text-to-SQL benchmark (academic)
├── tpc-h/            # TPC-H analytics benchmark
├── tpc-ds/           # TPC-DS complex analytics
├── sqlite-compat/    # SQLite compatibility tests
├── duckdb/           # DuckDB test queries
├── sqlglot/          # SQLGlot transpiler tests
├── real-world/       # Anonymized production queries
└── regression/       # Bug-fix regression tests
```

---

## Benchmark Sources

### Spider (Text-to-SQL)

**Source:** https://yale-lily.github.io/spider
**License:** CC BY-SA 4.0
**Size:** 10,181 queries across 200 databases

The Spider benchmark is ideal for testing because:
- Wide variety of SQL constructs
- Multiple complexity levels (easy → extra hard)
- Real database schemas
- Ground truth for equivalence (multiple valid SQL per question)

**Setup:**
```bash
cd benchmarks/spider
wget https://drive.google.com/uc?id=1iRDVHLr4mX2wQKSgA9J8Pire73Jahh0m -O spider.zip
unzip spider.zip
```

**Files:**
- `train_spider.json` - Training queries
- `dev.json` - Development set
- `tables.json` - Database schemas

---

### TPC-H (Analytics Benchmark)

**Source:** https://www.tpc.org/tpch/
**License:** Free for research/benchmarking
**Size:** 22 queries

Standard analytics benchmark with:
- Complex joins (up to 8 tables)
- Aggregations with GROUP BY
- Subqueries and CTEs
- Date arithmetic

**Files:**
- `queries/` - The 22 TPC-H queries
- `schema.sql` - Table definitions

---

### TPC-DS (Complex Analytics)

**Source:** https://www.tpc.org/tpcds/
**License:** Free for research
**Size:** 99 queries

More complex than TPC-H:
- Window functions
- ROLLUP/CUBE
- Complex subqueries
- Multiple query variants

**Files:**
- `queries/` - The 99 TPC-DS queries
- `schema.sql` - Table definitions (24 tables)

---

### SQLite Compatibility

**Source:** SQLite test suite, Turso/libSQL, litestream
**License:** Public domain (SQLite), varies for others

Edge cases specific to SQLite:
- Type affinity behavior
- NULL handling quirks
- ROWID behavior
- Collation sequences
- Expression evaluation order

**Subdirectories:**
- `core/` - Core SQL functionality
- `null-handling/` - Three-valued logic edge cases
- `type-coercion/` - Implicit type conversion
- `edge-cases/` - Unusual but valid SQL

---

### DuckDB Tests

**Source:** https://github.com/duckdb/duckdb/tree/main/test/sql
**License:** MIT

Modern analytical SQL tests:
- Window functions
- CTEs and recursive queries
- Advanced aggregations
- Large result sets

---

### SQLGlot Tests

**Source:** https://github.com/tobymao/sqlglot/tree/main/tests
**License:** MIT

SQL transpilation test cases:
- Dialect variations
- Parse/unparse round-trips
- Optimization transformations

---

### Real-World Queries

Anonymized queries from production systems. Use the sql_anonymizer tool before contributing:

```bash
cd tools/sql_anonymizer
python sql_anonymize.py /path/to/queries.sql \
  -o ../benchmarks/real-world/contribution.sql \
  -m mapping.json
```

**Subdirectories:**
- `analytics/` - BI and reporting queries
- `transactional/` - OLTP patterns
- `etl/` - Data transformation queries
- `migrations/` - Schema evolution patterns

**Contributing:**
1. Anonymize all table/column names and literals
2. Remove any comments with business context
3. Include a brief description of query purpose
4. Note the source database dialect

---

### Regression Tests

Queries that exposed bugs or edge cases:
- Parser failures
- Incorrect semantic evaluation
- Optimizer incorrectness
- Performance issues

**Format:**
```sql
-- regression/issue-123.sql
-- Description: Parser failed on nested CASE expressions
-- Fixed in: commit abc123
-- Original error: "unexpected token WHEN"

SELECT
  CASE
    WHEN x > 0 THEN
      CASE WHEN y > 0 THEN 'positive' ELSE 'mixed' END
    ELSE 'negative'
  END
FROM t;
```

---

## Query Format

All queries should be in `.sql` files with metadata comments:

```sql
-- File: spider/train/query_0001.sql
-- Source: Spider benchmark
-- Complexity: easy
-- Tables: employee, department
-- Features: JOIN, WHERE, aggregate

SELECT department.name, COUNT(*)
FROM employee
JOIN department ON employee.dept_id = department.id
WHERE employee.salary > 50000
GROUP BY department.name;
```

---

## Equivalence Pairs

For testing equivalence verification, create paired files:

```
equivalence/
├── pair_001_a.sql    # Original query
├── pair_001_b.sql    # Equivalent rewrite
├── pair_001.json     # Metadata (should be equivalent: true/false)
```

Example `pair_001.json`:
```json
{
  "name": "IN-to-EXISTS transformation",
  "equivalent": true,
  "notes": "Standard IN subquery to correlated EXISTS rewrite"
}
```

---

## Running Benchmarks

### Parse All Queries
```bash
lake exe sql_equiv_test --benchmark spider/
```

### Check Equivalence Pairs
```bash
lake exe sql_equiv_test --equiv-pairs equivalence/
```

### Generate Coverage Report
```bash
lake exe sql_equiv_test --coverage benchmarks/ > coverage_report.txt
```

---

## Statistics

| Benchmark | Queries | Parsed | Failed | Coverage |
|-----------|---------|--------|--------|----------|
| Spider | 10,181 | - | - | - |
| TPC-H | 22 | - | - | - |
| TPC-DS | 99 | - | - | - |
| SQLite | - | - | - | - |
| Real-world | - | - | - | - |

*(To be updated as benchmarks are added)*

---

## Contributing

1. **Academic benchmarks**: Download and extract to appropriate directory
2. **Real-world queries**: Anonymize first using `tools/sql_anonymizer/`
3. **Regression tests**: Include issue number and fix commit
4. **Equivalence pairs**: Verify both queries are semantically equivalent

See [CONTRIBUTING.md](../CONTRIBUTING.md) for full guidelines.

---

## Legal Notes

- **Spider**: Academic use, cite the paper
- **TPC-H/TPC-DS**: Free for research, cannot claim TPC compliance without audit
- **SQLite tests**: Public domain
- **Real-world**: Must be anonymized, no PII or business secrets
