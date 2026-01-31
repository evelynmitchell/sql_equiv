# SQL Implementation Gap Analysis

This document provides a comprehensive analysis of SQL feature coverage in the sql_equiv project, comparing against SQL standards (SQL-92, SQL-99, SQL:2003+) and common database dialects.

---

## Executive Summary

The sql_equiv project implements approximately **80-85% of SQL features** needed for query equivalence verification, with strong coverage of core DML operations. The implementation targets the Spider benchmark and formal verification use cases rather than complete dialect compatibility.

**Strengths:**
- Comprehensive SELECT/JOIN/subquery support
- Proper three-valued NULL logic
- CTEs including recursive queries
- Window function basics
- Formal semantic foundation

**Key Gaps:**
- Type casting (CAST)
- Date/time types and functions
- Extended scalar function library
- Window frame specifications
- Some SQL-99+ features

---

## 1. Feature Coverage Matrix

### 1.1 Data Manipulation Language (DML)

| Feature | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|---------|:------:|:------:|:--------:|:------:|-------|
| SELECT | ✓ | ✓ | ✓ | ✅ Full | All standard clauses |
| SELECT DISTINCT | ✓ | ✓ | ✓ | ✅ Full | |
| SELECT * | ✓ | ✓ | ✓ | ✅ Full | With optional table qualifier |
| Column aliases (AS) | ✓ | ✓ | ✓ | ✅ Full | |
| FROM clause | ✓ | ✓ | ✓ | ✅ Full | Tables, subqueries, joins |
| Table aliases | ✓ | ✓ | ✓ | ✅ Full | |
| WHERE clause | ✓ | ✓ | ✓ | ✅ Full | |
| GROUP BY | ✓ | ✓ | ✓ | ✅ Full | |
| HAVING | ✓ | ✓ | ✓ | ✅ Full | |
| ORDER BY | ✓ | ✓ | ✓ | ✅ Full | ASC/DESC supported |
| LIMIT | - | - | ✓ | ✅ Full | Non-standard but common |
| OFFSET | - | - | ✓ | ✅ Full | |
| FETCH FIRST/NEXT | - | - | ✓ | ❌ Missing | Standard pagination |
| INSERT VALUES | ✓ | ✓ | ✓ | ✅ Full | |
| INSERT SELECT | ✓ | ✓ | ✓ | ✅ Full | |
| UPDATE | ✓ | ✓ | ✓ | ✅ Full | |
| DELETE | ✓ | ✓ | ✓ | ✅ Full | |
| MERGE | - | ✓ | ✓ | ❌ Missing | Upsert operation |
| TRUNCATE | - | ✓ | ✓ | ❌ Missing | |

### 1.2 Joins

| Feature | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|---------|:------:|:------:|:--------:|:------:|-------|
| INNER JOIN | ✓ | ✓ | ✓ | ✅ Full | |
| LEFT OUTER JOIN | ✓ | ✓ | ✓ | ✅ Full | |
| RIGHT OUTER JOIN | ✓ | ✓ | ✓ | ✅ Full | |
| FULL OUTER JOIN | ✓ | ✓ | ✓ | ✅ Full | |
| CROSS JOIN | ✓ | ✓ | ✓ | ✅ Full | |
| ON clause | ✓ | ✓ | ✓ | ✅ Full | |
| USING clause | ✓ | ✓ | ✓ | ❌ Missing | `JOIN t USING (col)` |
| NATURAL JOIN | ✓ | ✓ | ✓ | ❌ Missing | Implicit column matching |
| LATERAL | - | ✓ | ✓ | ❌ Missing | Correlated derived tables |
| CROSS APPLY | - | - | - | ❌ Missing | SQL Server specific |
| OUTER APPLY | - | - | - | ❌ Missing | SQL Server specific |

### 1.3 Subqueries

| Feature | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|---------|:------:|:------:|:--------:|:------:|-------|
| Scalar subquery | ✓ | ✓ | ✓ | ✅ Full | Single value in expression |
| IN subquery | ✓ | ✓ | ✓ | ✅ Full | |
| NOT IN subquery | ✓ | ✓ | ✓ | ✅ Full | |
| EXISTS subquery | ✓ | ✓ | ✓ | ✅ Full | |
| NOT EXISTS subquery | ✓ | ✓ | ✓ | ✅ Full | |
| Correlated subquery | ✓ | ✓ | ✓ | ✅ Full | References outer query |
| Derived table (FROM subquery) | ✓ | ✓ | ✓ | ✅ Full | |
| ANY/SOME | ✓ | ✓ | ✓ | ❌ Missing | `x > ANY (SELECT ...)` |
| ALL | ✓ | ✓ | ✓ | ❌ Missing | `x > ALL (SELECT ...)` |

### 1.4 Set Operations

| Feature | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|---------|:------:|:------:|:--------:|:------:|-------|
| UNION | ✓ | ✓ | ✓ | ✅ Full | Removes duplicates |
| UNION ALL | ✓ | ✓ | ✓ | ✅ Full | Keeps duplicates |
| INTERSECT | ✓ | ✓ | ✓ | ✅ Full | |
| INTERSECT ALL | - | ✓ | ✓ | ❌ Missing | |
| EXCEPT | ✓ | ✓ | ✓ | ✅ Full | |
| EXCEPT ALL | - | ✓ | ✓ | ❌ Missing | |

### 1.5 Common Table Expressions (CTEs)

| Feature | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|---------|:------:|:------:|:--------:|:------:|-------|
| WITH clause | - | ✓ | ✓ | ✅ Full | |
| Multiple CTEs | - | ✓ | ✓ | ✅ Full | `WITH a AS (...), b AS (...)` |
| WITH RECURSIVE | - | ✓ | ✓ | ✅ Full | |
| SEARCH clause | - | - | ✓ | ❌ Missing | BFS/DFS ordering |
| CYCLE clause | - | - | ✓ | ❌ Missing | Cycle detection |

### 1.6 Aggregate Functions

| Feature | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|---------|:------:|:------:|:--------:|:------:|-------|
| COUNT(*) | ✓ | ✓ | ✓ | ✅ Full | |
| COUNT(expr) | ✓ | ✓ | ✓ | ✅ Full | |
| COUNT(DISTINCT expr) | ✓ | ✓ | ✓ | ✅ Full | |
| SUM | ✓ | ✓ | ✓ | ✅ Full | |
| AVG | ✓ | ✓ | ✓ | ✅ Full | |
| MIN | ✓ | ✓ | ✓ | ✅ Full | |
| MAX | ✓ | ✓ | ✓ | ✅ Full | |
| STDDEV / STDDEV_POP | - | ✓ | ✓ | ❌ Missing | Standard deviation |
| VARIANCE / VAR_POP | - | ✓ | ✓ | ❌ Missing | |
| STDDEV_SAMP / VAR_SAMP | - | ✓ | ✓ | ❌ Missing | Sample variants |
| PERCENTILE_CONT | - | - | ✓ | ❌ Missing | |
| PERCENTILE_DISC | - | - | ✓ | ❌ Missing | |
| MODE | - | - | ✓ | ❌ Missing | |
| LISTAGG / STRING_AGG | - | - | ✓ | ❌ Missing | String aggregation |
| ARRAY_AGG | - | - | ✓ | ❌ Missing | |
| FILTER clause | - | - | ✓ | ❌ Missing | `COUNT(*) FILTER (WHERE ...)` |

### 1.7 Window Functions

| Feature | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|---------|:------:|:------:|:--------:|:------:|-------|
| OVER clause | - | ✓ | ✓ | ✅ Full | |
| PARTITION BY | - | ✓ | ✓ | ✅ Full | |
| ORDER BY in OVER | - | ✓ | ✓ | ✅ Full | |
| ROW_NUMBER() | - | ✓ | ✓ | ✅ Full | |
| RANK() | - | ✓ | ✓ | ✅ Full | |
| DENSE_RANK() | - | ✓ | ✓ | ✅ Full | |
| NTILE(n) | - | ✓ | ✓ | ❌ Missing | |
| LAG(expr, offset) | - | - | ✓ | ❌ Missing | Previous row value |
| LEAD(expr, offset) | - | - | ✓ | ❌ Missing | Next row value |
| FIRST_VALUE(expr) | - | - | ✓ | ❌ Missing | |
| LAST_VALUE(expr) | - | - | ✓ | ❌ Missing | |
| NTH_VALUE(expr, n) | - | - | ✓ | ❌ Missing | |
| CUME_DIST() | - | - | ✓ | ❌ Missing | Cumulative distribution |
| PERCENT_RANK() | - | - | ✓ | ❌ Missing | |
| Window aggregates (SUM OVER) | - | ✓ | ✓ | ✅ Full | |
| ROWS frame | - | ✓ | ✓ | ❌ Missing | `ROWS BETWEEN ...` |
| RANGE frame | - | ✓ | ✓ | ❌ Missing | `RANGE BETWEEN ...` |
| GROUPS frame | - | - | ✓ | ❌ Missing | SQL:2011 |
| UNBOUNDED PRECEDING | - | ✓ | ✓ | ❌ Missing | |
| CURRENT ROW | - | ✓ | ✓ | ❌ Missing | |
| UNBOUNDED FOLLOWING | - | ✓ | ✓ | ❌ Missing | |
| EXCLUDE clause | - | - | ✓ | ❌ Missing | |
| Named windows | - | ✓ | ✓ | ❌ Missing | `WINDOW w AS (...)` |

### 1.8 Expressions and Operators

| Feature | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|---------|:------:|:------:|:--------:|:------:|-------|
| Arithmetic (+, -, *, /, %) | ✓ | ✓ | ✓ | ✅ Full | |
| Comparison (=, <>, <, <=, >, >=) | ✓ | ✓ | ✓ | ✅ Full | |
| Logical (AND, OR, NOT) | ✓ | ✓ | ✓ | ✅ Full | |
| String concatenation (‖) | ✓ | ✓ | ✓ | ✅ Full | |
| IS NULL / IS NOT NULL | ✓ | ✓ | ✓ | ✅ Full | |
| IS TRUE / FALSE / UNKNOWN | - | ✓ | ✓ | ❌ Missing | |
| IS DISTINCT FROM | - | ✓ | ✓ | ❌ Missing | NULL-safe equality |
| BETWEEN | ✓ | ✓ | ✓ | ✅ Full | |
| IN (value list) | ✓ | ✓ | ✓ | ✅ Full | |
| LIKE | ✓ | ✓ | ✓ | ✅ Full | |
| SIMILAR TO | - | ✓ | ✓ | ❌ Missing | Regex-like patterns |
| CASE WHEN THEN ELSE END | ✓ | ✓ | ✓ | ✅ Full | |
| Simple CASE (CASE x WHEN) | ✓ | ✓ | ✓ | ⚠️ Partial | Syntax may vary |
| NULLIF(a, b) | ✓ | ✓ | ✓ | ❌ Missing | |
| COALESCE(a, b, ...) | ✓ | ✓ | ✓ | ❌ Missing | |
| CAST(x AS type) | ✓ | ✓ | ✓ | ❌ Missing | **High priority** |
| :: operator (PostgreSQL) | - | - | - | ❌ Missing | Dialect-specific |

### 1.9 Scalar Functions

#### 1.9.1 String Functions

| Function | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|----------|:------:|:------:|:--------:|:------:|-------|
| LENGTH | ✓ | ✓ | ✓ | ✅ Implemented | |
| CHAR_LENGTH | ✓ | ✓ | ✓ | ❌ Missing | Alias for LENGTH |
| UPPER | ✓ | ✓ | ✓ | ✅ Implemented | |
| LOWER | ✓ | ✓ | ✓ | ✅ Implemented | |
| SUBSTRING | ✓ | ✓ | ✓ | ❌ Missing | **High priority** |
| SUBSTR | - | - | - | ❌ Missing | Common alias |
| TRIM | ✓ | ✓ | ✓ | ❌ Missing | |
| LTRIM | - | - | - | ❌ Missing | Left trim |
| RTRIM | - | - | - | ❌ Missing | Right trim |
| REPLACE | - | ✓ | ✓ | ❌ Missing | |
| POSITION / INSTR | ✓ | ✓ | ✓ | ❌ Missing | Find substring |
| CONCAT | - | ✓ | ✓ | ❌ Missing | Multi-arg concat |
| LPAD / RPAD | - | - | - | ❌ Missing | Padding |
| LEFT / RIGHT | - | - | - | ❌ Missing | Substring shortcuts |
| REVERSE | - | - | - | ❌ Missing | |
| SPLIT_PART | - | - | - | ❌ Missing | PostgreSQL |
| REGEXP_REPLACE | - | - | - | ❌ Missing | Regex replace |

#### 1.9.2 Numeric Functions

| Function | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|----------|:------:|:------:|:--------:|:------:|-------|
| ABS | ✓ | ✓ | ✓ | ❌ Missing | |
| ROUND | - | ✓ | ✓ | ❌ Missing | |
| TRUNC / TRUNCATE | - | ✓ | ✓ | ❌ Missing | |
| FLOOR | - | ✓ | ✓ | ❌ Missing | |
| CEIL / CEILING | - | ✓ | ✓ | ❌ Missing | |
| MOD | ✓ | ✓ | ✓ | ❌ Missing | % operator exists |
| POWER | - | ✓ | ✓ | ❌ Missing | |
| SQRT | - | ✓ | ✓ | ❌ Missing | |
| EXP | - | ✓ | ✓ | ❌ Missing | |
| LN / LOG | - | ✓ | ✓ | ❌ Missing | |
| SIGN | - | ✓ | ✓ | ❌ Missing | |
| GREATEST | - | - | - | ❌ Missing | Max of args |
| LEAST | - | - | - | ❌ Missing | Min of args |
| RANDOM / RAND | - | - | - | ❌ Missing | |

#### 1.9.3 Date/Time Functions

| Function | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|----------|:------:|:------:|:--------:|:------:|-------|
| DATE type | ✓ | ✓ | ✓ | ❌ Missing | **High priority** |
| TIME type | ✓ | ✓ | ✓ | ❌ Missing | |
| TIMESTAMP type | ✓ | ✓ | ✓ | ❌ Missing | |
| INTERVAL type | ✓ | ✓ | ✓ | ❌ Missing | |
| CURRENT_DATE | ✓ | ✓ | ✓ | ❌ Missing | |
| CURRENT_TIME | ✓ | ✓ | ✓ | ❌ Missing | |
| CURRENT_TIMESTAMP | ✓ | ✓ | ✓ | ❌ Missing | |
| NOW() | - | - | - | ❌ Missing | Common alias |
| EXTRACT(part FROM date) | ✓ | ✓ | ✓ | ❌ Missing | **High priority** |
| DATE_PART | - | - | - | ❌ Missing | PostgreSQL |
| DATE_ADD / DATE_SUB | - | - | - | ❌ Missing | Date arithmetic |
| DATEDIFF | - | - | - | ❌ Missing | |
| DATE_TRUNC | - | - | - | ❌ Missing | PostgreSQL |
| TO_DATE / TO_CHAR | - | - | - | ❌ Missing | Formatting |
| AGE | - | - | - | ❌ Missing | PostgreSQL |

#### 1.9.4 Conditional Functions

| Function | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|----------|:------:|:------:|:--------:|:------:|-------|
| COALESCE | ✓ | ✓ | ✓ | ❌ Missing | **High priority** |
| NULLIF | ✓ | ✓ | ✓ | ❌ Missing | |
| NVL | - | - | - | ❌ Missing | Oracle |
| IFNULL | - | - | - | ❌ Missing | MySQL |
| IIF | - | - | - | ❌ Missing | SQL Server |
| DECODE | - | - | - | ❌ Missing | Oracle |

### 1.10 Data Types

| Type | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|------|:------:|:------:|:--------:|:------:|-------|
| INTEGER / INT | ✓ | ✓ | ✓ | ✅ Full | |
| SMALLINT | ✓ | ✓ | ✓ | ❌ Missing | |
| BIGINT | - | ✓ | ✓ | ❌ Missing | |
| DECIMAL / NUMERIC | ✓ | ✓ | ✓ | ❌ Missing | Precision/scale |
| FLOAT / REAL / DOUBLE | ✓ | ✓ | ✓ | ❌ Missing | |
| CHAR(n) | ✓ | ✓ | ✓ | ❌ Missing | Fixed-length |
| VARCHAR(n) | ✓ | ✓ | ✓ | ⚠️ Partial | As STRING |
| TEXT | - | - | - | ⚠️ Partial | As STRING |
| BOOLEAN | - | ✓ | ✓ | ✅ Full | |
| DATE | ✓ | ✓ | ✓ | ❌ Missing | |
| TIME | ✓ | ✓ | ✓ | ❌ Missing | |
| TIMESTAMP | ✓ | ✓ | ✓ | ❌ Missing | |
| INTERVAL | ✓ | ✓ | ✓ | ❌ Missing | |
| BLOB / BYTEA | - | ✓ | ✓ | ❌ Missing | Binary |
| CLOB / TEXT | - | ✓ | ✓ | ❌ Missing | Large text |
| ARRAY | - | ✓ | ✓ | ❌ Missing | |
| JSON / JSONB | - | - | ✓ | ❌ Missing | |
| UUID | - | - | - | ❌ Missing | |

### 1.11 Data Definition Language (DDL)

| Feature | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|---------|:------:|:------:|:--------:|:------:|-------|
| CREATE TABLE | ✓ | ✓ | ✓ | ❌ Missing | Not needed for equiv |
| DROP TABLE | ✓ | ✓ | ✓ | ❌ Missing | |
| ALTER TABLE | ✓ | ✓ | ✓ | ❌ Missing | |
| CREATE INDEX | ✓ | ✓ | ✓ | ❌ Missing | |
| CREATE VIEW | ✓ | ✓ | ✓ | ❌ Missing | |
| PRIMARY KEY | ✓ | ✓ | ✓ | ❌ Missing | |
| FOREIGN KEY | ✓ | ✓ | ✓ | ❌ Missing | |
| UNIQUE | ✓ | ✓ | ✓ | ❌ Missing | |
| CHECK | ✓ | ✓ | ✓ | ❌ Missing | |
| DEFAULT | ✓ | ✓ | ✓ | ❌ Missing | |
| NOT NULL | ✓ | ✓ | ✓ | ❌ Missing | |

### 1.12 Advanced Features

| Feature | SQL-92 | SQL-99 | SQL:2003 | Status | Notes |
|---------|:------:|:------:|:--------:|:------:|-------|
| GROUP BY ROLLUP | - | ✓ | ✓ | ❌ Missing | |
| GROUP BY CUBE | - | ✓ | ✓ | ❌ Missing | |
| GROUPING SETS | - | - | ✓ | ❌ Missing | |
| GROUPING() function | - | ✓ | ✓ | ❌ Missing | |
| NULLS FIRST/LAST | - | ✓ | ✓ | ❌ Missing | ORDER BY option |
| COLLATE | ✓ | ✓ | ✓ | ❌ Missing | |
| Transactions | ✓ | ✓ | ✓ | ❌ Missing | Not needed |
| Stored procedures | - | ✓ | ✓ | ❌ Missing | Not needed |
| Triggers | ✓ | ✓ | ✓ | ❌ Missing | Not needed |

---

## 2. Database Dialect Differences

### 2.1 Syntax Variations

| Feature | Standard SQL | PostgreSQL | MySQL | SQLite | SQL Server |
|---------|--------------|------------|-------|--------|------------|
| String quotes | `'single'` | `'single'` | `'single'` or `"double"` | `'single'` | `'single'` |
| Identifier quotes | `"double"` | `"double"` | `` `backtick` `` | `"double"` or `` ` `` | `[brackets]` |
| String concat | `‖` | `‖` | `CONCAT()` | `‖` | `+` |
| Boolean literals | TRUE/FALSE | TRUE/FALSE | TRUE/FALSE/1/0 | 1/0 | 1/0 |
| LIMIT syntax | FETCH FIRST | LIMIT n | LIMIT n or LIMIT o,n | LIMIT n | TOP n |
| Type cast | CAST(x AS t) | `x::type` | CAST/CONVERT | CAST | CAST/CONVERT |
| ILIKE (case-insensitive) | LIKE + COLLATE | ILIKE | LIKE (case varies) | LIKE | LIKE |
| Auto-increment | GENERATED | SERIAL | AUTO_INCREMENT | AUTOINCREMENT | IDENTITY |

### 2.2 Dialect-Specific Features Not Supported

**PostgreSQL:**
- Array operations (`ARRAY[]`, `@>`, `<@`, `&&`)
- JSONB operations (`->`, `->>`, `#>`, `@?`)
- `RETURNING` clause
- `ON CONFLICT` (upsert)
- Table inheritance
- Range types
- `DISTINCT ON`
- `ILIKE` operator
- `::` cast syntax

**MySQL:**
- `LIMIT offset, count` syntax
- `ON DUPLICATE KEY UPDATE`
- `REPLACE INTO`
- `@@` session variables
- `STRAIGHT_JOIN`
- Full-text search (`MATCH ... AGAINST`)
- `GROUP_CONCAT`

**SQLite:**
- `rowid` pseudo-column
- Type affinity (flexible typing)
- `GLOB` operator
- `PRAGMA` statements
- `INSERT OR REPLACE`
- `INDEXED BY` hints

**SQL Server:**
- `TOP n` instead of LIMIT
- `OUTPUT` clause (like RETURNING)
- `CROSS APPLY` / `OUTER APPLY`
- `FOR XML` / `FOR JSON`
- `PIVOT` / `UNPIVOT`
- Table variables (`@table`)
- CTEs with `;WITH` prefix
- `MERGE` statement

**Oracle:**
- `ROWNUM` pseudo-column
- `(+)` outer join syntax (deprecated)
- `CONNECT BY` hierarchical queries
- `DECODE` function
- `NVL`, `NVL2`
- Sequences (`nextval`, `currval`)
- `MINUS` instead of EXCEPT

---

## 3. Priority Recommendations

### 3.1 High Priority (Common in Real Queries)

| Feature | Effort | Impact | Notes |
|---------|--------|--------|-------|
| CAST(x AS type) | Medium | High | Essential for type handling |
| COALESCE | Low | High | Very common NULL handling |
| NULLIF | Low | Medium | Common with COALESCE |
| SUBSTRING/SUBSTR | Low | High | String manipulation |
| DATE/TIME types | High | High | Business queries |
| EXTRACT | Medium | High | Date part extraction |
| LAG/LEAD | Medium | High | Common analytics |
| Window frames | High | High | Running totals, moving avg |

### 3.2 Medium Priority

| Feature | Effort | Impact | Notes |
|---------|--------|--------|-------|
| GREATEST/LEAST | Low | Medium | Multi-value comparison |
| ABS/ROUND/FLOOR/CEIL | Low | Medium | Numeric processing |
| TRIM/LTRIM/RTRIM | Low | Medium | String cleanup |
| USING clause | Low | Low | Join syntax convenience |
| FIRST_VALUE/LAST_VALUE | Medium | Medium | Window analytics |
| IS DISTINCT FROM | Low | Medium | NULL-safe comparison |
| ANY/ALL | Medium | Low | Subquery comparisons |

### 3.3 Low Priority (Specialized Use)

| Feature | Effort | Impact | Notes |
|---------|--------|--------|-------|
| ROLLUP/CUBE | High | Low | Advanced aggregation |
| GROUPING SETS | High | Low | Advanced aggregation |
| SIMILAR TO | Medium | Low | Regex patterns |
| LATERAL | Medium | Low | Advanced subqueries |
| MERGE | High | Low | Upsert operations |
| Array types | High | Low | PostgreSQL specific |
| JSON functions | High | Low | Modern feature |

---

## 4. Implementation Roadmap

### Phase 1: Essential Functions (2-3 weeks)

```
Priority 1A: Type Casting
├── CAST(expr AS type)
├── Implicit type coercion rules
└── Type validation in comparisons

Priority 1B: NULL Handling
├── COALESCE(a, b, ...)
├── NULLIF(a, b)
└── IS DISTINCT FROM

Priority 1C: Core String Functions
├── SUBSTRING(str, start, length)
├── TRIM / LTRIM / RTRIM
├── REPLACE
└── POSITION / INSTR
```

### Phase 2: Date/Time Support (3-4 weeks)

```
Priority 2A: Date/Time Types
├── DATE, TIME, TIMESTAMP
├── INTERVAL
└── Literal parsing

Priority 2B: Date/Time Functions
├── EXTRACT(part FROM date)
├── CURRENT_DATE/TIME/TIMESTAMP
├── Date arithmetic (+ INTERVAL)
└── DATE_TRUNC (PostgreSQL-style)
```

### Phase 3: Window Enhancements (2-3 weeks)

```
Priority 3A: Missing Window Functions
├── LAG(expr, offset, default)
├── LEAD(expr, offset, default)
├── FIRST_VALUE / LAST_VALUE
├── NTILE(n)
└── NTH_VALUE(expr, n)

Priority 3B: Window Frames
├── ROWS BETWEEN ... AND ...
├── RANGE BETWEEN ... AND ...
├── UNBOUNDED PRECEDING/FOLLOWING
├── CURRENT ROW
└── Frame exclusion (EXCLUDE)
```

### Phase 4: Numeric Functions (1 week)

```
├── ABS, SIGN
├── ROUND, TRUNC, FLOOR, CEIL
├── POWER, SQRT, EXP, LOG
├── GREATEST, LEAST
└── MOD (function form)
```

### Phase 5: Advanced Features (Optional)

```
├── ROLLUP / CUBE / GROUPING SETS
├── GROUPING() function
├── NULLS FIRST / LAST
├── LATERAL subqueries
└── NATURAL JOIN / USING
```

---

## 5. Testing Strategy

### 5.1 Spider Benchmark Coverage

The Spider benchmark should be analyzed to identify:
1. Which missing features appear in benchmark queries
2. Frequency of each feature
3. Priority based on actual usage

### 5.2 Regression Testing

Each new feature should include:
- Parser tests (syntax accepted)
- Semantics tests (correct evaluation)
- Equivalence tests (optimizer transforms preserve semantics)
- Round-trip tests (parse → pretty-print → parse)

### 5.3 Dialect Compatibility Testing

For users of specific databases:
- Test suite per dialect
- Document unsupported constructs
- Provide dialect-specific parsing modes (future)

---

## 6. Conclusion

The sql_equiv project has solid foundations covering the core of SQL needed for query equivalence verification. The main gaps are:

1. **Type system** - CAST and date/time types
2. **Scalar functions** - COALESCE, string functions, numeric functions
3. **Window frames** - ROWS/RANGE BETWEEN specifications
4. **Convenience features** - USING clause, IS DISTINCT FROM

For the Spider benchmark and typical analytic queries, implementing Phase 1-3 would bring coverage to approximately **95%** of practical queries.

---

## Appendix: Quick Reference

### Currently Supported (Use Freely)

```sql
-- All of these work:
SELECT a, b, COUNT(*), SUM(x), AVG(y)
FROM table1 t1
JOIN table2 t2 ON t1.id = t2.fk
LEFT JOIN table3 t3 ON t2.id = t3.fk
WHERE x > 10 AND y IS NOT NULL
  AND z IN (1, 2, 3)
  AND name LIKE 'A%'
  AND EXISTS (SELECT 1 FROM other WHERE other.id = t1.id)
GROUP BY a, b
HAVING COUNT(*) > 5
ORDER BY a DESC, b ASC
LIMIT 100 OFFSET 20;

WITH RECURSIVE cte AS (
  SELECT 1 AS n
  UNION ALL
  SELECT n + 1 FROM cte WHERE n < 10
)
SELECT * FROM cte;

SELECT name, salary,
       RANK() OVER (PARTITION BY dept ORDER BY salary DESC)
FROM employees;
```

### Currently NOT Supported (Avoid or Rewrite)

```sql
-- These will fail or produce errors:

-- Type casting
SELECT CAST(x AS INTEGER)         -- Not supported
SELECT x::integer                  -- PostgreSQL syntax not supported

-- Missing functions
SELECT COALESCE(a, b, c)          -- Not supported
SELECT SUBSTRING(name, 1, 10)     -- Not supported
SELECT EXTRACT(YEAR FROM date)    -- Not supported (no DATE type)

-- Window frames
SELECT SUM(x) OVER (
  ORDER BY date
  ROWS BETWEEN 3 PRECEDING AND CURRENT ROW  -- Not supported
)

-- Advanced features
SELECT * FROM t1 NATURAL JOIN t2  -- Not supported
SELECT * FROM t1 JOIN t2 USING (id)  -- Not supported
GROUP BY ROLLUP(a, b)             -- Not supported
```
