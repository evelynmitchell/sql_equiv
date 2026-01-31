# Real-World Query Collection

Anonymized SQL queries from production systems.

## Contributing Queries

**IMPORTANT**: All queries must be anonymized before submission.

### Step 1: Anonymize

```bash
cd tools/sql_anonymizer
python sql_anonymize.py /path/to/your/queries.sql \
  -o anonymized.sql \
  -m mapping.json
```

### Step 2: Verify Anonymization

Check that no confidential information remains:
- Table names replaced with `t_N`
- Column names replaced with `c_N`
- String literals replaced with `'s_N'`
- Numeric literals randomized

### Step 3: Add Metadata

Create a header comment:
```sql
-- Source: [company type, e.g., "e-commerce", "fintech", "healthcare"]
-- Dialect: [PostgreSQL/MySQL/SQLite/SQL Server/Oracle]
-- Category: [analytics/transactional/etl/reporting]
-- Features: [list SQL features used]
-- Anonymized: yes
-- Date contributed: YYYY-MM-DD

SELECT ...
```

### Step 4: Submit

Place in appropriate subdirectory:
- `analytics/` - BI, dashboards, reporting
- `transactional/` - OLTP, CRUD operations
- `etl/` - Data pipelines, transformations
- `migrations/` - Schema changes, data migrations

## Categories

### Analytics
Complex queries for business intelligence:
- Multi-table aggregations
- Window functions for trends
- Cohort analysis
- Funnel queries

### Transactional
High-frequency OLTP patterns:
- Lookup by primary key
- Insert with returning
- Conditional updates
- Optimistic locking patterns

### ETL
Data transformation queries:
- Deduplication
- Slowly changing dimensions
- Incremental loads
- Data quality checks

## Legal

By contributing, you confirm:
1. Queries are fully anonymized
2. No proprietary business logic is disclosed
3. You have permission to share query patterns
4. Queries are licensed under project license (MIT)
