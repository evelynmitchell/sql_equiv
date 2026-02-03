# SQL Equivalence Pitfalls and Gotchas

Queries that look equivalent but aren't—and why.

---

## The Hall of Shame

These are real mistakes people make. Learn from them.

---

## 1. NULL Pitfalls

### NOT IN with NULLs

```sql
-- These are NOT equivalent when s.y can be NULL!

-- Query A: Returns rows where x matches nothing in s
SELECT * FROM t WHERE x NOT IN (SELECT y FROM s)

-- Query B: Returns rows with no matching s row
SELECT * FROM t WHERE NOT EXISTS (SELECT 1 FROM s WHERE s.y = t.x)
```

**Why?**

If s contains `(y: NULL)`:
- `NOT IN` compares x to each value. `x <> NULL` is UNKNOWN. `NOT IN` with any UNKNOWN becomes UNKNOWN. **No rows returned.**
- `NOT EXISTS` only checks if the subquery returns rows. `t.x = NULL` is UNKNOWN, so no match. **Row is returned.**

**Example:**
```
t = [(x: 1)]
s = [(y: 2), (y: NULL)]

Query A: 1 NOT IN (2, NULL)
       = NOT (1 = 2 OR 1 = NULL)
       = NOT (FALSE OR UNKNOWN)
       = NOT UNKNOWN
       = UNKNOWN → row excluded

Query B: NOT EXISTS (WHERE 2 = 1 [FALSE] OR NULL = 1 [UNKNOWN])
       = NOT EXISTS (returns nothing)
       = TRUE → row included
```

**Safe transformation:**
```sql
-- If you need NOT IN behavior but s might have NULLs:
SELECT * FROM t
WHERE NOT EXISTS (SELECT 1 FROM s WHERE s.y = t.x)
  AND NOT EXISTS (SELECT 1 FROM s WHERE s.y IS NULL)
```

---

### COUNT(*) vs COUNT(column)

```sql
-- NOT equivalent!
SELECT COUNT(*) FROM t
SELECT COUNT(x) FROM t
```

**Why?**
- `COUNT(*)` counts all rows
- `COUNT(x)` counts rows where x IS NOT NULL

**Example:**
```
t = [(x: 1), (x: NULL), (x: 3)]

COUNT(*) = 3
COUNT(x) = 2
```

---

### SUM with Empty Tables

```sql
-- NOT equivalent!
SELECT COUNT(*) FROM t
SELECT SUM(1) FROM t
```

**Why?**

When t is empty:
- `COUNT(*)` = 0
- `SUM(1)` = NULL (no rows to sum)

---

### Equality with NULL

```sql
-- NOT equivalent!
SELECT * FROM t WHERE x = x
SELECT * FROM t  -- or WHERE TRUE
```

**Why?**

If x is NULL: `NULL = NULL` is UNKNOWN, row excluded from first query.

**Safe version:**
```sql
SELECT * FROM t WHERE x IS NOT DISTINCT FROM x  -- SQL:1999
SELECT * FROM t WHERE x = x OR x IS NULL        -- Portable
```

---

## 2. JOIN Pitfalls

### LEFT vs INNER with Foreign Keys

```sql
-- Only equivalent IF foreign key constraint exists and is enforced!

-- Query A
SELECT o.*, c.name FROM orders o LEFT JOIN customers c ON o.cust_id = c.id

-- Query B
SELECT o.*, c.name FROM orders o INNER JOIN customers c ON o.cust_id = c.id
```

**Why?**

LEFT JOIN keeps orders with no matching customer (cust_id = NULL or invalid).
INNER JOIN excludes them.

**Safe only when:**
- `orders.cust_id` has FOREIGN KEY to `customers.id`
- `orders.cust_id` is NOT NULL

---

### JOIN vs IN/EXISTS (Duplicates)

```sql
-- NOT equivalent if p.id has duplicates!

-- Query A (correct for "orders from premium customers")
SELECT * FROM orders WHERE customer_id IN (SELECT id FROM premium)

-- Query B (may return duplicate orders!)
SELECT o.* FROM orders o JOIN premium p ON o.customer_id = p.id
```

**Why?**

If premium has duplicates of id=100:
- IN: Returns each order once (is 100 in the list? yes/no)
- JOIN: Returns each order multiple times (once per matching premium row)

**Safe version:**
```sql
SELECT DISTINCT o.* FROM orders o JOIN premium p ON o.customer_id = p.id
-- or --
SELECT o.* FROM orders o JOIN (SELECT DISTINCT id FROM premium) p ON ...
```

---

### CROSS JOIN Explosion

```sql
-- These produce vastly different row counts!

-- Query A: All combinations
SELECT * FROM t1 CROSS JOIN t2

-- Query B: Matching rows only
SELECT * FROM t1 JOIN t2 ON t1.id = t2.id
```

This seems obvious, but people sometimes accidentally write CROSS JOIN when they mean INNER JOIN (forgetting the ON clause in some SQL dialects).

---

## 3. Aggregate Pitfalls

### GROUP BY Changes Row Identity

```sql
-- NOT equivalent!
SELECT * FROM t GROUP BY x
SELECT DISTINCT x FROM t
```

**Why?**

`SELECT *` with `GROUP BY x` is actually invalid in standard SQL (what value of other columns to show?). Some databases allow it but pick arbitrary values.

**Also not equivalent:**
```sql
SELECT x, y FROM t GROUP BY x
SELECT DISTINCT x, y FROM t
```

First groups by x only (y is arbitrary within group).
Second removes duplicate (x, y) pairs.

---

### HAVING vs WHERE Timing

```sql
-- NOT equivalent!

-- Query A: Filter before grouping
SELECT dept, COUNT(*) FROM emp WHERE salary > 50000 GROUP BY dept

-- Query B: Filter after grouping
SELECT dept, COUNT(*) FROM emp GROUP BY dept HAVING salary > 50000
```

Query B is actually **invalid SQL**—HAVING can only reference aggregate expressions or GROUP BY columns, not individual row columns.

But this IS a valid gotcha:

```sql
-- NOT equivalent!

-- Query A: Count employees with salary > 50000
SELECT dept, COUNT(*) FROM emp WHERE salary > 50000 GROUP BY dept

-- Query B: Count all employees, keep depts where someone has > 50000
SELECT dept, COUNT(*) FROM emp GROUP BY dept HAVING MAX(salary) > 50000
```

---

### AVG vs SUM/COUNT

```sql
-- NOT equivalent due to NULL handling!

SELECT AVG(x) FROM t
SELECT SUM(x) / COUNT(*) FROM t  -- WRONG
SELECT SUM(x) / COUNT(x) FROM t  -- Correct
```

**Why?**

AVG ignores NULL values. `SUM(x) / COUNT(*)` divides by total rows including NULLs.

**Example:**
```
t = [(x: 10), (x: NULL), (x: 20)]

AVG(x) = (10 + 20) / 2 = 15
SUM(x) / COUNT(*) = 30 / 3 = 10  -- Wrong!
SUM(x) / COUNT(x) = 30 / 2 = 15  -- Correct
```

---

## 4. Subquery Pitfalls

### Scalar Subquery Returns Multiple Rows

```sql
-- This can FAIL at runtime!
SELECT * FROM t WHERE x = (SELECT y FROM s)
```

If the subquery returns more than one row, this is an error in most databases.

**Safe version:**
```sql
SELECT * FROM t WHERE x IN (SELECT y FROM s)  -- Multiple values OK
SELECT * FROM t WHERE x = (SELECT MAX(y) FROM s)  -- Guaranteed single value
```

---

### Correlated vs Uncorrelated

```sql
-- NOT equivalent in general!

-- Uncorrelated: Subquery runs once
SELECT * FROM t WHERE x > (SELECT AVG(y) FROM s)

-- Correlated: Subquery runs per row of t
SELECT * FROM t WHERE x > (SELECT AVG(y) FROM s WHERE s.z = t.z)
```

If someone "optimizes" by pulling out the subquery:

```sql
-- WRONG if original was correlated!
SELECT * FROM t, (SELECT AVG(y) as avg_y FROM s) sub WHERE x > sub.avg_y
```

This loses the correlation with t.z.

---

## 5. ORDER BY Pitfalls

### ORDER BY Without LIMIT

```sql
-- NOT equivalent!
SELECT * FROM (SELECT * FROM t ORDER BY x) sub
SELECT * FROM t ORDER BY x
```

**Why?**

The ORDER BY in the subquery may be **optimized away** by some databases because subquery results have no defined order.

**Safe version:**
```sql
SELECT * FROM (SELECT * FROM t ORDER BY x LIMIT 999999999) sub  -- Keeps order
-- or just --
SELECT * FROM t ORDER BY x  -- Order at the outermost level
```

---

### ORDER BY Column Aliases

```sql
-- Behavior varies by database!
SELECT x + 1 as y FROM t ORDER BY y
SELECT x + 1 as y FROM t ORDER BY x + 1
```

Some databases allow ORDER BY alias, others don't. When moving between systems, this can break.

---

## 6. Set Operation Pitfalls

### UNION vs UNION ALL

```sql
-- NOT equivalent!
SELECT x FROM t1 UNION SELECT x FROM t2
SELECT x FROM t1 UNION ALL SELECT x FROM t2
```

UNION removes duplicates (across both sets).
UNION ALL keeps all rows.

**Performance note:** UNION ALL is faster (no deduplication). Only use UNION when you need deduplication.

---

### EXCEPT NULL Behavior

```sql
-- Tricky NULL semantics!
SELECT x FROM t1 EXCEPT SELECT x FROM t2
```

This removes from t1 any rows that appear in t2. But NULL behavior varies:
- Standard SQL: NULL = NULL is UNKNOWN, so NULLs might not be removed
- Some databases: Treat NULLs as equal for EXCEPT

Test your database's behavior!

---

## 7. Type Coercion Pitfalls

### String vs Number Comparison

```sql
-- NOT equivalent across databases!
SELECT * FROM t WHERE x = 123
SELECT * FROM t WHERE x = '123'
```

If x is VARCHAR:
- Some databases: `123` is coerced to `'123'`, matches
- Some databases: `'123'` is coerced to `123`, matches
- Some databases: Type error

If x is INT:
- Similar issues with `'123'`

**Safe version:** Match types explicitly:
```sql
SELECT * FROM t WHERE x = CAST(123 AS VARCHAR)
SELECT * FROM t WHERE CAST(x AS INT) = 123
```

---

### Date String Formats

```sql
-- NOT equivalent across databases!
SELECT * FROM t WHERE date_col > '2024-01-15'
SELECT * FROM t WHERE date_col > '01/15/2024'
SELECT * FROM t WHERE date_col > '15-Jan-2024'
```

Date parsing varies wildly. Use explicit conversion:

```sql
SELECT * FROM t WHERE date_col > DATE '2024-01-15'  -- Standard SQL
SELECT * FROM t WHERE date_col > TO_DATE('2024-01-15', 'YYYY-MM-DD')  -- Oracle
```

---

## 8. Dialect-Specific Pitfalls

### LIMIT Syntax

```sql
-- MySQL/PostgreSQL/SQLite
SELECT * FROM t LIMIT 10 OFFSET 5

-- SQL Server
SELECT TOP 10 * FROM t  -- No OFFSET in TOP

-- Oracle (old)
SELECT * FROM t WHERE ROWNUM <= 10

-- Standard SQL
SELECT * FROM t FETCH FIRST 10 ROWS ONLY OFFSET 5 ROWS
```

These behave similarly but have subtle differences with ORDER BY interaction.

---

### Boolean Handling

```sql
-- PostgreSQL: TRUE/FALSE literals
SELECT * FROM t WHERE flag = TRUE

-- MySQL: TRUE = 1, FALSE = 0
SELECT * FROM t WHERE flag = 1

-- SQL Server: No boolean type
SELECT * FROM t WHERE flag = 'Y'  -- Common convention
```

---

### Empty String vs NULL

```sql
-- Oracle: Empty string '' is NULL!
SELECT * FROM t WHERE x = ''  -- Never matches in Oracle
SELECT * FROM t WHERE x IS NULL  -- Use this instead

-- Other databases: '' is distinct from NULL
```

---

## Quick Reference: What Breaks Equivalence

| Factor | Can Break Equivalence? | Example |
|--------|----------------------|---------|
| NULL values | ✓ | `NOT IN`, `= NULL`, aggregates |
| Duplicate rows | ✓ | JOIN vs IN, DISTINCT |
| Empty tables | ✓ | COUNT vs SUM, AVG |
| Row order | ✓ | Subquery ORDER BY |
| Column order | ✓ | SELECT a, b vs SELECT b, a |
| Type coercion | ✓ | String/number comparison |
| Constraints | ✓ | FK presence, NOT NULL |
| Database dialect | ✓ | Date formats, LIMIT syntax |

---

## 9. Formal Verification Pitfalls

### COALESCE(NULL, NULL) and Typed NULLs

The axiom `coalesce_null_left` claims:

```
COALESCE(NULL, x) = x   -- for all x
```

This is **unsound** when `x` is itself a NULL value (`some (.null _)` in our
representation). The actual `evalFunc` implementation uses `List.find?` to
locate the first non-null argument, and when both arguments are null, `find?`
returns `none`. But `none` is not the same as `some (.null t)` in Lean's type
system:

```
evalFunc "COALESCE" [some (.null t), some (.null t')]
  = [some (.null t), some (.null t')].find? (fun v => !isNullValue v) |>.join
  = none.join       -- find? found no non-null value
  = none            -- actual result

-- But the axiom claims the result is:
  = some (.null t') -- WRONG
```

**Why this matters:** `none` (no value produced) and `some (.null _)` (a typed
SQL NULL was produced) are distinct in our semantic model. Any proof chain that
applies `coalesce_null_left` with a null second argument is technically unsound
-- it could derive `False`.

**The corrected version** is `coalesce_null_left_nonnull`, which adds the
precondition `isNullValue v = false`:

```lean
theorem coalesce_null_left_nonnull (t : Option SqlType) (v : Option Value)
    (hv : isNullValue v = false) :
    evalFunc "COALESCE" [some (.null t), v] = v
```

**Broader lesson:** The distinction between `none` and `some (.null _)` is a
recurring source of subtlety in formalized SQL semantics. `none` means "evaluation
failed or produced no value" while `some (.null _)` means "evaluation succeeded
and produced a SQL NULL." Any axiom quantifying over `Option Value` should be
checked against both cases.

---

## Testing Checklist

Before claiming two queries are equivalent, test with:

- [ ] NULL values in every column
- [ ] Empty tables
- [ ] Duplicate rows (where allowed)
- [ ] Boundary values (0, -1, MAX_INT)
- [ ] Empty strings (especially Oracle!)
- [ ] Tables with one row
- [ ] Tables with many rows
- [ ] Cross-database if applicable
