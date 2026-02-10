# Tutorial 6: Aggregate and GROUP BY Rules

**Time:** 25 minutes
**Prerequisites:** Tutorial 5

---

## What You'll Learn

- How GROUP BY semantics work precisely and how NULLs interact with grouping
- Which aggregate transformations preserve equivalence
- When HAVING and WHERE are interchangeable and when they aren't
- How aggregate pushdown through joins works (and when it fails)

---

## GROUP BY Semantics

GROUP BY partitions rows into groups based on one or more columns, then applies aggregate functions to each group.

### The Grouping Process

```sql
SELECT dept, COUNT(*), AVG(salary)
FROM employees
GROUP BY dept
```

Conceptually:
1. **Partition**: Split rows by `dept` values
2. **Aggregate**: Apply COUNT(*) and AVG(salary) to each partition
3. **Output**: One row per group

### What Can Appear in SELECT With GROUP BY?

Only two things can appear in the SELECT list:
1. **GROUP BY columns** (or expressions thereof)
2. **Aggregate functions** applied to any column

```sql
-- VALID: dept is in GROUP BY, COUNT(*) is aggregate
SELECT dept, COUNT(*) FROM employees GROUP BY dept

-- INVALID in standard SQL: name is not in GROUP BY or an aggregate
SELECT dept, name, COUNT(*) FROM employees GROUP BY dept
-- Some databases (MySQL) allow this, picking an arbitrary name from the group
```

### NULL as a Grouping Value

All NULLs are placed in **one group**, even though `NULL = NULL` is UNKNOWN elsewhere:

```sql
-- employees: [(dept: 'Sales'), (dept: NULL), (dept: NULL), (dept: 'Eng')]
SELECT dept, COUNT(*) FROM employees GROUP BY dept

-- Result:
-- dept    | count
-- --------|------
-- Sales   | 1
-- NULL    | 2     ← Both NULLs in one group
-- Eng     | 1
```

This is an intentional inconsistency in SQL: GROUP BY treats NULLs as equal for partitioning, even though comparisons don't.

### Empty Groups Don't Appear

If no rows match a particular group value, that group simply doesn't appear in the output. GROUP BY only creates groups from values that actually exist in the data.

---

## Aggregate Function Properties

### NULL Handling

Most aggregates skip NULL values. This is a critical source of non-obvious behavior:

```sql
-- Given: t = [(x: 10), (x: NULL), (x: 20), (x: NULL)]

SELECT COUNT(*)  FROM t    -- 4 (counts all rows, including NULLs)
SELECT COUNT(x)  FROM t    -- 2 (skips NULLs)
SELECT SUM(x)    FROM t    -- 30 (10 + 20, skips NULLs)
SELECT AVG(x)    FROM t    -- 15 (30 / 2, not 30 / 4!)
SELECT MIN(x)    FROM t    -- 10
SELECT MAX(x)    FROM t    -- 20
```

### Empty Set Behavior

When there are no rows (or no non-NULL values):

```sql
-- Empty table:
SELECT COUNT(*)  FROM empty_t    -- 0
SELECT COUNT(x)  FROM empty_t    -- 0
SELECT SUM(x)    FROM empty_t    -- NULL (not 0!)
SELECT AVG(x)    FROM empty_t    -- NULL
SELECT MIN(x)    FROM empty_t    -- NULL
SELECT MAX(x)    FROM empty_t    -- NULL
```

This means `COUNT(*) = 0` is NOT the same as `SUM(1) = 0`:

```lean
-- count_star_nonneg: COUNT(*) >= 0
-- count_star_empty: COUNT(*) = 0 on empty table
-- count_star_singleton: COUNT(*) = 1 on single-row table
```

Note: The codebase lemma `sum_empty` proves `[].foldl (+) 0 = 0`, which is about the underlying list fold helper, not the SQL-level SUM aggregate. In SQL, `SUM` on an empty table returns NULL. The SQL aggregate layer wraps the fold and converts empty-input cases to NULL.

### DISTINCT in Aggregates

```sql
-- Given: t = [(x: 1), (x: 2), (x: 1), (x: NULL)]

SELECT COUNT(x)          FROM t    -- 3 (skips NULL)
SELECT COUNT(DISTINCT x) FROM t    -- 2 (1 and 2, skips NULL)
```

```lean
-- count_distinct_le_count: COUNT(DISTINCT x) ≤ COUNT(x)
-- distinct_idempotent: DISTINCT(DISTINCT(xs)) = DISTINCT(xs)
```

### Decomposability

Some aggregates can be decomposed across partitions. This matters for parallel execution and aggregate pushdown through joins.

| Aggregate | Decomposable? | Decomposition |
|-----------|---------------|---------------|
| COUNT(*) | Yes | SUM of partial counts |
| COUNT(x) | Yes | SUM of partial counts |
| SUM(x) | Yes | SUM of partial sums |
| MIN(x) | Yes | MIN of partial mins |
| MAX(x) | Yes | MAX of partial maxes |
| AVG(x) | **No** | Requires SUM + COUNT separately |
| COUNT(DISTINCT x) | **No** | Cannot decompose (duplicates across partitions) |

```lean
-- sum_singleton: SUM([n]) = n
-- sum_add_zero: SUM(xs ++ [0]) = SUM(xs)
-- min_singleton: MIN([n]) = n
-- max_singleton: MAX([n]) = n
-- min_le_elem: MIN(xs) ≤ any element in xs
-- max_ge_elem: MAX(xs) ≥ any element in xs
```

---

## DISTINCT ↔ GROUP BY

### The Core Equivalence

```sql
-- These ARE equivalent (no aggregates):
SELECT DISTINCT a, b FROM t
SELECT a, b FROM t GROUP BY a, b
```

Both remove duplicate `(a, b)` pairs. Without aggregate functions, GROUP BY acts exactly like DISTINCT.

### When They Differ

With aggregates present, they are very different:

```sql
-- NOT equivalent!
SELECT DISTINCT dept, COUNT(*) FROM employees GROUP BY dept
SELECT dept, COUNT(*) FROM employees GROUP BY dept
```

The first adds a redundant DISTINCT (each dept already appears once after GROUP BY). The second is the standard form. In this case they happen to produce the same result, but DISTINCT is misleading.

```sql
-- Genuinely different:
SELECT DISTINCT dept FROM employees
SELECT dept, COUNT(*) FROM employees GROUP BY dept
```

First returns just department names. Second returns department names WITH counts.

---

## HAVING vs WHERE

### WHERE Filters Before Grouping

```sql
SELECT dept, COUNT(*)
FROM employees
WHERE salary > 50000
GROUP BY dept
```

1. Filter: Keep only rows with salary > 50000
2. Group: Partition remaining rows by dept
3. Aggregate: Count rows in each group

### HAVING Filters After Grouping

```sql
SELECT dept, COUNT(*)
FROM employees
GROUP BY dept
HAVING COUNT(*) > 5
```

1. Group: Partition ALL rows by dept
2. Aggregate: Count rows in each group
3. Filter: Keep only groups with count > 5

### Moving Predicates Between HAVING and WHERE

**Safe**: HAVING predicate on a GROUP BY column can move to WHERE:

```sql
-- These ARE equivalent:
SELECT dept, COUNT(*) FROM emp GROUP BY dept HAVING dept = 'Sales'
SELECT dept, COUNT(*) FROM emp WHERE dept = 'Sales' GROUP BY dept
```

The WHERE version is more efficient—it filters before grouping, reducing the amount of data to process.

**Unsafe**: HAVING predicate on an aggregate CANNOT move to WHERE:

```sql
-- NOT equivalent (and the second is INVALID):
SELECT dept, COUNT(*) FROM emp GROUP BY dept HAVING COUNT(*) > 5
SELECT dept, COUNT(*) FROM emp WHERE COUNT(*) > 5 GROUP BY dept  -- ERROR!
```

WHERE runs before aggregation, so aggregate functions aren't available yet.

### HAVING Without GROUP BY

```sql
SELECT COUNT(*) FROM employees HAVING COUNT(*) > 10
```

When HAVING is used without GROUP BY, the entire table is treated as one group. This returns the count if it's > 10, or no rows otherwise.

---

## Aggregate Pushdown

Aggregate pushdown is an optimization that moves aggregation below joins. This can dramatically reduce the amount of data flowing through the join.

### When Pushdown Is Safe

```sql
-- Original: Aggregate after JOIN
SELECT d.name, SUM(e.salary) as total_salary
FROM employees e
JOIN departments d ON e.dept_id = d.id
GROUP BY d.name

-- Pushed down: Aggregate before JOIN
SELECT d.name, sub.total_salary
FROM (
  SELECT dept_id, SUM(salary) as total_salary
  FROM employees
  GROUP BY dept_id
) sub
JOIN departments d ON sub.dept_id = d.id
```

This is safe when:
1. The GROUP BY keys include the join key (`dept_id`)
2. The aggregate is decomposable (SUM is)
3. The join doesn't create duplicates

### Why AVG Is Not Decomposable

Unlike SUM, you cannot combine AVGs from partitions to get the overall AVG:

```
AVG of partitions != AVG of whole

Example:
  Partition 1: [10, 20] -> AVG = 15
  Partition 2: [30]     -> AVG = 30

  AVG of averages: (15 + 30) / 2 = 22.5
  True AVG: (10 + 20 + 30) / 3 = 20     -- Different!
```

The error is that AVG-of-AVGs doesn't weight by partition size.

### AVG Pushdown: The Safe Way

To push AVG below a join, decompose it into SUM and COUNT (which are both decomposable):

```sql
-- Original
SELECT d.name, AVG(e.salary)
FROM employees e JOIN departments d ON e.dept_id = d.id
GROUP BY d.name

-- Correct pushdown: decompose AVG into SUM/COUNT
SELECT d.name, sub.total_salary / sub.emp_count as avg_salary
FROM (
  SELECT dept_id, SUM(salary) as total_salary, COUNT(salary) as emp_count
  FROM employees
  GROUP BY dept_id
) sub
JOIN departments d ON sub.dept_id = d.id
```

Note: In this specific example (1-to-many join where each employee belongs to exactly one department), pushing a bare AVG also happens to give the correct result because the GROUP BY key (`dept_id`) is the same as the join key. But the SUM/COUNT decomposition is the generally safe pattern and works regardless of join cardinality.

### When Pushdown Fails: Duplicating Joins

If the join can produce duplicates, pushing aggregation below it changes the count:

```sql
-- If an employee can belong to multiple departments (many-to-many):
SELECT d.name, COUNT(*)
FROM employees e
JOIN dept_assignments da ON e.id = da.emp_id
JOIN departments d ON da.dept_id = d.id
GROUP BY d.name

-- Pushing COUNT(*) below the join would count employees, not assignments
```

---

## Hands-On Exercises

### Exercise 1: NULL in Aggregates

What does each expression return?

```sql
-- Given: t = [(x: 1), (x: NULL), (x: 3)]

SELECT COUNT(*), COUNT(x), SUM(x), AVG(x) FROM t
```

<details>
<summary>Answer</summary>

```
COUNT(*) = 3    (counts all rows)
COUNT(x) = 2    (skips NULLs: only 1 and 3)
SUM(x)   = 4    (1 + 3, skips NULLs)
AVG(x)   = 2    (4 / 2, divides by non-NULL count)
```

Common mistake: thinking AVG(x) = 4/3 ≈ 1.33. AVG divides by COUNT(x), not COUNT(*).

</details>

### Exercise 2: DISTINCT vs GROUP BY

Are these equivalent?

```sql
-- Query A
SELECT DISTINCT dept FROM employees

-- Query B
SELECT dept FROM employees GROUP BY dept
```

<details>
<summary>Answer</summary>

**Yes, equivalent.** Both return one row per unique dept value (including one row for NULL if any employees have no department).

Without aggregate functions, GROUP BY and DISTINCT produce the same result. This equivalence is not yet a named theorem in the codebase, but follows from the definitions of DISTINCT (deduplication) and GROUP BY without aggregates (partitioning that collapses to unique keys).

</details>

### Exercise 3: HAVING Migration

Can this HAVING become WHERE?

```sql
SELECT dept, COUNT(*) FROM emp GROUP BY dept HAVING dept = 'Sales'
```

<details>
<summary>Answer</summary>

**Yes.** The HAVING predicate `dept = 'Sales'` only references a GROUP BY column, not an aggregate. It can safely move to WHERE:

```sql
SELECT dept, COUNT(*) FROM emp WHERE dept = 'Sales' GROUP BY dept
```

The WHERE version is more efficient: it filters before grouping, so the database only groups rows from the Sales department.

</details>

### Exercise 4: Aggregate Pushdown

Is this pushdown valid?

```sql
-- Original
SELECT d.name, SUM(e.salary)
FROM employees e JOIN departments d ON e.dept_id = d.id
GROUP BY d.name

-- Proposed pushdown
SELECT d.name, sub.total
FROM (SELECT dept_id, SUM(salary) as total FROM employees GROUP BY dept_id) sub
JOIN departments d ON sub.dept_id = d.id
```

<details>
<summary>Answer</summary>

**Yes, this is valid** because:

1. **GROUP BY key includes join key**: We GROUP BY `dept_id`, which is the join key
2. **SUM is decomposable**: SUM of groups = SUM of whole (when partitioned by the same key)
3. **1-to-many relationship**: Each employee belongs to one department, so the join doesn't create duplicates

The pushdown reduces the number of rows flowing through the join from (number of employees) to (number of departments), which can be a significant performance improvement.

</details>

---

## Key Theorems Reference

| Theorem | Statement | Used For |
|---------|-----------|----------|
| `count_star_nonneg` | `COUNT(*) ≥ 0` | Count is non-negative |
| `count_star_empty` | `COUNT(*) = 0` on empty | Empty table behavior |
| `count_star_singleton` | `COUNT(*) = 1` on single row | Singleton behavior |
| `count_after_filter_le` | `COUNT(*) WHERE p ≤ COUNT(*)` | Filter reduces count |
| `sum_empty` | `[].foldl (+) 0 = 0` (list fold, not SQL SUM) | Empty list fold |
| `sum_singleton` | `SUM([n]) = n` | Singleton sum |
| `sum_add_zero` | `SUM(xs ++ [0]) = SUM(xs)` | Zero identity |
| `min_singleton` | `MIN([n]) = n` | Singleton min |
| `max_singleton` | `MAX([n]) = n` | Singleton max |
| `min_le_elem` | `MIN(xs) ≤ n` for n in xs | Min bound |
| `max_ge_elem` | `MAX(xs) ≥ n` for n in xs | Max bound |
| `count_distinct_le_count` | `COUNT(DISTINCT x) ≤ COUNT(x)` | Distinct reduces count |
| `distinct_idempotent` | `DISTINCT(DISTINCT(xs)) = DISTINCT(xs)` | Idempotence |

---

## Aggregate Properties Quick Reference

| Aggregate | NULL handling | Empty set | Decomposable | Commutative |
|-----------|--------------|-----------|--------------|-------------|
| COUNT(*) | Counts NULLs | 0 | Yes (SUM of counts) | N/A |
| COUNT(x) | Skips NULLs | 0 | Yes (SUM of counts) | N/A |
| SUM(x) | Skips NULLs | NULL | Yes (SUM of sums) | Yes |
| AVG(x) | Skips NULLs | NULL | **No** (use SUM/COUNT) | Yes |
| MIN(x) | Skips NULLs | NULL | Yes (MIN of mins) | Yes |
| MAX(x) | Skips NULLs | NULL | Yes (MAX of maxes) | Yes |
| COUNT(DISTINCT x) | Skips NULLs | 0 | **No** | N/A |

---

## Pitfalls

| Transformation | Pitfall | Condition for Safety |
|----------------|---------|---------------------|
| HAVING → WHERE | HAVING on aggregate fails | Predicate uses only GROUP BY cols |
| GROUP BY removal | Changes cardinality | Only if guaranteed unique |
| Aggregate pushdown | Wrong grouping | GROUP BY matches join keys |
| AVG pushdown | Can't just push AVG | Decompose to SUM/COUNT |
| COUNT(*) → COUNT(x) | Different with NULLs | Column is NOT NULL |
| SUM(x) / COUNT(*) | Wrong AVG | Use SUM(x) / COUNT(x) |
| GROUP BY + SELECT * | Arbitrary non-grouped cols | Non-standard SQL behavior |

---

## Next Steps

- [Tutorial 7: Formal Methods Intro](07-formal-methods-intro.md) - How equivalence proofs work
- [Tutorial 8: Reading and Writing Proofs in Lean](08-lean-proofs.md) - Hands-on with Lean proofs
- [Pitfalls Guide](reference/pitfalls.md) - Complete reference of aggregate traps
- [Equivalence Catalog](reference/equivalence-catalog.md) - All proven aggregate equivalences
