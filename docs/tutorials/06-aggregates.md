# Tutorial 6: Aggregate and GROUP BY Rules

**Time:** 25 minutes
**Prerequisites:** Tutorial 5

---

## Learning Objectives

By the end of this tutorial, you will:
- Understand GROUP BY semantics precisely
- Know which aggregate transformations are valid
- Handle HAVING vs WHERE correctly

---

## Outline

### 1. GROUP BY Semantics (5 min)
- Partitioning rows into groups
- What columns can appear in SELECT with GROUP BY
- NULL as a grouping value (all NULLs in one group)
- Empty groups don't appear in output

### 2. Aggregate Function Properties (7 min)
- **NULL handling**: Most aggregates ignore NULLs
- **Empty set behavior**: COUNT=0, others=NULL
- **DISTINCT in aggregates**: COUNT(DISTINCT x)
- **Decomposability**: SUM is decomposable, AVG is not

### 3. DISTINCT ↔ GROUP BY (5 min)
- `SELECT DISTINCT a, b` ≡ `SELECT a, b GROUP BY a, b`
- When they differ: aggregates present
- Using GROUP BY for deduplication

### 4. HAVING vs WHERE (4 min)
- WHERE filters before grouping
- HAVING filters after grouping
- HAVING without GROUP BY: entire table is one group
- Moving predicates between HAVING and WHERE

### 5. Aggregate Pushdown (4 min)
- Pushing aggregation below joins
- When pushdown is safe (GROUP BY keys match join keys)
- Decomposing aggregates: SUM of SUMs, MAX of MAXs
- AVG requires SUM and COUNT separately

---

## Exercises

1. **NULL in aggregates**: What does each return?
   ```sql
   SELECT COUNT(*), COUNT(x), SUM(x), AVG(x) FROM t
   -- Given: t = [(x: 1), (x: NULL), (x: 3)]
   ```

2. **DISTINCT vs GROUP BY**: Are these equivalent?
   ```sql
   SELECT DISTINCT dept FROM employees
   SELECT dept FROM employees GROUP BY dept
   ```

3. **HAVING migration**: Can this HAVING become WHERE?
   ```sql
   SELECT dept, COUNT(*) FROM emp GROUP BY dept HAVING dept = 'Sales'
   ```

4. **Aggregate pushdown**: Is this valid?
   ```sql
   -- Original
   SELECT d.name, SUM(e.salary)
   FROM employees e JOIN departments d ON e.dept_id = d.id
   GROUP BY d.name

   -- Proposed (push SUM below JOIN)
   SELECT d.name, sub.total
   FROM (SELECT dept_id, SUM(salary) as total FROM employees GROUP BY dept_id) sub
   JOIN departments d ON sub.dept_id = d.id
   ```

---

## Key Theorems

- `distinct_group_by`: DISTINCT cols ≡ GROUP BY cols (no aggregates)
- `count_star_vs_col`: COUNT(*) ≠ COUNT(nullable_col)
- `having_to_where`: HAVING on grouping column → WHERE (safe)
- `agg_decompose_sum`: SUM over partitions = SUM of partial SUMs
- `agg_decompose_avg`: AVG requires (SUM, COUNT) decomposition

---

## Aggregate Properties Reference

| Aggregate | NULL handling | Empty set | Decomposable |
|-----------|---------------|-----------|--------------|
| COUNT(*) | Counts NULLs | 0 | SUM of counts |
| COUNT(x) | Ignores NULLs | 0 | SUM of counts |
| SUM(x) | Ignores NULLs | NULL | SUM of sums |
| AVG(x) | Ignores NULLs | NULL | No (use SUM/COUNT) |
| MIN(x) | Ignores NULLs | NULL | MIN of mins |
| MAX(x) | Ignores NULLs | NULL | MAX of maxes |
| COUNT(DISTINCT x) | Ignores NULLs | 0 | No |

---

## Pitfalls

| Transformation | Pitfall | Condition for Safety |
|----------------|---------|---------------------|
| HAVING → WHERE | HAVING on aggregate fails | Predicate uses only GROUP BY cols |
| GROUP BY removal | Changes cardinality | Only if guaranteed unique |
| Aggregate pushdown | Wrong grouping | GROUP BY matches join keys |
| AVG pushdown | Can't just push AVG | Decompose to SUM/COUNT |
| COUNT(*) → COUNT(x) | Different with NULLs | Column is NOT NULL |
