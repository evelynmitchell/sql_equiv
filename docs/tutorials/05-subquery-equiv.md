# Tutorial 5: Subquery Equivalences

**Time:** 30 minutes
**Prerequisites:** Tutorial 4

---

## Learning Objectives

By the end of this tutorial, you will:
- Classify subqueries by type (scalar, row, table, correlated)
- Transform subqueries to joins and vice versa
- Recognize when subquery flattening is safe

---

## Outline

### 1. Subquery Taxonomy (5 min)
- **Scalar subquery**: Returns single value
- **Row subquery**: Returns single row
- **Table subquery**: Returns multiple rows/columns
- **Correlated**: References outer query
- **Uncorrelated**: Independent of outer query

### 2. Scalar Subquery Equivalences (7 min)
- Scalar in SELECT: Can become LEFT JOIN
- Scalar in WHERE: Various transformations
- Error conditions: What if subquery returns multiple rows?
- NULL behavior when subquery returns empty

### 3. IN/EXISTS Transformations (8 min)
- `IN (subquery)` ↔ `EXISTS (correlated subquery)`
- `IN (subquery)` → Semi-join
- `NOT IN` ↔ `NOT EXISTS` — The NULL trap revisited
- `= ANY` and `= ALL` equivalences

### 4. Correlated Subquery Flattening (5 min)
- Decorrelation: Move correlation to join condition
- When decorrelation is possible
- Performance implications
- Preserving semantics with DISTINCT/aggregation

### 5. Nested Subqueries (5 min)
- Flattening nested IN/EXISTS
- Order of flattening matters
- When nesting cannot be flattened

---

## Exercises

1. **Classify subqueries**: Identify type for each:
   ```sql
   SELECT (SELECT MAX(x) FROM t2) FROM t1
   SELECT * FROM t1 WHERE id IN (SELECT id FROM t2 WHERE t2.x = t1.x)
   SELECT * FROM t1 WHERE EXISTS (SELECT 1 FROM t2)
   ```

2. **Transform to JOIN**:
   ```sql
   SELECT * FROM orders WHERE amount > (SELECT AVG(amount) FROM orders)
   ```

3. **NOT IN to NOT EXISTS**: Safely transform:
   ```sql
   SELECT * FROM t1 WHERE x NOT IN (SELECT y FROM t2)
   ```

4. **Decorrelate**: Remove the correlation:
   ```sql
   SELECT * FROM employees e
   WHERE salary > (SELECT AVG(salary) FROM employees WHERE dept = e.dept)
   ```

---

## Key Theorems

- `in_to_exists`: `x IN (SELECT y FROM s)` ≡ `EXISTS (SELECT 1 FROM s WHERE s.y = x)`
- `scalar_to_left_join`: Scalar subquery to LEFT JOIN (with uniqueness)
- `decorrelate_safe`: Conditions for safe decorrelation
- `not_in_not_exists_null`: NOT IN ≢ NOT EXISTS when NULLs present

---

## Pitfalls

| Transformation | Pitfall | Condition for Safety |
|----------------|---------|---------------------|
| NOT IN → NOT EXISTS | Different NULL semantics | No NULLs in subquery column |
| Scalar → JOIN | Multiple matches cause error/duplication | Subquery returns ≤ 1 row |
| IN → JOIN | Duplicates | Add DISTINCT |
| Decorrelation | Changes evaluation order | No side effects, deterministic |
| Flatten nested | Wrong scoping | Careful with aliases |

---

## Visual: Subquery Decision Tree

```
Is the subquery...
├─ In SELECT clause?
│  └─ Scalar subquery → Consider LEFT JOIN
├─ In WHERE with IN?
│  ├─ NOT IN?
│  │  └─ Check for NULLs → NOT EXISTS safer
│  └─ IN?
│     └─ Semi-join or EXISTS
├─ In WHERE with EXISTS?
│  └─ Can often stay as EXISTS (optimizer handles)
├─ In WHERE with comparison?
│  └─ Scalar → JOIN or inline (if uncorrelated)
└─ In FROM clause?
   └─ Derived table → May be flattenable
```
