# Tutorial 5: Subquery Equivalences

**Time:** 30 minutes
**Prerequisites:** Tutorial 4

---

## What You'll Learn

- How to classify subqueries by type and behavior
- Which subquery-to-join transformations preserve equivalence
- When subquery flattening is safe and when it isn't
- How correlated and uncorrelated subqueries differ semantically

---

## Subquery Taxonomy

Not all subqueries are equal. Understanding their type is the first step to safe transformation.

### By Return Shape

| Type | Returns | Example |
|------|---------|---------|
| **Scalar** | Single value | `(SELECT MAX(x) FROM t)` |
| **Row** | Single row | `(SELECT x, y FROM t WHERE id = 1)` |
| **Table** | Multiple rows/columns | `(SELECT id FROM t WHERE x > 5)` |

### By Correlation

| Type | Depends on Outer Query? | Evaluation |
|------|------------------------|------------|
| **Uncorrelated** | No | Runs once, result reused |
| **Correlated** | Yes (references outer columns) | Runs once per outer row |

```lean
-- uncorrelated_subquery_independent: Uncorrelated subquery result is independent of outer row
-- correlated_subquery_uses_context: Correlated subquery uses outer row context
```

### By Usage Context

```
Is the subquery...
├─ In SELECT clause?
│  └─ Scalar subquery → Consider LEFT JOIN
├─ In WHERE with IN?
│  ├─ NOT IN?
│  │  └─ Check for NULLs → NOT EXISTS is safer
│  └─ IN?
│     └─ Semi-join or EXISTS
├─ In WHERE with EXISTS?
│  └─ Can often stay as EXISTS (optimizer handles it)
├─ In WHERE with comparison?
│  └─ Scalar → JOIN or inline (if uncorrelated)
└─ In FROM clause?
   └─ Derived table → May be flattenable
```

---

## Scalar Subquery Equivalences

A scalar subquery returns exactly one value. It can appear almost anywhere a value is allowed.

### Basic Behavior

```sql
-- Scalar subquery returns a single value
SELECT name, (SELECT MAX(salary) FROM employees) as max_sal
FROM departments
```

What happens in edge cases?

```lean
-- scalar_subquery_empty_null: Scalar subquery on empty result returns NULL
-- scalar_subquery_is_first: Scalar subquery returns first column of first row
-- subquery_limit_one: Subquery with LIMIT 1 returns at most 1 row
```

If the subquery returns **no rows**, the scalar value is NULL.
If the subquery returns **more than one row**, it's a runtime error in most databases.

### Scalar in SELECT → LEFT JOIN

```sql
-- Original: Scalar subquery in SELECT
SELECT
  o.id,
  o.total,
  (SELECT c.name FROM customers c WHERE c.id = o.customer_id) as cust_name
FROM orders o

-- Equivalent: LEFT JOIN (requires customers.id is unique)
SELECT o.id, o.total, c.name as cust_name
FROM orders o
LEFT JOIN customers c ON c.id = o.customer_id
```

**Why LEFT JOIN, not INNER?** Because the scalar subquery returns NULL when no match is found. LEFT JOIN preserves this behavior—unmatched orders get `cust_name = NULL`.

**Why uniqueness matters**: If `customers.id` isn't unique, the JOIN could produce duplicate rows per order, which the scalar subquery wouldn't.

### Scalar in WHERE → Various Transformations

```sql
-- Original: Scalar subquery in WHERE
SELECT * FROM orders WHERE amount > (SELECT AVG(amount) FROM orders)

-- Equivalent: Cross join with derived table (uncorrelated subquery)
SELECT o.*
FROM orders o, (SELECT AVG(amount) as avg_amt FROM orders) sub
WHERE o.amount > sub.avg_amt
```

This works because the subquery is uncorrelated—it computes the same value regardless of the outer row.

---

## IN and EXISTS Transformations

### IN Subquery ↔ EXISTS

These are among the most important equivalences:

```sql
-- IN subquery
SELECT * FROM orders o
WHERE o.customer_id IN (SELECT c.id FROM customers c WHERE c.status = 'VIP')

-- Equivalent EXISTS
SELECT * FROM orders o
WHERE EXISTS (
  SELECT 1 FROM customers c
  WHERE c.id = o.customer_id AND c.status = 'VIP'
)
```

```lean
-- in_subquery_as_exists:
--   x IN (SELECT y FROM s) ≡ EXISTS (SELECT 1 FROM s WHERE y = x)
```

Both ask the same question: "Is there a matching VIP customer for this order?" The IN version compares the result set; the EXISTS version checks for any matching row.

### NOT IN ↔ NOT EXISTS (The NULL Trap, Revisited)

```sql
-- NOT IN
SELECT * FROM customers
WHERE id NOT IN (SELECT customer_id FROM orders)

-- NOT EXISTS
SELECT * FROM customers c
WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.id)
```

```lean
-- not_in_subquery_as_not_exists:
--   x NOT IN (SELECT y FROM s) ≡ NOT EXISTS (SELECT 1 FROM s WHERE y = x)
```

**Critical caveat**: This equivalence only holds when the subquery column has **no NULLs**. As covered in [Tutorial 3](03-null-logic.md), NOT IN with NULLs in the subquery result can return no rows at all.

```lean
-- not_exists_empty_true: NOT EXISTS (empty) = TRUE
-- not_exists_nonempty_false: NOT EXISTS (non-empty) = FALSE
-- not_not_exists: NOT (NOT EXISTS) = EXISTS
```

### IN with Empty Subquery

```lean
-- in_empty_subquery_false: x IN (empty subquery) = FALSE
-- not_in_empty_subquery_true: x NOT IN (empty subquery) = TRUE
```

If the subquery returns no rows:
- `x IN (empty)` is always FALSE
- `x NOT IN (empty)` is always TRUE

### IN with Singleton

```lean
-- in_singleton_subquery: x IN (single value v) = (x = v)
```

When the subquery returns exactly one value, IN degenerates to simple equality.

---

## EXISTS Properties

EXISTS is a boolean test: does the subquery produce any rows?

```lean
-- exists_empty_false: EXISTS (empty) = FALSE
-- exists_nonempty_true: EXISTS (non-empty) = TRUE
-- not_exists_empty_true: NOT EXISTS (empty) = TRUE
-- not_exists_nonempty_false: NOT EXISTS (non-empty) = FALSE
```

### EXISTS as COUNT

```lean
-- exists_as_count_gt_zero: EXISTS ≡ (COUNT(*) > 0)
-- not_exists_as_count_eq_zero: NOT EXISTS ≡ (COUNT(*) = 0)
```

This means:

```sql
-- Equivalent:
WHERE EXISTS (SELECT 1 FROM orders WHERE customer_id = 5)
WHERE (SELECT COUNT(*) FROM orders WHERE customer_id = 5) > 0
```

In practice, EXISTS is preferred because the database can stop as soon as it finds one row, while COUNT(*) must scan all matching rows.

### EXISTS is Monotonic

```lean
-- exists_monotonic: EXISTS is monotonic (superset preserves TRUE)
```

If EXISTS is TRUE for a set S, it's TRUE for any superset of S. Adding more rows to a table can never make EXISTS go from TRUE to FALSE.

### Subquery WHERE TRUE and FALSE

```lean
-- subquery_where_true: Adding WHERE TRUE doesn't change subquery result
-- subquery_where_false: Adding WHERE FALSE makes subquery empty
```

---

## Correlated Subquery Flattening

Correlated subqueries reference the outer query, making them conceptually execute once per outer row.

### When Flattening Works

```sql
-- Correlated subquery
SELECT * FROM employees e
WHERE salary > (SELECT AVG(salary) FROM employees WHERE dept = e.dept)

-- CANNOT simply flatten to:
SELECT * FROM employees e, (SELECT dept, AVG(salary) as avg_sal FROM employees GROUP BY dept) sub
WHERE e.dept = sub.dept AND e.salary > sub.avg_sal
```

Wait—this one actually CAN be flattened! The correlation `e.dept` maps cleanly to a GROUP BY + JOIN.

But be careful:

```sql
-- Correlated subquery with side effects or non-determinism
SELECT * FROM t1
WHERE x > (SELECT RANDOM() FROM t2 WHERE t2.id = t1.id)

-- CANNOT flatten: RANDOM() must be evaluated per outer row
```

### Decorrelation Steps

1. **Identify the correlation**: What outer column does the subquery reference?
2. **Can it become a join condition?** If the correlation is a simple equality, yes
3. **Does the subquery aggregate?** If so, you need GROUP BY in the derived table
4. **Is there a uniqueness guarantee?** Scalar subqueries must return ≤ 1 row

```lean
-- uncorrelated_subquery_independent: Uncorrelated subqueries produce the same result regardless of outer row
-- correlated_subquery_uses_context: Correlated subqueries depend on the outer row
```

---

## Subquery Unnesting

Subquery unnesting (also called "subquery flattening") is a key optimizer transformation.

### IN → Semi-Join

```sql
-- Original
SELECT * FROM orders
WHERE customer_id IN (SELECT id FROM vip_customers)

-- Unnested to semi-join
SELECT DISTINCT o.*
FROM orders o JOIN vip_customers v ON o.customer_id = v.id
```

```lean
-- in_subquery_unnest_to_join: IN subquery becomes semi-join with DISTINCT
-- in_subquery_implies_join_match: IN true → join match exists
-- join_match_implies_in_subquery: join match → IN true
```

### NOT IN → Anti-Join

```sql
-- Original
SELECT * FROM customers
WHERE id NOT IN (SELECT customer_id FROM orders)

-- Unnested to anti-join
SELECT c.*
FROM customers c
LEFT JOIN orders o ON c.id = o.customer_id
WHERE o.customer_id IS NULL
```

```lean
-- not_in_subquery_unnest_to_antijoin: NOT IN becomes anti-join
```

### When Unnesting Is NOT Safe

Not all subqueries can be unnested:

1. **Correlated with non-equality predicates**: `WHERE t1.x > (SELECT ... WHERE t2.y < t1.z)` — the `<` correlation doesn't map to a standard equi-join
2. **Subqueries with LIMIT/OFFSET**: Unnesting changes evaluation order
3. **Subqueries with ORDER BY**: Order matters for scalar subqueries with LIMIT 1
4. **Non-deterministic functions**: RANDOM(), NOW() in subqueries

---

## Nested Subqueries

Subqueries can nest within each other:

```sql
SELECT * FROM t1
WHERE x IN (
  SELECT y FROM t2
  WHERE z IN (SELECT w FROM t3)
)
```

### Flattening Order Matters

You can flatten from inside out or outside in. Inside-out is generally simpler:

```sql
-- Step 1: Flatten inner subquery
SELECT * FROM t1
WHERE x IN (
  SELECT t2.y FROM t2
  JOIN t3 ON t2.z = t3.w
)

-- Step 2: Flatten outer subquery
SELECT DISTINCT t1.*
FROM t1
JOIN (SELECT DISTINCT t2.y FROM t2 JOIN t3 ON t2.z = t3.w) sub
ON t1.x = sub.y
```

### When Nesting Cannot Be Flattened

```sql
-- Double negation pattern: "Find customers who have ordered ALL products"
SELECT * FROM customers c
WHERE NOT EXISTS (
  SELECT 1 FROM products p
  WHERE NOT EXISTS (
    SELECT 1 FROM orders o
    WHERE o.customer_id = c.id AND o.product_id = p.id
  )
)
```

This "relational division" pattern is inherently nested. Attempting to flatten it changes semantics.

---

## Hands-On Exercises

### Exercise 1: Classify Subqueries

Identify the type (scalar/table, correlated/uncorrelated) for each:

```sql
-- A
SELECT (SELECT MAX(x) FROM t2) FROM t1

-- B
SELECT * FROM t1 WHERE id IN (SELECT id FROM t2 WHERE t2.x = t1.x)

-- C
SELECT * FROM t1 WHERE EXISTS (SELECT 1 FROM t2)
```

<details>
<summary>Answer</summary>

**A**: Scalar, uncorrelated. Returns single value, doesn't reference `t1`.

**B**: Table, correlated. The `t2.x = t1.x` references the outer `t1`, and the subquery returns a set of IDs.

**C**: Table, uncorrelated. EXISTS checks for rows, but the subquery doesn't reference `t1`. The WHERE condition is the same for every row of t1—either always TRUE or always FALSE.

</details>

### Exercise 2: Transform to JOIN

Convert this scalar subquery to a JOIN:

```sql
SELECT * FROM orders
WHERE amount > (SELECT AVG(amount) FROM orders)
```

<details>
<summary>Answer</summary>

The subquery is uncorrelated, so compute it once as a derived table:

```sql
SELECT o.*
FROM orders o
CROSS JOIN (SELECT AVG(amount) as avg_amt FROM orders) sub
WHERE o.amount > sub.avg_amt
```

CROSS JOIN is appropriate because the derived table always returns exactly one row. Alternatively:

```sql
SELECT o.*
FROM orders o, (SELECT AVG(amount) as avg_amt FROM orders) sub
WHERE o.amount > sub.avg_amt
```

The comma syntax is equivalent to CROSS JOIN here.

</details>

### Exercise 3: NOT IN to NOT EXISTS

Safely transform this, considering NULL behavior:

```sql
SELECT * FROM t1 WHERE x NOT IN (SELECT y FROM t2)
```

<details>
<summary>Answer</summary>

```sql
SELECT * FROM t1
WHERE NOT EXISTS (SELECT 1 FROM t2 WHERE t2.y = t1.x)
```

**Why this is safer**: If `t2.y` contains NULLs, the NOT IN version returns **no rows at all** (the NOT IN trap). The NOT EXISTS version correctly returns rows from t1 that have no match in t2, ignoring NULLs.

If you need exact NOT IN semantics (including the NULL behavior), you'd need:
```sql
SELECT * FROM t1
WHERE NOT EXISTS (SELECT 1 FROM t2 WHERE t2.y = t1.x)
  AND NOT EXISTS (SELECT 1 FROM t2 WHERE t2.y IS NULL)
```

</details>

### Exercise 4: Decorrelate

Remove the correlation from this subquery:

```sql
SELECT * FROM employees e
WHERE salary > (SELECT AVG(salary) FROM employees WHERE dept = e.dept)
```

<details>
<summary>Answer</summary>

```sql
SELECT e.*
FROM employees e
JOIN (
  SELECT dept, AVG(salary) as avg_salary
  FROM employees
  GROUP BY dept
) dept_avg ON e.dept = dept_avg.dept
WHERE e.salary > dept_avg.avg_salary
```

The correlation `dept = e.dept` becomes a GROUP BY + JOIN condition. This is a standard decorrelation pattern that most query optimizers perform automatically.

Note: We use INNER JOIN (not LEFT JOIN) because the original correlated subquery always returns a value for each department that has employees.

</details>

---

## Key Theorems Reference

| Theorem | Statement | Used For |
|---------|-----------|----------|
| `in_subquery_as_exists` | `x IN (subq) ≡ EXISTS (correlated)` | IN to EXISTS |
| `not_in_subquery_as_not_exists` | `NOT IN ≡ NOT EXISTS` (no NULLs) | Anti-pattern |
| `exists_empty_false` | `EXISTS (empty) = FALSE` | Empty subquery |
| `exists_nonempty_true` | `EXISTS (non-empty) = TRUE` | Non-empty subquery |
| `exists_as_count_gt_zero` | `EXISTS ≡ COUNT(*) > 0` | Alternative formulation |
| `not_not_exists` | `NOT NOT EXISTS = EXISTS` | Double negation |
| `scalar_subquery_empty_null` | Empty scalar subquery = NULL | NULL behavior |
| `scalar_subquery_is_first` | Scalar = first col of first row | Scalar semantics |
| `uncorrelated_subquery_independent` | Uncorrelated is constant | Decorrelation |
| `in_subquery_unnest_to_join` | IN → semi-join with DISTINCT | Unnesting |
| `not_in_subquery_unnest_to_antijoin` | NOT IN → anti-join | Unnesting |
| `exists_monotonic` | Superset preserves EXISTS TRUE | Monotonicity |

---

## Pitfalls

| Transformation | Pitfall | Condition for Safety |
|----------------|---------|---------------------|
| NOT IN → NOT EXISTS | Different NULL semantics | No NULLs in subquery column |
| Scalar → JOIN | Multiple matches cause duplication | Subquery returns ≤ 1 row |
| IN → JOIN | Duplicates | Add DISTINCT |
| Decorrelation | Changes evaluation order | No side effects, deterministic |
| Flatten nested | Wrong scoping | Careful with aliases |
| EXISTS → JOIN | May change cardinality | Use semi-join (DISTINCT) |

---

## Next Steps

- [Tutorial 6: Aggregate and GROUP BY Rules](06-aggregates.md) - Aggregation equivalences
- [Tutorial 7: Formal Methods Intro](07-formal-methods-intro.md) - How these proofs work under the hood
- [Pitfalls Guide](reference/pitfalls.md) - Complete pitfall reference
