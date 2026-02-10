# Tutorial 3: Understanding NULL and Three-Valued Logic

**Time:** 25 minutes
**Prerequisites:** Tutorial 2

---

## What You'll Learn

- Why SQL uses three-valued logic (TRUE, FALSE, UNKNOWN)
- How NULL propagates through expressions and breaks intuitive equivalences
- Common NULL-related pitfalls with formal proofs
- Safe patterns for writing NULL-aware queries

---

## Why NULL Exists

In SQL, data can be **missing** for multiple reasons:

- **Unknown**: "What is this customer's phone number?" (we don't know yet)
- **Inapplicable**: "What is a company's maiden name?" (doesn't apply)
- **Not yet available**: "What is the final score?" (game still in progress)

SQL represents all of these with a single concept: **NULL**. NULL is not a value—it's the *absence* of a value. This single design choice has profound consequences for query equivalence.

### The Fundamental Rule

Because NULL means "unknown," comparing anything to NULL produces UNKNOWN:

```sql
-- All of these evaluate to UNKNOWN, not TRUE or FALSE:
NULL = NULL       -- Is unknown equal to unknown? Unknown!
NULL = 42         -- Is unknown equal to 42? Unknown!
NULL <> 42        -- Is unknown not equal to 42? Unknown!
NULL > 0          -- Is unknown greater than 0? Unknown!
```

This is formally captured in sql_equiv:

```lean
-- NULL propagates through comparisons
-- null_eq_left: NULL = x evaluates to NULL (representing UNKNOWN)
-- null_eq_right: x = NULL evaluates to NULL (representing UNKNOWN)
```

---

## Three-Valued Logic Truth Tables

Standard Boolean logic has two values: TRUE and FALSE. SQL adds a third: **UNKNOWN** (represented internally as our `Trilean` type).

### AND Truth Table

```
        TRUE     FALSE    UNKNOWN
TRUE    TRUE     FALSE    UNKNOWN
FALSE   FALSE    FALSE    FALSE      ← FALSE dominates
UNKNOWN UNKNOWN  FALSE    UNKNOWN
```

Key insight: **FALSE dominates** in AND. If either side is FALSE, the result is FALSE regardless. This is formally proven:

```lean
-- false_and_null: FALSE AND NULL = FALSE (FALSE dominates)
-- null_and_false: NULL AND FALSE = FALSE
-- true_and_null: TRUE AND NULL = NULL (propagates unknown)
-- null_and_null: NULL AND NULL = NULL
```

### OR Truth Table

```
        TRUE     FALSE    UNKNOWN
TRUE    TRUE     TRUE     TRUE       ← TRUE dominates
FALSE   TRUE     FALSE    UNKNOWN
UNKNOWN TRUE     UNKNOWN  UNKNOWN
```

Key insight: **TRUE dominates** in OR. If either side is TRUE, the result is TRUE regardless.

```lean
-- true_or_null: TRUE OR NULL = TRUE (TRUE dominates)
-- false_or_null: FALSE OR NULL = NULL (propagates unknown)
-- null_or_null: NULL OR NULL = NULL
```

### NOT Truth Table

```
TRUE    → FALSE
FALSE   → TRUE
UNKNOWN → UNKNOWN    ← NOT does NOT resolve unknowns!
```

```lean
-- trilean_not_not: NOT (NOT t) = t  (double negation still works)
```

### Why This Matters for Equivalence

Consider this seemingly innocent transformation:

```sql
-- Query A
SELECT * FROM t WHERE NOT (x > 5)

-- Query B
SELECT * FROM t WHERE x <= 5
```

In two-valued logic, these are equivalent. In SQL? **Not if x can be NULL.**

- If x is NULL: `NOT (NULL > 5)` = `NOT UNKNOWN` = `UNKNOWN` → row excluded
- If x is NULL: `NULL <= 5` = `UNKNOWN` → row excluded

They happen to agree here! But consider:

```sql
-- Query A
SELECT * FROM t WHERE NOT (x > 5 AND y > 10)

-- Query B (De Morgan's law)
SELECT * FROM t WHERE x <= 5 OR y <= 10
```

These are still equivalent because De Morgan's laws hold in three-valued logic:

```lean
-- not_and: NOT (a AND b) =~e (NOT a OR NOT b)
-- not_or:  NOT (a OR b) =~e (NOT a AND NOT b)
-- not_lt_is_ge: NOT (x < y) = (x >= y)
-- not_le_is_gt: NOT (x <= y) = (x > y)
```

The key is that comparison negation flips correctly even with NULLs, because both sides produce UNKNOWN when either operand is NULL.

---

## NULL in Comparisons

### The `= NULL` Trap

The most common NULL mistake:

```sql
-- WRONG: Always returns zero rows (regardless of data!)
SELECT * FROM employees WHERE manager_id = NULL

-- CORRECT: Use IS NULL
SELECT * FROM employees WHERE manager_id IS NULL
```

Why? `manager_id = NULL` evaluates to UNKNOWN for *every* row, and WHERE filters out anything that isn't TRUE.

sql_equiv proves the correct behavior:

```lean
-- is_null_on_null: IS NULL on a NULL value returns TRUE
-- is_null_on_int/string/bool: IS NULL on non-NULL returns FALSE
-- is_not_null_on_null: IS NOT NULL on NULL returns FALSE
-- is_not_null_on_int/string/bool: IS NOT NULL on non-NULL returns TRUE
-- is_null_is_not_null_complement: IS NULL and IS NOT NULL are complementary
```

### IS NULL vs = NULL: A Formal View

```lean
-- These are NOT equivalent:
-- WHERE x = NULL  → always UNKNOWN (no rows pass)
-- WHERE x IS NULL → TRUE when x is NULL, FALSE otherwise

-- IS NULL is the ONLY correct way to test for NULL
```

### NULL-Safe Comparison Pattern

When you need "equal, treating NULLs as equal":

```sql
-- Standard SQL (not all databases support)
SELECT * FROM t WHERE x IS NOT DISTINCT FROM y

-- Portable equivalent
SELECT * FROM t WHERE (x = y) OR (x IS NULL AND y IS NULL)
```

---

## NULL in Arithmetic

NULL propagates through all arithmetic operations:

```sql
5 + NULL    = NULL
NULL - 3    = NULL
NULL * 100  = NULL
10 / NULL   = NULL
```

This is formally proven in sql_equiv:

```lean
-- null_add_left: NULL + x = NULL
-- null_add_right: x + NULL = NULL
-- null_sub_left: NULL - x = NULL
-- null_sub_right: x - NULL = NULL
-- null_mul_left: NULL * x = NULL
-- null_mul_right: x * NULL = NULL
-- null_div_left: NULL / x = NULL
-- null_div_right: x / NULL = NULL
```

### The Consequence for Identity Laws

You might expect `x + 0 = x` to always hold. And it does—for non-NULL values:

```lean
-- expr_add_zero: x + 0 = x  (includes NULL case: NULL + 0 = NULL = NULL ✓)
-- expr_zero_add: 0 + x = x
-- expr_mul_one: x * 1 = x
-- expr_one_mul: 1 * x = x
```

But `x * 0 = 0` does NOT hold when x is NULL:

```
NULL * 0 = NULL  (not 0!)
```

sql_equiv handles this correctly in its optimizer by checking for NULL before applying simplifications.

---

## NULL in Aggregates

Aggregates have special NULL behavior that often surprises:

### COUNT(*) vs COUNT(column)

```sql
-- Given: t = [(x: 1), (x: NULL), (x: 3)]

SELECT COUNT(*)  FROM t    -- Returns 3 (counts all rows)
SELECT COUNT(x)  FROM t    -- Returns 2 (skips NULLs)
```

These are NOT equivalent! sql_equiv captures this:

```lean
-- count_star_nonneg: COUNT(*) >= 0
-- count_star_empty: COUNT(*) = 0 on empty table
-- count_star_singleton: COUNT(*) = 1 on single-row table
```

### SUM, AVG, MIN, MAX Ignore NULLs

```sql
-- Given: t = [(x: 10), (x: NULL), (x: 20)]

SELECT SUM(x) FROM t     -- 30 (ignores NULL)
SELECT AVG(x) FROM t     -- 15 (30/2, not 30/3)
SELECT MIN(x) FROM t     -- 10
SELECT MAX(x) FROM t     -- 20
```

AVG divides by the count of non-NULL values, not total rows. This means:

```sql
-- NOT equivalent!
SELECT AVG(x) FROM t
SELECT SUM(x) / COUNT(*) FROM t     -- WRONG: divides by all rows
SELECT SUM(x) / COUNT(x) FROM t     -- CORRECT: divides by non-NULL count
```

### Empty Table: COUNT Returns 0, Others Return NULL

```sql
-- When t is empty:
SELECT COUNT(*) FROM t    -- 0
SELECT COUNT(x) FROM t    -- 0
SELECT SUM(x)   FROM t    -- NULL (not 0!)
SELECT AVG(x)   FROM t    -- NULL
SELECT MIN(x)   FROM t    -- NULL
SELECT MAX(x)   FROM t    -- NULL
```

```lean
-- count_star_empty: COUNT(*) of empty table returns 0
```

Note: In SQL, `SUM` on an empty table returns NULL, not 0. The codebase lemma `sum_empty` proves that `[].foldl (+) 0 = 0`, which is about the underlying list fold, not the SQL aggregate. The SQL-level SUM wraps this and returns NULL when no rows are present.

### COALESCE for Default Values

`COALESCE(x, y, ...)` returns the first non-NULL argument:

```sql
SELECT COALESCE(phone, email, 'N/A') FROM contacts
-- Returns phone if not null, else email if not null, else 'N/A'
```

```lean
-- coalesce_null_left_nonnull: COALESCE(NULL, x) = x (when x is non-null)
-- coalesce_int_left: COALESCE(n, y) = n for non-null int
-- coalesce_string_left: COALESCE(s, y) = s for non-null string
-- coalesce_bool_left: COALESCE(b, y) = b for non-null bool
```

**Important subtlety**: The axiom `COALESCE(NULL, x) = x` is only valid when x is non-NULL. When both arguments are NULL, COALESCE returns NULL (represented as `none` internally), which differs from the second argument's typed NULL representation (`some (.null t)`). See the [Pitfalls guide](reference/pitfalls.md#coalescenull-null-and-typed-nulls) for details.

---

## The NOT IN Trap

This is the most dangerous NULL pitfall in practice.

### The Problem

```sql
-- "Find customers who have NOT placed orders"
-- Attempt 1: NOT IN
SELECT * FROM customers
WHERE id NOT IN (SELECT customer_id FROM orders)
```

This works perfectly—**until a NULL appears in `orders.customer_id`**.

### Why It Breaks

```
customers = [(id: 1), (id: 2), (id: 3)]
orders.customer_id = [1, NULL]

For customer id=2:
  2 NOT IN (1, NULL)
  = NOT (2 = 1 OR 2 = NULL)
  = NOT (FALSE OR UNKNOWN)
  = NOT UNKNOWN
  = UNKNOWN
  → Row excluded!
```

**Every customer is excluded**, even id=2 and id=3 who genuinely have no orders!

### The Safe Alternative

```sql
-- NOT EXISTS doesn't have this problem:
SELECT * FROM customers c
WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.id)

-- For customer id=2:
--   Is there a row in orders where customer_id = 2? No.
--   NOT EXISTS (empty) = TRUE → Row included! ✓
```

### Formal Statement

```lean
-- in_empty_subquery_false: x IN (empty) = FALSE
-- not_in_empty_subquery_true: x NOT IN (empty) = TRUE
-- in_subquery_as_exists: x IN (SELECT y FROM s) ≡ EXISTS (SELECT 1 FROM s WHERE y = x)
-- not_in_subquery_as_not_exists: x NOT IN (SELECT y FROM s) ≡ NOT EXISTS (SELECT 1 FROM s WHERE y = x)
```

Note: The `not_in_subquery_as_not_exists` equivalence is an axiom that holds when the subquery column has no NULLs. When NULLs are present, NOT IN and NOT EXISTS have different semantics.

---

## Hands-On Exercises

### Exercise 1: Truth Table Practice

Evaluate step by step:

```sql
(TRUE AND UNKNOWN) OR FALSE
```

<details>
<summary>Answer</summary>

```
Step 1: TRUE AND UNKNOWN = UNKNOWN  (UNKNOWN doesn't resolve)
Step 2: UNKNOWN OR FALSE = UNKNOWN  (neither side resolves it)

Final: UNKNOWN
```

The row would be filtered out by a WHERE clause.

</details>

### Exercise 2: Find the Bug

A developer writes:

```sql
-- "Find employees not in the engineering department"
SELECT * FROM employees WHERE dept_id <> (SELECT id FROM departments WHERE name = 'Engineering')
```

What happens when the subquery returns NULL or no rows?

<details>
<summary>Answer</summary>

**Two bugs:**

1. **If no Engineering department exists**: The subquery returns empty, which becomes NULL as a scalar subquery. Then `dept_id <> NULL` = UNKNOWN for every row. **No rows returned.**

2. **If dept_id can be NULL**: Employees with `dept_id = NULL` have `NULL <> (any value)` = UNKNOWN. They're excluded even though they're clearly not in Engineering.

**Safe version:**
```sql
SELECT * FROM employees e
WHERE NOT EXISTS (
  SELECT 1 FROM departments d
  WHERE d.name = 'Engineering' AND d.id = e.dept_id
)
```

</details>

### Exercise 3: Fix the Query

This query is supposed to show employees with their manager's name, including those with no manager:

```sql
SELECT e.name, m.name as manager_name
FROM employees e, employees m
WHERE e.manager_id = m.id
```

Why does it exclude employees with no manager? How would you fix it?

<details>
<summary>Answer</summary>

The implicit join (`FROM a, b WHERE ...`) acts as an INNER JOIN. When `e.manager_id` is NULL, the condition `NULL = m.id` evaluates to UNKNOWN for every manager row, so the employee is excluded.

**Fix: Use LEFT JOIN:**
```sql
SELECT e.name, m.name as manager_name
FROM employees e
LEFT JOIN employees m ON e.manager_id = m.id
```

Now employees with `manager_id = NULL` are kept, with `manager_name = NULL`.

</details>

### Exercise 4: NULL in GROUP BY

What happens with NULL values in GROUP BY?

```sql
SELECT dept, COUNT(*) FROM employees GROUP BY dept
-- Given: departments include NULL (some employees unassigned)
```

<details>
<summary>Answer</summary>

All rows with `dept = NULL` are grouped together into **one group**. This is one of the few places where SQL treats NULLs as "equal."

```
dept     | count
---------|------
Sales    | 5
NULL     | 3     ← All unassigned employees in one group
Engineering | 8
```

This is a notable inconsistency: `NULL = NULL` is UNKNOWN in comparisons, but NULLs are grouped together in GROUP BY.

</details>

---

## Key Theorems Reference

| Theorem | Statement | Used For |
|---------|-----------|----------|
| `trilean_not_not` | `NOT (NOT t) = t` | Double negation |
| `trilean_and_comm` | `t AND u = u AND t` | AND commutativity |
| `trilean_or_comm` | `t OR u = u OR t` | OR commutativity |
| `trilean_de_morgan_and` | `NOT(a AND b) = NOT a OR NOT b` | De Morgan's laws |
| `trilean_de_morgan_or` | `NOT(a OR b) = NOT a AND NOT b` | De Morgan's laws |
| `false_and_null` | `FALSE AND NULL = FALSE` | Short-circuit |
| `true_or_null` | `TRUE OR NULL = TRUE` | Short-circuit |
| `is_null_on_null` | `IS NULL` on NULL = TRUE | NULL testing |
| `is_null_is_not_null_complement` | IS NULL / IS NOT NULL complement | NULL testing |
| `null_add_left/right` | `NULL + x = NULL` | NULL propagation |
| `coalesce_null_left_nonnull` | `COALESCE(NULL, x) = x` (x non-null) | Default values |

---

## Common Mistakes

| Pattern | Problem | Safe Alternative |
|---------|---------|------------------|
| `WHERE x = NULL` | Always UNKNOWN | `WHERE x IS NULL` |
| `WHERE x <> NULL` | Always UNKNOWN | `WHERE x IS NOT NULL` |
| `NOT IN (subquery)` | Fails if subquery has NULLs | `NOT EXISTS` |
| `COUNT(nullable_col)` | Excludes NULLs | `COUNT(*)` or `COUNT(COALESCE(...))` |
| `AVG(x)` = `SUM(x)/COUNT(*)` | Wrong denominator | Use `SUM(x)/COUNT(x)` |
| `x + 0 = x` in optimizer | Holds (NULL + 0 = NULL) | Safe |
| `x * 0 = 0` in optimizer | Fails: NULL * 0 = NULL | Guard with NULL check |

---

## Next Steps

- [Tutorial 4: Join Transformations](04-join-transforms.md) - Which join rewrites are safe?
- [Pitfalls Guide](reference/pitfalls.md) - Complete reference of NULL traps
- [Equivalence Catalog](reference/equivalence-catalog.md) - All proven equivalences
