# Tutorial 1: Your First Equivalence Proof

**Time:** 15 minutes
**Prerequisites:** Basic SQL knowledge

---

## What You'll Learn

- What "query equivalence" means precisely
- How to use sql_equiv to check simple equivalences
- Why some obvious-looking equivalences are actually true

---

## The Big Question

You have a query that works but runs slowly:

```sql
SELECT * FROM orders WHERE status = 'pending' AND amount > 100
```

You want to rewrite it for performance. Can you swap the conditions?

```sql
SELECT * FROM orders WHERE amount > 100 AND status = 'pending'
```

**Intuition says**: "Of course! AND is commutative!"

**But are you sure?** What if there's some edge case with NULLs? What if the database evaluates them differently?

This is where sql_equiv helps—it *proves* the equivalence, not just tests it.

---

## Your First Equivalence Check

Let's verify that AND is indeed commutative:

```bash
lake exe sql_equiv check \
  "SELECT * FROM t WHERE a = 1 AND b = 2" \
  "SELECT * FROM t WHERE b = 2 AND a = 1"
```

Output:
```
✓ EQUIVALENT

Proof: AND commutativity (Equiv.and_comm)
  a AND b ≡ b AND a
```

**What just happened?**

1. sql_equiv parsed both queries into abstract syntax trees (ASTs)
2. It recognized the structural pattern: `(P AND Q)` vs `(Q AND P)`
3. It applied the theorem `and_comm` which proves AND is commutative
4. It confirmed the queries are equivalent for *all possible* tables `t`

---

## A Slightly Harder Example

What about reordering columns in SELECT?

```sql
-- Query A
SELECT name, age FROM users

-- Query B
SELECT age, name FROM users
```

Let's check:

```bash
lake exe sql_equiv check \
  "SELECT name, age FROM users" \
  "SELECT age, name FROM users"
```

Output:
```
✗ NOT EQUIVALENT

Reason: Column order differs
  Query A returns: (name, age)
  Query B returns: (age, name)

Note: Results contain same data but in different column positions.
      This may or may not matter for your use case.
```

**Important insight**: "Same data" ≠ "equivalent queries"

SQL query equivalence is precise—the results must be *identical*, including column order. If your application doesn't care about column order, that's fine, but sql_equiv is telling you the queries are technically different.

---

## Equivalences That Do Work

### 1. WHERE clause reordering

```sql
-- These are equivalent
SELECT * FROM t WHERE a = 1 AND b = 2 AND c = 3
SELECT * FROM t WHERE c = 3 AND a = 1 AND b = 2
```
✓ AND is commutative and associative

### 2. Double negation

```sql
-- These are equivalent
SELECT * FROM t WHERE NOT NOT active
SELECT * FROM t WHERE active
```
✓ NOT NOT x ≡ x (in two-valued logic)

### 3. Table alias changes

```sql
-- These are equivalent
SELECT x.name FROM users x WHERE x.id = 1
SELECT y.name FROM users y WHERE y.id = 1
```
✓ Alias names don't affect semantics

### 4. Redundant parentheses

```sql
-- These are equivalent
SELECT * FROM t WHERE (a = 1) AND (b = 2)
SELECT * FROM t WHERE a = 1 AND b = 2
```
✓ Parentheses only affect parsing, not semantics

---

## Equivalences That Don't Work

### 1. Column order (as we saw)

```sql
SELECT a, b FROM t    -- NOT equivalent to
SELECT b, a FROM t
```

### 2. Row order (without ORDER BY)

```sql
-- NOT guaranteed equivalent!
SELECT * FROM t
SELECT * FROM t       -- Same query, but results may differ
```

Wait, what? The same query isn't equivalent to itself?

Actually, without ORDER BY, SQL makes no guarantees about row order. Two executions of the same query might return rows in different orders. sql_equiv uses **bag semantics** (multiset), so row order doesn't matter for equivalence—but if you add ORDER BY, then order does matter.

### 3. NULL complications

```sql
SELECT * FROM t WHERE x = x      -- NOT equivalent to
SELECT * FROM t WHERE TRUE
```

Why? Because if `x` is NULL, then `NULL = NULL` is UNKNOWN (not TRUE), so that row would be filtered out!

We'll cover NULL handling in [Tutorial 3](03-null-logic.md).

---

## Hands-On Exercises

Try these yourself:

### Exercise 1
Are these equivalent?
```sql
SELECT * FROM t WHERE a > 5 OR a > 10
SELECT * FROM t WHERE a > 5
```

<details>
<summary>Answer</summary>

✓ **Yes, equivalent**

If `a > 10`, then `a > 5` is also true.
If `a > 5` but not `a > 10`, then `a > 5 OR a > 10` is still true (because `a > 5`).
If `a <= 5`, both sides are false.

The condition `a > 10` is absorbed by `a > 5`.

</details>

### Exercise 2
Are these equivalent?
```sql
SELECT DISTINCT * FROM t
SELECT * FROM t
```

<details>
<summary>Answer</summary>

✗ **Not equivalent** (in general)

DISTINCT removes duplicate rows. If `t` has duplicate rows, the results differ.

However, if `t` has a PRIMARY KEY, then no duplicates can exist, so they would be equivalent *for that specific table*. But sql_equiv proves equivalence for *all possible* tables.

</details>

### Exercise 3
Are these equivalent?
```sql
SELECT * FROM t WHERE x IN (1, 2, 3)
SELECT * FROM t WHERE x = 1 OR x = 2 OR x = 3
```

<details>
<summary>Answer</summary>

✓ **Yes, equivalent**

`IN (list)` is defined as a disjunction of equalities.

</details>

---

## What You've Learned

1. **Query equivalence** means same results for *all possible* database states
2. **sql_equiv proves** equivalence, not just tests it
3. **Some intuitive equivalences hold** (AND commutativity)
4. **Some intuitive equivalences don't** (column order matters)
5. **NULL creates surprises** (coming in Tutorial 3)

---

## Next Steps

- [Tutorial 2: Easy vs Hard](02-easy-vs-hard.md) - Learn which equivalences are provable
- [Equivalence Catalog](reference/equivalence-catalog.md) - Reference of common transformations

---

## Key Theorems Used

| Theorem | Statement | Used For |
|---------|-----------|----------|
| `and_comm` | `a AND b ≡ b AND a` | WHERE reordering |
| `and_assoc` | `(a AND b) AND c ≡ a AND (b AND c)` | Flattening ANDs |
| `or_comm` | `a OR b ≡ b OR a` | OR reordering |
| `double_neg` | `NOT NOT a ≡ a` | Simplification |
