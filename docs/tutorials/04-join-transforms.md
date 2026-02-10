# Tutorial 4: Join Transformations

**Time:** 30 minutes
**Prerequisites:** Tutorial 3

---

## What You'll Learn

- Which join transformations preserve equivalence and which don't
- How join order affects results for different join types
- How to safely convert between joins and subqueries
- Where predicate placement matters (ON vs WHERE)

---

## Join Fundamentals

A join combines rows from two tables. The join type determines what happens when rows don't match:

| Join Type | Unmatched Left Rows | Unmatched Right Rows |
|-----------|-------------------|---------------------|
| INNER JOIN | Excluded | Excluded |
| LEFT JOIN | Kept (NULLs for right) | Excluded |
| RIGHT JOIN | Excluded | Kept (NULLs for left) |
| FULL JOIN | Kept (NULLs for right) | Kept (NULLs for left) |
| CROSS JOIN | N/A (all combinations) | N/A (all combinations) |

### Join as Filtered Cartesian Product

Conceptually, every join is:

1. Take the Cartesian product (CROSS JOIN) of both tables
2. Apply the ON condition to filter rows
3. For outer joins, add back unmatched rows with NULLs

This is formally captured:

```lean
-- inner_join_to_where: A INNER JOIN B ON cond = (A CROSS JOIN B) WHERE cond
-- cross_join_cardinality: |A × B| = |A| * |B|
-- inner_join_cardinality_le: |A ⋈ B| ≤ |A| * |B|
```

---

## INNER JOIN Properties

INNER JOIN has the strongest algebraic properties. This is why optimizers love to work with inner joins.

### Commutativity: `A JOIN B = B JOIN A`

```sql
-- These are equivalent:
SELECT * FROM orders o INNER JOIN customers c ON o.cust_id = c.id
SELECT * FROM customers c INNER JOIN orders o ON c.id = o.cust_id
```

The row content is the same—only column order in the output might differ. Formally:

```lean
-- join_comm: INNER JOIN is commutative (row membership)
-- join_comm_full: INNER JOIN commutativity (full equality)
```

**Why this matters**: Query optimizers can freely swap the order of inner joins to put the smaller table first, improving performance with hash joins or nested loop joins.

### Associativity: `(A JOIN B) JOIN C = A JOIN (B JOIN C)`

```sql
-- These are equivalent:
SELECT * FROM (orders o JOIN customers c ON o.cust_id = c.id)
  JOIN products p ON o.prod_id = p.id

SELECT * FROM orders o
  JOIN (customers c JOIN products p ON TRUE) ON o.cust_id = c.id AND o.prod_id = p.id
```

```lean
-- join_assoc: INNER JOIN is associative
```

Together, commutativity and associativity mean an optimizer can evaluate a multi-way inner join in **any order**. For n tables, that's n! possible orderings.

### Identity and Empty Properties

```lean
-- inner_join_true_is_cross: A INNER JOIN B ON TRUE = A CROSS JOIN B
-- inner_join_false_empty: A INNER JOIN B ON FALSE = ∅
-- inner_join_empty_left: ∅ INNER JOIN B = ∅
-- inner_join_empty_right: A INNER JOIN ∅ = ∅
```

These are useful in optimizer reasoning: if we can prove the condition is always false (e.g., type mismatch), the entire join can be eliminated.

---

## OUTER JOIN Restrictions

Outer joins are much less flexible. Most properties of inner joins do NOT hold.

### LEFT JOIN is NOT Commutative

```sql
-- NOT equivalent!
SELECT * FROM orders o LEFT JOIN customers c ON o.cust_id = c.id
SELECT * FROM customers c LEFT JOIN orders o ON c.id = o.cust_id
```

**Why?** The first keeps all orders (even with invalid customer IDs). The second keeps all customers (even those with no orders). Different rows survive.

### LEFT JOIN is NOT Associative (in general)

```sql
-- NOT equivalent in general!
SELECT * FROM (A LEFT JOIN B ON ...) LEFT JOIN C ON ...
SELECT * FROM A LEFT JOIN (B LEFT JOIN C ON ...) ON ...
```

The NULL-padding from the first LEFT JOIN can affect the second join's condition.

### What CAN You Do With Outer Joins?

**Convert LEFT to RIGHT (and vice versa):**

```sql
-- These ARE equivalent:
SELECT * FROM A LEFT JOIN B ON A.x = B.x
SELECT * FROM B RIGHT JOIN A ON B.x = A.x
```

**Convert outer to inner (with NULL filter):**

If you filter out the NULL-padded rows anyway, a LEFT JOIN becomes an INNER JOIN:

```sql
-- Equivalent when filtering requires non-null right column:
SELECT * FROM A LEFT JOIN B ON A.x = B.x WHERE B.y > 10
SELECT * FROM A INNER JOIN B ON A.x = B.x WHERE B.y > 10
```

The `WHERE B.y > 10` excludes any row where B columns are NULL (from unmatched left rows), so the LEFT JOIN's extra rows are removed.

```lean
-- left_join_filter_null_is_inner: LEFT JOIN filtered by non-null right = INNER JOIN
```

### Cardinality Guarantees

Even without full algebraic properties, outer joins provide cardinality guarantees:

```lean
-- left_join_cardinality_ge: |A LEFT JOIN B| ≥ |A|
-- right_join_cardinality_ge: |A RIGHT JOIN B| ≥ |B|
-- left_join_preserves_left: LEFT JOIN preserves all left rows
-- right_join_preserves_right: RIGHT JOIN preserves all right rows
-- left_join_false_all_left: |A LEFT JOIN B ON FALSE| = |A|
```

A LEFT JOIN **never loses** rows from the left table. This is its fundamental guarantee.

---

## CROSS JOIN Properties

CROSS JOIN (Cartesian product) is the simplest join—no condition.

```lean
-- cross_join_comm: CROSS JOIN is commutative (row membership)
-- cross_join_assoc: CROSS JOIN is associative
-- cross_join_cardinality_comm: |A × B| = |B × A|
-- cross_join_cardinality: |A × B| = |A| * |B|
-- cross_join_assoc_cardinality: |(A × B) × C| = |A × (B × C)|
-- cross_join_empty_left: ∅ × B = ∅
-- cross_join_empty_right: A × ∅ = ∅
```

**Practical note**: CROSS JOINs are rarely intentional. If you see one without a WHERE clause, it's usually a bug producing a massive result.

---

## JOIN ↔ Subquery Conversions

Converting between joins and subqueries is one of the most common query transformations. Getting it right requires care.

### IN Subquery → Semi-Join

```sql
-- Original: IN subquery
SELECT * FROM orders
WHERE customer_id IN (SELECT id FROM vip_customers)

-- Equivalent: Semi-join (INNER JOIN + DISTINCT)
SELECT DISTINCT o.*
FROM orders o
INNER JOIN vip_customers v ON o.customer_id = v.id
```

**Why DISTINCT?** Without it, if a customer appears multiple times in vip_customers, each order gets duplicated. IN tests membership (yes/no), while JOIN produces one output per match.

```lean
-- in_subquery_as_exists: x IN (SELECT y FROM s) ≡ EXISTS (SELECT 1 FROM s WHERE y = x)
-- in_subquery_unnest_to_join: IN subquery becomes semi-join with DISTINCT
```

### EXISTS → Semi-Join

```sql
-- Original: EXISTS
SELECT * FROM orders o
WHERE EXISTS (SELECT 1 FROM vip_customers v WHERE v.id = o.customer_id)

-- Equivalent: Same semi-join as above
SELECT DISTINCT o.*
FROM orders o
INNER JOIN vip_customers v ON o.customer_id = v.id
```

```lean
-- exists_empty_false: EXISTS on empty = FALSE
-- exists_nonempty_true: EXISTS on non-empty = TRUE
-- exists_as_count_gt_zero: EXISTS ≡ (COUNT(*) > 0)
```

### NOT IN → Anti-Join (With Caveats!)

```sql
-- Original: NOT IN
SELECT * FROM customers
WHERE id NOT IN (SELECT customer_id FROM orders)

-- Anti-join pattern:
SELECT c.*
FROM customers c
LEFT JOIN orders o ON c.id = o.customer_id
WHERE o.customer_id IS NULL
```

**The NULL caveat**: As discussed in [Tutorial 3](03-null-logic.md), NOT IN behaves unexpectedly when the subquery contains NULLs. The anti-join pattern is safer because the LEFT JOIN + IS NULL approach doesn't suffer from the NOT IN trap.

```lean
-- not_in_subquery_as_not_exists: NOT IN ≡ NOT EXISTS (when no NULLs)
-- not_in_subquery_unnest_to_antijoin: NOT IN becomes anti-join
```

### NOT EXISTS → Anti-Join

```sql
-- Original: NOT EXISTS
SELECT * FROM customers c
WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.id)

-- Equivalent anti-join:
SELECT c.*
FROM customers c
LEFT JOIN orders o ON c.id = o.customer_id
WHERE o.customer_id IS NULL
```

```lean
-- not_exists_empty_true: NOT EXISTS on empty = TRUE
-- not_exists_nonempty_false: NOT EXISTS on non-empty = FALSE
-- not_not_exists: NOT NOT EXISTS = EXISTS
```

### Scalar Subquery → LEFT JOIN

```sql
-- Original: Scalar subquery in SELECT
SELECT o.id,
       (SELECT c.name FROM customers c WHERE c.id = o.customer_id) as customer_name
FROM orders o

-- Equivalent: LEFT JOIN (only if customers.id is unique!)
SELECT o.id, c.name as customer_name
FROM orders o
LEFT JOIN customers c ON c.id = o.customer_id
```

**Requires**: The join key is unique in the right table. Otherwise the JOIN produces duplicates.

```lean
-- scalar_subquery_empty_null: Scalar subquery on empty returns NULL
-- scalar_subquery_is_first: Scalar subquery returns first column of first row
```

---

## Predicate Placement: ON vs WHERE

### For INNER JOINs: ON and WHERE Are Equivalent

```sql
-- These are equivalent:
SELECT * FROM A INNER JOIN B ON A.x = B.x AND B.status = 'active'
SELECT * FROM A INNER JOIN B ON A.x = B.x WHERE B.status = 'active'
```

Since INNER JOIN excludes unmatched rows anyway, it doesn't matter whether you filter in ON or WHERE.

```lean
-- inner_join_to_where: A ⋈ B ON cond = (A × B) WHERE cond
-- inner_subset_cross: |A ⋈ B ON cond| ≤ |A × B|
```

### For OUTER JOINs: ON and WHERE Are NOT Equivalent

```sql
-- NOT equivalent!

-- Query A: Filter in ON (applied before NULL padding)
SELECT * FROM orders o
LEFT JOIN customers c ON o.cust_id = c.id AND c.country = 'US'

-- Query B: Filter in WHERE (applied after NULL padding)
SELECT * FROM orders o
LEFT JOIN customers c ON o.cust_id = c.id
WHERE c.country = 'US'
```

**Query A**: Returns ALL orders. Non-US customers show NULL in customer columns.
**Query B**: Returns only orders with US customers. Non-US customers are filtered OUT (including orders with no customer match).

This is one of the most common join mistakes. The rule:

- **ON clause filter**: Affects which rows are matched, but unmatched left rows are still kept (with NULLs)
- **WHERE clause filter**: Filters the final result, including NULL-padded rows

### Predicate Pushdown Through Joins

An optimizer might try to push a WHERE predicate into a JOIN's ON clause. This is safe for inner joins but not outer joins:

```lean
-- filter_and_eq_filter_filter: filter(p AND q) = filter(q, filter(p))
-- filter_comm: filter(q, filter(p)) = filter(p, filter(q))
-- predicate_pushdown: WHERE predicate pushdown through FROM
```

---

## Hands-On Exercises

### Exercise 1: Commutativity Check

Which of these pairs are equivalent?

```sql
-- Pair 1
SELECT * FROM A INNER JOIN B ON A.id = B.id
SELECT * FROM B INNER JOIN A ON B.id = A.id

-- Pair 2
SELECT * FROM A LEFT JOIN B ON A.id = B.id
SELECT * FROM B LEFT JOIN A ON B.id = A.id

-- Pair 3
SELECT * FROM A LEFT JOIN B ON A.id = B.id
SELECT * FROM B RIGHT JOIN A ON B.id = A.id
```

<details>
<summary>Answer</summary>

**Pair 1: Equivalent** - INNER JOIN is commutative.

**Pair 2: NOT Equivalent** - LEFT JOIN is not commutative. The first keeps all A rows; the second keeps all B rows.

**Pair 3: Equivalent** - `A LEFT JOIN B` = `B RIGHT JOIN A`. Swapping the tables and changing LEFT to RIGHT preserves semantics.

</details>

### Exercise 2: Predicate Placement

Is it safe to move the WHERE to ON?

```sql
SELECT * FROM a LEFT JOIN b ON a.id = b.id WHERE b.status = 'active'
```

<details>
<summary>Answer</summary>

**Moving to ON changes the semantics**, but in this case the WHERE already **converts the LEFT JOIN to an INNER JOIN**.

The `WHERE b.status = 'active'` filters out any row where `b.status` is NULL, which includes all unmatched left rows. So the LEFT JOIN is already effectively an INNER JOIN.

Both of these are equivalent to the original:
```sql
-- Equivalent: LEFT JOIN becomes INNER JOIN
SELECT * FROM a INNER JOIN b ON a.id = b.id WHERE b.status = 'active'

-- Equivalent: Move predicate to ON (only because it's now effectively an INNER JOIN)
SELECT * FROM a INNER JOIN b ON a.id = b.id AND b.status = 'active'
```

But this is NOT equivalent:
```sql
-- NOT equivalent: keeps unmatched 'a' rows with NULL b columns
SELECT * FROM a LEFT JOIN b ON a.id = b.id AND b.status = 'active'
```

</details>

### Exercise 3: Subquery to JOIN

Convert this to a JOIN and verify equivalence:

```sql
SELECT * FROM orders
WHERE customer_id IN (SELECT id FROM vip_customers)
```

<details>
<summary>Answer</summary>

**Option 1: INNER JOIN with DISTINCT**
```sql
SELECT DISTINCT o.*
FROM orders o
INNER JOIN vip_customers v ON o.customer_id = v.id
```

**Option 2: EXISTS (often preferred by optimizers)**
```sql
SELECT * FROM orders o
WHERE EXISTS (SELECT 1 FROM vip_customers v WHERE v.id = o.customer_id)
```

Both are equivalent to the original. Option 1 needs DISTINCT to avoid duplicates if vip_customers has duplicate IDs. Option 2 avoids that issue entirely.

</details>

### Exercise 4: Multi-Way Join Reordering

Given these table sizes:
- `orders`: 1,000,000 rows
- `customers`: 10,000 rows
- `products`: 500 rows

Which join order is more efficient?

```sql
-- Order A
SELECT * FROM orders o
  JOIN customers c ON o.cust_id = c.id
  JOIN products p ON o.prod_id = p.id

-- Order B
SELECT * FROM orders o
  JOIN products p ON o.prod_id = p.id
  JOIN customers c ON o.cust_id = c.id
```

<details>
<summary>Answer</summary>

Both are **semantically equivalent** (INNER JOIN is commutative and associative). But performance can differ significantly.

**Order B is likely faster** because:
1. `orders JOIN products` (500 products) filters down orders first
2. The intermediate result is then joined with 10,000 customers

The general heuristic: join with the smallest table first to reduce intermediate result size.

This is exactly why join reordering is one of the most important optimizer transformations, and why it's critical to prove it preserves equivalence:

```lean
-- join_assoc: (A ⋈ B) ⋈ C ≡ A ⋈ (B ⋈ C)
-- join_comm: A ⋈ B ≡ B ⋈ A
```

</details>

---

## Key Theorems Reference

| Theorem | Statement | Used For |
|---------|-----------|----------|
| `join_comm` | `A ⋈ B ≡ B ⋈ A` | Join reordering |
| `join_assoc` | `(A ⋈ B) ⋈ C ≡ A ⋈ (B ⋈ C)` | Join reordering |
| `cross_join_comm` | `A × B ≡ B × A` | Cross join symmetry |
| `cross_join_assoc` | `(A × B) × C ≡ A × (B × C)` | Cross join reordering |
| `inner_join_to_where` | `A ⋈ B ON cond = (A × B) WHERE cond` | ON/WHERE equivalence |
| `inner_join_true_is_cross` | `A ⋈ B ON TRUE = A × B` | Unconditional join |
| `inner_join_false_empty` | `A ⋈ B ON FALSE = ∅` | Dead join elimination |
| `left_join_preserves_left` | LEFT JOIN keeps all left rows | Cardinality reasoning |
| `left_join_filter_null_is_inner` | LEFT JOIN + non-null filter = INNER JOIN | Outer-to-inner conversion |
| `in_subquery_as_exists` | `x IN (subq) ≡ EXISTS (correlated subq)` | Subquery unnesting |
| `not_in_subquery_as_not_exists` | `NOT IN ≡ NOT EXISTS` (no NULLs) | Anti-join conversion |

---

## Pitfalls

| Transformation | Pitfall | Condition for Safety |
|----------------|---------|---------------------|
| LEFT → INNER | Loses unmatched rows | FK constraint + NOT NULL |
| Reorder LEFT joins | Changes result | Only specific patterns safe |
| IN → JOIN | May duplicate rows | Use DISTINCT or EXISTS |
| NOT IN → LEFT JOIN | NULL handling differs | Source has no NULLs |
| ON → WHERE (outer) | Filters unmatched rows | Only for inner joins |
| Join elimination | Removes needed rows | Only if provably unused |

---

## Next Steps

- [Tutorial 5: Subquery Equivalences](05-subquery-equiv.md) - Deep dive into subquery transformations
- [Tutorial 7: Formal Methods Intro](07-formal-methods-intro.md) - How these proofs are constructed
- [Pitfalls Guide](reference/pitfalls.md) - Complete reference of join traps
