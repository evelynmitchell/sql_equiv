# Tutorial 2: Easy vs Hard — When Can We Prove Equivalence?

**Time:** 20 minutes
**Prerequisites:** Tutorial 1

---

## What You'll Learn

- The spectrum from "trivially provable" to "impossible without context"
- How to recognize which category a query pair falls into
- When to trust the tool vs when to think harder

---

## The Provability Spectrum

Not all equivalence questions are equally hard:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│  SYNTACTIC          SEMANTIC           CONTEXTUAL        UNDECIDABLE   │
│  (Easy)             (Medium)           (Hard)            (Impossible)  │
│                                                                         │
│  • Reorder AND      • IN → EXISTS      • "VIP" means     • Halting     │
│  • Rename alias     • Flatten subq     •  amount > 1000    problem     │
│  • Add parens       • Push predicate   • Column X is     • Infinite    │
│                     • Reorder joins      unique             recursion  │
│                                                                         │
│  ───────────────────────────────────────────────────────────────────▶  │
│  sql_equiv handles        Needs human         Cannot be automated      │
│  automatically            insight                                       │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Level 1: Syntactic Equivalences (Easy)

These equivalences are purely about *structure*—no semantic reasoning required.

### What Makes Them Easy

- Both queries have nearly identical ASTs
- Transformation is mechanical (swap, rename, remove redundancy)
- Can be verified by pattern matching

### Examples

```sql
-- ✓ Commutativity (swap operands)
WHERE a = 1 AND b = 2    ≡    WHERE b = 2 AND a = 1

-- ✓ Associativity (regroup)
WHERE (a AND b) AND c    ≡    WHERE a AND (b AND c)

-- ✓ Alias renaming
SELECT t.x FROM tab t    ≡    SELECT s.x FROM tab s

-- ✓ Redundant parens
WHERE ((x > 5))          ≡    WHERE x > 5

-- ✓ Idempotence
WHERE x = 1 AND x = 1    ≡    WHERE x = 1
```

### sql_equiv Says

```
✓ EQUIVALENT (syntactic transformation)
```

The tool handles these automatically with high confidence.

---

## Level 2: Semantic Equivalences (Medium)

These require understanding what the SQL *means*, not just how it's written.

### What Makes Them Medium

- Queries look structurally different
- Equivalence depends on SQL semantics (how operations are defined)
- Requires algebraic reasoning

### Examples

```sql
-- ✓ IN to EXISTS transformation
SELECT * FROM orders
WHERE customer_id IN (SELECT id FROM vip_customers)

≡

SELECT * FROM orders o
WHERE EXISTS (SELECT 1 FROM vip_customers v WHERE v.id = o.customer_id)
```

Why equivalent? Both return orders where the customer_id appears in vip_customers. The IN checks membership; EXISTS checks for any matching row.

```sql
-- ✓ Subquery flattening (uncorrelated)
SELECT * FROM orders
WHERE amount > (SELECT AVG(amount) FROM orders)

≡

SELECT o.* FROM orders o, (SELECT AVG(amount) as avg_amt FROM orders) sub
WHERE o.amount > sub.avg_amt
```

```sql
-- ✓ Join commutativity (INNER only!)
SELECT * FROM a JOIN b ON a.x = b.x

≡

SELECT * FROM b JOIN a ON b.x = a.x
```

**Caution**: This does NOT work for LEFT/RIGHT joins!

### sql_equiv Says

```
✓ EQUIVALENT (semantic transformation)
Proof: in_to_exists theorem
```

The tool can prove these using built-in theorems, but might need hints.

---

## Level 3: Contextual Equivalences (Hard)

These depend on facts about your *specific* data that aren't expressed in the query.

### What Makes Them Hard

- Equivalence requires domain knowledge
- The tool can't know your business rules
- Must be verified by human reasoning

### Examples

#### Example 1: Uniqueness Assumption

```sql
-- Query A
SELECT DISTINCT customer_id FROM orders

-- Query B
SELECT customer_id FROM orders
```

**Are they equivalent?**

- If `customer_id` can repeat: **NO** (DISTINCT removes duplicates)
- If each customer has at most one order: **YES** (no duplicates to remove)

sql_equiv says: `NOT EQUIVALENT` (conservative)

**You know**: Each customer has at most one order (business rule)

**Resolution**: You must verify this constraint holds in your system.

#### Example 2: Value Range Assumption

```sql
-- Query A
SELECT * FROM products WHERE price > 0

-- Query B
SELECT * FROM products
```

**Are they equivalent?**

- If prices can be zero or negative: **NO**
- If business rule says "all prices are positive": **YES**

sql_equiv says: `NOT EQUIVALENT`

**You know**: Price CHECK constraint enforces price > 0

#### Example 3: Referential Integrity

```sql
-- Query A
SELECT o.*, c.name
FROM orders o
JOIN customers c ON o.customer_id = c.id

-- Query B
SELECT o.*, c.name
FROM orders o
LEFT JOIN customers c ON o.customer_id = c.id
```

**Are they equivalent?**

- If orders can have invalid customer_ids: **NO** (LEFT JOIN keeps orphans)
- If FOREIGN KEY enforces valid customer_id: **YES** (no orphans exist)

sql_equiv says: `NOT EQUIVALENT`

**You know**: FOREIGN KEY constraint exists

### How to Handle Level 3

1. **Recognize** that the equivalence requires context
2. **Document** the assumption needed
3. **Verify** the assumption holds in your system
4. **Proceed** with the transformation (with documentation)

```sql
-- EQUIVALENCE NOTE:
-- The following transformation assumes FOREIGN KEY constraint:
--   orders.customer_id REFERENCES customers.id
-- Verified in schema: schema.sql line 45
```

---

## Level 4: Undecidable (Impossible)

Some equivalences cannot be decided by any algorithm.

### What Makes Them Impossible

- Would require solving undecidable problems
- Infinite search space
- Depend on arbitrary computation

### Examples

#### Example 1: User-Defined Functions

```sql
SELECT * FROM t WHERE my_function(x) = 1
SELECT * FROM t WHERE my_other_function(x) = 1
```

If `my_function` and `my_other_function` are arbitrary code, determining if they always return the same value is equivalent to the halting problem—provably undecidable.

#### Example 2: Recursive CTEs Without Bounds

```sql
WITH RECURSIVE cte AS (
  SELECT 1 AS n
  UNION ALL
  SELECT n + 1 FROM cte WHERE complicated_condition(n)
)
SELECT * FROM cte
```

Determining what this returns requires knowing if the recursion terminates—again, undecidable in general.

#### Example 3: External Dependencies

```sql
SELECT * FROM t WHERE RANDOM() > 0.5
```

Non-deterministic functions make equivalence meaningless—even the query isn't equivalent to itself!

### How to Handle Level 4

1. **Recognize** the undecidability
2. **Simplify** if possible (bound recursion, remove UDFs)
3. **Test** instead of prove (if simplification isn't possible)
4. **Document** the limitation

---

## Decision Flowchart

```
                    ┌─────────────────────┐
                    │ Are the queries     │
                    │ structurally        │
                    │ similar?            │
                    └──────────┬──────────┘
                               │
              ┌────────────────┴────────────────┐
              │ YES                             │ NO
              ▼                                 ▼
    ┌─────────────────┐              ┌─────────────────────┐
    │ Level 1:        │              │ Do they use the     │
    │ Syntactic       │              │ same SQL features?  │
    │ (tool handles)  │              └──────────┬──────────┘
    └─────────────────┘                         │
                                   ┌────────────┴────────────┐
                                   │ YES                     │ NO
                                   ▼                         ▼
                        ┌─────────────────┐      ┌─────────────────────┐
                        │ Level 2:        │      │ Does equivalence    │
                        │ Semantic        │      │ require external    │
                        │ (tool + hints)  │      │ knowledge?          │
                        └─────────────────┘      └──────────┬──────────┘
                                                            │
                                               ┌────────────┴────────────┐
                                               │ YES                     │ NO
                                               ▼                         ▼
                                    ┌─────────────────┐      ┌─────────────────┐
                                    │ Level 3:        │      │ Contains UDFs,  │
                                    │ Contextual      │      │ RANDOM, or      │
                                    │ (human verify)  │      │ unbounded       │
                                    └─────────────────┘      │ recursion?      │
                                                             └────────┬────────┘
                                                                      │
                                                         ┌────────────┴────────────┐
                                                         │ YES                     │ NO
                                                         ▼                         ▼
                                              ┌─────────────────┐      ┌─────────────────┐
                                              │ Level 4:        │      │ Check tool      │
                                              │ Undecidable     │      │ output—might be │
                                              │ (cannot prove)  │      │ a known pattern │
                                              └─────────────────┘      └─────────────────┘
```

---

## Practical Examples

### Example A: Optimizer Transformation

You're reviewing an optimizer that rewrites:

```sql
-- Before
SELECT * FROM orders o
WHERE o.customer_id IN (
  SELECT c.id FROM customers c WHERE c.country = 'US'
)

-- After
SELECT o.* FROM orders o
INNER JOIN customers c ON o.customer_id = c.id
WHERE c.country = 'US'
```

**Analysis:**
- Structurally different: subquery → join
- Same SQL features: SELECT, WHERE, JOIN
- No external knowledge needed

**Level**: 2 (Semantic) → Tool can verify with `in_to_semijoin` theorem ✓

### Example B: Manual Rewrite for Performance

You're manually rewriting:

```sql
-- Before (slow)
SELECT * FROM big_table WHERE category IN ('A', 'B', 'C')

-- After (fast, uses index)
SELECT * FROM big_table WHERE category = 'A'
UNION ALL
SELECT * FROM big_table WHERE category = 'B'
UNION ALL
SELECT * FROM big_table WHERE category = 'C'
```

**Analysis:**
- Structurally different
- Same SQL features
- No external knowledge needed

**Level**: 2 (Semantic) → Tool can verify (IN expansion theorem) ✓

### Example C: Business Rule Dependent

```sql
-- Before
SELECT * FROM employees WHERE department_id IS NOT NULL

-- After
SELECT * FROM employees
```

**Analysis:**
- Someone claims "all employees have departments"
- Requires knowledge: is NULL allowed in department_id?

**Level**: 3 (Contextual) → Check NOT NULL constraint manually

### Example D: UDF Involved

```sql
-- Before
SELECT * FROM orders WHERE validate_order(order_data) = TRUE

-- After
SELECT * FROM orders WHERE order_data IS NOT NULL AND LENGTH(order_data) > 0
```

**Analysis:**
- validate_order() is a custom function
- We can't know if it's equivalent to the NULL/LENGTH check

**Level**: 4 (Undecidable) → Must test, cannot prove

---

## Summary Table

| Level | Recognizable By | Tool Support | Your Action |
|-------|-----------------|--------------|-------------|
| 1 Syntactic | Same structure, minor differences | ✅ Automatic | Trust the tool |
| 2 Semantic | Different structure, standard SQL | ✅ With theorems | Check proof |
| 3 Contextual | Equivalence needs "but in our data..." | ⚠️ Flags as NOT EQUIVALENT | Verify constraint |
| 4 Undecidable | UDFs, RANDOM, unbounded recursion | ❌ Cannot help | Test, don't prove |

---

## Exercises

### Exercise 1
Classify this equivalence:
```sql
SELECT * FROM t WHERE x > 5 AND x < 10
SELECT * FROM t WHERE x BETWEEN 6 AND 9
```

<details>
<summary>Answer</summary>

**Level 2 (Semantic)** - but actually NOT EQUIVALENT!

`x > 5 AND x < 10` includes values like 5.5, 9.9
`x BETWEEN 6 AND 9` only includes integers 6, 7, 8, 9

If x is an integer, they're equivalent. If x is a float, they're not.

This shows why formal verification matters—easy to miss edge cases!

</details>

### Exercise 2
Classify this equivalence:
```sql
SELECT DISTINCT a, b FROM t
SELECT a, b FROM t GROUP BY a, b
```

<details>
<summary>Answer</summary>

**Level 2 (Semantic)** - EQUIVALENT ✓

DISTINCT and GROUP BY both remove duplicates. With no aggregates, GROUP BY acts like DISTINCT.

sql_equiv can prove this using the `distinct_group_by` theorem.

</details>

### Exercise 3
Classify this equivalence:
```sql
SELECT * FROM orders WHERE status = 'shipped'
SELECT * FROM orders WHERE status IN ('shipped', 'delivered')
```

<details>
<summary>Answer</summary>

**Level 3 (Contextual)**

- If 'delivered' orders exist: NOT EQUIVALENT
- If business rule says "we change status to 'archived' not 'delivered'": EQUIVALENT

Requires domain knowledge to answer.

</details>

---

## Next Steps

- [Tutorial 3: NULL and Three-Valued Logic](03-null-logic.md) - The #1 source of unexpected non-equivalence
- [Tutorial 7: Formal Methods Intro](07-formal-methods-intro.md) - Understand *how* the proofs work
