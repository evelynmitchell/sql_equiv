# Tutorial 9: Manual Proof Techniques

**Time:** 45 minutes
**Prerequisites:** Tutorials 1-8

---

## What You'll Learn

- What to do when sql_equiv says "cannot prove"
- Manual reasoning techniques for SQL equivalence
- How to build convincing arguments without automation
- When to accept uncertainty and document assumptions

---

## When Automation Fails

sql_equiv can prove many equivalences automatically, but sometimes it says:

```
⚠ CANNOT DETERMINE EQUIVALENCE

The tool could not prove these queries equivalent or find a counterexample.
This doesn't mean they're not equivalent—it means manual analysis is needed.
```

This happens when:
1. The equivalence is true but requires reasoning the tool doesn't support
2. The equivalence depends on domain knowledge
3. The queries use features without formalized semantics
4. The proof would require complex induction or case analysis

---

## Manual Proof Strategies

### Strategy 1: Semantic Decomposition

Break the query into parts and reason about each.

**Example:**
```sql
-- Query A
SELECT * FROM orders
WHERE status = 'pending' AND (priority = 'high' OR priority = 'urgent')

-- Query B
SELECT * FROM orders
WHERE (status = 'pending' AND priority = 'high')
   OR (status = 'pending' AND priority = 'urgent')
```

**Manual proof:**

1. Let P = `status = 'pending'`
2. Let H = `priority = 'high'`
3. Let U = `priority = 'urgent'`

4. Query A: `P AND (H OR U)`
5. Query B: `(P AND H) OR (P AND U)`

6. By the distributive law of Boolean algebra:
   `P AND (H OR U) ≡ (P AND H) OR (P AND U)` ✓

7. Therefore, Query A ≡ Query B

**Documentation:**
```sql
-- EQUIVALENCE PROOF:
-- By Boolean distributive law: A AND (B OR C) = (A AND B) OR (A AND C)
-- Verified manually; distributive law is a tautology in Boolean algebra
```

---

### Strategy 2: Case Analysis

Enumerate all possible cases and show the results match.

**Example:**
```sql
-- Query A
SELECT * FROM t WHERE x IS NULL OR x = 0

-- Query B
SELECT * FROM t WHERE COALESCE(x, 0) = 0
```

**Manual proof via cases:**

| Case | x value | Query A WHERE | Query B WHERE | Match? |
|------|---------|---------------|---------------|--------|
| 1 | NULL | `TRUE OR UNKNOWN = TRUE` | `COALESCE(NULL,0)=0 → 0=0 = TRUE` | ✓ |
| 2 | 0 | `FALSE OR TRUE = TRUE` | `COALESCE(0,0)=0 → 0=0 = TRUE` | ✓ |
| 3 | 5 | `FALSE OR FALSE = FALSE` | `COALESCE(5,0)=0 → 5=0 = FALSE` | ✓ |
| 4 | -3 | `FALSE OR FALSE = FALSE` | `COALESCE(-3,0)=0 → -3=0 = FALSE` | ✓ |

All cases match → Queries are equivalent ✓

**Note:** Case 1 and 2 are the "interesting" cases; Case 3 and 4 represent "all other values."

---

### Strategy 3: Counterexample Search

If you suspect queries are NOT equivalent, find a counterexample.

**Example:**
```sql
-- Query A (someone's "optimization")
SELECT * FROM t WHERE x > 5 OR x < 10

-- Query B
SELECT * FROM t WHERE TRUE
```

**Are these equivalent?**

Let's think: "x > 5 OR x < 10"

- If x = 7: `TRUE OR TRUE = TRUE` ✓
- If x = 3: `FALSE OR TRUE = TRUE` ✓
- If x = 12: `TRUE OR FALSE = TRUE` ✓
- If x = NULL: `UNKNOWN OR UNKNOWN = UNKNOWN` ≠ TRUE ✗

**Counterexample found!**

When x is NULL, Query A returns UNKNOWN (row excluded), but Query B returns TRUE (row included).

```sql
-- COUNTEREXAMPLE:
-- Given: t = [(x: NULL)]
-- Query A returns: [] (empty, because NULL > 5 is UNKNOWN)
-- Query B returns: [(x: NULL)] (TRUE always matches)
-- Therefore: NOT EQUIVALENT
```

---

### Strategy 4: Algebraic Manipulation

Transform one query into the other using known equivalences.

**Example:**
```sql
-- Query A
SELECT DISTINCT customer_id FROM orders WHERE amount > 100

-- Query B
SELECT customer_id FROM orders WHERE amount > 100 GROUP BY customer_id
```

**Algebraic proof:**

```
Query A:
  = DISTINCT(π_customer_id(σ_amount>100(orders)))

  [DISTINCT is idempotent with GROUP BY on same columns]

  = π_customer_id(γ_customer_id(σ_amount>100(orders)))

  = Query B ✓
```

Where:
- π = projection (SELECT columns)
- σ = selection (WHERE)
- γ = grouping (GROUP BY)

**The key insight:** DISTINCT on columns X is equivalent to GROUP BY X (with no aggregates).

---

### Strategy 5: Semantic Argument

Argue from the *meaning* of the queries, not their structure.

**Example:**
```sql
-- Query A
SELECT * FROM orders o
WHERE EXISTS (SELECT 1 FROM premium_customers p WHERE p.id = o.customer_id)

-- Query B
SELECT o.* FROM orders o
INNER JOIN premium_customers p ON p.id = o.customer_id
```

**Wait—are these actually equivalent?**

**Semantic analysis:**

Query A returns: Orders where *at least one* matching premium_customer exists

Query B returns: Orders joined with premium_customers

**Problem:** If a customer appears multiple times in premium_customers, Query B returns duplicate orders!

```sql
-- COUNTEREXAMPLE:
-- orders: [(id: 1, customer_id: 100)]
-- premium_customers: [(id: 100), (id: 100)]  -- duplicate!
--
-- Query A returns: [(id: 1, customer_id: 100)]  -- one row
-- Query B returns: [(id: 1, customer_id: 100),
--                   (id: 1, customer_id: 100)]  -- two rows!
--
-- NOT EQUIVALENT (unless premium_customers.id is UNIQUE)
```

**Correct equivalence (with DISTINCT):**
```sql
-- Query B (corrected)
SELECT DISTINCT o.* FROM orders o
INNER JOIN premium_customers p ON p.id = o.customer_id
```

---

### Strategy 6: Constraint-Dependent Reasoning

Some equivalences hold only under certain constraints.

**Example:**
```sql
-- Query A
SELECT * FROM orders o
LEFT JOIN customers c ON o.customer_id = c.id

-- Query B
SELECT * FROM orders o
INNER JOIN customers c ON o.customer_id = c.id
```

**Analysis:**

These are equivalent **if and only if:**
- Every `orders.customer_id` has a matching `customers.id`

This holds when:
- `orders.customer_id` has a FOREIGN KEY to `customers.id`, OR
- `orders.customer_id` is NOT NULL and business logic guarantees validity

**Documentation:**
```sql
-- CONDITIONAL EQUIVALENCE:
-- Query A ≡ Query B IF:
--   FOREIGN KEY (orders.customer_id) REFERENCES customers(id)
--   AND orders.customer_id IS NOT NULL
--
-- Verified: Schema defines FK constraint (schema.sql:45)
-- Verified: customer_id column is NOT NULL (schema.sql:23)
```

---

## Building a Convincing Argument

When you can't get machine-checked proof, build a human-readable argument:

### Template for Manual Equivalence Proof

```markdown
## Equivalence Claim

**Query A:**
```sql
[Query A here]
```

**Query B:**
```sql
[Query B here]
```

## Proof Strategy
[Case analysis / Algebraic manipulation / Semantic argument]

## Proof

### Step 1: [Description]
[Details]

### Step 2: [Description]
[Details]

### Step N: [Conclusion]
[Therefore Query A ≡ Query B]

## Assumptions
- [List any required constraints]
- [List any domain assumptions]

## Edge Cases Considered
- NULL values: [How handled]
- Empty tables: [How handled]
- Duplicates: [How handled]

## Confidence Level
[High/Medium/Low] - [Explanation]

## Reviewer Sign-off
Reviewed by: [Name]
Date: [Date]
```

---

## Example: Complete Manual Proof

### Equivalence Claim

**Query A:**
```sql
SELECT department, AVG(salary) as avg_sal
FROM employees
WHERE hire_date > '2020-01-01'
GROUP BY department
HAVING AVG(salary) > 50000
```

**Query B:**
```sql
SELECT department, avg_sal
FROM (
  SELECT department, AVG(salary) as avg_sal
  FROM employees
  WHERE hire_date > '2020-01-01'
  GROUP BY department
) sub
WHERE avg_sal > 50000
```

### Proof Strategy
Algebraic manipulation showing HAVING is equivalent to filtering a derived table.

### Proof

**Step 1:** Identify the operations in Query A
```
Query A = HAVING_{AVG(salary)>50000}(
            GROUP BY_{department}(
              AVG(salary),
              σ_{hire_date>'2020-01-01'}(employees)
            )
          )
```

**Step 2:** Identify the operations in Query B
```
Query B = σ_{avg_sal>50000}(
            AS sub(
              GROUP BY_{department}(
                AVG(salary) AS avg_sal,
                σ_{hire_date>'2020-01-01'}(employees)
              )
            )
          )
```

**Step 3:** Apply HAVING equivalence
The HAVING clause filters groups after GROUP BY. This is semantically identical to:
1. Performing the GROUP BY with aggregates
2. Wrapping in a subquery
3. Filtering with WHERE on the aggregate result

Formally: `HAVING cond ≡ σ_cond ∘ γ`

**Step 4:** Verify column reference
- Query A: `AVG(salary) > 50000` references the aggregate directly
- Query B: `avg_sal > 50000` references the aliased column

These refer to the same computed value.

**Step 5:** Conclusion
By the HAVING-to-subquery equivalence:
Query A ≡ Query B ✓

### Assumptions
- None (this is a general SQL equivalence)

### Edge Cases Considered
- **NULL salaries:** AVG ignores NULLs; both queries handle identically
- **Empty groups:** Groups with no rows after WHERE don't appear in either result
- **No matching departments:** Both return empty result

### Confidence Level
**High** - This is a well-known transformation used by query optimizers.

---

## Common Pitfalls in Manual Proofs

### Pitfall 1: Forgetting NULL

```sql
-- WRONG claim: These are equivalent
SELECT * FROM t WHERE NOT (x > 5)
SELECT * FROM t WHERE x <= 5
```

**Counterexample:** If x is NULL
- `NOT (NULL > 5) = NOT UNKNOWN = UNKNOWN` → row excluded
- `NULL <= 5 = UNKNOWN` → row excluded

Wait, they both exclude the row? Let's check more carefully:

Actually, in this case they ARE equivalent because both expressions evaluate to UNKNOWN when x is NULL. But consider:

```sql
-- These are NOT equivalent!
SELECT * FROM t WHERE NOT (x = 5)
SELECT * FROM t WHERE x <> 5
```

Hmm, these are also equivalent. The real pitfall is:

```sql
-- NOT equivalent!
SELECT * FROM t WHERE x NOT IN (SELECT y FROM s)
SELECT * FROM t WHERE NOT EXISTS (SELECT 1 FROM s WHERE s.y = t.x)
```

If s contains NULL, the NOT IN version returns no rows (any comparison with NULL yields UNKNOWN, and NOT IN with UNKNOWN yields UNKNOWN).

### Pitfall 2: Assuming Column Uniqueness

```sql
-- Only equivalent if p.id is UNIQUE
SELECT * FROM orders WHERE customer_id IN (SELECT id FROM premium)
SELECT o.* FROM orders o JOIN premium p ON o.customer_id = p.id
```

### Pitfall 3: Ignoring Empty Tables

```sql
-- NOT equivalent when t is empty!
SELECT COUNT(*) FROM t
SELECT SUM(1) FROM t
```

When t is empty:
- `COUNT(*)` returns 0
- `SUM(1)` returns NULL

### Pitfall 4: ORDER BY Without LIMIT

```sql
-- NOT equivalent (unless both have ORDER BY)!
SELECT * FROM t ORDER BY x LIMIT 10
SELECT * FROM (SELECT * FROM t ORDER BY x) sub LIMIT 10
```

The inner ORDER BY may be optimized away by some databases!

---

## When to Give Up

Sometimes you can't prove equivalence. That's okay—document it:

```markdown
## Equivalence Status: UNVERIFIED

**Queries appear equivalent based on:**
- Manual inspection
- Testing with sample data
- Similar patterns in documentation

**Cannot formally prove because:**
- Involves UDF `custom_validate()`
- Would require induction over recursive CTE
- Depends on transaction isolation level

**Risk mitigation:**
- Added comprehensive test cases
- Monitoring for result differences in production
- Documented in runbook for manual verification

**Decision:** Proceeding with transformation.
**Owner:** [Name]
**Date:** [Date]
```

---

## Exercises

### Exercise 1
Prove or disprove:
```sql
SELECT * FROM t WHERE a = 1 OR a = 2 OR a = 3
SELECT * FROM t WHERE a IN (1, 2, 3)
```

<details>
<summary>Solution</summary>

**EQUIVALENT** ✓

**Proof:** By definition, `a IN (v1, v2, v3)` is equivalent to `a = v1 OR a = v2 OR a = v3`.

This is a syntactic equivalence—IN is literally defined as a disjunction of equalities.

**NULL case:** If a is NULL:
- `NULL = 1 OR NULL = 2 OR NULL = 3 = UNKNOWN OR UNKNOWN OR UNKNOWN = UNKNOWN`
- `NULL IN (1, 2, 3) = UNKNOWN`

Both handle NULL identically. ✓

</details>

### Exercise 2
Prove or disprove:
```sql
SELECT * FROM t WHERE x > ALL (SELECT y FROM s)
SELECT * FROM t WHERE x > (SELECT MAX(y) FROM s)
```

<details>
<summary>Solution</summary>

**NOT EQUIVALENT** in general!

**Counterexample:** When s is empty:
- `x > ALL (empty set)` is TRUE (vacuous truth)
- `x > (SELECT MAX(y) FROM s)` is `x > NULL = UNKNOWN`

Given: `t = [(x: 5)]`, `s = []`
- Query A returns: `[(x: 5)]` (5 > all zero elements = TRUE)
- Query B returns: `[]` (5 > NULL = UNKNOWN, filtered out)

**Conditional equivalence:** They ARE equivalent when s is guaranteed non-empty.

</details>

### Exercise 3
What constraint would make these equivalent?
```sql
SELECT DISTINCT * FROM orders
SELECT * FROM orders
```

<details>
<summary>Solution</summary>

**Equivalent if:** orders has a PRIMARY KEY (or any UNIQUE constraint covering all columns).

With a PRIMARY KEY, no duplicate rows can exist, so DISTINCT has no effect.

**Documentation:**
```sql
-- EQUIVALENT under constraint:
-- orders has PRIMARY KEY on (id)
-- Verified: schema.sql line 12
```

</details>

---

## Summary

| When Tool Says | Your Action |
|----------------|-------------|
| ✓ EQUIVALENT | Trust it, document the theorem used |
| ✗ NOT EQUIVALENT | Check the counterexample, it's real |
| ⚠ CANNOT DETERMINE | Apply manual proof techniques |

| Manual Technique | Best For |
|------------------|----------|
| Semantic decomposition | Complex Boolean expressions |
| Case analysis | NULL handling, edge cases |
| Counterexample search | Suspected non-equivalence |
| Algebraic manipulation | Standard transformations |
| Semantic argument | Understanding "why" |
| Constraint reasoning | Context-dependent equivalences |

---

## Next Steps

- [Tutorial 10: When the Tool Can't Help](10-beyond-automation.md) - Advanced cases
- [Pitfalls and Gotchas](reference/pitfalls.md) - Common mistakes
- [Equivalence Catalog](reference/equivalence-catalog.md) - Proven transformations to reference
