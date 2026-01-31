# Equivalence Catalog

A reference of proven SQL transformations organized by category.

---

## How to Use This Catalog

Each entry shows:
- **Transformation**: Before → After
- **Theorem**: Formal name in sql_equiv
- **Conditions**: When the transformation is valid
- **Pitfalls**: Common mistakes

---

## 1. Boolean Expression Equivalences

### 1.1 Commutativity

| Before | After | Theorem |
|--------|-------|---------|
| `A AND B` | `B AND A` | `and_comm` |
| `A OR B` | `B OR A` | `or_comm` |
| `A = B` | `B = A` | `eq_comm` |
| `A + B` | `B + A` | `add_comm` |
| `A * B` | `B * A` | `mul_comm` |

### 1.2 Associativity

| Before | After | Theorem |
|--------|-------|---------|
| `(A AND B) AND C` | `A AND (B AND C)` | `and_assoc` |
| `(A OR B) OR C` | `A OR (B OR C)` | `or_assoc` |

### 1.3 Distributivity

| Before | After | Theorem |
|--------|-------|---------|
| `A AND (B OR C)` | `(A AND B) OR (A AND C)` | `and_or_distrib` |
| `A OR (B AND C)` | `(A OR B) AND (A OR C)` | `or_and_distrib` |

### 1.4 Absorption

| Before | After | Theorem |
|--------|-------|---------|
| `A AND (A OR B)` | `A` | `and_absorb_or` |
| `A OR (A AND B)` | `A` | `or_absorb_and` |
| `A OR TRUE` | `TRUE` | `or_true` |
| `A AND FALSE` | `FALSE` | `and_false` |
| `A OR FALSE` | `A` | `or_false` |
| `A AND TRUE` | `A` | `and_true` |

### 1.5 Negation

| Before | After | Theorem | Conditions |
|--------|-------|---------|------------|
| `NOT NOT A` | `A` | `double_neg` | Two-valued logic only |
| `NOT (A AND B)` | `NOT A OR NOT B` | `de_morgan_and` | |
| `NOT (A OR B)` | `NOT A AND NOT B` | `de_morgan_or` | |
| `NOT (A = B)` | `A <> B` | `not_eq` | |
| `NOT (A < B)` | `A >= B` | `not_lt` | Nulls handled |

### 1.6 Idempotence

| Before | After | Theorem |
|--------|-------|---------|
| `A AND A` | `A` | `and_idempotent` |
| `A OR A` | `A` | `or_idempotent` |

---

## 2. Comparison Equivalences

### 2.1 Range Expressions

| Before | After | Theorem |
|--------|-------|---------|
| `A BETWEEN B AND C` | `A >= B AND A <= C` | `between_expand` |
| `A IN (x, y, z)` | `A = x OR A = y OR A = z` | `in_expand` |
| `A > B OR A = B` | `A >= B` | `gt_or_eq` |
| `A < B OR A = B` | `A <= B` | `lt_or_eq` |

### 2.2 Redundant Conditions

| Before | After | Theorem | Conditions |
|--------|-------|---------|------------|
| `A > 5 AND A > 3` | `A > 5` | `range_absorb` | |
| `A > 5 OR A > 3` | `A > 3` | `range_absorb_or` | |
| `A = 5 AND A > 3` | `A = 5` | `eq_absorbs_range` | |

### 2.3 NULL Comparisons

| Before | After | Theorem |
|--------|-------|---------|
| `A = NULL` | `UNKNOWN` | `eq_null_unknown` |
| `A IS NULL` | (proper check) | `is_null_defined` |
| `NOT (A IS NULL)` | `A IS NOT NULL` | `not_is_null` |

---

## 3. JOIN Equivalences

### 3.1 INNER JOIN Properties

| Before | After | Theorem |
|--------|-------|---------|
| `A INNER JOIN B ON c` | `B INNER JOIN A ON c` | `inner_join_comm` |
| `(A JOIN B) JOIN C` | `A JOIN (B JOIN C)` | `inner_join_assoc` |
| `A CROSS JOIN B` | `B CROSS JOIN A` | `cross_join_comm` |
| `A CROSS JOIN B WHERE c` | `A INNER JOIN B ON c` | `cross_to_inner` |

### 3.2 OUTER JOIN Conversions

| Before | After | Theorem | Conditions |
|--------|-------|---------|------------|
| `A LEFT JOIN B` | `A INNER JOIN B` | `left_to_inner` | FK + NOT NULL on join col |
| `A LEFT JOIN B` | `B RIGHT JOIN A` | `left_right_swap` | |
| `A RIGHT JOIN B` | `B LEFT JOIN A` | `right_left_swap` | |

### 3.3 Predicate Placement

| Before | After | Theorem | Conditions |
|--------|-------|---------|------------|
| `A JOIN B ON c WHERE p` | `A JOIN B ON c AND p` | `where_to_on_inner` | INNER join only |
| `A JOIN B ON c AND p` | `A JOIN B ON c WHERE p` | `on_to_where_inner` | INNER join only |

⚠️ **Warning**: These do NOT work for OUTER joins!

---

## 4. Subquery Equivalences

### 4.1 IN/EXISTS Conversions

| Before | After | Theorem | Conditions |
|--------|-------|---------|------------|
| `x IN (SELECT y FROM s)` | `EXISTS (SELECT 1 FROM s WHERE s.y = x)` | `in_to_exists` | |
| `x NOT IN (SELECT y FROM s)` | `NOT EXISTS (...)` | `not_in_to_not_exists` | **s.y NOT NULL** |

### 4.2 Subquery Flattening

| Before | After | Theorem | Conditions |
|--------|-------|---------|------------|
| `... WHERE x IN (SELECT y FROM s)` | `... JOIN s ON x = s.y` + DISTINCT | `in_to_semijoin` | Add DISTINCT |
| `... WHERE EXISTS (SELECT ...)` | Semi-join | `exists_to_semijoin` | |
| Scalar subquery | LEFT JOIN | `scalar_to_join` | Subquery returns ≤ 1 row |

---

## 5. Aggregate Equivalences

### 5.1 DISTINCT and GROUP BY

| Before | After | Theorem |
|--------|-------|---------|
| `SELECT DISTINCT a, b` | `SELECT a, b GROUP BY a, b` | `distinct_to_group_by` |
| `SELECT a, b GROUP BY a, b` | `SELECT DISTINCT a, b` | `group_by_to_distinct` |

### 5.2 HAVING and WHERE

| Before | After | Theorem | Conditions |
|--------|-------|---------|------------|
| `GROUP BY a HAVING a = 1` | `WHERE a = 1 GROUP BY a` | `having_to_where` | Predicate on GROUP BY col |

### 5.3 Aggregate Properties

| Before | After | Theorem |
|--------|-------|---------|
| `COUNT(*) ... GROUP BY` | `SUM(partial_counts)` | `count_decompose` |
| `SUM(x) ... GROUP BY` | `SUM(partial_sums)` | `sum_decompose` |
| `MAX(x) ... GROUP BY` | `MAX(partial_maxes)` | `max_decompose` |
| `MIN(x) ... GROUP BY` | `MIN(partial_mins)` | `min_decompose` |

⚠️ AVG cannot be decomposed directly: use `SUM(x)/COUNT(x)`

---

## 6. Set Operation Equivalences

| Before | After | Theorem |
|--------|-------|---------|
| `A UNION B` | `B UNION A` | `union_comm` |
| `A INTERSECT B` | `B INTERSECT A` | `intersect_comm` |
| `A UNION A` | `A` | `union_idempotent` |
| `A INTERSECT A` | `A` | `intersect_idempotent` |
| `A UNION ALL B` | `B UNION ALL A` | `union_all_comm` |

---

## 7. Normalization Equivalences

| Before | After | Theorem |
|--------|-------|---------|
| Nested ANDs | Flattened AND list | `flatten_and` |
| Nested ORs | Flattened OR list | `flatten_or` |
| `((A))` | `A` | `remove_parens` |
| `a AND b` (unordered) | Canonical order | `normalize_and` |

---

## Quick Lookup by Goal

**Want to simplify a WHERE clause?**
→ See Section 1 (Boolean) and Section 2 (Comparison)

**Want to reorder JOINs?**
→ See Section 3.1 (INNER only!)

**Want to flatten a subquery?**
→ See Section 4

**Want to push down predicates?**
→ See Section 3.3 (pitfalls for OUTER joins)

**Want to rewrite aggregates?**
→ See Section 5

---

## Unsafe Transformations (NOT in Catalog)

These look equivalent but often aren't:

| Transformation | Why It Fails |
|----------------|--------------|
| `NOT IN` → `NOT EXISTS` | NULL handling differs |
| `LEFT JOIN` → `INNER JOIN` | Loses unmatched rows |
| `SELECT *` reorder columns | Column order changes |
| `IN subquery` → `JOIN` | Duplicates without DISTINCT |
| `COUNT(*)` ↔ `COUNT(col)` | NULL handling differs |
| `AVG(x)` → `SUM(x)/COUNT(*)` | NULL handling differs |

See [Pitfalls](pitfalls.md) for details.
