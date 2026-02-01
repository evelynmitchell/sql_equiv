# Tutorial 4: Join Transformations

**Time:** 30 minutes
**Prerequisites:** Tutorial 3

---

## Learning Objectives

By the end of this tutorial, you will:
- Know which join transformations preserve equivalence
- Understand when join order matters
- Apply join rewriting rules safely

---

## Outline

### 1. Join Fundamentals Review (5 min)
- INNER, LEFT, RIGHT, FULL, CROSS joins
- Join as filtered Cartesian product
- ON clause vs WHERE clause semantics

### 2. INNER JOIN Properties (7 min)
- **Commutativity**: `A JOIN B` ≡ `B JOIN A`
- **Associativity**: `(A JOIN B) JOIN C` ≡ `A JOIN (B JOIN C)`
- Why these enable join reordering optimizations
- Proof sketches for each property

### 3. OUTER JOIN Restrictions (8 min)
- LEFT JOIN is NOT commutative: `A LEFT JOIN B` ≢ `B LEFT JOIN A`
- LEFT JOIN is NOT associative in general
- When can we reorder outer joins? (Limited cases)
- Converting outer to inner: requires NOT NULL knowledge

### 4. JOIN ↔ Subquery Conversions (5 min)
- IN subquery → Semi-join (INNER JOIN + DISTINCT)
- EXISTS → Semi-join
- NOT IN → Anti-join (LEFT JOIN + NULL check) — with caveats!
- NOT EXISTS → Anti-join
- Scalar subquery → LEFT JOIN with uniqueness constraint

### 5. Predicate Placement (5 min)
- ON clause vs WHERE clause for INNER joins (equivalent)
- ON clause vs WHERE clause for OUTER joins (NOT equivalent!)
- Pushing predicates through joins
- When pushdown is safe vs unsafe

---

## Exercises

1. **Commutativity check**: Which are equivalent?
   - `A INNER JOIN B` vs `B INNER JOIN A`
   - `A LEFT JOIN B` vs `B LEFT JOIN A`
   - `A LEFT JOIN B` vs `B RIGHT JOIN A`

2. **Predicate placement**: Move the WHERE to ON—is it safe?
   ```sql
   SELECT * FROM a LEFT JOIN b ON a.id = b.id WHERE b.status = 'active'
   ```

3. **Subquery to JOIN**: Convert and verify equivalence
   ```sql
   SELECT * FROM orders WHERE customer_id IN (SELECT id FROM vip)
   ```

4. **Multi-way join**: Reorder for efficiency (given cardinalities)

---

## Key Theorems

- `inner_join_comm`: A ⋈ B ≡ B ⋈ A
- `inner_join_assoc`: (A ⋈ B) ⋈ C ≡ A ⋈ (B ⋈ C)
- `left_join_not_comm`: Counterexample for A ⟕ B ≡ B ⟕ A
- `in_to_semijoin`: IN subquery to semi-join conversion
- `predicate_push_inner`: Safe to push predicates through inner joins
- `predicate_push_outer_unsafe`: Counterexample for outer join pushdown

---

## Pitfalls

| Transformation | Pitfall | Condition for Safety |
|----------------|---------|---------------------|
| LEFT → INNER | Loses unmatched rows | FK constraint + NOT NULL |
| Reorder LEFT joins | Changes result | Only specific patterns safe |
| IN → JOIN | May duplicate rows | Use DISTINCT or EXISTS |
| NOT IN → LEFT JOIN | NULL handling | Source has no NULLs |
| ON → WHERE (outer) | Filters unmatched rows | Only for inner joins |
