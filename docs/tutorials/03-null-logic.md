# Tutorial 3: Understanding NULL and Three-Valued Logic

**Time:** 25 minutes
**Prerequisites:** Tutorial 2

---

## Learning Objectives

By the end of this tutorial, you will:
- Understand why SQL uses three-valued logic (TRUE, FALSE, UNKNOWN)
- Recognize common NULL-related equivalence failures
- Apply safe patterns for NULL-handling queries

---

## Outline

### 1. Why NULL Exists (5 min)
- Missing vs inapplicable vs unknown data
- NULL is not a value—it's the absence of a value
- Why `NULL = NULL` is UNKNOWN, not TRUE

### 2. Three-Valued Logic Truth Tables (5 min)
- AND truth table with UNKNOWN
- OR truth table with UNKNOWN
- NOT truth table with UNKNOWN
- Why `NOT UNKNOWN = UNKNOWN`

### 3. NULL in Comparisons (5 min)
- `x = NULL` is always UNKNOWN
- `x <> NULL` is always UNKNOWN
- IS NULL vs = NULL
- IS DISTINCT FROM (NULL-safe equality)

### 4. NULL in Aggregates (5 min)
- COUNT(*) vs COUNT(column)
- SUM, AVG, MIN, MAX ignore NULLs
- Empty set: COUNT returns 0, others return NULL
- COALESCE for default values

### 5. The NOT IN Trap (5 min)
- Why `x NOT IN (1, 2, NULL)` returns no rows
- Safe alternatives: NOT EXISTS, LEFT JOIN with NULL check
- When IN is safe vs dangerous

---

## Exercises

1. **Truth table practice**: Evaluate `(TRUE AND UNKNOWN) OR FALSE`
2. **Find the bug**: Why does this query return no results?
3. **Fix the query**: Rewrite NOT IN safely
4. **NULL in GROUP BY**: What happens to NULL groups?

---

## Key Theorems

- `null_eq_unknown`: `NULL = x` evaluates to UNKNOWN for any x
- `is_null_complete`: `x IS NULL` is TRUE iff x is NULL, FALSE otherwise
- `not_in_null_trap`: Formal statement of the NOT IN with NULL issue

---

## Common Mistakes

| Pattern | Problem | Safe Alternative |
|---------|---------|------------------|
| `WHERE x = NULL` | Always UNKNOWN | `WHERE x IS NULL` |
| `WHERE x <> NULL` | Always UNKNOWN | `WHERE x IS NOT NULL` |
| `NOT IN (subquery)` | Fails if subquery has NULLs | `NOT EXISTS` |
| `COUNT(nullable_col)` | Excludes NULLs | `COUNT(*)` or `COUNT(COALESCE(...))` |
