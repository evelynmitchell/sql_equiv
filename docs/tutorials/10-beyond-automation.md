# Tutorial 10: When the Tool Can't Help

**Time:** 30 minutes
**Prerequisites:** Tutorial 9

---

## Learning Objectives

By the end of this tutorial, you will:
- Recognize queries that are fundamentally hard or impossible to verify
- Know workarounds and alternative approaches
- Make informed decisions about when to proceed without proof

---

## Outline

### 1. Categories of Unsupported Queries (5 min)

**Unsupported SQL features:**
- User-defined functions (UDFs)
- Stored procedures
- Database-specific syntax
- Features not in AST (PIVOT, CONNECT BY, etc.)

**Inherently undecidable:**
- Recursive CTEs without bounds
- Non-deterministic functions (RANDOM, NOW)
- Queries with side effects

**Context-dependent:**
- Relies on CHECK constraints
- Depends on triggers
- Assumes specific data distribution

### 2. Workarounds for UDFs (7 min)

**Option A: Inline the UDF**
```sql
-- Before (can't verify)
SELECT * FROM t WHERE validate(x)

-- After (if validate checks x > 0 AND x < 100)
SELECT * FROM t WHERE x > 0 AND x < 100
```

**Option B: Axiomatize the UDF**
```lean
-- Assume UDF behavior
axiom validate_equiv (x : Value) : validate x = (x > 0 && x < 100)
```

**Option C: Test instead of prove**
- Property-based testing with many inputs
- Document that verification is testing-based

### 3. Handling Recursive CTEs (7 min)

**The problem:**
```sql
WITH RECURSIVE cte AS (
  SELECT 1 as n
  UNION ALL
  SELECT n + 1 FROM cte WHERE n < ?  -- Termination depends on ?
)
SELECT * FROM cte
```

**Workaround: Bound the recursion**
```sql
WITH RECURSIVE cte AS (
  SELECT 1 as n, 1 as depth
  UNION ALL
  SELECT n + 1, depth + 1 FROM cte WHERE n < ? AND depth < 1000
)
SELECT n FROM cte
```

**For equivalence:** Prove properties for bounded version, note limitation.

### 4. Non-Deterministic Queries (5 min)

**Queries that aren't equivalent to themselves:**
```sql
SELECT RANDOM()              -- Different each time
SELECT CURRENT_TIMESTAMP     -- Changes
SELECT * FROM t              -- Row order undefined
```

**Approach:**
- For RANDOM: Treat as opaque; can't prove much
- For timestamps: Fix time for verification
- For ordering: Use bag semantics (ignore order)

### 5. Making Progress Without Full Verification (6 min)

**Partial verification:**
- Prove what you can
- Document what you can't
- Test the remainder

**Risk assessment template:**
```markdown
## Verification Status

Transformation: [describe]

### Verified Properties
- ✓ Preserves WHERE semantics (proven)
- ✓ Handles NULL correctly (proven)

### Unverified Properties
- ⚠ UDF `custom_check` assumed correct
- ⚠ Recursive CTE bounded to 1000 iterations

### Testing Performed
- 10,000 random inputs
- All production query patterns
- Edge cases: empty table, NULLs, duplicates

### Risk Level: MEDIUM
Proceeding because: [justification]

### Sign-off
Approved by: [name]
Date: [date]
```

---

## Decision Framework

```
Can sql_equiv verify it?
├─ YES → Use the proof ✓
└─ NO → Why not?
    ├─ Missing SQL feature → Request feature or use workaround
    ├─ Uses UDF → Inline, axiomatize, or test
    ├─ Recursive without bound → Add bound or test
    ├─ Non-deterministic → Redesign or accept limitation
    ├─ Context-dependent → Document assumptions, verify separately
    └─ Fundamentally undecidable → Test extensively, accept risk
```

---

## Exercises

1. **Classify the blocker**: Why can't these be verified automatically?
   ```sql
   a) SELECT * FROM t WHERE my_regex_match(x, '[0-9]+')
   b) SELECT * FROM t ORDER BY RANDOM() LIMIT 1
   c) WITH RECURSIVE ... (unbounded)
   d) SELECT * FROM t WHERE col = 'value'  -- col has CHECK constraint
   ```

2. **Propose workaround**: How would you handle each of the above?

3. **Write risk assessment**: For a real transformation you're considering

4. **Design test suite**: For a query pair that can't be formally verified

---

## Templates

### Axiom for UDF
```lean
/-- Assumed behavior of business_rule_check UDF -/
axiom business_rule_check_spec (x : Value) :
  business_rule_check x = (x.isPositive && x < maxLimit)
```

### Documentation for Unverified Transformation
```sql
-- =============================================================================
-- TRANSFORMATION: Flatten correlated subquery
-- STATUS: Partially verified
-- =============================================================================
-- PROVEN:
--   - Uncorrelated portion preserves semantics
--   - NULL handling correct
--
-- UNVERIFIED:
--   - UDF process_value(x) in SELECT assumed to be pure
--   - Behavior identical only if process_value has no side effects
--
-- TESTING:
--   - Compared results on 30 days production data
--   - 0 differences found (10M rows)
--
-- APPROVED BY: [name]
-- DATE: [date]
-- =============================================================================
```

---

## Key Takeaways

1. **Not everything can be proven** — and that's okay
2. **Workarounds exist** for many "impossible" cases
3. **Testing complements proving** — use both
4. **Documentation is crucial** when verification is incomplete
5. **Risk assessment** helps make informed decisions

---

## Further Reading

- [Pitfalls and Gotchas](reference/pitfalls.md) - Common sources of non-equivalence
- [Manual Proof Techniques](09-manual-proofs.md) - When automation fails
- Rice's Theorem - Why some properties are undecidable
