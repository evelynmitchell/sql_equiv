# Design Review Process for Optimizer Modules

This document outlines a lightweight design review process to catch semantic issues before implementation.

## Motivation

During PR reviews for PredicatePushdown and JoinReordering, several issues were caught late:
- CROSS JOIN converted to INNER JOIN (lost semantic distinction)
- LEFT JOIN predicates incorrectly placed in ON clause (changed query results)
- Column references not transformed when pushing into subqueries
- Missing edge cases for FULL OUTER JOIN

These could have been caught earlier with upfront design discussion.

## Process Overview

```
1. Design Doc (30 min - 1 hour)
         ↓
2. Async Review (1-2 days)
         ↓
3. Implementation (with design as guide)
         ↓
4. PR Review (fewer iterations)
```

---

## Step 1: Write a Design Doc

Before implementing a new optimizer transformation, create a GitHub issue with:

### Required Sections

**1. Transformation Description**
- What does this optimization do?
- When should it apply?
- What performance benefit does it provide?

**2. Correctness Invariant**
- What property must be preserved?
- State it precisely (this becomes the axiom/theorem)

Example:
> For any database and predicate, filtering the pushed FROM clause by the remaining predicate produces the same rows as filtering the original FROM clause by the full predicate.

**3. Join Type Behavior Table**

| Join Type | Behavior | Why |
|-----------|----------|-----|
| INNER | ... | ... |
| LEFT | ... | ... |
| RIGHT | ... | ... |
| FULL | ... | ... |
| CROSS | ... | ... |

**4. Edge Cases**
- Subqueries (scope boundaries)
- Aggregates and GROUP BY
- NULL handling
- Empty tables
- Column qualification (qualified vs unqualified)

**5. Examples**

For each join type, show before/after:
```sql
-- Before
SELECT * FROM a LEFT JOIN b ON a.id = b.a_id WHERE b.x > 10

-- After (WRONG - changes semantics)
SELECT * FROM a LEFT JOIN b ON a.id = b.a_id AND b.x > 10

-- After (CORRECT - predicate stays in WHERE)
SELECT * FROM a LEFT JOIN b ON a.id = b.a_id WHERE b.x > 10
```

**6. Test Scenarios**
List the test cases you plan to write (reference TESTING_CHECKLIST.md).

---

## Step 2: Async Review

- Post the design doc as a GitHub issue
- Tag relevant reviewers
- Allow 1-2 days for feedback
- Focus review on:
  - Is the correctness invariant stated correctly?
  - Are edge cases covered?
  - Do the examples look right?
  - Any join types or SQL features missed?

---

## Step 3: Implementation

With an approved design:
- The correctness invariant becomes your axiom
- The examples become your tests
- The edge cases guide your safety checks
- Fewer surprises during PR review

---

## Step 4: PR Review

PR review now focuses on:
- Does the implementation match the design?
- Are all planned tests present?
- Code quality and style

Rather than:
- Did you consider LEFT JOIN semantics? (already covered)
- What about subqueries? (already covered)

---

## Template

```markdown
## [Optimization Name] Design

### Description
[What does this do and why?]

### Correctness Invariant
[Precise statement of what must be preserved]

### Join Type Behavior

| Join Type | Behavior | Rationale |
|-----------|----------|-----------|
| INNER | | |
| LEFT | | |
| RIGHT | | |
| FULL | | |
| CROSS | | |

### Edge Cases
- [ ] Subqueries
- [ ] Aggregates / GROUP BY
- [ ] NULL values
- [ ] Qualified vs unqualified columns
- [ ] [Other relevant cases]

### Examples

#### INNER JOIN
\`\`\`sql
-- Before
-- After
\`\`\`

#### LEFT JOIN
\`\`\`sql
-- Before
-- After (and why)
\`\`\`

[Continue for other join types...]

### Test Scenarios
[List from TESTING_CHECKLIST.md with any additions]
```

---

## When to Skip This Process

For trivial changes:
- Bug fixes with obvious solutions
- Code cleanup / refactoring without semantic changes
- Adding tests for existing functionality

Use judgment - if you're unsure whether a change affects correctness, write the design doc.
