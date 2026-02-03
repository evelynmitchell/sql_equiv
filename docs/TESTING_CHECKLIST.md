# Optimizer Module Testing Checklist

Use this checklist when implementing new optimizer modules to ensure comprehensive test coverage before PR submission.

## General Principles

- Test both positive cases (transformation applies) and negative cases (transformation blocked)
- Include edge cases discovered during code review
- Verify semantic preservation, not just structural changes
- Test interactions with other SQL features (subqueries, aggregates, etc.)

---

## Predicate Pushdown

### Base Cases
- [ ] Base table - predicate remains in WHERE
- [ ] Literal-only predicate (no column refs)

### Join Types
- [ ] INNER JOIN - predicate pushed to ON clause
- [ ] CROSS JOIN - converted to INNER JOIN when predicate added (CROSS ignores ON)
- [ ] LEFT JOIN - right-side predicate remains in WHERE (not ON)
- [ ] LEFT JOIN - left-side predicate to base table remains in WHERE
- [ ] RIGHT JOIN - left-side predicate remains in WHERE (not ON)
- [ ] RIGHT JOIN - right-side predicate to base table remains in WHERE
- [ ] FULL OUTER JOIN - predicate remains in WHERE (no pushdown)

### Predicate Placement
- [ ] Left-only columns - pushed to left side
- [ ] Right-only columns - pushed to right side
- [ ] Both sides referenced - added to ON for INNER/CROSS
- [ ] Existing ON clause - new predicate combined with AND

### Column References
- [ ] Qualified columns (table.column)
- [ ] Unqualified columns - handled correctly (typically ON clause for INNER)
- [ ] Column transformation when pushing into subquery (sub.id -> t.id)

### Subquery Pushdown
- [ ] Simple subquery - predicate pushed to inner WHERE
- [ ] Blocked by projection - column not in SELECT
- [ ] GROUP BY with grouping key - allowed
- [ ] GROUP BY with non-grouping column - blocked
- [ ] Aggregate in predicate - blocked
- [ ] Qualified predicate referencing subquery alias

### Multiple Predicates
- [ ] Multiple AND conjuncts - each pushed independently
- [ ] Nested AND expressions - flattened and pushed

---

## Join Reordering

### Safety Checks
- [ ] Single table - no-op
- [ ] INNER JOIN - can reorder
- [ ] CROSS JOIN - can reorder
- [ ] LEFT JOIN - cannot reorder (returns unchanged)
- [ ] RIGHT JOIN - cannot reorder
- [ ] FULL OUTER JOIN - cannot reorder
- [ ] Mixed join types - cannot reorder

### Reordering Behavior
- [ ] Two tables - produces valid join
- [ ] Three+ tables - verify cost-based ordering
- [ ] Predicates preserved after reorder
- [ ] Predicate count unchanged

### Join Type Preservation
- [ ] INNER JOIN with predicates - stays INNER
- [ ] CROSS JOIN (no predicates) - stays CROSS
- [ ] Mixed INNER/CROSS - appropriate type per join

### Cost Estimation
- [ ] Cross join cost = row1 * row2
- [ ] Filtered join cost = row1 * row2 * selectivity
- [ ] Greedy algorithm joins smallest tables first

### Graph/Node Operations
- [ ] Leaf extraction from nested joins
- [ ] Edge detection between tables
- [ ] Node combination preserves table lists

---

## Expression Normalization

### Commutative Operators
- [ ] AND - operands sorted
- [ ] OR - operands sorted
- [ ] ADD - operands sorted
- [ ] MUL - operands sorted
- [ ] EQ - operands sorted

### Non-Commutative Operators
- [ ] SUB - order preserved
- [ ] DIV - order preserved
- [ ] LT/GT/LE/GE - order preserved

### Nested Expressions
- [ ] Nested AND - flattened and sorted
- [ ] Nested OR - flattened and sorted
- [ ] Mixed nesting - each level normalized

### Weight-Based Ordering
- [ ] Literals before columns
- [ ] Columns before binary ops
- [ ] Consistent ordering for equivalent expressions

### All Expression Types
- [ ] Literals (int, string, bool, null)
- [ ] Column references
- [ ] Binary operations
- [ ] Unary operations (NOT, negative)
- [ ] BETWEEN
- [ ] IN list
- [ ] CASE expressions
- [ ] Function calls
- [ ] Aggregates
- [ ] Window functions

---

## Adding New Optimizer Modules

When creating a new optimizer transformation:

1. **Identify all SQL constructs affected** - joins, subqueries, aggregates, etc.
2. **List edge cases** - NULL handling, empty results, boundary conditions
3. **Define what "correct" means** - semantic preservation property
4. **Write tests before or during implementation** - not after
5. **Review this checklist** - adapt categories to your transformation
