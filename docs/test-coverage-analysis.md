# Test Coverage Analysis

## Current State

The project has ~850+ discrete test cases across 9 test modules (`Test/`) plus 114 LSpec
property-based tests (`LSpecTests/`), organized into three layers:

| Layer | Files | Approach |
|-------|-------|----------|
| **Unit / functional** | `Test/*.lean` (9 modules) | Hand-written assertions against mock databases |
| **Property-based (custom)** | `Test/PropertyTest.lean` | Custom LCG RNG, 4 properties × 100 iterations |
| **Property-based (LSpec)** | `LSpecTests/*.lean` (4 modules) | SlimCheck generators, 114 properties |
| **Axiom coverage** | `Test/AxiomCoverageTest.lean` | Runtime validation of all declared axioms |
| **Proof verification** | `Test/EquivTest.lean` | 100+ `#check` directives for type-checking axioms |

### What is well-covered

- **Parsing**: 45 round-trip tests covering SELECT variants, WHERE, JOINs, GROUP BY,
  aggregates, subqueries, set operations, CTEs, DML, and parse-failure rejection
  (`Test/ParserTest.lean`).
- **Core expression evaluation**: Arithmetic, comparison, logical operators, basic NULL
  propagation, COALESCE/NULLIF against sample databases (`Test/SemanticsTest.lean`, 80+ tests).
- **Optimizer constant folding and boolean simplification**: Constant folding for arithmetic
  and comparisons, double negation, AND/OR identity laws, De Morgan, arithmetic identities
  (`Test/OptimizerTest.lean`, 60+ tests).
- **Expression normalization**: Commutativity reordering, AND/OR flattening, weight-based
  ordering, idempotency (`Test/ExprNormalizationTest.lean`, 42 tests).
- **Predicate pushdown**: Basic pushdown into tables, INNER/LEFT/RIGHT/FULL join safety,
  subquery pushdown with column transformation, GROUP BY constraints
  (`Test/PredicatePushdownTest.lean`, 32 tests).
- **Join reordering**: Safety checks, greedy cost-based ordering, semantics preservation
  forward/backward properties (`Test/JoinReorderingTest.lean`, 40 tests).
- **Algebraic properties (LSpec)**: Commutativity, associativity, De Morgan, distributivity,
  identity/annihilation, idempotence, complement, absorption, arithmetic identities,
  comparison flips (`LSpecTests/ExprAlgebra.lean`, 36 properties).
- **NULL semantics (LSpec)**: Arithmetic/comparison NULL propagation, three-valued logic
  dominance rules, IS NULL/IS NOT NULL complementarity, COALESCE basics
  (`LSpecTests/NullSemantics.lean`, 31 properties).
- **Optimizer equivalence (LSpec)**: Guard correctness for identity laws, double negation,
  idempotent/complement laws on non-boolean operands, arithmetic soundness with NULL and
  type mismatches, individual pass isolation (`LSpecTests/OptimizerEquiv.lean`, 47 properties).

---

## Coverage Gaps

### 1. Three-valued NULL logic in compound expressions (High Priority)

**What's missing**: The LSpec NULL semantics tests cover pairwise propagation (e.g.,
`NULL + x = NULL`, `FALSE AND NULL = FALSE`) but not compound/nested scenarios.

**Specific tests to add**:
- `(NULL AND x) OR y` — does OR dominance work after NULL propagation?
- `(a OR NOT a)` where `a` is NULL — should be NULL, not TRUE
- `NULL = NULL` — must return NULL, not TRUE or FALSE
- `NOT (NULL AND FALSE)` — should be TRUE (since `NULL AND FALSE = FALSE`)
- `COALESCE(NULL, NULL, x)` — multi-NULL fallthrough
- `NULLIF(x, x)` — should always return NULL for non-NULL x

**Where to add**: `LSpecTests/NullSemantics.lean` (new "compound NULL" section).

### 2. Window function evaluation (High Priority)

**What's missing**: Window functions (`ROW_NUMBER`, `RANK`, `DENSE_RANK`, aggregate windows)
have semantic evaluation code in `Semantics.lean:partitionRows`, `computeRanks`,
`computeDenseRanks`, `evalWindowFn` but minimal test coverage.

**Specific tests to add**:
- `RANK()` and `DENSE_RANK()` with ties (multiple rows sharing same sort key)
- `ROW_NUMBER()` determinism within a partition when sort keys collide
- `PARTITION BY` with multiple columns
- `PARTITION BY` + `ORDER BY` combinations with NULLs in partition/sort keys
- Aggregate window functions: `SUM() OVER (PARTITION BY ...)`, `COUNT() OVER ()`
- Empty partitions (no matching rows for a partition key)
- Window function with no ORDER BY clause

**Where to add**: New `Test/WindowFunctionTest.lean` or extend `Test/SemanticsTest.lean`.

### 3. Recursive CTE semantics (High Priority)

**What's missing**: `Semantics.lean:evalRecursiveCTE` implements fixed-point iteration with a
max recursion limit of 1000, but there are no tests for this logic.

**Specific tests to add**:
- Simple recursive CTE (e.g., generate sequence 1..10)
- Recursive CTE that reaches fixed point before limit
- Recursive CTE that hits the recursion limit (verify graceful termination)
- Recursive CTE with UNION vs UNION ALL base/recursive combination
- Empty base case (recursive CTE produces no initial rows)
- Cycle detection: rows that would repeat indefinitely

**Where to add**: New `Test/RecursiveCTETest.lean`.

### 4. LIKE pattern matching (Medium Priority)

**What's missing**: `Semantics.lean:simpleLike` implements SQL LIKE matching but has no
dedicated tests. The parser tests verify LIKE parses, but not that evaluation is correct.

**Specific tests to add**:
- `'hello' LIKE 'hello'` — exact match
- `'hello' LIKE 'h%'` — prefix wildcard
- `'hello' LIKE '%lo'` — suffix wildcard
- `'hello' LIKE '%ell%'` — infix wildcard
- `'hello' LIKE 'h_llo'` — single-char wildcard
- `'' LIKE '%'` — empty string with wildcard
- `'' LIKE '_'` — empty string with single char (should be FALSE)
- `'hello' LIKE '%'` — match-all
- NULL LIKE '%' — NULL propagation
- `'hello' LIKE NULL` — NULL propagation
- Multiple `%` wildcards: `'abc' LIKE '%b%c%'`

**Where to add**: `Test/SemanticsTest.lean` (new LIKE section).

### 5. Correlated subqueries (Medium Priority)

**What's missing**: `Semantics.lean` supports correlated subqueries (evalExprWithDb passes
outer row context) but no test explicitly validates that the outer row is correctly
referenced inside an inner query.

**Specific tests to add**:
- `SELECT * FROM users u WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id)`
- Correlated scalar subquery: `SELECT (SELECT MAX(amount) FROM orders WHERE user_id = u.id) FROM users u`
- Correlated IN: `SELECT * FROM users WHERE id IN (SELECT user_id FROM orders WHERE amount > 100)`
- Multiple levels of correlation (nested correlated subqueries)
- Correlated subquery referencing a column that doesn't exist in outer scope (error case)

**Where to add**: `Test/SemanticsTest.lean` (new correlated subquery section).

### 6. Aggregate edge cases (Medium Priority)

**What's missing**: Aggregates are tested for basic correctness, but edge cases around
NULL handling, empty groups, and type behavior are not covered.

**Specific tests to add**:
- `COUNT(*)` on empty table — should return 0
- `COUNT(col)` where all values are NULL — should return 0
- `SUM(col)` on empty group — should return NULL
- `AVG(col)` with all NULLs — should return NULL
- `MIN/MAX` on empty group — should return NULL
- `SUM(col)` where col has mixed NULL and non-NULL values — NULLs should be skipped
- `GROUP BY` producing zero-member groups (after HAVING filter, verify empty result)
- `HAVING` without `GROUP BY` — whole table as one group
- `COUNT(DISTINCT col)` with NULLs — NULLs should not be counted

**Where to add**: `Test/SemanticsTest.lean` (new aggregate edge cases section).

### 7. ORDER BY with NULLs (Medium Priority)

**What's missing**: SQL defines that NULL sort order depends on implementation (typically
NULLS LAST for ASC, NULLS FIRST for DESC). No tests verify the chosen behavior.

**Specific tests to add**:
- ORDER BY ascending with NULL values — verify NULL position
- ORDER BY descending with NULL values — verify NULL position
- Multi-column ORDER BY where first column has NULLs
- ORDER BY on expression result that evaluates to NULL for some rows

**Where to add**: `Test/SemanticsTest.lean`.

### 8. Pretty-printer correctness (Medium Priority)

**What's missing**: `Pretty.lean` (~1000 lines) converts AST back to SQL strings. The
parser round-trip tests indirectly validate it, but there are no direct tests for
formatting correctness, operator precedence in output, or edge cases.

**Specific tests to add**:
- Operator precedence: `a + b * c` should not produce `(a + b) * c`
- Parenthesization of nested AND/OR: `a AND (b OR c)` preserved correctly
- String escaping: single quotes inside strings (`O'Brien`)
- NULL literal rendering
- CASE expression formatting
- Subquery in FROM clause formatting (aliased correctly)
- Window function OVER clause formatting

**Where to add**: New `Test/PrettyTest.lean`.

### 9. Cross-pass optimizer interactions (Medium Priority)

**What's missing**: Individual optimization passes are tested, but their composition is not.
The optimizer applies passes sequentially; no test verifies that the composition is
sound.

**Specific tests to add**:
- De Morgan followed by identity law: `NOT (a AND TRUE)` → `NOT a OR FALSE` → `NOT a`
- Constant fold then boolean simplify: `(3 > 2) AND x` → `TRUE AND x` → `x`
- Predicate pushdown after boolean simplification
- Expression normalization after constant folding
- Full `optimize` on complex queries and verify output equals expected optimized form
- `optimize(optimize(q)) = optimize(q)` — idempotency of full pipeline

**Where to add**: `LSpecTests/OptimizerEquiv.lean` (new cross-pass section) or
`Test/OptimizerTest.lean`.

### 10. Query-level optimization (Lower Priority)

**What's missing**: The LSpec optimizer tests focus on expression-level optimization. No
LSpec properties test `optimizeSelectStmt` or `optimizeQuery`.

**Specific tests to add**:
- `optimizeSelectStmt` preserves evaluation result on random SelectStmt inputs
- `optimizeQuery` preserves evaluation result on random Query inputs
- Dead code elimination: `WHERE FALSE` → empty result
- WHERE TRUE elimination at query level
- CTE optimization (unused CTEs, recursive CTE with constant base)

**Where to add**: `LSpecTests/OptimizerEquiv.lean` with new generators for SelectStmt/Query.

### 11. LSpec generator expansion (Lower Priority)

**What's missing**: The current SlimCheck generators in `LSpecTests/Generators.lean` only
produce ground expressions (no column references, no function calls, no aggregates, no
window functions, no BETWEEN/IN/EXISTS).

**Generators to add**:
- Function call expressions: `COALESCE(...)`, `NULLIF(...)`, `ABS(...)`, `LENGTH(...)`,
  `UPPER(...)`, `LOWER(...)`, `CONCAT(...)`
- BETWEEN expressions
- IN list expressions (with small literal lists)
- CASE expressions with arbitrary depth
- Boundary-value integers: 0, 1, -1, max/min int
- Special strings: empty string, single char, strings with quotes

**Where to add**: `LSpecTests/Generators.lean`.

### 12. DML statement evaluation (Lower Priority)

**What's missing**: INSERT, UPDATE, DELETE are parsed and AST types exist, but
`evalInsert`, `evalUpdate`, `evalDelete` in `Semantics.lean` have no test coverage.

**Specific tests to add**:
- INSERT into table and verify row added
- UPDATE with WHERE clause and verify changed rows
- DELETE with WHERE clause and verify removed rows
- UPDATE/DELETE with no WHERE (affects all rows)
- INSERT with column list subset
- UPDATE SET with expression (not just literal)

**Where to add**: `Test/SemanticsTest.lean` (new DML section).

---

## Suggested prioritization

| Priority | Area | Rationale |
|----------|------|-----------|
| **P0** | Compound NULL logic | Core SQL semantics correctness; subtle bugs hide here |
| **P0** | Window functions | Significant code with minimal coverage |
| **P0** | Recursive CTEs | Entirely untested evaluation path |
| **P1** | LIKE pattern matching | Untested evaluation function |
| **P1** | Correlated subqueries | Complex scoping logic with no direct tests |
| **P1** | Aggregate edge cases | NULL/empty behavior affects real queries |
| **P1** | ORDER BY with NULLs | Undefined behavior without tests |
| **P2** | Pretty-printer | Indirectly covered by round-trip, but edge cases untested |
| **P2** | Cross-pass optimizer | Composition soundness not verified |
| **P2** | Query-level optimization | LSpec only covers expression-level |
| **P3** | Generator expansion | Enables broader property coverage |
| **P3** | DML evaluation | Least critical path for query equivalence work |
