# Aggregate Pushdown

## Cleanroom Specification

**Module:** `SqlEquiv/AggregatePushdown.lean`
**Phase:** 4 - Advanced Transformations
**Dependencies:** PR 0 (OptimizerUtils), PR B (PredicatePushdown), Advanced Cost Estimation

---

## 1. Intended Function

Aggregate Pushdown reduces intermediate result sizes by performing GROUP BY aggregations before joins when semantically safe, thereby reducing the number of rows that need to be joined.

### 1.1 Black-Box Specification

```
pushAggregateDown : SelectStmt → SelectStmt

Given a SELECT statement with GROUP BY and joins, produces a semantically
equivalent statement where aggregations are computed as early as possible
in the query plan.
```

### 1.2 Motivating Example

```sql
-- Before: Join then aggregate (processes all matching rows)
SELECT d.name, SUM(e.salary)
FROM employees e
JOIN departments d ON e.dept_id = d.id
GROUP BY d.name

-- After: Aggregate then join (processes fewer rows)
SELECT d.name, e_agg.total_salary
FROM (SELECT dept_id, SUM(salary) AS total_salary
      FROM employees
      GROUP BY dept_id) e_agg
JOIN departments d ON e_agg.dept_id = d.id
```

### 1.3 External Interface

| Function | Signature | Purpose |
|----------|-----------|---------|
| `canPushAggregateDown` | `SelectStmt → Bool` | Check if pushdown is applicable |
| `pushAggregateDown` | `SelectStmt → SelectStmt` | Perform the transformation |
| `identifyAggregateGroups` | `SelectStmt → List AggregateGroup` | Find pushable aggregate groups |

---

## 2. Data Structures

### 2.1 Aggregate Group

```lean
/-- A group of aggregates that can be pushed together -/
structure AggregateGroup where
  /-- Target table/subquery for pushdown -/
  targetFrom : FromClause
  /-- Columns to group by (must be from target) -/
  groupingColumns : List ColumnRef
  /-- Aggregates to compute (must reference only target) -/
  aggregates : List AggregateExpr
  /-- Join columns needed after aggregation -/
  joinColumns : List ColumnRef
  deriving Repr

/-- A single aggregate expression -/
structure AggregateExpr where
  /-- Aggregate function (SUM, COUNT, etc.) -/
  func : AggFunc
  /-- Input expression -/
  input : Option Expr
  /-- DISTINCT modifier -/
  distinct : Bool
  /-- Alias for result -/
  alias : String
  deriving Repr

/-- Result of aggregate pushdown analysis -/
structure AggregatePushdownResult where
  /-- Whether pushdown is possible -/
  canPush : Bool
  /-- Groups that can be pushed -/
  pushableGroups : List AggregateGroup
  /-- Reason if cannot push -/
  blockerReason : Option String
  deriving Repr
```

### 2.2 Decomposable Aggregates

```lean
/-- Aggregates that can be computed in parts and combined -/
inductive DecomposableAggregate where
  | sum      -- SUM(partial_sum) = total_sum
  | count    -- SUM(partial_count) = total_count
  | min      -- MIN(partial_min) = total_min
  | max      -- MAX(partial_max) = total_max
  | countStar -- SUM(partial_count) = total_count
  deriving Repr, BEq

/-- Aggregates that cannot be decomposed -/
inductive NonDecomposableAggregate where
  | avg      -- Requires SUM/COUNT decomposition
  | countDistinct -- Cannot split distinct across partitions
  | median   -- Requires full data
  | percentile -- Requires full data
  deriving Repr, BEq
```

---

## 3. Functional Specifications

### 3.1 Safety Analysis

#### 3.1.1 Aggregate Decomposability

```
Function: isDecomposable
Input: agg : AggFunc, distinct : Bool
Output: Bool

Intended Function:
  IF distinct = true
  THEN false  -- DISTINCT aggregates cannot be decomposed
  ELSE
    CASE agg OF
      | SUM => true
      | COUNT => true
      | MIN => true
      | MAX => true
      | AVG => false  -- must decompose to SUM/COUNT
      | _ => false
```

#### 3.1.2 Column Locality

```
Function: aggregateReferencesOnlyTable
Input: agg : AggregateExpr, table : FromClause
Output: Bool

Intended Function:
  CASE agg.input OF
    | none => true  -- COUNT(*)
    | some expr => exprReferencesOnlyFrom table expr
```

#### 3.1.3 Grouping Column Availability

```
Function: groupingColumnsAvailableIn
Input: groupBy : List Expr, table : FromClause
Output: Bool

Intended Function:
  groupBy.all (fun g =>
    CASE g OF
      | Col c => columnAvailableIn c table
      | _ => false  -- only simple column groupings supported
  )
```

#### 3.1.4 Join Preserves Cardinality

```
Function: joinPreservesGroupCardinality
Input: join : FromClause, groupingCols : List ColumnRef
Output: Bool

Intended Function:
  -- A join preserves group cardinality if:
  -- 1. It's a many-to-one join (grouping side → other side)
  -- 2. Or grouping columns include the join key
  CASE join OF
    | Join left jtype right (some cond) =>
        -- Check if join is on a key that determines the grouping
        isKeyPreservingJoin cond groupingCols
    | _ => false
```

---

### 3.2 Pushdown Decision

#### 3.2.1 Analyze Query for Pushdown

```
Function: analyzeForAggregatePushdown
Input: stmt : SelectStmt
Output: AggregatePushdownResult

Intended Function:
  -- Must have GROUP BY
  IF stmt.groupBy.isEmpty
  THEN AggregatePushdownResult.mk false [] "No GROUP BY clause"

  -- Must have joins
  ELSE IF NOT hasJoins stmt.fromClause
  THEN AggregatePushdownResult.mk false [] "No joins to push through"

  -- Find all aggregates in SELECT
  ELSE
    LET aggs = extractAggregates stmt.items
    LET groups = FOR EACH table IN getJoinLeaves stmt.fromClause:
      LET tableAggs = aggs.filter (aggregateReferencesOnlyTable · table)
      LET tableGroupCols = stmt.groupBy.filter (exprReferencesOnlyFrom table ·)
      IF tableAggs.nonEmpty AND tableGroupCols.nonEmpty AND
         tableAggs.all (isDecomposable ·.func ·.distinct)
      THEN some (AggregateGroup.mk table tableGroupCols tableAggs [])
      ELSE none
    IN AggregatePushdownResult.mk groups.nonEmpty (groups.filterMap id) none
```

#### 3.2.2 Cost-Based Decision

```
Function: shouldPushAggregate
Input: group : AggregateGroup, stats : Statistics
Output: Bool

Intended Function:
  LET beforeRows = estimateCardinality group.targetFrom stats
  LET distinctGroups = estimateDistinctGroups group.groupingColumns stats
  LET reduction = beforeRows / distinctGroups

  -- Push if reduction is significant (e.g., > 10x)
  IN reduction > AGGREGATE_PUSHDOWN_THRESHOLD
```

---

### 3.3 Transformation

#### 3.3.1 Create Aggregated Subquery

```
Function: createAggregatedSubquery
Input: group : AggregateGroup
Output: FromClause

Intended Function:
  LET selectItems =
    -- Include grouping columns
    group.groupingColumns.map (fun c => SelectItem.exprItem (Expr.col c) (some c.column)) ++
    -- Include join columns (if different from grouping)
    group.joinColumns.filter (NOT · ∈ group.groupingColumns)
                     .map (fun c => SelectItem.exprItem (Expr.col c) (some c.column)) ++
    -- Include aggregates with aliases
    group.aggregates.map (fun a => SelectItem.exprItem (aggregateToExpr a) (some a.alias))

  LET subquery = SelectStmt.mk
    false  -- not distinct
    selectItems
    (some group.targetFrom)
    none   -- no WHERE (already in original)
    group.groupingColumns.map Expr.col
    none   -- no HAVING
    []     -- no ORDER BY
    none   -- no LIMIT
    none   -- no OFFSET

  IN FromClause.subquery subquery (generateAlias group.targetFrom)
```

#### 3.3.2 Rewrite Join

```
Function: rewriteJoinWithPushedAggregate
Input: originalFrom : FromClause, group : AggregateGroup, subquery : FromClause
Output: FromClause

Intended Function:
  -- Replace the target table with the aggregated subquery
  replaceInFrom originalFrom group.targetFrom subquery
```

#### 3.3.3 Rewrite SELECT Items

```
Function: rewriteSelectItems
Input: items : List SelectItem, group : AggregateGroup, subqueryAlias : String
Output: List SelectItem

Intended Function:
  items.map (fun item =>
    CASE item OF
      | ExprItem expr alias =>
          LET newExpr = rewriteAggregateReferences expr group subqueryAlias
          IN SelectItem.exprItem newExpr alias
      | star => star
  )
```

#### 3.3.4 Main Transformation

```
Function: pushAggregateDown
Input: stmt : SelectStmt
Output: SelectStmt

Intended Function:
  LET analysis = analyzeForAggregatePushdown stmt
  IF NOT analysis.canPush
  THEN stmt  -- return unchanged
  ELSE
    -- Apply pushdown for each group (in order of benefit)
    LET sortedGroups = analysis.pushableGroups.sortBy estimatedBenefit
    LET result = sortedGroups.foldl (fun acc group =>
      IF shouldPushAggregate group stats
      THEN applyAggregatePushdown acc group
      ELSE acc
    ) stmt
    IN result
```

---

## 4. Decomposition Rules

### 4.1 AVG Decomposition

```
Function: decomposeAvg
Input: avgExpr : Expr
Output: (sumExpr : Expr, countExpr : Expr, combineExpr : Expr → Expr → Expr)

Intended Function:
  -- AVG(x) = SUM(x) / COUNT(x)
  -- Pushed: SELECT SUM(x) as _sum_x, COUNT(x) as _count_x ...
  -- Combined: _sum_x / _count_x

  LET arg = getAggregateArg avgExpr
  LET sumExpr = Expr.agg .sum (some arg) false
  LET countExpr = Expr.agg .count (some arg) false
  LET combineExpr = fun sumCol countCol => Expr.binOp .div sumCol countCol
  IN (sumExpr, countExpr, combineExpr)
```

### 4.2 Multi-Level Aggregation

```
Function: createPartialAggregate
Input: agg : AggFunc
Output: AggFunc

Intended Function:
  CASE agg OF
    | SUM => SUM      -- SUM of partial SUMs
    | COUNT => SUM    -- SUM of partial COUNTs
    | MIN => MIN      -- MIN of partial MINs
    | MAX => MAX      -- MAX of partial MAXs
    | AVG => error    -- must be decomposed first
```

---

## 5. Correctness Conditions

### 5.1 Semantic Preservation

```lean
/-- Aggregate pushdown preserves query semantics -/
axiom aggregate_pushdown_preserves_semantics (stmt : SelectStmt) :
  ∀ db, evalSelect db (pushAggregateDown stmt) = evalSelect db stmt
```

### 5.2 Decomposition Correctness

```lean
/-- SUM can be decomposed across partitions -/
theorem sum_decomposition (rows : List Row) (partitions : List (List Row))
  (h : rows = partitions.join) (col : ColumnRef) :
  sum (rows.map (getColumn col)) =
  sum (partitions.map (fun p => sum (p.map (getColumn col))))

/-- COUNT can be decomposed across partitions -/
theorem count_decomposition (rows : List Row) (partitions : List (List Row))
  (h : rows = partitions.join) :
  rows.length = sum (partitions.map (·.length))

/-- MIN can be decomposed across partitions -/
theorem min_decomposition (rows : List Row) (partitions : List (List Row))
  (h : rows = partitions.join) (h2 : rows.nonEmpty) (col : ColumnRef) :
  min (rows.map (getColumn col)) =
  min (partitions.filter (·.nonEmpty) |>.map (fun p => min (p.map (getColumn col))))

/-- MAX can be decomposed across partitions -/
theorem max_decomposition (rows : List Row) (partitions : List (List Row))
  (h : rows = partitions.join) (h2 : rows.nonEmpty) (col : ColumnRef) :
  max (rows.map (getColumn col)) =
  max (partitions.filter (·.nonEmpty) |>.map (fun p => max (p.map (getColumn col))))
```

### 5.3 Join Cardinality Preservation

```lean
/-- Pushdown is only valid when join preserves group cardinality -/
theorem pushdown_requires_cardinality_preservation
  (stmt : SelectStmt) (group : AggregateGroup) :
  canPushAggregateDown stmt = true →
  joinPreservesGroupCardinality stmt.fromClause group.groupingColumns = true
```

---

## 6. Safety Constraints

### 6.1 When Pushdown is NOT Safe

| Scenario | Reason | Example |
|----------|--------|---------|
| COUNT DISTINCT | Cannot merge distinct counts | `COUNT(DISTINCT x)` |
| Correlated aggregates | Depends on outer query | `SUM(a.x + b.y)` |
| Many-to-many joins | Group cardinality changes | N:M relationship |
| HAVING with cross-table refs | Filter after join | `HAVING a.x > b.y` |
| Window functions | Different semantics | `SUM(x) OVER (...)` |

### 6.2 Conservative Defaults

```lean
/-- Default configuration is conservative -/
structure AggregatePushdownConfig where
  /-- Minimum row reduction to justify pushdown -/
  AGGREGATE_PUSHDOWN_THRESHOLD : Nat := 10
  /-- Allow AVG decomposition -/
  allowAvgDecomposition : Bool := true
  /-- Allow pushing through outer joins -/
  allowOuterJoinPushdown : Bool := false
  /-- Require statistics for cost-based decision -/
  requireStatistics : Bool := false
  deriving Repr
```

---

## 7. Algorithm

### 7.1 Main Algorithm

```
Algorithm: AggregatePushdown

Input: stmt : SelectStmt
Output: stmt' : SelectStmt where evalSelect db stmt' = evalSelect db stmt

1. ANALYZE phase
   a. Extract all aggregates from SELECT and HAVING
   b. Extract GROUP BY columns
   c. Extract join structure from FROM

2. IDENTIFY phase
   FOR EACH leaf table T in FROM:
     a. Find aggregates referencing only T
     b. Find GROUP BY columns from T
     c. Check if all such aggregates are decomposable
     d. Check join cardinality preservation
     IF all checks pass:
       Record AggregateGroup for T

3. COST phase (if statistics available)
   FOR EACH AggregateGroup G:
     a. Estimate rows before aggregation
     b. Estimate distinct groups
     c. Compute reduction ratio
     IF ratio < threshold:
       Remove G from candidates

4. TRANSFORM phase
   FOR EACH remaining AggregateGroup G (in benefit order):
     a. Create aggregated subquery for G.targetFrom
     b. Replace G.targetFrom with subquery in FROM
     c. Rewrite SELECT items to reference subquery aliases
     d. Rewrite HAVING if needed
     e. Update GROUP BY to reference subquery columns

5. RETURN transformed statement
```

### 7.2 Complexity

- Time: O(A × T × J) where A = aggregates, T = tables, J = join predicates
- Space: O(A + T) for tracking aggregate groups

---

## 8. Integration Points

### 8.1 With Predicate Pushdown (PR B)

```lean
/-- Push predicates before aggregation when possible -/
def optimizeWithPredicateThenAggregate (stmt : SelectStmt) : SelectStmt :=
  -- First push predicates (reduces rows before aggregation)
  let stmt1 := pushPredicateDown stmt
  -- Then push aggregates (reduces rows before join)
  let stmt2 := pushAggregateDown stmt1
  stmt2
```

### 8.2 With Join Reordering (PR C)

```lean
/-- Aggregate pushdown may change optimal join order -/
def optimizeWithAggregateAwareReordering (stmt : SelectStmt) : SelectStmt :=
  -- Option A: Reorder first, then push aggregates
  -- Option B: Push aggregates first, then reorder remaining joins
  -- Current implementation: Option A (simpler)
  let stmt1 := reorderJoins stmt
  let stmt2 := pushAggregateDown stmt1
  stmt2
```

### 8.3 With Cost Estimation

```lean
/-- Use cost estimation to decide whether to push -/
def costBasedAggregatePushdown (stmt : SelectStmt) (stats : Statistics) : SelectStmt :=
  let analysis := analyzeForAggregatePushdown stmt
  let worthwhileGroups := analysis.pushableGroups.filter (fun g =>
    let benefit := estimatePushdownBenefit g stats
    benefit > MINIMUM_BENEFIT_THRESHOLD
  )
  applyPushdownForGroups stmt worthwhileGroups
```

---

## 9. Testing Strategy

### 9.1 Unit Tests

```lean
-- Basic SUM pushdown
#guard_msgs in
testAggregatePushdown
  "SELECT d.name, SUM(e.salary) FROM employees e JOIN departments d ON e.dept_id = d.id GROUP BY d.name"
  "SELECT d.name, e_agg.total FROM (SELECT dept_id, SUM(salary) as total FROM employees GROUP BY dept_id) e_agg JOIN departments d ON e_agg.dept_id = d.id"

-- COUNT pushdown
#guard_msgs in
testAggregatePushdown
  "SELECT category, COUNT(*) FROM products p JOIN categories c ON p.cat_id = c.id GROUP BY category"
  -- Expected: COUNT pushed into products subquery

-- AVG decomposition
#guard_msgs in
testAggregatePushdown
  "SELECT region, AVG(amount) FROM orders o JOIN regions r ON o.region_id = r.id GROUP BY region"
  -- Expected: Decomposed to SUM/COUNT in subquery, combined in outer
```

### 9.2 Negative Tests

```lean
-- Should NOT push COUNT DISTINCT
#guard (canPushAggregateDown parseSelect
  "SELECT dept, COUNT(DISTINCT emp_id) FROM ... GROUP BY dept") = false

-- Should NOT push when aggregate spans tables
#guard (canPushAggregateDown parseSelect
  "SELECT dept, SUM(e.salary + d.bonus) FROM ... GROUP BY dept") = false
```

### 9.3 Property Tests

```lean
/-- Pushdown preserves result -/
def prop_pushdown_preserves_result (stmt : SelectStmt) (db : Database) : Bool :=
  evalSelect db (pushAggregateDown stmt) == evalSelect db stmt

/-- Pushdown reduces intermediate rows (when applicable) -/
def prop_pushdown_reduces_rows (stmt : SelectStmt) (stats : Statistics) : Bool :=
  let pushed := pushAggregateDown stmt
  estimateIntermediateRows pushed stats ≤ estimateIntermediateRows stmt stats
```

---

## 10. References

- Yan & Larson, "Eager Aggregation and Lazy Aggregation" (VLDB 1995)
- Chaudhuri & Shim, "Including Group-By in Query Optimization" (VLDB 1994)
- Galindo-Legaria & Joshi, "Orthogonal Optimization of Subqueries and Aggregation" (SIGMOD 2001)
