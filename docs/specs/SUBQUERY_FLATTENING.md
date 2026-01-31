# Subquery Flattening

## Cleanroom Specification

**Module:** `SqlEquiv/SubqueryFlattening.lean`
**Phase:** 4 - Advanced Transformations
**Dependencies:** PR 0 (OptimizerUtils), PR B (PredicatePushdown), PR C (JoinReordering)

---

## 1. Intended Function

Subquery Flattening transforms nested subqueries into equivalent join operations, enabling the optimizer to consider more efficient execution strategies and apply other optimizations like join reordering.

### 1.1 Black-Box Specification

```
flattenSubqueries : SelectStmt → SelectStmt

Given a SELECT statement containing subqueries (IN, EXISTS, scalar, or FROM),
produces a semantically equivalent statement where subqueries have been
converted to joins where possible.
```

### 1.2 Transformation Categories

| Subquery Type | Target Transformation |
|---------------|----------------------|
| Uncorrelated IN | Semi-join |
| Uncorrelated NOT IN | Anti-join (with NULL handling) |
| Uncorrelated EXISTS | Semi-join |
| NOT EXISTS | Anti-join |
| Scalar subquery | Left join + scalar extraction |
| Correlated subquery | Decorrelation + join |
| FROM subquery | Merge into parent (when safe) |

### 1.3 External Interface

| Function | Signature | Purpose |
|----------|-----------|---------|
| `flattenSubquery` | `Expr → FromClause → (Expr × FromClause)` | Flatten single subquery |
| `flattenAllSubqueries` | `SelectStmt → SelectStmt` | Flatten all subqueries in statement |
| `canFlatten` | `Expr → Bool` | Check if subquery can be flattened |
| `decorrelate` | `SelectStmt → ColumnRef → SelectStmt` | Remove correlation |

---

## 2. Data Structures

### 2.1 Subquery Classification

```lean
/-- Classification of subquery types -/
inductive SubqueryType where
  | inList        -- x IN (SELECT ...)
  | notInList     -- x NOT IN (SELECT ...)
  | exists        -- EXISTS (SELECT ...)
  | notExists     -- NOT EXISTS (SELECT ...)
  | scalar        -- (SELECT single_value ...)
  | fromClause    -- FROM (SELECT ...) AS alias
  deriving Repr, BEq

/-- Correlation status -/
inductive CorrelationType where
  | uncorrelated  -- No references to outer query
  | correlated    -- References outer query columns
  deriving Repr, BEq

/-- Complete subquery analysis -/
structure SubqueryInfo where
  /-- The subquery expression -/
  subquery : SelectStmt
  /-- Type classification -/
  sqType : SubqueryType
  /-- Correlation status -/
  correlation : CorrelationType
  /-- Outer columns referenced (if correlated) -/
  outerRefs : List ColumnRef
  /-- Context where subquery appears -/
  context : SubqueryContext
  deriving Repr
```

### 2.2 Flattening Result

```lean
/-- Result of flattening transformation -/
structure FlattenResult where
  /-- New FROM clause incorporating the subquery -/
  newFrom : FromClause
  /-- Replacement expression for original subquery location -/
  replacementExpr : Option Expr
  /-- Additional WHERE predicates -/
  additionalPredicates : List Expr
  /-- Whether deduplication is needed -/
  needsDistinct : Bool
  deriving Repr
```

### 2.3 Semi-Join and Anti-Join

```lean
/-- Extended join types for subquery flattening -/
inductive ExtendedJoinType where
  | inner
  | left
  | right
  | full
  | cross
  | semi      -- Returns left rows that have a match (no duplicates)
  | antiSemi  -- Returns left rows that have no match
  deriving Repr, BEq

/-- Semi-join representation using standard constructs -/
-- Note: SQL doesn't have native semi-join syntax
-- We represent it as: SELECT DISTINCT left.* FROM left WHERE EXISTS (...)
-- Or equivalently: left JOIN (SELECT DISTINCT key FROM right) ON key
```

---

## 3. Functional Specifications

### 3.1 Subquery Analysis

#### 3.1.1 Detect Subquery Type

```
Function: classifySubquery
Input: expr : Expr
Output: Option SubqueryInfo

Intended Function:
  CASE expr OF
    | InSubquery e negated subq =>
        LET sqType = if negated then notInList else inList
        LET corr = analyzeCorrelation subq
        IN some (SubqueryInfo.mk subq sqType corr (getOuterRefs subq) InPredicate)

    | Exists negated subq =>
        LET sqType = if negated then notExists else exists
        LET corr = analyzeCorrelation subq
        IN some (SubqueryInfo.mk subq sqType corr (getOuterRefs subq) ExistsPredicate)

    | Subquery subq =>
        LET corr = analyzeCorrelation subq
        IN some (SubqueryInfo.mk subq scalar corr (getOuterRefs subq) ScalarContext)

    | _ => none
```

#### 3.1.2 Analyze Correlation

```
Function: analyzeCorrelation
Input: subq : SelectStmt
Output: CorrelationType × List ColumnRef

Intended Function:
  LET allRefs = getReferencedColumns (selectToExpr subq)
  LET subqTables = getFromClauseTableNames subq.fromClause
  LET outerRefs = allRefs.filter (fun c =>
    c.table.isSome AND NOT (c.table.get! ∈ subqTables)
  )
  IN IF outerRefs.isEmpty
     THEN (uncorrelated, [])
     ELSE (correlated, outerRefs)
```

#### 3.1.3 Check Flattenability

```
Function: canFlatten
Input: info : SubqueryInfo
Output: Bool

Intended Function:
  -- Always flattenable
  IF info.sqType ∈ [inList, exists, notExists] AND info.correlation = uncorrelated
  THEN true

  -- NOT IN with NULLs is tricky
  ELSE IF info.sqType = notInList
  THEN canHandleNotInNulls info.subquery

  -- Scalar requires single row guarantee
  ELSE IF info.sqType = scalar
  THEN guaranteesSingleRow info.subquery

  -- Correlated requires successful decorrelation
  ELSE IF info.correlation = correlated
  THEN canDecorrelate info.subquery info.outerRefs

  ELSE false
```

---

### 3.2 Uncorrelated Transformations

#### 3.2.1 IN to Semi-Join

```
Function: flattenInSubquery
Input: col : Expr, subq : SelectStmt, from_ : FromClause
Output: FlattenResult

Precondition: subq is uncorrelated, subq.items has exactly one column

Intended Function:
  -- x IN (SELECT y FROM T WHERE p)
  -- becomes:
  -- FROM original_from JOIN (SELECT DISTINCT y FROM T WHERE p) AS sq ON x = sq.y

  LET subqCol = extractSingleColumn subq.items
  LET distinctSubq = SelectStmt.mk
    true  -- DISTINCT
    subq.items
    subq.fromClause
    subq.whereClause
    [] [] [] none none

  LET alias = generateFreshAlias "sq"
  LET joinCond = Expr.binOp .eq col (Expr.col ⟨subqCol, some alias⟩)

  LET newFrom = FromClause.join
    from_
    .inner
    (FromClause.subquery distinctSubq alias)
    (some joinCond)

  IN FlattenResult.mk newFrom none [] false
```

#### 3.2.2 NOT IN to Anti-Join

```
Function: flattenNotInSubquery
Input: col : Expr, subq : SelectStmt, from_ : FromClause
Output: FlattenResult

Precondition: subq is uncorrelated

Intended Function:
  -- x NOT IN (SELECT y FROM T WHERE p)
  -- becomes:
  -- FROM original_from LEFT JOIN (SELECT DISTINCT y FROM T WHERE p) AS sq ON x = sq.y
  -- WHERE sq.y IS NULL

  -- IMPORTANT: NOT IN has special NULL semantics
  -- If subquery returns any NULL, entire NOT IN is UNKNOWN for non-NULL x values
  -- We handle this by adding: AND sq.y IS NOT NULL to the original subquery

  LET subqCol = extractSingleColumn subq.items
  LET safeSubq = addNotNullFilter subq subqCol  -- Exclude NULLs from subquery
  LET distinctSubq = SelectStmt.mk true safeSubq.items safeSubq.fromClause safeSubq.whereClause [] [] [] none none

  LET alias = generateFreshAlias "sq"
  LET joinCond = Expr.binOp .eq col (Expr.col ⟨subqCol, some alias⟩)

  LET newFrom = FromClause.join
    from_
    .left
    (FromClause.subquery distinctSubq alias)
    (some joinCond)

  LET antiPred = Expr.unaryOp .isNull (Expr.col ⟨subqCol, some alias⟩)

  IN FlattenResult.mk newFrom none [antiPred] false
```

#### 3.2.3 EXISTS to Semi-Join

```
Function: flattenExistsSubquery
Input: subq : SelectStmt, from_ : FromClause, negated : Bool
Output: FlattenResult

Precondition: subq is uncorrelated

Intended Function:
  -- EXISTS (SELECT * FROM T WHERE p)
  -- becomes:
  -- FROM original_from, (SELECT 1 FROM T WHERE p LIMIT 1) AS sq
  -- (Cross join with single-row subquery that exists iff EXISTS is true)

  -- For uncorrelated EXISTS, we can simplify:
  -- If subquery returns any rows, include all original rows
  -- If subquery returns no rows, include no original rows

  -- Implementation: Use a LEFT JOIN with a marker
  LET markerSubq = SelectStmt.mk
    true  -- DISTINCT (ensures at most 1 row)
    [SelectItem.exprItem (Expr.lit (Value.int 1)) (some "_exists_marker")]
    subq.fromClause
    subq.whereClause
    [] [] [] (some 1) none  -- LIMIT 1

  LET alias = generateFreshAlias "exists_sq"
  LET newFrom = FromClause.join
    from_
    .cross
    (FromClause.subquery markerSubq alias)
    none

  IF negated
  THEN
    -- NOT EXISTS: Left join + null check
    LET leftJoinFrom = FromClause.join from_ .left (FromClause.subquery markerSubq alias) none
    LET antiPred = Expr.unaryOp .isNull (Expr.col ⟨"_exists_marker", some alias⟩)
    IN FlattenResult.mk leftJoinFrom none [antiPred] false
  ELSE
    -- EXISTS: Cross join (only produces rows if subquery non-empty)
    IN FlattenResult.mk newFrom none [] false
```

#### 3.2.4 Scalar Subquery to Left Join

```
Function: flattenScalarSubquery
Input: subq : SelectStmt, from_ : FromClause
Output: FlattenResult

Precondition: subq returns at most one row (verified by guaranteesSingleRow)

Intended Function:
  -- (SELECT MAX(y) FROM T WHERE p)
  -- becomes:
  -- LEFT JOIN (SELECT MAX(y) AS _scalar FROM T WHERE p) AS sq ON TRUE
  -- Reference: sq._scalar

  LET scalarCol = extractSingleColumn subq.items
  LET alias = generateFreshAlias "scalar_sq"
  LET aliasedSubq = SelectStmt.mk
    subq.distinct
    [SelectItem.exprItem (itemToExpr subq.items[0]) (some "_scalar")]
    subq.fromClause
    subq.whereClause
    subq.groupBy
    subq.having
    [] none none

  -- Use LEFT JOIN ON TRUE to preserve all outer rows
  LET newFrom = FromClause.join
    from_
    .left
    (FromClause.subquery aliasedSubq alias)
    (some (Expr.lit (Value.bool true)))

  LET replacement = Expr.col ⟨"_scalar", some alias⟩

  IN FlattenResult.mk newFrom (some replacement) [] false
```

---

### 3.3 Correlated Subquery Decorrelation

#### 3.3.1 Decorrelation Strategy

```
Function: decorrelate
Input: subq : SelectStmt, outerRefs : List ColumnRef
Output: Option (SelectStmt × Expr)

Intended Function:
  -- Correlated: SELECT * FROM T WHERE T.x = outer.y
  -- Decorrelated: SELECT DISTINCT x, ... FROM T
  -- Join condition: T.x = outer.y (moved outside)

  -- Step 1: Add outer reference columns to SELECT
  LET augmentedItems = subq.items ++ outerRefs.map (fun c =>
    SelectItem.exprItem (Expr.col c) (some (correlationAlias c))
  )

  -- Step 2: Extract correlation predicates from WHERE
  LET (correlationPreds, remainingWhere) = extractCorrelationPredicates subq.whereClause outerRefs

  -- Step 3: Add GROUP BY to handle duplicates (if not already aggregated)
  LET groupBy = IF subq.groupBy.isEmpty AND NOT hasAggregate subq
                THEN outerRefs.map (fun c => Expr.col c)
                ELSE subq.groupBy

  -- Step 4: Build decorrelated subquery
  LET decorrelated = SelectStmt.mk
    true  -- DISTINCT to eliminate duplicates
    augmentedItems
    subq.fromClause
    remainingWhere
    groupBy
    subq.having
    [] none none

  -- Step 5: Build join condition from correlation predicates
  LET joinCond = correlationPreds.foldl (fun acc p =>
    rewriteCorrelationPredicate p outerRefs
  ) (Expr.lit (Value.bool true))

  IN some (decorrelated, joinCond)
```

#### 3.3.2 Correlation Predicate Extraction

```
Function: extractCorrelationPredicates
Input: where_ : Option Expr, outerRefs : List ColumnRef
Output: (correlationPreds : List Expr, remaining : Option Expr)

Intended Function:
  CASE where_ OF
    | none => ([], none)
    | some expr =>
        LET conjuncts = flattenAnd expr
        LET (corr, nonCorr) = conjuncts.partition (referencesAny · outerRefs)
        IN (corr, unflattenAnd nonCorr)
```

#### 3.3.3 Flatten Correlated IN

```
Function: flattenCorrelatedIn
Input: col : Expr, subq : SelectStmt, from_ : FromClause, outerRefs : List ColumnRef
Output: Option FlattenResult

Intended Function:
  -- x IN (SELECT y FROM T WHERE T.z = outer.w)
  -- becomes:
  -- FROM original_from JOIN (SELECT DISTINCT y, z FROM T) AS sq ON x = sq.y AND outer.w = sq.z

  MATCH decorrelate subq outerRefs WITH
    | none => none
    | some (decorrelated, joinCond) =>
        LET subqCol = extractSingleColumn subq.items
        LET alias = generateFreshAlias "corr_sq"
        LET fullJoinCond = Expr.binOp .and
          (Expr.binOp .eq col (Expr.col ⟨subqCol, some alias⟩))
          joinCond

        LET newFrom = FromClause.join
          from_
          .inner
          (FromClause.subquery decorrelated alias)
          (some fullJoinCond)

        IN some (FlattenResult.mk newFrom none [] true)
```

---

### 3.4 FROM Clause Subquery Merging

#### 3.4.1 Merge Conditions

```
Function: canMergeFromSubquery
Input: subq : SelectStmt
Output: Bool

Intended Function:
  -- Can merge if subquery is "simple":
  NOT subq.distinct AND
  subq.groupBy.isEmpty AND
  subq.having.isNone AND
  subq.orderBy.isEmpty AND
  subq.limitVal.isNone AND
  subq.offsetVal.isNone AND
  NOT hasWindowFunctions subq AND
  NOT hasAggregates subq
```

#### 3.4.2 Merge Subquery into Parent

```
Function: mergeFromSubquery
Input: parent : SelectStmt, subqAlias : String, subq : SelectStmt
Output: SelectStmt

Precondition: canMergeFromSubquery subq = true

Intended Function:
  -- Merge subquery's FROM into parent's FROM
  LET newFrom = mergeFromClauses parent.fromClause subq.fromClause subqAlias

  -- Merge WHERE clauses
  LET newWhere = mergeWhereClauses parent.whereClause subq.whereClause

  -- Rewrite column references from alias.col to original
  LET rewrittenItems = parent.items.map (rewriteAlias subqAlias subq)
  LET rewrittenWhere = newWhere.map (rewriteAlias subqAlias subq)

  IN SelectStmt.mk
    parent.distinct
    rewrittenItems
    newFrom
    rewrittenWhere
    parent.groupBy
    parent.having
    parent.orderBy
    parent.limitVal
    parent.offsetVal
```

---

## 4. Correctness Conditions

### 4.1 Semantic Preservation

```lean
/-- IN flattening preserves semantics -/
axiom flatten_in_preserves_semantics (col : Expr) (subq : SelectStmt) (from_ : FromClause) :
  let result := flattenInSubquery col subq from_
  ∀ db row,
    evalExpr db row (Expr.inSubquery col false subq) =
    evalWithFlattenedJoin db row result.newFrom result.additionalPredicates

/-- NOT IN flattening preserves semantics (including NULL handling) -/
axiom flatten_not_in_preserves_semantics (col : Expr) (subq : SelectStmt) (from_ : FromClause) :
  let result := flattenNotInSubquery col subq from_
  ∀ db row,
    evalExpr db row (Expr.inSubquery col true subq) =
    evalWithFlattenedJoin db row result.newFrom result.additionalPredicates

/-- EXISTS flattening preserves semantics -/
axiom flatten_exists_preserves_semantics (subq : SelectStmt) (from_ : FromClause) (neg : Bool) :
  let result := flattenExistsSubquery subq from_ neg
  ∀ db row,
    evalExpr db row (Expr.exists neg subq) =
    (evalFrom db result.newFrom).any (fun _ => true)
```

### 4.2 Decorrelation Correctness

```lean
/-- Decorrelation preserves subquery result for each outer row -/
axiom decorrelation_correct (subq : SelectStmt) (outerRefs : List ColumnRef) (outerRow : Row) :
  match decorrelate subq outerRefs with
  | none => True
  | some (decorrelated, joinCond) =>
      evalSubquery db outerRow subq =
      (evalFrom db (FromClause.subquery decorrelated "_")).filter
        (fun row => evalPred db (bindOuterRow joinCond outerRow) row)
```

### 4.3 NULL Handling for NOT IN

```lean
/-- NOT IN with NULLs follows SQL semantics -/
theorem not_in_null_semantics (x : Value) (values : List Value) :
  -- If x is NULL, result is UNKNOWN
  x = Value.null →
    evalNotIn x values = Value.null
  -- If values contains NULL and x not in non-null values, result is UNKNOWN
  ∧ (Value.null ∈ values ∧ x ∉ values.filter (· ≠ Value.null)) →
    evalNotIn x values = Value.null
  -- Otherwise, standard NOT IN semantics
  ∧ (Value.null ∉ values) →
    evalNotIn x values = Value.bool (x ∉ values)
```

---

## 5. Safety Constraints

### 5.1 When Flattening is NOT Safe

| Scenario | Reason | Example |
|----------|--------|---------|
| LIMIT in subquery | Changes result cardinality | `IN (SELECT x LIMIT 5)` |
| ORDER BY in scalar | Order may affect which row selected | `(SELECT x ORDER BY y LIMIT 1)` |
| Volatile functions | Multiple evaluations differ | `IN (SELECT random())` |
| Recursive CTE | Complex semantics | `WITH RECURSIVE ...` |

### 5.2 NOT IN NULL Pitfalls

```
-- This query:
SELECT * FROM t1 WHERE x NOT IN (SELECT y FROM t2)

-- When t2.y contains NULL, returns NO ROWS for any t1
-- Because: x NOT IN (1, 2, NULL) = x != 1 AND x != 2 AND x != NULL
--                                = ... AND UNKNOWN = UNKNOWN

-- Safe transformation must filter NULLs or use NOT EXISTS
```

---

## 6. Algorithm

### 6.1 Main Algorithm

```
Algorithm: FlattenAllSubqueries

Input: stmt : SelectStmt
Output: stmt' : SelectStmt

1. COLLECT all subqueries in stmt (WHERE, SELECT items, HAVING)
   subqueries := findAllSubqueries(stmt)

2. SORT by nesting depth (deepest first)
   -- This ensures inner subqueries are flattened before outer ones

3. FOR EACH subquery sq in sorted order:
   a. Analyze: info := classifySubquery(sq)
   b. Check: IF canFlatten(info)
   c. Transform:
      CASE info.sqType OF
        | inList => result := flattenInSubquery(...)
        | notInList => result := flattenNotInSubquery(...)
        | exists => result := flattenExistsSubquery(...)
        | scalar => result := flattenScalarSubquery(...)
      d. Update stmt with result:
         - Replace FROM clause
         - Replace subquery expression with replacement
         - Add additional predicates to WHERE

4. MERGE FROM clause subqueries where possible
   FOR EACH FromClause.subquery in stmt.fromClause:
     IF canMergeFromSubquery(subquery)
     THEN stmt := mergeFromSubquery(stmt, ...)

5. RETURN stmt
```

### 6.2 Complexity

- Time: O(S × C) where S = number of subqueries, C = cost of correlation analysis
- Space: O(D) where D = maximum nesting depth

---

## 7. Integration Points

### 7.1 With Join Reordering (PR C)

```lean
/-- After flattening, newly created joins can be reordered -/
def flattenThenReorder (stmt : SelectStmt) : SelectStmt :=
  let flattened := flattenAllSubqueries stmt
  -- New joins from subquery flattening are now eligible for reordering
  reorderJoins flattened
```

### 7.2 With Predicate Pushdown (PR B)

```lean
/-- Flattening enables more predicate pushdown opportunities -/
def flattenThenPushdown (stmt : SelectStmt) : SelectStmt :=
  let flattened := flattenAllSubqueries stmt
  -- Predicates that were in subquery WHERE can now be pushed further
  pushPredicateDown flattened
```

---

## 8. Testing Strategy

### 8.1 Unit Tests

```lean
-- Uncorrelated IN
testFlatten
  "SELECT * FROM orders WHERE customer_id IN (SELECT id FROM customers WHERE country = 'US')"
  -- Expected: INNER JOIN with customers

-- NOT IN with NULL handling
testFlatten
  "SELECT * FROM t1 WHERE x NOT IN (SELECT y FROM t2)"
  -- Expected: LEFT JOIN with IS NULL check, y IS NOT NULL filter

-- EXISTS
testFlatten
  "SELECT * FROM customers c WHERE EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.id)"
  -- Expected: Semi-join pattern

-- Scalar subquery
testFlatten
  "SELECT name, (SELECT MAX(amount) FROM orders WHERE customer_id = c.id) FROM customers c"
  -- Expected: LEFT JOIN with aggregated subquery
```

### 8.2 Property Tests

```lean
/-- Flattening preserves query result -/
def prop_flatten_preserves_result (stmt : SelectStmt) (db : Database) : Bool :=
  evalSelect db (flattenAllSubqueries stmt) == evalSelect db stmt

/-- Flattening reduces subquery count -/
def prop_flatten_reduces_subqueries (stmt : SelectStmt) : Bool :=
  countSubqueries (flattenAllSubqueries stmt) ≤ countSubqueries stmt
```

---

## 9. References

- Seshadri et al., "Complex Query Decorrelation" (ICDE 1996)
- Galindo-Legaria & Joshi, "Orthogonal Optimization of Subqueries and Aggregation" (SIGMOD 2001)
- Kim, "On Optimizing an SQL-like Nested Query" (TODS 1982)
- PostgreSQL documentation on subquery optimization
