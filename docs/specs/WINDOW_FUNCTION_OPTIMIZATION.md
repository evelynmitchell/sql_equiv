# Window Function Optimization

## Cleanroom Specification

**Module:** `SqlEquiv/WindowOptimization.lean`
**Phase:** 4 - Advanced Transformations
**Dependencies:** PR 0 (OptimizerUtils), Predicate Pushdown, Advanced Cost Estimation

---

## 1. Intended Function

Window Function Optimization improves the performance of queries containing window functions by optimizing evaluation order, eliminating redundant sorts, and enabling predicate pushdown around window computations.

### 1.1 Black-Box Specification

```
optimizeWindowFunctions : SelectStmt → SelectStmt

Given a SELECT statement containing window functions, produces a semantically
equivalent statement with optimized window function evaluation.
```

### 1.2 Optimization Categories

| Optimization | Description | Benefit |
|--------------|-------------|---------|
| Sort elimination | Share sorts between compatible windows | Reduce I/O and CPU |
| Window ordering | Evaluate windows in optimal order | Minimize re-sorting |
| Predicate pushdown | Push filters below windows when safe | Reduce rows processed |
| Frame optimization | Simplify frame specifications | Reduce computation |
| Partition pruning | Eliminate partitions via predicates | Skip unnecessary work |

### 1.3 External Interface

| Function | Signature | Purpose |
|----------|-----------|---------|
| `optimizeWindowFunctions` | `SelectStmt → SelectStmt` | Main entry point |
| `groupCompatibleWindows` | `List WindowExpr → List WindowGroup` | Group by sort order |
| `orderWindowGroups` | `List WindowGroup → List WindowGroup` | Optimal evaluation order |
| `canPushPastWindow` | `Expr → WindowExpr → Bool` | Check predicate pushdown safety |

---

## 2. Data Structures

### 2.1 Window Expression Analysis

```lean
/-- Analyzed window function expression -/
structure WindowExpr where
  /-- Original expression containing window function -/
  expr : Expr
  /-- Window function type -/
  func : WindowFunc
  /-- Argument to window function -/
  arg : Option Expr
  /-- PARTITION BY columns -/
  partitionBy : List Expr
  /-- ORDER BY specification -/
  orderBy : List OrderItem
  /-- Frame specification -/
  frame : Option FrameSpec
  /-- Position in SELECT list -/
  selectIndex : Nat
  deriving Repr

/-- Frame specification -/
structure FrameSpec where
  /-- Frame type: ROWS, RANGE, or GROUPS -/
  frameType : FrameType
  /-- Start bound -/
  startBound : FrameBound
  /-- End bound -/
  endBound : FrameBound
  /-- Exclusion clause -/
  exclusion : Option FrameExclusion
  deriving Repr

inductive FrameBound where
  | unboundedPreceding
  | preceding (n : Nat)
  | currentRow
  | following (n : Nat)
  | unboundedFollowing
  deriving Repr, BEq

inductive FrameType where
  | rows   -- Physical rows
  | range  -- Logical range based on ORDER BY
  | groups -- Groups of peers
  deriving Repr, BEq
```

### 2.2 Window Groups

```lean
/-- Group of windows with compatible sort requirements -/
structure WindowGroup where
  /-- Windows in this group -/
  windows : List WindowExpr
  /-- Required PARTITION BY (intersection of all) -/
  partitionBy : List Expr
  /-- Required ORDER BY (union covering all) -/
  orderBy : List OrderItem
  /-- Estimated cost to evaluate this group -/
  cost : Cost
  deriving Repr

/-- Sort compatibility between windows -/
inductive SortCompatibility where
  | identical      -- Same PARTITION BY and ORDER BY
  | partitionOnly  -- Same PARTITION BY, different ORDER BY
  | incompatible   -- Different PARTITION BY
  deriving Repr, BEq
```

### 2.3 Evaluation Plan

```lean
/-- Plan for evaluating window functions -/
structure WindowEvalPlan where
  /-- Ordered groups to evaluate -/
  groups : List WindowGroup
  /-- Sort operations needed -/
  sorts : List SortOperation
  /-- Estimated total cost -/
  totalCost : Cost
  deriving Repr

/-- A single sort operation -/
structure SortOperation where
  /-- Columns to sort by -/
  sortKey : List OrderItem
  /-- Which window groups use this sort -/
  usedBy : List Nat  -- indices into groups
  deriving Repr
```

---

## 3. Functional Specifications

### 3.1 Window Extraction and Analysis

#### 3.1.1 Extract Window Functions

```
Function: extractWindowFunctions
Input: stmt : SelectStmt
Output: List WindowExpr

Intended Function:
  LET windows = []
  FOR EACH (item, idx) IN stmt.items.zipWithIndex:
    LET found = findWindowsInExpr item.expr
    FOR EACH wf IN found:
      windows := windows ++ [WindowExpr.mk item.expr wf.func wf.arg
                              wf.spec.partitionBy wf.spec.orderBy
                              wf.spec.frame idx]
  IN windows
```

#### 3.1.2 Analyze Sort Compatibility

```
Function: sortCompatibility
Input: w1 : WindowExpr, w2 : WindowExpr
Output: SortCompatibility

Intended Function:
  IF w1.partitionBy ≠ w2.partitionBy
  THEN incompatible

  ELSE IF w1.orderBy = w2.orderBy
  THEN identical

  ELSE IF isPrefixOf w1.orderBy w2.orderBy OR isPrefixOf w2.orderBy w1.orderBy
  THEN partitionOnly  -- One can piggyback on the other's sort

  ELSE partitionOnly  -- Same partition, need re-sort for ORDER BY
```

---

### 3.2 Window Grouping

#### 3.2.1 Group Compatible Windows

```
Function: groupCompatibleWindows
Input: windows : List WindowExpr
Output: List WindowGroup

Intended Function:
  LET groups = []
  FOR EACH w IN windows:
    LET compatGroup = groups.find? (fun g =>
      g.windows.all (fun w' => sortCompatibility w w' ≠ incompatible)
    )
    CASE compatGroup OF
      | some g =>
          -- Add to existing group
          LET newOrderBy = mergeOrderBy g.orderBy w.orderBy
          groups := groups.replace g { g with
            windows := g.windows ++ [w]
            orderBy := newOrderBy
          }
      | none =>
          -- Create new group
          groups := groups ++ [WindowGroup.mk [w] w.partitionBy w.orderBy defaultCost]
  IN groups
```

#### 3.2.2 Merge ORDER BY Specifications

```
Function: mergeOrderBy
Input: o1 : List OrderItem, o2 : List OrderItem
Output: List OrderItem

Intended Function:
  -- Find minimal ORDER BY that satisfies both
  IF isPrefixOf o1 o2
  THEN o2
  ELSE IF isPrefixOf o2 o1
  THEN o1
  ELSE
    -- Need to pick one; prefer longer (more specific)
    IF o1.length >= o2.length THEN o1 ELSE o2
```

---

### 3.3 Evaluation Order Optimization

#### 3.3.1 Optimize Group Order

```
Function: orderWindowGroups
Input: groups : List WindowGroup, stats : Statistics
Output: List WindowGroup

Intended Function:
  -- Goal: Minimize total sorting cost
  -- Strategy: Order groups to maximize sort reuse

  LET orderedGroups = []
  LET remaining = groups

  -- Greedy: Pick group that reuses most from previous
  WHILE remaining.nonEmpty:
    LET prevSort = orderedGroups.lastOption.map (·.orderBy)
    LET best = remaining.minBy (fun g =>
      sortTransitionCost prevSort g.orderBy stats
    )
    orderedGroups := orderedGroups ++ [best]
    remaining := remaining.erase best

  IN orderedGroups
```

#### 3.3.2 Sort Transition Cost

```
Function: sortTransitionCost
Input: prevSort : Option (List OrderItem), newSort : List OrderItem, stats : Statistics
Output: Cost

Intended Function:
  CASE prevSort OF
    | none =>
        -- First group: full sort cost
        estimateSortCost newSort stats
    | some prev =>
        IF prev = newSort
        THEN Cost.zero  -- No sort needed
        ELSE IF isPrefixOf prev newSort
        THEN estimatePartialSortCost (newSort.drop prev.length) stats
        ELSE estimateSortCost newSort stats  -- Full re-sort
```

---

### 3.4 Predicate Pushdown Around Windows

#### 3.4.1 Safety Check

```
Function: canPushPastWindow
Input: pred : Expr, window : WindowExpr
Output: Bool

Intended Function:
  -- A predicate can be pushed past a window function if:
  -- 1. Predicate doesn't reference the window function result
  -- 2. Predicate only references columns in PARTITION BY
  --    (ensures predicate applies to complete partitions)

  LET predCols = getReferencedColumns pred
  LET partitionCols = window.partitionBy.flatMap getReferencedColumns

  NOT referencesWindowResult pred window AND
  predCols.all (fun c => c ∈ partitionCols)
```

#### 3.4.2 Push Predicate Below Window

```
Function: pushPredicateBelowWindow
Input: stmt : SelectStmt, pred : Expr
Output: SelectStmt

Precondition: All windows in stmt satisfy canPushPastWindow pred window

Intended Function:
  -- Move predicate from HAVING/outer WHERE to inner WHERE
  LET newWhere = match stmt.whereClause with
    | none => some pred
    | some w => some (Expr.binOp .and w pred)

  IN { stmt with whereClause := newWhere }
```

#### 3.4.3 Filter After Window

```
Function: canFilterAfterWindow
Input: pred : Expr, window : WindowExpr
Output: Bool

Intended Function:
  -- Some predicates can only be applied after window computation
  -- E.g., WHERE row_number() <= 10

  referencesWindowResult pred window
```

---

### 3.5 Frame Optimization

#### 3.5.1 Simplify Frame

```
Function: simplifyFrame
Input: frame : FrameSpec, func : WindowFunc
Output: FrameSpec

Intended Function:
  -- Some window functions ignore frame; use simplest
  IF func ∈ [.rowNumber, .rank, .denseRank, .ntile, .lead, .lag]
  THEN defaultFrame  -- These ignore ROWS/RANGE specification

  -- UNBOUNDED PRECEDING to CURRENT ROW is default for aggregates
  ELSE IF frame = defaultAggregateFrame
  THEN frame  -- Already optimal

  -- Check if frame can be reduced
  ELSE IF frameIsEntirePartition frame
  THEN FrameSpec.mk .range .unboundedPreceding .unboundedFollowing none

  ELSE frame
```

#### 3.5.2 Frame Equivalence

```
Function: framesEquivalent
Input: f1 : FrameSpec, f2 : FrameSpec, orderBy : List OrderItem
Output: Bool

Intended Function:
  -- RANGE and ROWS are equivalent when ORDER BY has no ties
  IF f1.frameType = .rows AND f2.frameType = .range
  THEN f1.startBound = f2.startBound AND f1.endBound = f2.endBound AND
       orderByHasNoTies orderBy
  ELSE f1 = f2
```

---

### 3.6 Partition Pruning

#### 3.6.1 Identify Prunable Partitions

```
Function: identifyPrunablePartitions
Input: stmt : SelectStmt, window : WindowExpr
Output: Option Expr

Intended Function:
  -- If WHERE clause restricts PARTITION BY columns,
  -- we only need to process matching partitions

  LET partCols = window.partitionBy.flatMap getReferencedColumns
  LET wherePreds = flattenAnd (stmt.whereClause.getD (Expr.lit (Value.bool true)))

  LET relevantPreds = wherePreds.filter (fun p =>
    (getReferencedColumns p).all (· ∈ partCols)
  )

  unflattenAnd relevantPreds
```

---

## 4. Correctness Conditions

### 4.1 Semantic Preservation

```lean
/-- Window optimization preserves query semantics -/
axiom window_optimization_preserves_semantics (stmt : SelectStmt) :
  ∀ db, evalSelect db (optimizeWindowFunctions stmt) = evalSelect db stmt
```

### 4.2 Predicate Pushdown Safety

```lean
/-- Predicate can only be pushed if it applies to complete partitions -/
theorem predicate_pushdown_safe (pred : Expr) (window : WindowExpr)
  (h : canPushPastWindow pred window = true) :
  ∀ db partition,
    (partition.filter (evalPred db pred)).windowResult window =
    partition.windowResult window |>.filter (evalPred db pred)
```

### 4.3 Sort Optimization Correctness

```lean
/-- Grouped windows produce same results as individual evaluation -/
theorem window_grouping_correct (windows : List WindowExpr) (rows : List Row) :
  let groups := groupCompatibleWindows windows
  let groupedResults := groups.flatMap (evaluateWindowGroup rows)
  let individualResults := windows.map (evaluateWindow rows)
  groupedResults.sortBy (·.selectIndex) = individualResults
```

---

## 5. Window Function Categories

### 5.1 Ranking Functions

| Function | Frame Matters? | Partition Required? | Order Required? |
|----------|---------------|---------------------|-----------------|
| `ROW_NUMBER()` | No | No | Yes |
| `RANK()` | No | No | Yes |
| `DENSE_RANK()` | No | No | Yes |
| `NTILE(n)` | No | No | Yes |
| `PERCENT_RANK()` | No | No | Yes |
| `CUME_DIST()` | No | No | Yes |

### 5.2 Value Functions

| Function | Frame Matters? | Partition Required? | Order Required? |
|----------|---------------|---------------------|-----------------|
| `LEAD(expr, n)` | No | No | Yes |
| `LAG(expr, n)` | No | No | Yes |
| `FIRST_VALUE(expr)` | Yes | No | Yes |
| `LAST_VALUE(expr)` | Yes | No | Yes |
| `NTH_VALUE(expr, n)` | Yes | No | Yes |

### 5.3 Aggregate Functions as Windows

| Function | Frame Matters? | Partition Required? | Order Required? |
|----------|---------------|---------------------|-----------------|
| `SUM(expr)` | Yes | No | Optional |
| `COUNT(expr)` | Yes | No | Optional |
| `AVG(expr)` | Yes | No | Optional |
| `MIN(expr)` | Yes | No | Optional |
| `MAX(expr)` | Yes | No | Optional |

---

## 6. Algorithm

### 6.1 Main Algorithm

```
Algorithm: OptimizeWindowFunctions

Input: stmt : SelectStmt
Output: stmt' : SelectStmt

1. EXTRACT window functions
   windows := extractWindowFunctions(stmt)
   IF windows.isEmpty THEN RETURN stmt

2. GROUP compatible windows
   groups := groupCompatibleWindows(windows)

3. ORDER groups for minimal sorting
   orderedGroups := orderWindowGroups(groups, stats)

4. PUSH predicates where safe
   FOR EACH pred IN extractPredicates(stmt):
     IF groups.all (fun g => g.windows.all (canPushPastWindow pred ·))
     THEN stmt := pushPredicateBelowWindow(stmt, pred)

5. SIMPLIFY frames
   FOR EACH window IN windows:
     window.frame := simplifyFrame(window.frame, window.func)

6. BUILD evaluation plan
   plan := buildEvalPlan(orderedGroups)

7. REWRITE statement with optimized window evaluation
   stmt' := rewriteWithPlan(stmt, plan)

8. RETURN stmt'
```

### 6.2 Complexity

- Grouping: O(W²) where W = number of window functions
- Ordering: O(G² × S) where G = groups, S = sort comparison cost
- Predicate analysis: O(P × W) where P = predicates

---

## 7. Integration Points

### 7.1 With Predicate Pushdown (PR B)

```lean
/-- Coordinate predicate pushdown with window optimization -/
def optimizeWithWindowAwarePushdown (stmt : SelectStmt) : SelectStmt :=
  -- First identify window-compatible predicates
  let (pushable, nonPushable) := partitionPredicates stmt
  -- Push compatible predicates first
  let stmt1 := pushPredicateDown pushable stmt
  -- Then optimize windows
  let stmt2 := optimizeWindowFunctions stmt1
  stmt2
```

### 7.2 With Cost Estimation

```lean
/-- Use cost model for window optimization decisions -/
def costBasedWindowOptimization (stmt : SelectStmt) (stats : Statistics) : SelectStmt :=
  let windows := extractWindowFunctions stmt
  let groups := groupCompatibleWindows windows

  -- Use cost model to determine if grouping is beneficial
  let groupedCost := estimateGroupedWindowCost groups stats
  let ungroupedCost := estimateUngroupedWindowCost windows stats

  if groupedCost < ungroupedCost
  then applyWindowGrouping stmt groups
  else stmt  -- Keep original order
```

---

## 8. Testing Strategy

### 8.1 Unit Tests

```lean
-- Sort sharing
testWindowOpt
  "SELECT ROW_NUMBER() OVER (PARTITION BY a ORDER BY b),
          RANK() OVER (PARTITION BY a ORDER BY b)
   FROM t"
  -- Expected: Single sort operation

-- Predicate pushdown
testWindowOpt
  "SELECT * FROM (
     SELECT x, ROW_NUMBER() OVER (PARTITION BY category ORDER BY date) AS rn
     FROM orders
   ) WHERE category = 'A'"
  -- Expected: category = 'A' pushed inside subquery

-- Frame simplification
testWindowOpt
  "SELECT ROW_NUMBER() OVER (ORDER BY x ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW)
   FROM t"
  -- Expected: Frame clause removed (ignored by ROW_NUMBER)
```

### 8.2 Property Tests

```lean
/-- Optimization preserves result -/
def prop_window_opt_preserves_result (stmt : SelectStmt) (db : Database) : Bool :=
  evalSelect db (optimizeWindowFunctions stmt) == evalSelect db stmt

/-- Grouping reduces sort operations -/
def prop_grouping_reduces_sorts (stmt : SelectStmt) : Bool :=
  let original := countSortOperations stmt
  let optimized := countSortOperations (optimizeWindowFunctions stmt)
  optimized ≤ original
```

---

## 9. References

- Cao et al., "Optimization of Analytic Window Functions" (VLDB 2012)
- Leis et al., "Query Processing and Optimization in Modern Database Systems" (Tutorial)
- PostgreSQL Window Function documentation
- SQL:2003 Standard (Window Function specification)
