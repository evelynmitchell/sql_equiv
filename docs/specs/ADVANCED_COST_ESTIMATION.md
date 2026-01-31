# Advanced Cost Estimation

## Cleanroom Specification

**Module:** `SqlEquiv/CostEstimation.lean`
**Phase:** 3 - Cost Model Enhancement
**Dependencies:** PR 0 (OptimizerUtils), PR C (JoinReordering)

---

## 1. Intended Function

The Advanced Cost Estimation module provides accurate cardinality and cost estimates for query plan nodes, replacing hardcoded defaults with statistics-based calculations.

### 1.1 Black-Box Specification

```
estimateCost : PlanNode × Statistics → Cost

Given a query plan node and database statistics, produces a cost estimate
representing the expected resource consumption (I/O, CPU, memory) to
evaluate that node.
```

### 1.2 External Interface

| Function | Signature | Purpose |
|----------|-----------|---------|
| `estimateCardinality` | `FromClause → Statistics → Nat` | Estimate output row count |
| `estimateSelectivity` | `Expr → Statistics → Float` | Estimate predicate pass rate |
| `estimateJoinCost` | `FromClause → FromClause → JoinType → Statistics → Cost` | Estimate join cost |
| `collectStatistics` | `Database → TableRef → TableStatistics` | Gather table statistics |

---

## 2. Data Structures

### 2.1 Statistics Repository

```lean
/-- Statistics for a single column -/
structure ColumnStatistics where
  /-- Column identifier -/
  column : ColumnRef
  /-- Number of distinct values -/
  distinctCount : Nat
  /-- Number of NULL values -/
  nullCount : Nat
  /-- Minimum value (for ordered types) -/
  minValue : Option Value
  /-- Maximum value (for ordered types) -/
  maxValue : Option Value
  /-- Histogram buckets for value distribution -/
  histogram : Option Histogram
  deriving Repr

/-- Statistics for a single table -/
structure TableStatistics where
  /-- Table identifier -/
  table : TableRef
  /-- Total row count -/
  rowCount : Nat
  /-- Average row size in bytes -/
  avgRowSize : Nat
  /-- Column-level statistics -/
  columns : List ColumnStatistics
  /-- When statistics were last updated -/
  lastUpdated : Timestamp
  deriving Repr

/-- Histogram for value distribution -/
structure Histogram where
  /-- Bucket boundaries (n+1 values for n buckets) -/
  boundaries : Array Value
  /-- Row count per bucket -/
  counts : Array Nat
  /-- Number of distinct values per bucket -/
  distinctsPerBucket : Array Nat
  deriving Repr

/-- Global statistics repository -/
structure Statistics where
  /-- Per-table statistics -/
  tables : List TableStatistics
  /-- Default cardinality for unknown tables -/
  defaultCardinality : Nat := 1000
  /-- Default selectivity for unknown predicates -/
  defaultSelectivity : Float := 0.1
  deriving Repr
```

### 2.2 Cost Model

```lean
/-- Cost estimate with breakdown -/
structure Cost where
  /-- Estimated I/O cost (disk reads) -/
  ioCost : Float
  /-- Estimated CPU cost (comparisons, computations) -/
  cpuCost : Float
  /-- Estimated memory cost (intermediate buffers) -/
  memoryCost : Float
  /-- Estimated output cardinality -/
  outputRows : Nat
  deriving Repr, BEq

/-- Total cost for comparison -/
def Cost.total (c : Cost) : Float :=
  c.ioCost + c.cpuCost + c.memoryCost
```

---

## 3. Functional Specifications

### 3.1 Cardinality Estimation

#### 3.1.1 Base Table Cardinality

```
Function: estimateTableCardinality
Input: t : TableRef, stats : Statistics
Output: Nat

Intended Function:
  IF stats contains entry for t
  THEN RETURN stats.tables[t].rowCount
  ELSE RETURN stats.defaultCardinality
```

**Postcondition:** Result > 0

#### 3.1.2 Filter Cardinality

```
Function: estimateFilterCardinality
Input: base : Nat, pred : Expr, stats : Statistics
Output: Nat

Intended Function:
  LET sel = estimateSelectivity pred stats
  IN RETURN max(1, floor(base * sel))
```

**Postcondition:** 1 ≤ Result ≤ base

#### 3.1.3 Join Cardinality

```
Function: estimateJoinCardinality
Input: left : Nat, right : Nat, jtype : JoinType, cond : Option Expr, stats : Statistics
Output: Nat

Intended Function:
  CASE jtype OF
    | inner =>
        LET sel = estimateJoinSelectivity cond stats
        IN max(1, floor(left * right * sel))
    | left =>
        max(left, estimateJoinCardinality left right inner cond stats)
    | right =>
        max(right, estimateJoinCardinality left right inner cond stats)
    | full =>
        left + right - estimateJoinCardinality left right inner cond stats
    | cross =>
        left * right
```

**Postconditions:**
- INNER: Result ≤ left × right
- LEFT: Result ≥ left
- RIGHT: Result ≥ right
- CROSS: Result = left × right

---

### 3.2 Selectivity Estimation

#### 3.2.1 Equality Predicate

```
Function: estimateEqualitySelectivity
Input: col : ColumnRef, val : Value, stats : Statistics
Output: Float

Intended Function:
  IF stats contains histogram for col
  THEN
    LET bucket = findBucket(stats.histogram, val)
    IN 1.0 / bucket.distinctCount
  ELSE IF stats contains distinctCount for col
  THEN 1.0 / stats.columns[col].distinctCount
  ELSE stats.defaultSelectivity
```

**Postcondition:** 0.0 < Result ≤ 1.0

#### 3.2.2 Range Predicate

```
Function: estimateRangeSelectivity
Input: col : ColumnRef, lo : Option Value, hi : Option Value, stats : Statistics
Output: Float

Intended Function:
  IF stats contains histogram for col
  THEN
    LET covered = countCoveredBuckets(stats.histogram, lo, hi)
    LET total = stats.histogram.counts.sum
    IN covered / total
  ELSE IF stats contains min/max for col
  THEN
    LET range = stats.columns[col].maxValue - stats.columns[col].minValue
    LET queryRange = (hi.getD max) - (lo.getD min)
    IN min(1.0, queryRange / range)
  ELSE 0.33  -- default for unbounded range
```

**Postcondition:** 0.0 ≤ Result ≤ 1.0

#### 3.2.3 Compound Predicate

```
Function: estimateCompoundSelectivity
Input: pred : Expr, stats : Statistics
Output: Float

Intended Function:
  CASE pred OF
    | BinOp AND p1 p2 =>
        -- Independence assumption
        estimateSelectivity p1 stats * estimateSelectivity p2 stats
    | BinOp OR p1 p2 =>
        -- Inclusion-exclusion
        LET s1 = estimateSelectivity p1 stats
        LET s2 = estimateSelectivity p2 stats
        IN s1 + s2 - (s1 * s2)
    | UnaryOp NOT p =>
        1.0 - estimateSelectivity p stats
    | _ =>
        estimateAtomicSelectivity pred stats
```

**Postcondition:** 0.0 ≤ Result ≤ 1.0

#### 3.2.4 Join Selectivity

```
Function: estimateJoinSelectivity
Input: cond : Option Expr, stats : Statistics
Output: Float

Intended Function:
  CASE cond OF
    | none => 1.0  -- cross join
    | some (BinOp EQ (Col c1) (Col c2)) =>
        -- Foreign key assumption: selectivity = 1/max(distinct(c1), distinct(c2))
        LET d1 = getDistinctCount c1 stats
        LET d2 = getDistinctCount c2 stats
        IN 1.0 / max(d1, d2)
    | some pred =>
        estimateSelectivity pred stats
```

**Postcondition:** 0.0 < Result ≤ 1.0

---

### 3.3 Cost Estimation

#### 3.3.1 Table Scan Cost

```
Function: estimateTableScanCost
Input: t : TableRef, stats : Statistics
Output: Cost

Intended Function:
  LET rows = estimateTableCardinality t stats
  LET rowSize = getAvgRowSize t stats
  LET pages = ceil(rows * rowSize / PAGE_SIZE)
  IN Cost.mk
       (ioCost := pages * IO_COST_PER_PAGE)
       (cpuCost := rows * CPU_COST_PER_ROW)
       (memoryCost := 0)
       (outputRows := rows)
```

#### 3.3.2 Filter Cost

```
Function: estimateFilterCost
Input: inputCost : Cost, pred : Expr, stats : Statistics
Output: Cost

Intended Function:
  LET sel = estimateSelectivity pred stats
  LET outputRows = max(1, floor(inputCost.outputRows * sel))
  IN Cost.mk
       (ioCost := inputCost.ioCost)  -- no additional I/O
       (cpuCost := inputCost.cpuCost + inputCost.outputRows * CPU_COST_PER_COMPARISON)
       (memoryCost := inputCost.memoryCost)
       (outputRows := outputRows)
```

#### 3.3.3 Hash Join Cost

```
Function: estimateHashJoinCost
Input: left : Cost, right : Cost, cond : Option Expr, stats : Statistics
Output: Cost

Intended Function:
  -- Build hash table on smaller input
  LET (build, probe) = if left.outputRows <= right.outputRows
                       then (left, right) else (right, left)
  LET sel = estimateJoinSelectivity cond stats
  LET outputRows = max(1, floor(left.outputRows * right.outputRows * sel))
  IN Cost.mk
       (ioCost := left.ioCost + right.ioCost)
       (cpuCost := left.cpuCost + right.cpuCost +
                   build.outputRows * CPU_COST_PER_HASH +
                   probe.outputRows * CPU_COST_PER_PROBE)
       (memoryCost := build.outputRows * HASH_ENTRY_SIZE)
       (outputRows := outputRows)
```

#### 3.3.4 Nested Loop Join Cost

```
Function: estimateNestedLoopCost
Input: outer : Cost, inner : Cost, cond : Option Expr, stats : Statistics
Output: Cost

Intended Function:
  LET sel = estimateJoinSelectivity cond stats
  LET outputRows = max(1, floor(outer.outputRows * inner.outputRows * sel))
  IN Cost.mk
       (ioCost := outer.ioCost + outer.outputRows * inner.ioCost)
       (cpuCost := outer.cpuCost + outer.outputRows * inner.cpuCost +
                   outer.outputRows * inner.outputRows * CPU_COST_PER_COMPARISON)
       (memoryCost := 0)  -- no memory for nested loop
       (outputRows := outputRows)
```

---

## 4. Statistics Collection

### 4.1 Full Table Scan Statistics

```
Function: collectTableStatistics
Input: db : Database, t : TableRef
Output: TableStatistics

Intended Function:
  LET rows = executeCount(db, t)
  LET columns = FOR EACH col IN schema(t):
    LET distinct = executeCountDistinct(db, t, col)
    LET nulls = executeCountNull(db, t, col)
    LET (minVal, maxVal) = executeMinMax(db, t, col)
    IN ColumnStatistics.mk col distinct nulls minVal maxVal none
  IN TableStatistics.mk t rows (estimateRowSize t) columns now()
```

### 4.2 Sampled Statistics

```
Function: collectSampledStatistics
Input: db : Database, t : TableRef, sampleRate : Float
Output: TableStatistics

Precondition: 0.0 < sampleRate ≤ 1.0

Intended Function:
  LET sample = executeSample(db, t, sampleRate)
  LET scaleFactor = 1.0 / sampleRate
  -- Collect statistics on sample, scale up counts
  LET rawStats = collectTableStatistics(sample)
  IN rawStats.scaleBy(scaleFactor)
```

### 4.3 Histogram Construction

```
Function: buildEquiHeightHistogram
Input: db : Database, t : TableRef, col : ColumnRef, numBuckets : Nat
Output: Histogram

Precondition: numBuckets > 0

Intended Function:
  LET sortedValues = executeOrderedSelect(db, t, col)
  LET rowsPerBucket = ceil(sortedValues.length / numBuckets)
  LET boundaries = [sortedValues[0],
                    sortedValues[rowsPerBucket],
                    sortedValues[2*rowsPerBucket],
                    ...,
                    sortedValues[sortedValues.length - 1]]
  LET counts = [rowsPerBucket, rowsPerBucket, ..., remainder]
  LET distincts = FOR EACH bucket: countDistinctInBucket(bucket)
  IN Histogram.mk boundaries counts distincts
```

---

## 5. Correctness Conditions

### 5.1 Cardinality Bounds

```lean
theorem cardinality_positive (from_ : FromClause) (stats : Statistics) :
  estimateCardinality from_ stats > 0

theorem filter_reduces_cardinality (base : Nat) (pred : Expr) (stats : Statistics) :
  estimateFilterCardinality base pred stats ≤ base

theorem cross_join_cardinality (l r : Nat) (stats : Statistics) :
  estimateJoinCardinality l r .cross none stats = l * r
```

### 5.2 Selectivity Bounds

```lean
theorem selectivity_in_unit_interval (pred : Expr) (stats : Statistics) :
  0.0 ≤ estimateSelectivity pred stats ∧ estimateSelectivity pred stats ≤ 1.0

theorem and_selectivity_product (p1 p2 : Expr) (stats : Statistics) :
  estimateSelectivity (Expr.binOp .and p1 p2) stats ≤
  min (estimateSelectivity p1 stats) (estimateSelectivity p2 stats)

theorem or_selectivity_sum (p1 p2 : Expr) (stats : Statistics) :
  estimateSelectivity (Expr.binOp .or p1 p2) stats ≥
  max (estimateSelectivity p1 stats) (estimateSelectivity p2 stats)
```

### 5.3 Cost Monotonicity

```lean
theorem filter_cost_bounded (input : Cost) (pred : Expr) (stats : Statistics) :
  (estimateFilterCost input pred stats).ioCost = input.ioCost

theorem join_cost_nonnegative (left right : Cost) (cond : Option Expr) (stats : Statistics) :
  (estimateHashJoinCost left right cond stats).total ≥ 0
```

---

## 6. Configuration Parameters

```lean
structure CostModelConfig where
  /-- I/O cost per page read -/
  IO_COST_PER_PAGE : Float := 1.0
  /-- CPU cost per row processed -/
  CPU_COST_PER_ROW : Float := 0.01
  /-- CPU cost per comparison -/
  CPU_COST_PER_COMPARISON : Float := 0.005
  /-- CPU cost per hash operation -/
  CPU_COST_PER_HASH : Float := 0.01
  /-- CPU cost per hash probe -/
  CPU_COST_PER_PROBE : Float := 0.005
  /-- Size of hash table entry in bytes -/
  HASH_ENTRY_SIZE : Nat := 16
  /-- Database page size in bytes -/
  PAGE_SIZE : Nat := 8192
  /-- Default histogram bucket count -/
  DEFAULT_HISTOGRAM_BUCKETS : Nat := 100
  deriving Repr
```

---

## 7. Error Handling

| Condition | Handling |
|-----------|----------|
| Table not in statistics | Use `defaultCardinality` |
| Column not in statistics | Use `defaultSelectivity` |
| Histogram bucket empty | Use uniform distribution |
| Overflow in cardinality | Cap at `Nat.max` |
| Division by zero in selectivity | Return `defaultSelectivity` |

---

## 8. Integration Points

### 8.1 With Join Reordering (PR C)

```lean
/-- Replace JoinNode.estimatedRows with statistics-based estimate -/
def JoinNode.leafWithStats (t : TableRef) (stats : Statistics) : JoinNode :=
  { table := t
  , estimatedRows := estimateTableCardinality t stats
  , originalTables := [getTableName t] }

/-- Replace findCheapestPair cost calculation -/
def estimatePairCost (n1 n2 : JoinNode) (edge : Option JoinEdge) (stats : Statistics) : Nat :=
  (estimateHashJoinCost
    (Cost.mk 0 0 0 n1.estimatedRows)
    (Cost.mk 0 0 0 n2.estimatedRows)
    (edge.map (·.predicate))
    stats).outputRows
```

### 8.2 With Predicate Pushdown (PR B)

```lean
/-- Estimate benefit of pushing predicate -/
def estimatePushdownBenefit (pred : Expr) (from_ : FromClause) (stats : Statistics) : Float :=
  let beforeCost := estimateCost from_ stats
  let sel := estimateSelectivity pred stats
  let afterCost := beforeCost.outputRows.toFloat * sel
  beforeCost.outputRows.toFloat - afterCost
```

---

## 9. Testing Strategy

### 9.1 Unit Tests

```lean
#guard estimateSelectivity (Expr.binOp .eq (Expr.col ⟨"x", none⟩) (Expr.lit (Value.int 1)))
       defaultStats == 0.1

#guard estimateCardinality (.table ⟨"users", none⟩)
       (Statistics.mk [TableStatistics.mk ⟨"users", none⟩ 5000 100 [] now] 1000 0.1) == 5000
```

### 9.2 Property Tests

```lean
/-- Selectivity is always in [0,1] -/
def prop_selectivity_bounded (pred : Expr) (stats : Statistics) : Bool :=
  let sel := estimateSelectivity pred stats
  0.0 ≤ sel ∧ sel ≤ 1.0

/-- AND selectivity ≤ min of operands -/
def prop_and_selectivity (p1 p2 : Expr) (stats : Statistics) : Bool :=
  estimateSelectivity (.binOp .and p1 p2) stats ≤
  min (estimateSelectivity p1 stats) (estimateSelectivity p2 stats)
```

### 9.3 Integration Tests

- Compare estimated vs actual cardinality on Spider benchmark
- Measure estimation error: `|estimated - actual| / actual`
- Target: median error < 2x, 90th percentile < 10x

---

## 10. References

- Selinger et al., "Access Path Selection in a Relational Database Management System" (1979)
- PostgreSQL EXPLAIN documentation
- "Query Optimization" chapter in Database System Concepts (Silberschatz)
