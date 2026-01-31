# Dynamic Programming Join Optimizer

## Cleanroom Specification

**Module:** `SqlEquiv/DPJoinOptimizer.lean`
**Phase:** 5 - Plan Space Expansion
**Dependencies:** PR 0 (OptimizerUtils), PR C (JoinReordering), Advanced Cost Estimation

---

## 1. Intended Function

The Dynamic Programming Join Optimizer replaces the greedy join ordering algorithm with a systematic exploration of all valid join orderings, guaranteeing an optimal plan within the considered search space.

### 1.1 Black-Box Specification

```
dpOptimizeJoins : FromClause × Statistics → FromClause

Given a FROM clause containing multiple joins and database statistics,
produces a semantically equivalent FROM clause with optimal join ordering
according to the cost model.
```

### 1.2 Comparison with Greedy

| Aspect | Greedy (PR C) | Dynamic Programming |
|--------|---------------|---------------------|
| Plans explored | O(n²) | O(3ⁿ) for bushy, O(n·2ⁿ) for left-deep |
| Optimality | Local (70-80% of optimal) | Global (within search space) |
| Memory | O(n) | O(2ⁿ) |
| Use case | > 10 tables | ≤ 10-12 tables |

### 1.3 External Interface

| Function | Signature | Purpose |
|----------|-----------|---------|
| `dpOptimizeJoins` | `FromClause → Statistics → FromClause` | Main entry point |
| `enumerateJoinOrders` | `List TableRef → List FromClause` | Generate all orderings |
| `dpBestPlan` | `Set TableRef → DPTable → Option PlanEntry` | Lookup best plan for subset |
| `computeJoinCost` | `PlanEntry → PlanEntry → JoinEdge → Statistics → Cost` | Cost a specific join |

---

## 2. Data Structures

### 2.1 Plan Representation

```lean
/-- A single plan entry in the DP table -/
structure PlanEntry where
  /-- Set of tables covered by this plan -/
  tables : Finset TableRef
  /-- The FROM clause representing this plan -/
  plan : FromClause
  /-- Best cost found so far -/
  cost : Cost
  /-- Interesting orderings (for merge joins) -/
  interestingOrders : List (List ColumnRef)
  deriving Repr

/-- DP table mapping table sets to best plans -/
abbrev DPTable := HashMap (Finset TableRef) PlanEntry
```

### 2.2 Join Graph

```lean
/-- Edge in the join graph -/
structure JoinGraphEdge where
  /-- Tables connected by this edge -/
  left : TableRef
  right : TableRef
  /-- Join predicate -/
  predicate : Expr
  /-- Estimated selectivity -/
  selectivity : Float
  deriving Repr, BEq

/-- Complete join graph -/
structure JoinGraph where
  /-- All tables (vertices) -/
  tables : List TableRef
  /-- All join predicates (edges) -/
  edges : List JoinGraphEdge
  /-- Cross-product predicates (not equality joins) -/
  crossProductPreds : List Expr
  deriving Repr
```

### 2.3 Search Space Configuration

```lean
/-- Configuration for DP search -/
structure DPConfig where
  /-- Maximum tables before falling back to greedy -/
  maxTablesForDP : Nat := 12
  /-- Consider bushy trees (not just left-deep) -/
  allowBushyTrees : Bool := true
  /-- Consider cross products -/
  allowCrossProducts : Bool := false
  /-- Prune plans worse than best by this factor -/
  pruningFactor : Float := 10.0
  /-- Track interesting orders for merge join -/
  trackInterestingOrders : Bool := true
  deriving Repr
```

---

## 3. Functional Specifications

### 3.1 Graph Construction

#### 3.1.1 Build Join Graph

```
Function: buildJoinGraph
Input: from_ : FromClause, predicates : List Expr
Output: JoinGraph

Intended Function:
  LET tables = extractLeafTables from_
  LET edges = FOR EACH pred IN predicates:
    IF isEquiJoinPredicate pred
    THEN
      LET (t1, t2) = extractJoinedTables pred
      some (JoinGraphEdge.mk t1 t2 pred (estimateSelectivity pred))
    ELSE none
  LET crossPreds = predicates.filter (NOT isEquiJoinPredicate ·)
  IN JoinGraph.mk tables (edges.filterMap id) crossPreds
```

#### 3.1.2 Extract Equi-Join Predicate

```
Function: isEquiJoinPredicate
Input: pred : Expr
Output: Bool

Intended Function:
  CASE pred OF
    | BinOp EQ (Col c1) (Col c2) =>
        c1.table ≠ c2.table  -- Must reference different tables
    | BinOp AND p1 p2 =>
        isEquiJoinPredicate p1 OR isEquiJoinPredicate p2
    | _ => false
```

---

### 3.2 Dynamic Programming Core

#### 3.2.1 Initialize Base Cases

```
Function: initializeDPTable
Input: graph : JoinGraph, stats : Statistics
Output: DPTable

Intended Function:
  LET table = HashMap.empty
  FOR EACH t IN graph.tables:
    LET singleton = Finset.singleton t
    LET baseCost = estimateTableScanCost t stats
    LET entry = PlanEntry.mk singleton (FromClause.table t) baseCost []
    table := table.insert singleton entry
  IN table
```

#### 3.2.2 Main DP Loop

```
Function: dpOptimize
Input: graph : JoinGraph, stats : Statistics, config : DPConfig
Output: PlanEntry

Intended Function:
  LET dp = initializeDPTable graph stats
  LET n = graph.tables.length

  -- Build plans of increasing size
  FOR size FROM 2 TO n:
    FOR EACH subset S of graph.tables WHERE |S| = size:
      LET bestPlan = none
      LET bestCost = infinity

      -- Try all ways to partition S into two non-empty parts
      FOR EACH (S1, S2) WHERE S1 ∪ S2 = S AND S1 ∩ S2 = ∅ AND S1 ≠ ∅ AND S2 ≠ ∅:
        -- Skip if not considering bushy trees and neither is single table
        IF NOT config.allowBushyTrees AND |S1| > 1 AND |S2| > 1
        THEN continue

        -- Get best plans for subsets
        LET p1 = dp.get S1
        LET p2 = dp.get S2

        IF p1.isNone OR p2.isNone
        THEN continue

        -- Find applicable join edges
        LET edges = findConnectingEdges graph.edges S1 S2
        IF edges.isEmpty AND NOT config.allowCrossProducts
        THEN continue

        -- Compute join cost
        LET joinCost = computeJoinCost p1.get! p2.get! edges stats

        IF joinCost.total < bestCost
        THEN
          bestPlan := some (buildJoinPlan p1.get! p2.get! edges)
          bestCost := joinCost.total

      -- Store best plan for this subset
      IF bestPlan.isSome
      THEN dp := dp.insert S (PlanEntry.mk S bestPlan.get! (Cost.mk bestCost ...) [])

  -- Return best plan for full set
  IN dp.get (Finset.ofList graph.tables)
```

#### 3.2.3 Find Connecting Edges

```
Function: findConnectingEdges
Input: edges : List JoinGraphEdge, s1 : Finset TableRef, s2 : Finset TableRef
Output: List JoinGraphEdge

Intended Function:
  edges.filter (fun e =>
    (e.left ∈ s1 AND e.right ∈ s2) OR
    (e.left ∈ s2 AND e.right ∈ s1)
  )
```

#### 3.2.4 Build Join Plan

```
Function: buildJoinPlan
Input: p1 : PlanEntry, p2 : PlanEntry, edges : List JoinGraphEdge
Output: FromClause

Intended Function:
  LET joinCond = edges.map (·.predicate) |> unflattenAnd |>.getD (Expr.lit (Value.bool true))
  IN FromClause.join p1.plan .inner p2.plan (some joinCond)
```

---

### 3.3 Cost Computation

#### 3.3.1 Join Cost Model

```
Function: computeJoinCost
Input: p1 : PlanEntry, p2 : PlanEntry, edges : List JoinGraphEdge, stats : Statistics
Output: Cost

Intended Function:
  LET leftRows = p1.cost.outputRows
  LET rightRows = p2.cost.outputRows

  -- Compute combined selectivity
  LET selectivity = edges.foldl (fun acc e => acc * e.selectivity) 1.0
  LET outputRows = max 1 (floor (leftRows * rightRows * selectivity))

  -- Choose join algorithm based on sizes
  LET joinAlgCost =
    IF leftRows < HASH_BUILD_THRESHOLD AND rightRows < HASH_BUILD_THRESHOLD
    THEN estimateHashJoinCost leftRows rightRows
    ELSE IF hasMatchingOrder p1 p2 edges
    THEN estimateMergeJoinCost leftRows rightRows
    ELSE estimateHashJoinCost leftRows rightRows

  IN Cost.mk
    (ioCost := p1.cost.ioCost + p2.cost.ioCost + joinAlgCost.ioCost)
    (cpuCost := p1.cost.cpuCost + p2.cost.cpuCost + joinAlgCost.cpuCost)
    (memoryCost := max p1.cost.memoryCost (joinAlgCost.memoryCost))
    (outputRows := outputRows)
```

---

### 3.4 Optimizations

#### 3.4.1 Pruning

```
Function: shouldPrune
Input: candidate : Cost, bestSoFar : Cost, config : DPConfig
Output: Bool

Intended Function:
  candidate.total > bestSoFar.total * config.pruningFactor
```

#### 3.4.2 Interesting Orders

```
Function: computeInterestingOrders
Input: plan : FromClause, edges : List JoinGraphEdge
Output: List (List ColumnRef)

Intended Function:
  -- Interesting orders are column orderings that could enable merge joins
  -- with pending joins or ORDER BY in outer query

  LET joinCols = edges.flatMap (fun e =>
    extractJoinColumns e.predicate
  )
  IN [joinCols]  -- Simplified: just track join column order
```

#### 3.4.3 Subset Enumeration

```
Function: enumerateSubsets
Input: tables : List TableRef, size : Nat
Output: List (Finset TableRef)

Intended Function:
  -- Generate all subsets of given size
  -- Use Gray code ordering for cache efficiency
  tables.combinations size |>.map Finset.ofList
```

---

## 4. Correctness Conditions

### 4.1 Semantic Preservation

```lean
/-- DP optimization preserves query semantics -/
axiom dp_preserves_semantics (from_ : FromClause) (stats : Statistics) :
  hasOnlyInnerJoins from_ = true →
  ∀ db, evalFrom db (dpOptimizeJoins from_ stats) = evalFrom db from_
```

### 4.2 Optimality

```lean
/-- DP finds optimal plan within search space -/
theorem dp_optimal (from_ : FromClause) (stats : Statistics) (config : DPConfig) :
  let result := dpOptimizeJoins from_ stats
  let allPlans := enumerateAllPlans from_ config
  ∀ plan ∈ allPlans,
    estimateCost result stats ≤ estimateCost plan stats
```

### 4.3 Completeness

```lean
/-- DP considers all valid join orderings -/
theorem dp_complete (tables : List TableRef) (config : DPConfig)
  (h : config.allowBushyTrees = true) :
  let explored := dpExploredPlans tables config
  let allValid := allValidJoinTrees tables
  allValid ⊆ explored
```

---

## 5. Search Space Analysis

### 5.1 Left-Deep Trees Only

```
Number of plans for n tables:
  n! (all permutations)

Example: 5 tables = 120 plans
         10 tables = 3,628,800 plans

Memory: O(2ⁿ) for DP table
Time: O(n · 2ⁿ) for enumeration
```

### 5.2 Bushy Trees (Full Search)

```
Number of plans for n tables:
  (2n-2)! / (n-1)!  (Catalan number variant)

Example: 5 tables = 1,680 plans
         10 tables ≈ 17.6 million plans

Memory: O(2ⁿ) for DP table (same)
Time: O(3ⁿ) for enumeration
```

### 5.3 Practical Limits

| Tables | Left-Deep Plans | Bushy Plans | Recommended |
|--------|-----------------|-------------|-------------|
| 5 | 120 | 1,680 | DP (either) |
| 8 | 40,320 | 2.0M | DP left-deep |
| 10 | 3.6M | 17.6M | DP left-deep |
| 12 | 479M | 28B | Greedy |
| 15 | 1.3T | — | Greedy + heuristics |

---

## 6. Algorithm Variants

### 6.1 Left-Deep Only

```
Function: dpLeftDeepOnly
Input: graph : JoinGraph, stats : Statistics
Output: PlanEntry

Intended Function:
  -- Only consider plans where right child is always a base table
  LET dp = initializeDPTable graph stats

  FOR size FROM 2 TO n:
    FOR EACH subset S WHERE |S| = size:
      FOR EACH table t IN S:
        LET S' = S \ {t}
        IF dp.contains S'
        THEN
          LET leftPlan = dp.get S'
          LET rightPlan = dp.get {t}
          -- Only consider t on the right (left-deep)
          LET cost = computeJoinCost leftPlan rightPlan ...
          updateIfBetter dp S cost (join leftPlan rightPlan)

  IN dp.get (Finset.ofList graph.tables)
```

### 6.2 With Cross Products (Star Queries)

```
Function: dpWithCrossProducts
Input: graph : JoinGraph, stats : Statistics
Output: PlanEntry

Intended Function:
  -- For star schemas, allow cross products between dimension tables
  -- if they'll eventually join with fact table

  LET dp = initializeDPTable graph stats

  FOR size FROM 2 TO n:
    FOR EACH subset S WHERE |S| = size:
      FOR EACH partition (S1, S2) of S:
        LET edges = findConnectingEdges graph.edges S1 S2

        -- Allow cross product if both will eventually connect to remaining tables
        LET allowCross = canEventuallyJoin (graph.tables \ S) S1 graph.edges AND
                         canEventuallyJoin (graph.tables \ S) S2 graph.edges

        IF edges.nonEmpty OR allowCross
        THEN
          -- ... standard DP logic
```

### 6.3 Adaptive Strategy

```
Function: adaptiveJoinOptimize
Input: from_ : FromClause, stats : Statistics
Output: FromClause

Intended Function:
  LET n = countTables from_

  IF n ≤ 6
  THEN dpOptimize from_ stats { allowBushyTrees := true }

  ELSE IF n ≤ 12
  THEN dpOptimize from_ stats { allowBushyTrees := false }  -- left-deep only

  ELSE
  -- Fall back to greedy for large queries
  greedyReorder from_ stats
```

---

## 7. Integration Points

### 7.1 Replacing Greedy (PR C)

```lean
/-- Replace greedyReorder with DP when beneficial -/
def reorderJoinsOptimal (from_ : FromClause) (stats : Statistics) : FromClause :=
  if countTables from_ ≤ dpConfig.maxTablesForDP
  then dpOptimizeJoins from_ stats
  else greedyReorder from_ stats  -- Fall back to greedy
```

### 7.2 With Cost Estimation

```lean
/-- DP requires good cost estimates to be effective -/
def dpWithStatistics (from_ : FromClause) (stats : Statistics) : FromClause :=
  if stats.tables.isEmpty
  then
    -- No statistics: use heuristics
    greedyReorder from_ defaultStats
  else
    dpOptimizeJoins from_ stats
```

---

## 8. Memory Management

### 8.1 DP Table Size

```lean
/-- Estimate memory for DP table -/
def estimateDPMemory (n : Nat) : Nat :=
  -- 2^n entries, each storing a plan
  let entries := 2 ^ n
  let bytesPerEntry := 256  -- Approximate
  entries * bytesPerEntry

-- Examples:
-- n=10: 1024 * 256 = 256 KB
-- n=15: 32768 * 256 = 8 MB
-- n=20: 1M * 256 = 256 MB
```

### 8.2 Pruning for Memory

```lean
/-- Prune DP table to limit memory -/
def pruneDPTable (dp : DPTable) (maxEntries : Nat) : DPTable :=
  if dp.size ≤ maxEntries
  then dp
  else
    -- Keep only best plans per size class
    let bySize := dp.toList.groupBy (fun e => e.1.card)
    let pruned := bySize.flatMap (fun (size, entries) =>
      entries.sortBy (fun e => e.2.cost.total)
             |>.take (maxEntries / dp.size.log2)
    )
    HashMap.ofList pruned
```

---

## 9. Testing Strategy

### 9.1 Correctness Tests

```lean
-- DP produces same result as exhaustive search (small cases)
#guard
  let from_ := parseFrom "a JOIN b ON a.x = b.x JOIN c ON b.y = c.y"
  let dpResult := dpOptimizeJoins from_ testStats
  let exhaustiveResult := exhaustiveSearch from_ testStats
  dpResult.cost == exhaustiveResult.cost

-- DP beats greedy on adversarial case
#guard
  let from_ := chainJoin 8  -- a JOIN b JOIN c JOIN ... (8 tables)
  let dpCost := (dpOptimizeJoins from_ skewedStats).cost
  let greedyCost := (greedyReorder from_ skewedStats).cost
  dpCost ≤ greedyCost
```

### 9.2 Performance Tests

```lean
-- DP completes in reasonable time
#guard_msgs in
  timeit "DP 10 tables" (dpOptimizeJoins (starSchema 10) testStats)
  -- Should complete in < 1 second

-- Memory stays bounded
#guard
  let dp := dpOptimizeJoins (chainJoin 12) testStats
  estimateMemoryUsed dp < 10_000_000  -- < 10 MB
```

### 9.3 Optimality Tests

```lean
/-- Verify DP finds known optimal for benchmark queries -/
def testKnownOptimal (query : String) (expectedCost : Nat) : Bool :=
  let from_ := parseFrom query
  let result := dpOptimizeJoins from_ benchmarkStats
  result.cost.total ≤ expectedCost.toFloat * 1.01  -- Within 1%
```

---

## 10. References

- Selinger et al., "Access Path Selection in a Relational Database Management System" (1979)
- Vance & Maier, "Rapid Bushy Join-Order Optimization with Cartesian Products" (SIGMOD 1996)
- Moerkotte & Neumann, "Analysis of Two Existing and One New Dynamic Programming Algorithm" (VLDB 2006)
- PostgreSQL GEQO (Genetic Query Optimizer) documentation
