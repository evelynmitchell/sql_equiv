# Partition Pruning

## Cleanroom Specification

**Module:** `SqlEquiv/PartitionPruning.lean`
**Phase:** 6 - Physical Optimization
**Dependencies:** PR 0 (OptimizerUtils), Predicate Pushdown, Advanced Cost Estimation

---

## 1. Intended Function

Partition Pruning eliminates irrelevant partitions from query execution by analyzing query predicates against table partition schemes, significantly reducing I/O for queries on partitioned tables.

### 1.1 Black-Box Specification

```
prunePartitions : SelectStmt × PartitionCatalog → SelectStmt × PrunedPartitions

Given a SELECT statement and partition metadata, produces a semantically
equivalent statement annotated with partition elimination information.
```

### 1.2 Pruning Categories

| Pruning Type | Description | Example |
|--------------|-------------|---------|
| Static pruning | Based on constant predicates | `WHERE year = 2024` |
| Dynamic pruning | Based on join predicates | `WHERE year = (SELECT ...)` |
| Range pruning | Based on range predicates | `WHERE date BETWEEN ...` |
| List pruning | Based on IN predicates | `WHERE region IN ('US', 'EU')` |
| Composite pruning | Multi-column partitions | `WHERE (year, month) = (2024, 1)` |

### 1.3 External Interface

| Function | Signature | Purpose |
|----------|-----------|---------|
| `analyzePartitionPruning` | `SelectStmt → PartitionCatalog → PruningAnalysis` | Analyze pruning opportunities |
| `prunePartitions` | `SelectStmt → PruningAnalysis → SelectStmt` | Apply pruning |
| `getPrunedPartitions` | `PruningAnalysis → List PartitionId` | Get eliminated partitions |
| `estimatePruningBenefit` | `PruningAnalysis → Statistics → Cost` | Estimate benefit |

---

## 2. Data Structures

### 2.1 Partition Definition

```lean
/-- Partitioning strategy for a table -/
inductive PartitionStrategy where
  | range       -- Partition by value ranges
  | list        -- Partition by explicit value lists
  | hash        -- Partition by hash of column value
  | composite   -- Combination of strategies
  deriving Repr, BEq

/-- Definition of a partitioned table -/
structure PartitionedTable where
  /-- Table name -/
  table : TableRef
  /-- Partitioning strategy -/
  strategy : PartitionStrategy
  /-- Partition key columns -/
  partitionKeys : List ColumnRef
  /-- Partition definitions -/
  partitions : List PartitionDef
  /-- Sub-partitioning (if any) -/
  subpartitioning : Option PartitionedTable
  deriving Repr

/-- Single partition definition -/
structure PartitionDef where
  /-- Partition identifier -/
  id : PartitionId
  /-- Partition name -/
  name : String
  /-- Boundary specification -/
  boundary : PartitionBoundary
  /-- Statistics for this partition -/
  statistics : Option PartitionStatistics
  deriving Repr

/-- Partition boundary specification -/
inductive PartitionBoundary where
  | rangeBound (lower : Option Value) (upper : Option Value) (upperInclusive : Bool)
  | listBound (values : List Value)
  | hashBound (modulus : Nat) (remainder : Nat)
  deriving Repr, BEq

/-- Partition-level statistics -/
structure PartitionStatistics where
  /-- Row count in partition -/
  rowCount : Nat
  /-- Size in bytes -/
  sizeBytes : Nat
  /-- Min/max values of partition key -/
  minValue : Option Value
  maxValue : Option Value
  deriving Repr
```

### 2.2 Partition Catalog

```lean
/-- Catalog of partitioned tables -/
structure PartitionCatalog where
  /-- All partitioned tables -/
  tables : List PartitionedTable
  /-- Lookup by table name -/
  byTable : HashMap TableRef PartitionedTable
  deriving Repr
```

### 2.3 Pruning Result

```lean
/-- Result of partition pruning analysis -/
structure PruningAnalysis where
  /-- Table being analyzed -/
  table : PartitionedTable
  /-- Predicates relevant to partition key -/
  relevantPredicates : List Expr
  /-- Partitions that must be scanned -/
  requiredPartitions : List PartitionId
  /-- Partitions that can be eliminated -/
  prunedPartitions : List PartitionId
  /-- Type of pruning applied -/
  pruningType : PruningType
  /-- Estimated rows eliminated -/
  estimatedRowsEliminated : Nat
  deriving Repr

/-- Type of pruning that can be applied -/
inductive PruningType where
  | none          -- No pruning possible
  | static        -- Pruning from constant predicates
  | dynamic       -- Pruning from runtime values
  | partial       -- Some partitions pruned
  | complete      -- All but one partition pruned
  deriving Repr, BEq
```

---

## 3. Functional Specifications

### 3.1 Predicate Analysis

#### 3.1.1 Extract Partition-Relevant Predicates

```
Function: extractPartitionPredicates
Input: where_ : Option Expr, partKeys : List ColumnRef
Output: List Expr

Intended Function:
  CASE where_ OF
    | none => []
    | some expr =>
        LET conjuncts = flattenAnd expr
        IN conjuncts.filter (fun p =>
          (getReferencedColumns p).any (· ∈ partKeys)
        )
```

#### 3.1.2 Classify Predicate for Pruning

```
Function: classifyPredicate
Input: pred : Expr, partKey : ColumnRef
Output: PredicateClass

Intended Function:
  CASE pred OF
    | BinOp EQ (Col c) (Lit v) =>
        IF c = partKey
        THEN equalityOnKey v
        ELSE notRelevant

    | BinOp EQ (Lit v) (Col c) =>
        IF c = partKey
        THEN equalityOnKey v
        ELSE notRelevant

    | BinOp op (Col c) (Lit v) WHERE op ∈ [LT, LE, GT, GE] =>
        IF c = partKey
        THEN rangeOnKey op v
        ELSE notRelevant

    | InList (Col c) false vals WHERE c = partKey =>
        listOnKey vals

    | BinOp AND p1 p2 =>
        combine (classifyPredicate p1 partKey) (classifyPredicate p2 partKey)

    | _ => notRelevant

inductive PredicateClass where
  | equalityOnKey (v : Value)
  | rangeOnKey (op : BinOp) (bound : Value)
  | listOnKey (vals : List Value)
  | notRelevant
  deriving Repr
```

---

### 3.2 Partition Elimination

#### 3.2.1 Prune Range Partitions

```
Function: pruneRangePartitions
Input: partitions : List PartitionDef, pred : PredicateClass
Output: List PartitionId

Intended Function:
  CASE pred OF
    | equalityOnKey v =>
        -- Only keep partition containing v
        partitions.filter (fun p =>
          CASE p.boundary OF
            | rangeBound lo hi _ =>
                (lo.isNone OR lo.get! <= v) AND
                (hi.isNone OR v < hi.get!)
            | _ => true
        ) |>.map (·.id)

    | rangeOnKey LT bound =>
        -- Keep partitions where lower bound < bound
        partitions.filter (fun p =>
          CASE p.boundary OF
            | rangeBound lo _ _ => lo.isNone OR lo.get! < bound
            | _ => true
        ) |>.map (·.id)

    | rangeOnKey GE bound =>
        -- Keep partitions where upper bound >= bound
        partitions.filter (fun p =>
          CASE p.boundary OF
            | rangeBound _ hi _ => hi.isNone OR hi.get! >= bound
            | _ => true
        ) |>.map (·.id)

    | listOnKey vals =>
        -- Keep partitions containing any of the values
        partitions.filter (fun p =>
          vals.any (valueInPartition · p.boundary)
        ) |>.map (·.id)

    | notRelevant =>
        -- No pruning possible
        partitions.map (·.id)
```

#### 3.2.2 Prune List Partitions

```
Function: pruneListPartitions
Input: partitions : List PartitionDef, pred : PredicateClass
Output: List PartitionId

Intended Function:
  CASE pred OF
    | equalityOnKey v =>
        -- Only keep partition containing v
        partitions.filter (fun p =>
          CASE p.boundary OF
            | listBound values => v ∈ values
            | _ => true
        ) |>.map (·.id)

    | listOnKey vals =>
        -- Keep partitions containing any of the values
        partitions.filter (fun p =>
          CASE p.boundary OF
            | listBound values => (vals ∩ values).nonEmpty
            | _ => true
        ) |>.map (·.id)

    | rangeOnKey _ _ =>
        -- Range predicates on list partitions: check each value
        partitions.filter (fun p =>
          CASE p.boundary OF
            | listBound values => values.any (satisfiesRangePredicate · pred)
            | _ => true
        ) |>.map (·.id)

    | notRelevant =>
        partitions.map (·.id)
```

#### 3.2.3 Prune Hash Partitions

```
Function: pruneHashPartitions
Input: partitions : List PartitionDef, pred : PredicateClass
Output: List PartitionId

Intended Function:
  CASE pred OF
    | equalityOnKey v =>
        -- Can prune to single partition
        LET h = hashValue v
        partitions.filter (fun p =>
          CASE p.boundary OF
            | hashBound modulus remainder => h % modulus = remainder
            | _ => true
        ) |>.map (·.id)

    | listOnKey vals =>
        -- Keep partitions matching any value's hash
        LET hashes = vals.map hashValue
        partitions.filter (fun p =>
          CASE p.boundary OF
            | hashBound modulus remainder =>
                hashes.any (fun h => h % modulus = remainder)
            | _ => true
        ) |>.map (·.id)

    | rangeOnKey _ _ =>
        -- Cannot prune hash partitions with range predicates
        partitions.map (·.id)

    | notRelevant =>
        partitions.map (·.id)
```

---

### 3.3 Composite Partition Pruning

#### 3.3.1 Analyze Composite Partitions

```
Function: analyzeCompositePartitions
Input: table : PartitionedTable, preds : List Expr
Output: PruningAnalysis

Intended Function:
  -- For composite partitions, analyze each level

  -- Level 1: Main partitions
  LET mainPreds = preds.filter (referencesColumn · table.partitionKeys[0])
  LET mainPruned = prunePartitions table.partitions mainPreds

  -- Level 2: Sub-partitions (if any)
  CASE table.subpartitioning OF
    | none =>
        PruningAnalysis.mk table preds mainPruned ...
    | some subTable =>
        LET subPreds = preds.filter (referencesColumn · subTable.partitionKeys[0])
        LET subPruned = FOR EACH mainPart IN mainPruned:
          prunePartitions mainPart.subpartitions subPreds
        PruningAnalysis.mk table preds (flatten subPruned) ...
```

#### 3.3.2 Multi-Column Range Pruning

```
Function: pruneMultiColumnRange
Input: partitions : List PartitionDef, preds : List (ColumnRef × PredicateClass)
Output: List PartitionId

Intended Function:
  -- For multi-column partition keys (year, month, day):
  -- WHERE year = 2024 AND month = 1 AND day BETWEEN 1 AND 15

  partitions.filter (fun p =>
    preds.all (fun (col, pred) =>
      partitionSatisfiesPredicate p col pred
    )
  ) |>.map (·.id)
```

---

### 3.4 Dynamic Pruning

#### 3.4.1 Identify Dynamic Pruning Opportunities

```
Function: identifyDynamicPruning
Input: stmt : SelectStmt, table : PartitionedTable
Output: Option DynamicPruningInfo

Intended Function:
  -- Look for join predicates that can enable runtime pruning
  -- E.g., SELECT * FROM sales s JOIN dates d ON s.date_id = d.id WHERE d.year = 2024

  LET joins = extractJoinPredicates stmt.fromClause
  LET partKey = table.partitionKeys[0]

  FOR EACH join IN joins:
    IF join.left = partKey OR join.right = partKey
    THEN
      LET otherSide = IF join.left = partKey THEN join.right ELSE join.left
      LET otherTable = getTable otherSide
      LET filterOnOther = findFilters stmt.whereClause otherTable

      IF filterOnOther.nonEmpty
      THEN RETURN some (DynamicPruningInfo.mk join otherTable filterOnOther)

  RETURN none

structure DynamicPruningInfo where
  /-- The join enabling dynamic pruning -/
  join : JoinPredicate
  /-- The dimension table -/
  dimensionTable : TableRef
  /-- Filters on dimension table -/
  dimensionFilters : List Expr
  deriving Repr
```

#### 3.4.2 Generate Runtime Filter

```
Function: generateRuntimeFilter
Input: info : DynamicPruningInfo, partTable : PartitionedTable
Output: RuntimeFilter

Intended Function:
  -- Generate a runtime filter that:
  -- 1. Executes the dimension query
  -- 2. Collects distinct partition key values
  -- 3. Uses them to prune partitions before scanning fact table

  LET dimensionQuery = SelectStmt.mk
    true  -- DISTINCT
    [SelectItem.exprItem (Expr.col info.join.dimensionCol) none]
    (some (FromClause.table info.dimensionTable))
    (unflattenAnd info.dimensionFilters)
    [] [] [] none none

  RuntimeFilter.mk
    partTable.table
    partTable.partitionKeys[0]
    dimensionQuery
```

---

## 4. Correctness Conditions

### 4.1 Pruning Safety

```lean
/-- Pruning never eliminates rows that satisfy the query -/
axiom partition_pruning_safe (stmt : SelectStmt) (analysis : PruningAnalysis) :
  ∀ db row,
    row ∈ evalSelect db stmt →
    getPartition row analysis.table ∈ analysis.requiredPartitions
```

### 4.2 Range Pruning Correctness

```lean
/-- Range partition pruning is correct -/
theorem range_pruning_correct (partitions : List PartitionDef)
  (bound : Value) (op : BinOp) (h : op ∈ [.lt, .le, .gt, .ge]) :
  let pruned := pruneRangePartitions partitions (rangeOnKey op bound)
  ∀ v, satisfies v op bound →
    ∃ p ∈ pruned, valueInPartition v p.boundary
```

### 4.3 List Pruning Correctness

```lean
/-- List partition pruning is correct -/
theorem list_pruning_correct (partitions : List PartitionDef) (vals : List Value) :
  let pruned := pruneListPartitions partitions (listOnKey vals)
  ∀ v ∈ vals,
    ∃ p ∈ pruned, valueInPartition v p.boundary
```

### 4.4 Completeness

```lean
/-- Pruning eliminates all irrelevant partitions -/
theorem pruning_complete (table : PartitionedTable) (pred : Expr)
  (h : isExactPredicate pred table.partitionKeys) :
  let analysis := analyzePartitionPruning stmt table pred
  ∀ p ∈ analysis.prunedPartitions,
    ∀ row ∈ partition p, NOT (evalPred db pred row)
```

---

## 5. Optimization Strategies

### 5.1 Predicate Ordering

```
Strategy: Evaluate most selective partition predicates first

Example:
  WHERE region = 'US' AND date >= '2024-01-01'

  If partitioned by (region, date):
  1. First prune by region (eliminates ~90% of partitions)
  2. Then prune by date within US region
```

### 5.2 Constraint Propagation

```
Function: propagateConstraints
Input: pred : Expr, partitions : List PartitionDef
Output: Expr

Intended Function:
  -- Use partition bounds to strengthen predicates

  -- Example: Partition p1 has date < '2024-01-01'
  -- Query: WHERE date >= '2024-01-01'
  -- Can skip p1 entirely (no rows can match)

  -- Also: For remaining partitions, can add implied predicates
  -- Partition p2 has '2024-01-01' <= date < '2024-02-01'
  -- Implied: date < '2024-02-01' is always true for p2
```

### 5.3 Partition-Wise Joins

```
Function: optimizePartitionWiseJoin
Input: stmt : SelectStmt, leftTable : PartitionedTable, rightTable : PartitionedTable
Output: SelectStmt

Intended Function:
  -- If both tables partitioned on join key with aligned boundaries,
  -- can join partition-by-partition

  IF alignedPartitioning leftTable rightTable
  THEN
    -- Rewrite as UNION ALL of per-partition joins
    LET partitionJoins = FOR i FROM 0 TO numPartitions:
      joinSinglePartition leftTable.partitions[i] rightTable.partitions[i]
    UNION ALL partitionJoins
  ELSE
    stmt  -- No optimization possible
```

---

## 6. Integration Points

### 6.1 With Predicate Pushdown (PR B)

```lean
/-- Push predicates before partition pruning analysis -/
def optimizeWithPartitionAwarePushdown (stmt : SelectStmt) (catalog : PartitionCatalog) : SelectStmt :=
  -- First push predicates as deep as possible
  let pushed := pushPredicateDown stmt
  -- Then analyze partition pruning with pushed predicates
  let pruned := analyzeAndApplyPruning pushed catalog
  pruned
```

### 6.2 With Cost Estimation

```lean
/-- Partition statistics improve cost estimates -/
def estimateCostWithPartitionStats (from_ : FromClause) (analysis : PruningAnalysis)
    (stats : Statistics) : Cost :=
  -- Use partition-level statistics instead of table-level
  let partitionStats := analysis.requiredPartitions.map (getPartitionStats stats)
  let totalRows := partitionStats.map (·.rowCount) |>.sum
  estimateCostWithRows from_ totalRows stats
```

### 6.3 With Query Execution

```lean
/-- Pass pruning information to executor -/
structure ExecutionPlan where
  /-- Logical plan -/
  logicalPlan : SelectStmt
  /-- Partition pruning hints -/
  partitionHints : List PruningAnalysis
  /-- Runtime filters for dynamic pruning -/
  runtimeFilters : List RuntimeFilter
  deriving Repr
```

---

## 7. Algorithm

### 7.1 Main Algorithm

```
Algorithm: PartitionPruning

Input: stmt : SelectStmt, catalog : PartitionCatalog
Output: (stmt' : SelectStmt, analyses : List PruningAnalysis)

1. IDENTIFY partitioned tables in query
   partTables := findPartitionedTables stmt.fromClause catalog

2. FOR EACH partitioned table T:
   a. Extract predicates relevant to T's partition key
      preds := extractPartitionPredicates stmt.whereClause T.partitionKeys

   b. Classify predicates
      classified := preds.map (classifyPredicate · T.partitionKeys[0])

   c. Prune partitions based on strategy
      CASE T.strategy OF
        | range => pruned := pruneRangePartitions T.partitions classified
        | list => pruned := pruneListPartitions T.partitions classified
        | hash => pruned := pruneHashPartitions T.partitions classified
        | composite => pruned := analyzeCompositePartitions T preds

   d. Record analysis
      analyses := analyses ++ [PruningAnalysis.mk T preds pruned ...]

3. CHECK for dynamic pruning opportunities
   FOR EACH partTable IN partTables:
     dynInfo := identifyDynamicPruning stmt partTable
     IF dynInfo.isSome THEN
       runtimeFilters := runtimeFilters ++ [generateRuntimeFilter dynInfo.get! partTable]

4. ANNOTATE statement with pruning information
   stmt' := annotateWithPruning stmt analyses

5. RETURN (stmt', analyses)
```

### 7.2 Complexity

- Predicate extraction: O(P) where P = predicate count
- Partition pruning: O(N × P) where N = partition count
- Dynamic pruning analysis: O(J × N) where J = join count

---

## 8. Testing Strategy

### 8.1 Unit Tests

```lean
-- Range pruning with equality
testPartitionPruning
  table: sales (PARTITION BY RANGE (year))
         p2022: year < 2023
         p2023: 2023 <= year < 2024
         p2024: 2024 <= year
  query: "SELECT * FROM sales WHERE year = 2024"
  expected: [p2024]

-- List pruning
testPartitionPruning
  table: orders (PARTITION BY LIST (region))
         p_us: 'US'
         p_eu: 'EU', 'UK'
         p_asia: 'JP', 'CN', 'IN'
  query: "SELECT * FROM orders WHERE region IN ('US', 'UK')"
  expected: [p_us, p_eu]

-- Range pruning with range predicate
testPartitionPruning
  table: logs (PARTITION BY RANGE (log_date))
         p_jan: log_date < '2024-02-01'
         p_feb: '2024-02-01' <= log_date < '2024-03-01'
         p_mar: '2024-03-01' <= log_date
  query: "SELECT * FROM logs WHERE log_date >= '2024-02-15'"
  expected: [p_feb, p_mar]
```

### 8.2 Property Tests

```lean
/-- Pruning never removes matching rows -/
def prop_pruning_safe (stmt : SelectStmt) (table : PartitionedTable) (db : Database) : Bool :=
  let analysis := analyzePartitionPruning stmt table
  let originalResult := evalSelect db stmt
  let prunedResult := evalSelectWithPruning db stmt analysis
  originalResult == prunedResult

/-- Pruning reduces partition count -/
def prop_pruning_reduces_partitions (stmt : SelectStmt) (table : PartitionedTable) : Bool :=
  let analysis := analyzePartitionPruning stmt table
  analysis.requiredPartitions.length ≤ table.partitions.length
```

---

## 9. References

- Graefe, "Query Evaluation Techniques for Large Databases" (ACM Computing Surveys 1993)
- Oracle Partition Pruning documentation
- PostgreSQL Table Partitioning documentation
- Hive Partition Pruning implementation
