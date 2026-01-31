# Materialized View Recognition

## Cleanroom Specification

**Module:** `SqlEquiv/MaterializedViewRecognition.lean`
**Phase:** 6 - Physical Optimization
**Dependencies:** PR A (ExprNormalization), Subquery Flattening, Advanced Cost Estimation

---

## 1. Intended Function

Materialized View Recognition detects when a query (or subquery) can be answered using pre-computed materialized views instead of accessing base tables, potentially providing significant performance improvements.

### 1.1 Black-Box Specification

```
rewriteWithMaterializedViews : SelectStmt × ViewCatalog → SelectStmt

Given a SELECT statement and a catalog of available materialized views,
produces a semantically equivalent statement that uses materialized views
where beneficial.
```

### 1.2 Rewrite Categories

| Category | Description | Example |
|----------|-------------|---------|
| Exact match | Query matches view definition exactly | View = Query |
| Subsumption | View contains superset of needed data | View has extra columns |
| Aggregation rollup | View has finer granularity than needed | Daily view → Monthly query |
| Join elimination | View pre-joins needed tables | View = A JOIN B |
| Partial match | View satisfies part of query | Use view for one subquery |

### 1.3 External Interface

| Function | Signature | Purpose |
|----------|-----------|---------|
| `findMatchingViews` | `SelectStmt → ViewCatalog → List ViewMatch` | Find candidate views |
| `rewriteWithView` | `SelectStmt → MaterializedView → SelectStmt` | Rewrite using view |
| `isViewApplicable` | `SelectStmt → MaterializedView → Bool` | Check view usability |
| `estimateViewBenefit` | `ViewMatch → Statistics → Cost` | Cost/benefit analysis |

---

## 2. Data Structures

### 2.1 Materialized View Definition

```lean
/-- Definition of a materialized view -/
structure MaterializedView where
  /-- View name -/
  name : String
  /-- View's SELECT statement -/
  definition : SelectStmt
  /-- Columns in the view -/
  columns : List ColumnDef
  /-- Whether view is kept up-to-date -/
  refreshMode : RefreshMode
  /-- When view was last refreshed -/
  lastRefresh : Timestamp
  /-- Base tables the view depends on -/
  baseTables : List TableRef
  /-- Statistics about view data -/
  statistics : Option TableStatistics
  deriving Repr

/-- Column definition in view -/
structure ColumnDef where
  /-- Column name in view -/
  name : String
  /-- Source expression -/
  sourceExpr : Expr
  /-- Whether this is a grouping column -/
  isGrouping : Bool
  /-- Whether this is an aggregate -/
  isAggregate : Bool
  deriving Repr

/-- View refresh mode -/
inductive RefreshMode where
  | immediate   -- Updated on base table change
  | deferred    -- Updated periodically
  | onDemand    -- Updated manually
  | stale       -- May contain outdated data
  deriving Repr, BEq
```

### 2.2 View Match Result

```lean
/-- Result of matching a query against views -/
structure ViewMatch where
  /-- The matching view -/
  view : MaterializedView
  /-- Type of match -/
  matchType : MatchType
  /-- Column mapping: query column → view column -/
  columnMapping : List (ColumnRef × ColumnRef)
  /-- Additional predicates needed on view -/
  additionalPredicates : List Expr
  /-- Additional aggregation needed -/
  additionalAggregation : Option AggregationSpec
  /-- Estimated benefit (cost reduction) -/
  estimatedBenefit : Float
  deriving Repr

/-- Type of view match -/
inductive MatchType where
  | exact           -- View definition = query
  | subsumption     -- View has superset of data
  | aggregationRollup -- View has finer granularity
  | partialCoverage -- View covers part of query
  deriving Repr, BEq

/-- Specification for additional aggregation -/
structure AggregationSpec where
  /-- Columns to group by -/
  groupBy : List ColumnRef
  /-- Aggregates to compute -/
  aggregates : List (AggFunc × ColumnRef × String)
  deriving Repr
```

### 2.3 View Catalog

```lean
/-- Catalog of available materialized views -/
structure ViewCatalog where
  /-- All defined views -/
  views : List MaterializedView
  /-- Index by base table -/
  byBaseTable : HashMap TableRef (List MaterializedView)
  /-- Index by column -/
  byColumn : HashMap ColumnRef (List MaterializedView)
  deriving Repr
```

---

## 3. Functional Specifications

### 3.1 View Matching

#### 3.1.1 Find Matching Views

```
Function: findMatchingViews
Input: query : SelectStmt, catalog : ViewCatalog
Output: List ViewMatch

Intended Function:
  LET candidates = []

  -- Find views that cover query's base tables
  LET queryTables = getFromClauseTableNames query.fromClause
  FOR EACH view IN catalog.views:
    IF queryTables ⊆ view.baseTables
    THEN candidates := candidates ++ [view]

  -- Check each candidate for usability
  LET matches = []
  FOR EACH view IN candidates:
    LET matchResult = tryMatchView query view
    IF matchResult.isSome
    THEN matches := matches ++ [matchResult.get!]

  -- Sort by estimated benefit
  IN matches.sortByDescending (·.estimatedBenefit)
```

#### 3.1.2 Try Match View

```
Function: tryMatchView
Input: query : SelectStmt, view : MaterializedView
Output: Option ViewMatch

Intended Function:
  -- Step 1: Check column coverage
  LET queryColumns = getReferencedColumns query
  LET viewColumns = view.columns.map (·.name)
  LET missingColumns = queryColumns.filter (NOT · ∈ viewColumns)
  IF missingColumns.nonEmpty AND NOT canDeriveColumns missingColumns view
  THEN RETURN none

  -- Step 2: Check predicate subsumption
  LET queryPreds = extractPredicates query
  LET viewPreds = extractPredicates view.definition
  IF NOT predicatesSubsumedBy viewPreds queryPreds
  THEN RETURN none

  -- Step 3: Check aggregation compatibility
  LET aggCompat = checkAggregationCompatibility query view
  IF aggCompat = incompatible
  THEN RETURN none

  -- Step 4: Build column mapping
  LET mapping = buildColumnMapping query view

  -- Step 5: Compute additional predicates
  LET additionalPreds = queryPreds.filter (NOT · ∈ viewPreds)

  -- Step 6: Compute additional aggregation if needed
  LET additionalAgg = IF aggCompat = needsRollup
                      THEN some (computeRollupSpec query view)
                      ELSE none

  -- Step 7: Estimate benefit
  LET benefit = estimateViewBenefit view query stats

  IN some (ViewMatch.mk view (classifyMatchType aggCompat)
           mapping additionalPreds additionalAgg benefit)
```

#### 3.1.3 Predicate Subsumption

```
Function: predicatesSubsumedBy
Input: viewPreds : List Expr, queryPreds : List Expr
Output: Bool

Intended Function:
  -- Query predicates must be at least as restrictive as view predicates
  -- E.g., view: year >= 2020, query: year = 2024 → OK (more restrictive)
  -- E.g., view: year = 2024, query: year >= 2020 → NOT OK (less restrictive)

  viewPreds.all (fun vp =>
    queryPreds.any (fun qp => impliesPredicate qp vp)
  )
```

#### 3.1.4 Check Implication

```
Function: impliesPredicate
Input: p1 : Expr, p2 : Expr
Output: Bool

Intended Function:
  -- p1 implies p2 if whenever p1 is true, p2 is also true

  -- Normalize both predicates
  LET n1 = normalizeExprCanonical p1
  LET n2 = normalizeExprCanonical p2

  -- Exact match
  IF n1 = n2
  THEN true

  -- Range implication: (x = 5) implies (x >= 0)
  ELSE IF isRangeSubset n1 n2
  THEN true

  -- Conjunction implication: (A AND B) implies A
  ELSE IF isConjunctionOf n1 n2
  THEN true

  ELSE false
```

---

### 3.2 Aggregation Compatibility

#### 3.2.1 Check Aggregation Compatibility

```
Function: checkAggregationCompatibility
Input: query : SelectStmt, view : MaterializedView
Output: AggregationCompatibility

Intended Function:
  LET queryGroupBy = query.groupBy
  LET viewGroupBy = view.definition.groupBy

  -- No aggregation in either
  IF queryGroupBy.isEmpty AND viewGroupBy.isEmpty
  THEN compatible

  -- Query needs aggregation, view doesn't have it
  ELSE IF queryGroupBy.nonEmpty AND viewGroupBy.isEmpty
  THEN incompatible

  -- View has aggregation, query doesn't
  ELSE IF queryGroupBy.isEmpty AND viewGroupBy.nonEmpty
  THEN
    -- OK if query references only grouping columns
    IF queryReferencesOnlyGroupingColumns query view
    THEN compatible
    ELSE incompatible

  -- Both have aggregation: check rollup possibility
  ELSE
    -- View granularity must be equal or finer than query
    IF isGroupByRefinement viewGroupBy queryGroupBy
    THEN needsRollup
    ELSE incompatible

inductive AggregationCompatibility where
  | compatible
  | needsRollup
  | incompatible
  deriving Repr, BEq
```

#### 3.2.2 Check Rollup Possibility

```
Function: isGroupByRefinement
Input: finer : List Expr, coarser : List Expr
Output: Bool

Intended Function:
  -- finer GROUP BY is a refinement of coarser if:
  -- 1. finer contains all columns from coarser
  -- 2. finer may have additional columns

  -- Example:
  -- View: GROUP BY year, month, day  (finer)
  -- Query: GROUP BY year, month      (coarser)
  -- → Valid rollup: SUM view totals per (year, month)

  coarser.all (fun c => c ∈ finer)
```

#### 3.2.3 Check Aggregate Rollup Validity

```
Function: canRollupAggregate
Input: agg : AggFunc
Output: Bool

Intended Function:
  -- Can roll up: SUM, COUNT, MIN, MAX
  -- Cannot roll up: AVG (need SUM/COUNT), COUNT DISTINCT, percentiles

  CASE agg OF
    | .sum => true       -- SUM(SUM(x)) = SUM(x)
    | .count => true     -- SUM(COUNT(x)) = COUNT(x)
    | .min => true       -- MIN(MIN(x)) = MIN(x)
    | .max => true       -- MAX(MAX(x)) = MAX(x)
    | .avg => false      -- Need SUM and COUNT separately
    | .countDistinct => false
    | _ => false
```

---

### 3.3 Query Rewriting

#### 3.3.1 Rewrite Query with View

```
Function: rewriteWithView
Input: query : SelectStmt, match : ViewMatch
Output: SelectStmt

Intended Function:
  -- Replace base table access with view access

  -- Step 1: Create FROM clause referencing view
  LET viewFrom = FromClause.table ⟨match.view.name, some "v"⟩

  -- Step 2: Rewrite SELECT items using column mapping
  LET newItems = query.items.map (rewriteSelectItem · match.columnMapping)

  -- Step 3: Add additional predicates as WHERE clause
  LET newWhere = unflattenAnd match.additionalPredicates

  -- Step 4: Add rollup aggregation if needed
  LET (newItems', newGroupBy) = MATCH match.additionalAggregation WITH
    | none => (newItems, [])
    | some spec =>
        LET rolledItems = applyRollupToItems newItems spec
        (rolledItems, spec.groupBy.map Expr.col)

  IN SelectStmt.mk
    query.distinct
    newItems'
    (some viewFrom)
    newWhere
    newGroupBy
    query.having
    query.orderBy
    query.limitVal
    query.offsetVal
```

#### 3.3.2 Rewrite Select Item

```
Function: rewriteSelectItem
Input: item : SelectItem, mapping : List (ColumnRef × ColumnRef)
Output: SelectItem

Intended Function:
  CASE item OF
    | ExprItem expr alias =>
        LET newExpr = rewriteExprWithMapping expr mapping
        SelectItem.exprItem newExpr alias
    | Star tableOpt =>
        -- Expand star to mapped columns
        expandStarWithMapping tableOpt mapping
```

#### 3.3.3 Apply Rollup

```
Function: applyRollupToItems
Input: items : List SelectItem, spec : AggregationSpec
Output: List SelectItem

Intended Function:
  items.map (fun item =>
    CASE item OF
      | ExprItem (Agg func arg _) alias =>
          -- Wrap aggregate: SUM(view_sum) instead of SUM(base_col)
          LET viewCol = findMappedColumn arg spec
          LET rollupFunc = getRollupFunction func
          SelectItem.exprItem (Expr.agg rollupFunc (some (Expr.col viewCol)) false) alias
      | other => other
  )
```

---

### 3.4 Freshness Checking

#### 3.4.1 Check View Freshness

```
Function: isViewFresh
Input: view : MaterializedView, query : SelectStmt, staleTolerance : Duration
Output: Bool

Intended Function:
  CASE view.refreshMode OF
    | immediate => true  -- Always fresh
    | deferred =>
        now() - view.lastRefresh < staleTolerance
    | onDemand =>
        now() - view.lastRefresh < staleTolerance
    | stale => false  -- Explicitly stale
```

#### 3.4.2 Staleness-Aware Matching

```
Function: findFreshMatchingViews
Input: query : SelectStmt, catalog : ViewCatalog, staleTolerance : Duration
Output: List ViewMatch

Intended Function:
  LET allMatches = findMatchingViews query catalog
  IN allMatches.filter (fun m => isViewFresh m.view query staleTolerance)
```

---

## 4. Correctness Conditions

### 4.1 Semantic Preservation

```lean
/-- View rewriting preserves query semantics -/
axiom view_rewrite_preserves_semantics
  (query : SelectStmt) (match : ViewMatch)
  (h : isViewFresh match.view query maxStaleness) :
  ∀ db, evalSelect db (rewriteWithView query match) = evalSelect db query
```

### 4.2 Subsumption Correctness

```lean
/-- View subsumes query iff view contains all needed rows -/
theorem view_subsumption_correct (query : SelectStmt) (view : MaterializedView)
  (h : predicatesSubsumedBy (extractPredicates view.definition) (extractPredicates query)) :
  ∀ db row,
    row ∈ evalSelect db query →
    row ∈ evalSelect db view.definition
```

### 4.3 Rollup Correctness

```lean
/-- Aggregate rollup produces correct results -/
theorem aggregate_rollup_correct (finer coarser : List Expr)
  (h : isGroupByRefinement finer coarser) (agg : AggFunc) (hd : canRollupAggregate agg) :
  ∀ db table,
    aggregate agg (groupBy coarser table) =
    rollupAggregate agg (aggregate agg (groupBy finer table)) coarser
```

---

## 5. Matching Algorithm Details

### 5.1 Lattice-Based Matching

```
View matching forms a subsumption lattice:

Query
  │
  ├─ View A (exact match)
  │
  ├─ View B (needs filter)
  │     │
  │     └─ View C (needs filter + rollup)
  │
  └─ View D (needs different columns)

Choose the lowest (most specific) applicable view.
```

### 5.2 Join View Matching

```
Function: matchJoinView
Input: query : SelectStmt, view : MaterializedView
Output: Option ViewMatch

Intended Function:
  -- View may pre-join tables that query joins separately

  LET queryJoins = extractJoins query.fromClause
  LET viewJoins = extractJoins view.definition.fromClause

  -- Check if view joins are subset of query joins
  IF queryJoins ⊇ viewJoins
  THEN
    -- View provides some of the needed joins
    LET remainingJoins = queryJoins \ viewJoins
    some (ViewMatch.mk view partialCoverage ...)
  ELSE
    none
```

---

## 6. Cost-Benefit Analysis

### 6.1 Estimate View Benefit

```
Function: estimateViewBenefit
Input: match : ViewMatch, queryStats : Statistics, viewStats : Statistics
Output: Float

Intended Function:
  LET queryWithoutView = estimateCost match.originalQuery queryStats
  LET queryWithView = estimateCost (rewriteWithView match.originalQuery match) viewStats

  -- Benefit = cost reduction
  LET benefit = queryWithoutView.total - queryWithView.total

  -- Penalize stale views
  LET freshnessPenalty = IF match.view.refreshMode = stale THEN 0.5 ELSE 1.0

  IN benefit * freshnessPenalty
```

### 6.2 View Selection

```
Function: selectBestView
Input: matches : List ViewMatch, stats : Statistics
Output: Option ViewMatch

Intended Function:
  IF matches.isEmpty
  THEN none
  ELSE
    -- Choose view with highest benefit
    LET withBenefits = matches.map (fun m => (m, estimateViewBenefit m stats))
    LET best = withBenefits.maxBy (·.2)
    IF best.2 > 0  -- Only use if beneficial
    THEN some best.1
    ELSE none
```

---

## 7. Integration Points

### 7.1 With Expression Normalization (PR A)

```lean
/-- Normalize expressions before matching for better detection -/
def matchWithNormalization (query : SelectStmt) (view : MaterializedView) : Bool :=
  let normQuery := normalizeSelectExprs query
  let normView := normalizeSelectExprs view.definition
  syntacticMatch normQuery normView
```

### 7.2 With Query Optimization Pipeline

```lean
/-- View matching happens early in optimization -/
def optimizeWithViews (query : SelectStmt) (catalog : ViewCatalog) : SelectStmt :=
  -- Try view rewriting first
  match selectBestView (findMatchingViews query catalog) stats with
  | some viewMatch =>
      let rewritten := rewriteWithView query viewMatch
      -- Continue with other optimizations on rewritten query
      optimizeSelectAdvanced rewritten
  | none =>
      -- No applicable view; proceed with normal optimization
      optimizeSelectAdvanced query
```

---

## 8. Testing Strategy

### 8.1 Unit Tests

```lean
-- Exact match
testViewMatch
  view: "CREATE MATERIALIZED VIEW sales_2024 AS SELECT * FROM sales WHERE year = 2024"
  query: "SELECT * FROM sales WHERE year = 2024"
  expected: exactMatch

-- Subsumption match
testViewMatch
  view: "CREATE MATERIALIZED VIEW recent_sales AS SELECT * FROM sales WHERE year >= 2020"
  query: "SELECT * FROM sales WHERE year = 2024"
  expected: subsumptionMatch with additionalPredicate (year = 2024)

-- Aggregation rollup
testViewMatch
  view: "CREATE MATERIALIZED VIEW daily_sales AS
         SELECT date, region, SUM(amount) as total FROM sales GROUP BY date, region"
  query: "SELECT region, SUM(amount) FROM sales GROUP BY region"
  expected: rollupMatch with rollup SUM(total) GROUP BY region
```

### 8.2 Property Tests

```lean
/-- Rewriting with view preserves result -/
def prop_view_rewrite_correct (query : SelectStmt) (view : MaterializedView)
  (db : Database) : Bool :=
  match tryMatchView query view with
  | none => true
  | some m => evalSelect db (rewriteWithView query m) == evalSelect db query

/-- Selected view provides benefit -/
def prop_view_selection_beneficial (query : SelectStmt) (catalog : ViewCatalog)
  (stats : Statistics) : Bool :=
  match selectBestView (findMatchingViews query catalog) stats with
  | none => true
  | some m => estimateViewBenefit m stats > 0
```

---

## 9. References

- Goldstein & Larson, "Optimizing Queries Using Materialized Views" (SIGMOD 2001)
- Halevy, "Answering Queries Using Views: A Survey" (VLDB Journal 2001)
- Agrawal et al., "Automated Selection of Materialized Views" (VLDB 2000)
- Oracle Materialized View documentation
- PostgreSQL Materialized Views documentation
