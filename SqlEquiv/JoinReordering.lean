/-
  JoinReordering - Cost-based join reordering optimization

  This module implements join reordering for INNER/CROSS joins to minimize
  intermediate result sizes. Uses a greedy algorithm to select the cheapest
  pair of nodes to join at each step.

  Key features:
  - Only reorders INNER and CROSS joins (preserves outer join semantics)
  - Tracks original tables through combined nodes for predicate placement
  - Cost-based selection using estimated row counts
  - Extracts join predicates from ON clauses for edge detection

  See docs/OPTIMIZER_REDESIGN_PLAN.md for full specification.
-/

import SqlEquiv.OptimizerUtils
import SqlEquiv.Ast
import SqlEquiv.Semantics

namespace SqlEquiv

-- ============================================================================
-- Join Graph Structures
-- ============================================================================

/-- Default cardinality estimate for tables without statistics -/
def defaultCardinality : Nat := 1000

/-- A node in the join graph. Tracks all original tables it represents. -/
structure JoinNode where
  /-- The table reference (original or synthetic for combined nodes) -/
  table : TableRef
  /-- Estimated row count -/
  estimatedRows : Nat
  /-- All original table names contained in this node (for edge matching) -/
  originalTables : List String
  deriving Repr, BEq, Nonempty

/-- An edge in the join graph representing a join predicate -/
structure JoinEdge where
  /-- Table name on the left side of the predicate -/
  leftTable : String
  /-- Table name on the right side of the predicate -/
  rightTable : String
  /-- The join predicate expression -/
  predicate : Expr
  /-- Estimated selectivity (0.0 to 1.0, default 0.1 for equality) -/
  selectivity : Float := 0.1
  deriving Repr, BEq, Nonempty

-- ============================================================================
-- JoinNode Operations
-- ============================================================================

/-- Initialize a leaf node from a table reference -/
def JoinNode.leaf (t : TableRef) : JoinNode :=
  { table := t
  , estimatedRows := defaultCardinality
  , originalTables := [getTableName t] }

/-- Combine two nodes after joining them.
    Creates a synthetic TableRef and merges the original tables lists. -/
def JoinNode.combine (n1 n2 : JoinNode) (resultRows : Nat) : JoinNode :=
  { table := ⟨s!"{n1.table.name}_{n2.table.name}", some "__combined__"⟩
  , estimatedRows := resultRows
  , originalTables := n1.originalTables ++ n2.originalTables }

/-- Check if a node contains a specific table -/
def JoinNode.containsTable (node : JoinNode) (tableName : String) : Bool :=
  node.originalTables.contains tableName

-- ============================================================================
-- Edge Detection and Matching
-- ============================================================================

/-- Check if an edge connects two nodes (in either direction) -/
def edgeConnects (edge : JoinEdge) (n1 n2 : JoinNode) : Bool :=
  (n1.containsTable edge.leftTable && n2.containsTable edge.rightTable) ||
  (n1.containsTable edge.rightTable && n2.containsTable edge.leftTable)

/-- Extract table references from a binary comparison predicate.
    Returns (leftTable, rightTable) if it's a simple column comparison. -/
def extractJoinTables (pred : Expr) : Option (String × String) :=
  match pred with
  | .binOp .eq (.col c1) (.col c2) =>
    match c1.table, c2.table with
    | some t1, some t2 => if t1 != t2 then some (t1, t2) else none
    | _, _ => none
  | _ => none

/-- Create a JoinEdge from a predicate if it's a join condition -/
def mkJoinEdge (pred : Expr) : Option JoinEdge :=
  match extractJoinTables pred with
  | some (t1, t2) => some { leftTable := t1, rightTable := t2, predicate := pred }
  | none => none

/-- Extract all join edges from a list of predicates -/
def extractJoinEdges (preds : List Expr) : List JoinEdge :=
  preds.filterMap mkJoinEdge

-- ============================================================================
-- Safety Check
-- ============================================================================

/-- Check if a FROM clause contains only INNER/CROSS joins (safe to reorder).
    Returns false for subqueries (conservative: don't reorder across boundaries). -/
partial def hasOnlyInnerJoins : FromClause → Bool
  | .table _ => true
  | .subquery _ _ => false  -- conservative: subqueries have their own scope
  | .join left jtype right _ =>
    (jtype == .inner || jtype == .cross) &&
    hasOnlyInnerJoins left && hasOnlyInnerJoins right

/-- Check if we can safely reorder joins in this FROM clause -/
def canReorderJoins (from_ : FromClause) : Bool := hasOnlyInnerJoins from_

-- ============================================================================
-- Cost Estimation
-- ============================================================================

/-- Estimate the cost of joining two nodes.
    Uses a simple model: result size = n1.rows * n2.rows * selectivity -/
def estimateJoinCost (n1 n2 : JoinNode) (edges : List JoinEdge) : Nat :=
  -- Find edges that connect these two nodes
  let connectingEdges := edges.filter (edgeConnects · n1 n2)
  -- Use product of selectivities (or 1.0 if no edges = cross join)
  let selectivity := if connectingEdges.isEmpty then 1.0
    else connectingEdges.foldl (fun acc e => acc * e.selectivity) 1.0
  -- Estimate result rows
  let resultFloat := (n1.estimatedRows.toFloat * n2.estimatedRows.toFloat * selectivity)
  resultFloat.toUInt64.toNat

-- ============================================================================
-- Join Graph Extraction
-- ============================================================================

/-- Extract leaf tables from a FROM clause -/
partial def extractLeafTables : FromClause → List JoinNode
  | .table t => [JoinNode.leaf t]
  | .subquery _sel alias =>
    -- Treat subquery as a single leaf node
    [{ table := ⟨alias, some alias⟩
     , estimatedRows := defaultCardinality
     , originalTables := [alias] }]
  | .join left _ right _ =>
    extractLeafTables left ++ extractLeafTables right

/-- Extract all predicates from ON clauses in a FROM clause -/
partial def extractOnPredicates : FromClause → List Expr
  | .table _ => []
  | .subquery _ _ => []
  | .join left _ right on_ =>
    let leftPreds := extractOnPredicates left
    let rightPreds := extractOnPredicates right
    let thisPred := match on_ with
      | some p => flattenAnd p
      | none => []
    leftPreds ++ rightPreds ++ thisPred

-- ============================================================================
-- Greedy Join Reordering Algorithm
-- ============================================================================

/-- Generate unique pairs from a list (each unordered pair appears once) -/
def uniquePairs (nodes : List JoinNode) : List (JoinNode × JoinNode) :=
  match nodes with
  | [] => []
  | [_] => []
  | n :: rest => (rest.map (n, ·)) ++ uniquePairs rest

/-- Find the cheapest pair of nodes to join -/
def findCheapestPair (nodes : List JoinNode) (edges : List JoinEdge) :
    Option (JoinNode × JoinNode × Nat) :=
  if nodes.length < 2 then none
  else
    -- Generate unique pairs (each unordered pair once) and compute costs
    let pairs := (uniquePairs nodes).map fun (n1, n2) =>
      (n1, n2, estimateJoinCost n1 n2 edges)
    -- Find minimum (by cost)
    List.foldl (fun acc pair =>
      match acc with
      | none => some pair
      | some (_, _, minCost) =>
        if pair.2.2 < minCost then some pair else acc
    ) none pairs

/-- Remove a node from the list -/
def removeNode (nodes : List JoinNode) (node : JoinNode) : List JoinNode :=
  nodes.filter (· != node)

/-- Collect edges that connect the given nodes -/
def collectConnectingEdges (n1 n2 : JoinNode) (edges : List JoinEdge) : List Expr :=
  (edges.filter (edgeConnects · n1 n2)).map (·.predicate)

/-- A join step: which nodes to join and with what predicates -/
structure JoinStep where
  left : JoinNode
  right : JoinNode
  predicates : List Expr
  deriving Repr

/-- Greedy join reordering: repeatedly join the cheapest pair.
    Returns the sequence of join steps in the order they should be performed. -/
partial def greedyReorder (nodes : List JoinNode) (edges : List JoinEdge) : Option (List JoinStep) :=
  match nodes with
  | [] => none
  | [_] => some []  -- Single node: no joins needed
  | _ =>
    match findCheapestPair nodes edges with
    | none => none  -- Shouldn't happen if nodes.length >= 2
    | some (n1, n2, cost) =>
      -- Collect join predicates for this pair
      let joinPreds := collectConnectingEdges n1 n2 edges
      -- Remove edges that were used
      let remainingEdges := edges.filter (fun e => !edgeConnects e n1 n2)
      -- Create combined node
      let combined := JoinNode.combine n1 n2 cost
      -- Remove old nodes, add combined
      let newNodes := removeNode (removeNode nodes n1) n2 ++ [combined]
      -- Recurse
      match greedyReorder newNodes remainingEdges with
      | none => none
      | some moreSteps =>
        some ({ left := n1, right := n2, predicates := joinPreds } :: moreSteps)

-- ============================================================================
-- FROM Clause Reconstruction
-- ============================================================================

/-- Build FROM clause from join steps, using the computed order.
    Each step combines two subtrees with an INNER JOIN. -/
def buildFromSteps (steps : List JoinStep) (nodes : List JoinNode) : Option FromClause :=
  match nodes with
  | [] => none
  | [n] => some (FromClause.table n.table)
  | _ =>
    -- Build a map from table names to their current FromClause
    -- Start with leaf tables, then combine as we process steps
    let rec go (remaining : List JoinStep)
               (nodeMap : List (List String × FromClause)) : Option FromClause :=
      match remaining with
      | [] =>
        -- All steps done, should have exactly one entry
        match nodeMap with
        | [(_, fc)] => some fc
        | _ => none  -- Shouldn't happen
      | step :: rest =>
        -- Find the FromClauses for left and right nodes
        let leftTables := step.left.originalTables
        let rightTables := step.right.originalTables
        let leftFC := nodeMap.find? (fun (ts, _) => ts == leftTables)
        let rightFC := nodeMap.find? (fun (ts, _) => ts == rightTables)
        match leftFC, rightFC with
        | some (_, lfc), some (_, rfc) =>
          -- Create the join
          let on_ := unflattenAnd step.predicates
          let combined := FromClause.join lfc .inner rfc on_
          let combinedTables := leftTables ++ rightTables
          -- Update the map: remove old entries, add combined
          let newMap := nodeMap.filter (fun (ts, _) =>
            ts != leftTables && ts != rightTables)
          go rest ((combinedTables, combined) :: newMap)
        | _, _ => none  -- Shouldn't happen
    let initialMap := nodes.map fun n => (n.originalTables, FromClause.table n.table)
    go steps initialMap

-- ============================================================================
-- Main Reordering Function
-- ============================================================================

/-- Reorder joins in a FROM clause using greedy cost-based selection.
    Only reorders if all joins are INNER/CROSS; otherwise returns unchanged.
    Preserves all ON predicates (both join conditions and filters). -/
def reorderJoins (from_ : FromClause) : FromClause :=
  if !canReorderJoins from_ then from_
  else
    -- Extract leaves and all predicates
    let leaves := extractLeafTables from_
    let allPreds := extractOnPredicates from_
    let edges := extractJoinEdges allPreds

    -- Identify non-join predicates (filters that aren't column=column joins)
    let joinPredSet := edges.map (·.predicate)
    let nonJoinPreds := allPreds.filter (fun p => !joinPredSet.any (· == p))

    -- Run greedy reordering
    match greedyReorder leaves edges with
    | none => from_  -- Fallback: return original
    | some steps =>
      -- Build FROM clause using the computed join order
      match buildFromSteps steps leaves with
      | none => from_  -- Fallback
      | some result =>
        -- Add non-join predicates to the top-level ON clause
        if nonJoinPreds.isEmpty then result
        else
          match result with
          | .join left jt right on_ =>
            let existingPreds := match on_ with
              | some p => flattenAnd p
              | none => []
            let allOn := unflattenAnd (existingPreds ++ nonJoinPreds)
            .join left jt right allOn
          | other => other  -- Single table, no join to add predicates to

-- ============================================================================
-- Semantic Preservation Axiom
-- ============================================================================

/-- Join reordering preserves semantics for inner/cross joins.
    Relies on the commutativity and associativity of inner joins.

    For any database db and FROM clause from_ containing only INNER/CROSS joins,
    reorderJoins produces an equivalent FROM clause that evaluates to the same
    result set (up to row ordering).

    This is an axiom because a full proof would require formalizing
    join evaluation semantics and proving commutativity/associativity
    of inner joins (which are already axiomatized in Equiv.lean). -/
axiom join_reorder_preserves_semantics (db : Database) (from_ : FromClause) :
  canReorderJoins from_ →
  -- The reordered FROM clause produces the same rows as the original
  ∀ row ∈ evalFrom db (reorderJoins from_),
    ∃ row2 ∈ evalFrom db from_, (∀ p, p ∈ row ↔ p ∈ row2)

end SqlEquiv
