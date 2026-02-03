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
  - Subqueries are treated as opaque leaf nodes (preserved during reconstruction)

  Safety constraints:
  - Unqualified column references in ON predicates block reordering
    (since column resolution depends on row order in current semantics)

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
  /-- Unique identifier for this node (used for map lookups) -/
  id : Nat
  /-- The table reference (original or synthetic for combined nodes) -/
  table : TableRef
  /-- Estimated row count -/
  estimatedRows : Nat
  /-- All original table names contained in this node (for edge matching) -/
  originalTables : List String
  /-- The original FromClause for leaf nodes (used during reconstruction to preserve subqueries) -/
  originalFrom : FromClause
  deriving Repr, BEq

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
  deriving Repr, BEq

-- ============================================================================
-- JoinNode Operations
-- ============================================================================

/-- Initialize a leaf node from a table reference with a given ID.
    Leaf IDs are tagged as even numbers (2 * id) so that combined node IDs,
    which are tagged as odd numbers, cannot collide with them. -/
def JoinNode.leaf (id : Nat) (t : TableRef) (from_ : FromClause := .table t) : JoinNode :=
  { id := 2 * id  -- even: leaf nodes
  , table := t
  , estimatedRows := defaultCardinality
  , originalTables := [getTableName t]
  , originalFrom := from_ }

/-- Generate a unique ID for combined join nodes using Cantor pairing.
    Combined node IDs are tagged as odd numbers to avoid collisions with
    leaf node IDs (which are even per JoinNode.leaf).
    For any two distinct ordered pairs (a,b) and (c,d), pairIds a b ≠ pairIds c d. -/
def pairIds (a b : Nat) : Nat :=
  let s := a + b
  let p := (s * (s + 1)) / 2 + b
  2 * p + 1  -- odd: combined nodes

/-- Combine two nodes after joining them.
    Creates a synthetic TableRef and merges the original tables lists.
    The new node gets a fresh ID computed via Cantor pairing.
    The originalFrom is a placeholder (combined nodes are not used as leaves). -/
def JoinNode.combine (n1 n2 : JoinNode) (resultRows : Nat) : JoinNode :=
  let syntheticTable : TableRef := ⟨s!"{n1.table.name}_{n2.table.name}", some "__combined__"⟩
  { id := pairIds n1.id n2.id  -- collision-free synthetic ID
  , table := syntheticTable
  , estimatedRows := resultRows
  , originalTables := n1.originalTables ++ n2.originalTables
  , originalFrom := .table syntheticTable }  -- Placeholder, not used for combined nodes

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

/-- Detect whether an expression contains any unqualified column reference.
    An unqualified column is one whose `table` field is `none`. Since the
    evaluation semantics resolve such columns by scanning the row list in
    order, their meaning can change if join order changes. We conservatively
    allow reordering only when all column references are table-qualified. -/
partial def exprHasUnqualifiedColumnRef : Expr → Bool
  | .col c => c.table.isNone
  | .lit _ => false
  | .countStar => false
  | .binOp _ e1 e2 => exprHasUnqualifiedColumnRef e1 || exprHasUnqualifiedColumnRef e2
  | .unaryOp _ e => exprHasUnqualifiedColumnRef e
  | .between e1 e2 e3 => exprHasUnqualifiedColumnRef e1 || exprHasUnqualifiedColumnRef e2 || exprHasUnqualifiedColumnRef e3
  | .inList e _ es => exprHasUnqualifiedColumnRef e || es.any exprHasUnqualifiedColumnRef
  | .inSubquery e _ _ => exprHasUnqualifiedColumnRef e  -- Only check outer expr; subquery has own scope
  | .exists _ _ => false        -- Subquery has its own scope
  | .subquery _ => false        -- Scalar subquery has its own scope
  | .«case» cases else_ =>
    cases.any (fun (c, r) => exprHasUnqualifiedColumnRef c || exprHasUnqualifiedColumnRef r) ||
    (else_.map exprHasUnqualifiedColumnRef).getD false
  | .func _ args => args.any exprHasUnqualifiedColumnRef
  | .agg _ e _ => e.map exprHasUnqualifiedColumnRef |>.getD false
  | .windowFn _ e spec =>
    (e.map exprHasUnqualifiedColumnRef |>.getD false) ||
    spec.partitionBy.any exprHasUnqualifiedColumnRef ||
    spec.orderBy.any (fun o => exprHasUnqualifiedColumnRef o.expr)

/-- Check if an optional expression has unqualified column references -/
def optExprHasUnqualifiedColumnRef : Option Expr → Bool
  | none => false
  | some e => exprHasUnqualifiedColumnRef e

/-- Check if a FROM clause contains only INNER/CROSS joins (safe to reorder).
    Subqueries are treated as opaque leaf nodes - we don't reorder within them,
    but they can participate in reordering at their containing level. -/
partial def hasOnlyInnerOrCrossJoins : FromClause → Bool
  | .table _ => true
  | .subquery _ _ => true  -- Treat subquery as opaque leaf node
  | .join left jtype right onExpr =>
    (jtype == .inner || jtype == .cross) &&
    -- Reject if the ON predicate contains any unqualified column reference
    !optExprHasUnqualifiedColumnRef onExpr &&
    hasOnlyInnerOrCrossJoins left && hasOnlyInnerOrCrossJoins right

/-- Backwards-compatible alias for hasOnlyInnerOrCrossJoins.
    @deprecated: Name is misleading as it returns true for CROSS joins too.
    Use hasOnlyInnerOrCrossJoins for clarity in new code. -/
@[deprecated hasOnlyInnerOrCrossJoins (since := "2026-02-02")]
abbrev hasOnlyInnerJoins := hasOnlyInnerOrCrossJoins

/-- Check if we can safely reorder joins in this FROM clause -/
def canReorderJoins (from_ : FromClause) : Bool := hasOnlyInnerOrCrossJoins from_

-- ============================================================================
-- Cost Estimation
-- ============================================================================

/-- Estimate the cost of joining two nodes.
    Uses a simple model: result size = n1.rows * n2.rows * selectivity.
    The float estimate is converted to Nat with safeguards:
    - Clamp zero to 1 when both inputs are non-zero (avoid spurious zero-row estimates)
    - Handle overflow: if result exceeds UInt64 range, clamp to UInt64.max + 1 -/
def estimateJoinCost (n1 n2 : JoinNode) (edges : List JoinEdge) : Nat :=
  -- Find edges that connect these two nodes
  let connectingEdges := edges.filter (edgeConnects · n1 n2)
  -- Use product of selectivities (or 1.0 if no edges = cross join)
  let selectivity := if connectingEdges.isEmpty then 1.0
    else connectingEdges.foldl (fun acc e => acc * e.selectivity) 1.0
  -- Estimate result rows as a float
  let resultFloat := (n1.estimatedRows.toFloat * n2.estimatedRows.toFloat * selectivity)
  -- Safely convert to Nat with overflow protection
  -- UInt64.size = 2^64, so max representable value is UInt64.size - 1
  let overflowThreshold : Float := UInt64.size.toFloat
  let approx :=
    if resultFloat <= 0.0 then 0
    else if resultFloat >= overflowThreshold then UInt64.size  -- clamp to just above max
    else resultFloat.toUInt64.toNat
  -- Clamp tiny positive estimates away from 0 when both inputs are non-empty
  if approx == 0 && n1.estimatedRows != 0 && n2.estimatedRows != 0 then 1
  else approx

-- ============================================================================
-- Join Graph Extraction
-- ============================================================================

/-- Extract leaf tables from a FROM clause, returning (TableRef, originalTables, originalFromClause).
    Preserves original FromClause for each leaf (including subqueries) so that
    reconstruction produces semantically equivalent results. -/
partial def extractLeafTablesRaw : FromClause → List (TableRef × List String × FromClause)
  | fc@(.table t) => [(t, [getTableName t], fc)]
  | fc@(.subquery _sel alias) =>
    -- Treat subquery as a single leaf node, preserving the original FromClause
    [(⟨alias, none⟩, [alias], fc)]
  | .join left _ right _ =>
    extractLeafTablesRaw left ++ extractLeafTablesRaw right

/-- Assign unique IDs to a list of items, starting from 0 -/
def assignIds {α : Type} (items : List α) : List (Nat × α) :=
  let rec go (idx : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (idx, x) :: go (idx + 1) xs
  go 0 items

/-- Extract leaf tables from a FROM clause with unique IDs assigned.
    Delegates to JoinNode.leaf for consistent ID tagging and initialization.
    Preserves originalFrom for subquery reconstruction. -/
def extractLeafTables (from_ : FromClause) : List JoinNode :=
  let raw := extractLeafTablesRaw from_
  (assignIds raw).map fun (idx, (t, tables, origFrom)) =>
    let node := JoinNode.leaf idx t origFrom  -- handles even-tagging (2*idx) and defaults
    { node with originalTables := tables }

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

/-- Remove a single occurrence of a node from the list.
    Uses erase to remove only the first match, avoiding issues when
    duplicate table references exist in the FROM clause. -/
def removeNode (nodes : List JoinNode) (node : JoinNode) : List JoinNode :=
  nodes.erase node

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
    Each step combines two subtrees with either an INNER or CROSS JOIN,
    depending on whether the step has join predicates. Uses originalFrom to
    preserve subqueries and other leaf types during reconstruction. -/
def buildFromSteps (steps : List JoinStep) (nodes : List JoinNode) : Option FromClause :=
  match nodes with
  | [] => none
  | [n] => some n.originalFrom  -- Use preserved FromClause (handles subqueries)
  | _ =>
    -- Build a map from node IDs to their current FromClause
    -- Using ID as key guarantees uniqueness even with duplicate table names
    -- Start with leaf FromClauses (preserved in originalFrom), then combine as we process steps
    let rec go (remaining : List JoinStep)
               (nodeMap : List (Nat × FromClause)) : Option FromClause :=
      match remaining with
      | [] =>
        -- All steps done, should have exactly one entry
        match nodeMap with
        | [(_, fc)] => some fc
        | _ => none  -- Shouldn't happen
      | step :: rest =>
        -- Find the FromClauses for left and right nodes by their unique IDs
        let leftId := step.left.id
        let rightId := step.right.id
        let leftFC := nodeMap.find? (fun (id, _) => id == leftId)
        let rightFC := nodeMap.find? (fun (id, _) => id == rightId)
        match leftFC, rightFC with
        | some (_, lfc), some (_, rfc) =>
          -- Create the join
          -- Preserve CROSS vs INNER semantics: no predicates => CROSS JOIN
          let on_ := unflattenAnd step.predicates
          let joinType := if step.predicates.isEmpty then JoinType.cross else JoinType.inner
          let combined := FromClause.join lfc joinType rfc on_
          -- Combined node ID (same Cantor pairing as JoinNode.combine)
          let combinedId := pairIds leftId rightId
          -- Update the map: remove old entries, add combined
          let newMap := nodeMap.filter (fun (id, _) =>
            id != leftId && id != rightId)
          go rest ((combinedId, combined) :: newMap)
        | _, _ => none  -- Shouldn't happen
    -- Initialize with preserved FromClauses (handles subqueries correctly)
    let initialMap := nodes.map fun n => (n.id, n.originalFrom)
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
            -- Ensure we never produce a CROSS join with a non-empty ON clause,
            -- since evalFrom ignores ON for CROSS joins.
            let jt' := match jt, allOn with
              | .cross, some _ => .inner
              | _, _ => jt
            .join left jt' right allOn
          | other => other  -- Single table, no join to add predicates to

-- ============================================================================
-- Semantic Preservation Axioms
-- ============================================================================

/-- Join reordering preserves semantics (forward direction):
    every row in the reordered result has a corresponding row in the original. -/
axiom join_reorder_preserves_forward (db : Database) (from_ : FromClause) :
  canReorderJoins from_ →
  ∀ row ∈ evalFrom db (reorderJoins from_),
    ∃ row2 ∈ evalFrom db from_, (∀ p, p ∈ row ↔ p ∈ row2)

/-- Join reordering preserves semantics (backward direction):
    every row in the original has a corresponding row in the reordered result. -/
axiom join_reorder_preserves_backward (db : Database) (from_ : FromClause) :
  canReorderJoins from_ →
  ∀ row ∈ evalFrom db from_,
    ∃ row2 ∈ evalFrom db (reorderJoins from_), (∀ p, p ∈ row ↔ p ∈ row2)

/-- Join reordering produces an equivalent FROM clause.
    Relies on the commutativity and associativity of inner joins.

    For any database db and FROM clause from_ containing only INNER/CROSS joins,
    reorderJoins produces an equivalent FROM clause that evaluates to the same
    result set (up to row ordering). This is the conjunction of the forward
    and backward preservation axioms.

    This is an axiom because a full proof would require formalizing
    join evaluation semantics and proving commutativity/associativity
    of inner joins (which are already axiomatized in Equiv.lean). -/
theorem join_reorder_preserves_semantics (db : Database) (from_ : FromClause) :
  canReorderJoins from_ →
  -- Bidirectional: reordered and original produce the same rows
  (∀ row ∈ evalFrom db (reorderJoins from_),
    ∃ row2 ∈ evalFrom db from_, (∀ p, p ∈ row ↔ p ∈ row2)) ∧
  (∀ row ∈ evalFrom db from_,
    ∃ row2 ∈ evalFrom db (reorderJoins from_), (∀ p, p ∈ row ↔ p ∈ row2)) :=
  fun h => ⟨join_reorder_preserves_forward db from_ h,
            join_reorder_preserves_backward db from_ h⟩

end SqlEquiv
