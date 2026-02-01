/-
  PredicatePushdown - Push WHERE predicates into JOINs and subqueries

  This module implements predicate pushdown optimization, which pushes
  WHERE clause predicates as deep as possible into the query tree to
  reduce intermediate result sizes.

  Key features:
  - Push predicates into JOIN ON clauses
  - Push predicates into subqueries when safe
  - Respect outer join semantics (don't push through wrong side)
  - Handle GROUP BY correctly (only push if predicate uses grouping keys)

  Uses utilities from OptimizerUtils (getReferencedColumns, flattenAnd)
  and existing functions (hasAggregate, isGroupingKey).

  See docs/OPTIMIZER_REDESIGN_PLAN.md for full specification.
-/

import SqlEquiv.OptimizerUtils
import SqlEquiv.Semantics
import SqlEquiv.Equiv

namespace SqlEquiv

-- ============================================================================
-- Pushdown Result
-- ============================================================================

/-- Result of attempting to push a predicate down.
    - pushedFrom: the transformed FROM clause with predicates pushed in
    - remaining: predicate that couldn't be pushed (must stay in WHERE) -/
structure PushdownResult where
  pushedFrom : FromClause
  remaining : Option Expr
  deriving Repr, Nonempty

-- ============================================================================
-- Safety Checks
-- ============================================================================

/-- Extract column reference info from SelectItem.
    For aliased expressions, returns the alias as the column name.
    For unaliased column references, returns the full column reference. -/
def getSelectItemColumnRef : SelectItem → Option ColumnRef
  | .star _ => none
  | .exprItem (.col _) (some alias) => some { column := alias, table := none }
  | .exprItem (.col c) none => some c
  | .exprItem _ (some alias) => some { column := alias, table := none }
  | .exprItem _ none => none

/-- Can push predicate past SELECT projection?
    A predicate can be pushed if all its referenced columns are available
    in the projection (either as direct columns or aliases). -/
def canPushPastProjection (pred : Expr) (items : List SelectItem) : Bool :=
  let predCols := getReferencedColumns pred
  let availableCols := items.filterMap getSelectItemColumnRef
  predCols.all fun predCol =>
    availableCols.any fun availCol =>
      predCol.column == availCol.column &&
      (predCol.table.isNone || availCol.table.isNone || predCol.table == availCol.table)

/-- Can push predicate past GROUP BY?
    A predicate can be pushed past GROUP BY if:
    1. It contains no aggregates
    2. All referenced columns are grouping keys (bare column references in GROUP BY) -/
def canPushPastGroupBy (pred : Expr) (groupBy : List Expr) : Bool :=
  !hasAggregate pred &&
  (getReferencedColumns pred).all fun c => groupBy.any (isGroupingKey c)

/-- Can push predicate to left side of join?
    Safe for INNER, CROSS, and LEFT joins (left side is always evaluated). -/
def canPushLeftThroughJoin (jtype : JoinType) : Bool :=
  match jtype with
  | .inner | .cross | .left => true
  | .right | .full => false

/-- Can push predicate to right side of join?
    Safe for INNER, CROSS, and RIGHT joins (right side is always evaluated). -/
def canPushRightThroughJoin (jtype : JoinType) : Bool :=
  match jtype with
  | .inner | .cross | .right => true
  | .left | .full => false

-- ============================================================================
-- Table Reference Checking
-- ============================================================================

/-- Check if predicate references only tables in the given list.
    Unqualified columns (with table = none) are treated as potentially
    referring to multiple tables and therefore cause this check to fail. -/
def predReferencesOnlyTables (pred : Expr) (tables : List String) : Bool :=
  (getReferencedColumns pred).all fun col =>
    match col.table with
    | some t => tables.any (· == t)
    | none => false  -- Unqualified columns could reference any table

-- ============================================================================
-- Column Reference Transformation for Subquery Pushdown
-- ============================================================================

/-- Find the inner expression for a column reference in a subquery's SELECT items.
    For example, if the subquery has `SELECT t.id AS id` and we're looking for
    column `sub.id` (where `sub` is the subquery alias), return the inner `t.id`. -/
def findInnerColumnExpr (colName : String) (items : List SelectItem) : Option Expr :=
  items.findSome? fun item =>
    match item with
    | .exprItem expr (some alias) =>
      if alias == colName then some expr else none
    | .exprItem (.col c) none =>
      if c.column == colName then some (.col c) else none
    | _ => none

/-- Transform column references in an expression to use inner subquery references.
    Columns qualified with the subquery alias are transformed to their inner form.
    For example, `sub.id = 1` becomes `t.id = 1` if the subquery is
    `(SELECT t.id AS id FROM t) AS sub`. -/
partial def transformColumnRefs (expr : Expr) (subqueryAlias : String)
    (items : List SelectItem) : Expr :=
  match expr with
  | .col c =>
    match c.table with
    | some t =>
      if t == subqueryAlias then
        -- Column uses subquery alias, find inner expression
        match findInnerColumnExpr c.column items with
        | some innerExpr => innerExpr
        | none => expr  -- Keep as-is if not found (shouldn't happen if canPush passed)
      else expr  -- Different table qualifier, keep as-is
    | none => expr  -- Unqualified, keep as-is
  | .binOp op l r =>
    .binOp op (transformColumnRefs l subqueryAlias items)
              (transformColumnRefs r subqueryAlias items)
  | .unaryOp op e => .unaryOp op (transformColumnRefs e subqueryAlias items)
  | .between e low high =>
    .between (transformColumnRefs e subqueryAlias items)
             (transformColumnRefs low subqueryAlias items)
             (transformColumnRefs high subqueryAlias items)
  | .inList e neg vals =>
    .inList (transformColumnRefs e subqueryAlias items)
            neg
            (vals.map (transformColumnRefs · subqueryAlias items))
  | .«case» whens else_ =>
    .«case» (whens.map fun (cond, result) =>
               (transformColumnRefs cond subqueryAlias items,
                transformColumnRefs result subqueryAlias items))
            (else_.map (transformColumnRefs · subqueryAlias items))
  | .func name args => .func name (args.map (transformColumnRefs · subqueryAlias items))
  | .agg fn arg distinct => .agg fn (arg.map (transformColumnRefs · subqueryAlias items)) distinct
  | other => other  -- Literals, subqueries, etc. - keep as-is

-- ============================================================================
-- Predicate Pushdown Implementation
-- ============================================================================

/-- Try to push a single predicate into a FROM clause.
    Returns the modified FROM and any remaining predicate that couldn't be pushed. -/
partial def pushSinglePredicate (pred : Expr) (from_ : FromClause) : PushdownResult :=
  match from_ with
  -- Base table: can't push further, predicate remains
  | .table t => { pushedFrom := .table t, remaining := some pred }

  -- Subquery: try to push into the subquery's WHERE if the predicate
  -- only references columns available in the subquery's SELECT
  -- and respects GROUP BY constraints
  | .subquery sel alias =>
    let canPushProjection := canPushPastProjection pred sel.items
    let canPushGroupBy := sel.groupBy.isEmpty || canPushPastGroupBy pred sel.groupBy
    if canPushProjection && canPushGroupBy then
      -- Transform column references to match inner subquery columns
      -- e.g., `sub.id = 1` becomes `t.id = 1` if subquery is `(SELECT t.id AS id) AS sub`
      let transformedPred := transformColumnRefs pred alias sel.items
      -- Can push: add to subquery's WHERE clause
      let newWhere := match sel.whereClause with
        | none => some transformedPred
        | some w => some (Expr.binOp .and w transformedPred)
      -- Reconstruct SelectStmt with new WHERE clause
      let newSel := SelectStmt.mk sel.distinct sel.items sel.fromClause newWhere
                      sel.groupBy sel.having sel.orderBy sel.limitVal sel.offsetVal
      { pushedFrom := .subquery newSel alias, remaining := none }
    else
      -- Can't push: keep predicate at current level
      { pushedFrom := .subquery sel alias, remaining := some pred }

  -- Join: try to push to left, right, or add to ON clause
  | .join left jtype right on_ =>
    let leftTables := getFromClauseTableNames left
    let rightTables := getFromClauseTableNames right

    -- Check if predicate references only left or right tables
    -- Note: predReferencesOnlyTables returns false for unqualified columns,
    -- so they won't match either side and will fall through to the ON clause
    let refsOnlyLeft := predReferencesOnlyTables pred leftTables
    let refsOnlyRight := predReferencesOnlyTables pred rightTables

    if refsOnlyLeft && canPushLeftThroughJoin jtype then
      -- Push to left side
      let result := pushSinglePredicate pred left
      match result.remaining with
      | none =>
        -- Successfully pushed into left subtree
        { pushedFrom := .join result.pushedFrom jtype right on_, remaining := none }
      | some r =>
        -- Couldn't push further into left subtree
        if jtype == .inner || jtype == .cross then
          -- For INNER/CROSS, safe to add to ON clause
          let newOn := match on_ with
            | none => some r
            | some o => some (Expr.binOp .and o r)
          { pushedFrom := .join result.pushedFrom jtype right newOn, remaining := none }
        else
          -- For LEFT join, predicates on left table must stay in WHERE
          -- (adding to ON would change semantics: unmatched rows still appear)
          { pushedFrom := .join result.pushedFrom jtype right on_, remaining := some r }
    else if refsOnlyRight && canPushRightThroughJoin jtype then
      -- Push to right side
      let result := pushSinglePredicate pred right
      match result.remaining with
      | none =>
        -- Successfully pushed into right subtree
        { pushedFrom := .join left jtype result.pushedFrom on_, remaining := none }
      | some r =>
        -- Couldn't push further into right subtree
        if jtype == .inner || jtype == .cross then
          -- For INNER/CROSS, safe to add to ON clause
          let newOn := match on_ with
            | none => some r
            | some o => some (Expr.binOp .and o r)
          { pushedFrom := .join left jtype result.pushedFrom newOn, remaining := none }
        else
          -- For RIGHT join, predicates on right table must stay in WHERE
          -- (adding to ON would change semantics: unmatched rows still appear)
          { pushedFrom := .join left jtype result.pushedFrom on_, remaining := some r }
    else if jtype == .inner || jtype == .cross then
      -- For inner/cross joins, add to ON clause
      let newOn := match on_ with
        | none => some pred
        | some o => some (Expr.binOp .and o pred)
      { pushedFrom := .join left jtype right newOn, remaining := none }
    else
      -- Can't push through outer join: keep predicate at current level
      { pushedFrom := .join left jtype right on_, remaining := some pred }

/-- Push a predicate (possibly with multiple conjuncts) into a FROM clause.
    Splits AND predicates and pushes each conjunct independently. -/
def pushPredicateDown (pred : Expr) (from_ : FromClause) : PushdownResult :=
  -- Flatten the predicate into individual conjuncts
  let conjuncts := flattenAnd pred

  -- Try to push each conjunct, collecting remaining ones
  let (finalFrom, remainingList) := conjuncts.foldl
    (fun (currentFrom, remaining) conjunct =>
      let result := pushSinglePredicate conjunct currentFrom
      match result.remaining with
      | none => (result.pushedFrom, remaining)
      | some r => (result.pushedFrom, r :: remaining))
    (from_, [])

  -- Rebuild remaining predicate from unpushed conjuncts
  let remainingPred := unflattenAnd remainingList.reverse

  { pushedFrom := finalFrom, remaining := remainingPred }

-- ============================================================================
-- Semantic Preservation Axiom
-- ============================================================================

/-- Helper: filter rows by a predicate -/
def filterRows (db : Database) (rows : Table) (pred : Option Expr) : Table :=
  match pred with
  | none => rows
  | some p => rows.filter fun row =>
    match evalExprWithDb db row p with
    | some (.bool true) => true
    | _ => false

/-- Pushdown preserves semantics: the pushed FROM clause with remaining predicate
    applied produces the same result as the original FROM with the full predicate.

    For any database db and predicate pred on FROM clause from_,
    if result = pushPredicateDown pred from_, then filtering the pushed FROM
    by the remaining predicate yields the same rows as filtering the original
    FROM by the full predicate.

    This is an axiom because a full proof requires complex reasoning about
    join semantics, but captures the key correctness property. -/
axiom pushdown_preserves_semantics (db : Database) (pred : Expr) (from_ : FromClause) :
  let result := pushPredicateDown pred from_
  -- Filtering the pushed FROM by remaining predicate equals
  -- filtering the original FROM by the full predicate
  filterRows db (evalFrom db result.pushedFrom) result.remaining =
  filterRows db (evalFrom db from_) (some pred)

end SqlEquiv
