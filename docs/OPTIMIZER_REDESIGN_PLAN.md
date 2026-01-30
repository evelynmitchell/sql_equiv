# Advanced Query Optimizer Redesign Plan

## Overview

This document outlines a cleaner implementation plan for advanced query optimization features: join reordering, expression normalization, and predicate pushdown. This replaces the approach in PR #1 which accumulated too many patches during review.

---

## Codebase Analysis (Added 2026-01-30)

### Existing Utilities That Can Be Reused

The following utilities already exist and should be leveraged:

| Utility | Location | Purpose |
|---------|----------|---------|
| `getFromClauseTableNames` | Equiv.lean:1201 | Extract table names/aliases from FROM clause |
| `exprReferencesOnlyTable` | Equiv.lean:1175 | Check if expr references only one table |
| `exprReferencesOnlyFrom` | Equiv.lean:1207 | Check if expr references only columns in a FROM |
| `hasAggregate` | Semantics.lean:190 | Detect aggregate functions in expressions |
| `Expr.isGround` | Equiv.lean | Check if expression has no column references |
| `normalizeExpr` | Equiv.lean:627 | Existing normalizer (commutative reordering) |

### Existing Axioms for Join Reordering

These axioms already exist in Equiv.lean and can be used by PR C:
- `join_assoc` - Inner join associativity
- `join_comm` / `join_comm_full` - Inner join commutativity
- `cross_join_assoc` / `cross_join_comm` - Cross join laws
- `filter_join_left` / `filter_join_right` - Predicate pushdown into joins

### Missing Shared Utilities (→ PR 0)

These utilities are needed by multiple PRs but don't exist:

```lean
/-- Extract all column references from an expression -/
partial def getReferencedColumns : Expr → List ColumnRef

/-- Flatten nested ANDs into a list of conjuncts: (a AND (b AND c)) → [a, b, c] -/
partial def flattenAnd : Expr → List Expr

/-- Rebuild AND chain from list: [a, b, c] → (a AND (b AND c)) -/
def unflattenAnd : List Expr → Option Expr

/-- Flatten nested ORs into a list of disjuncts -/
partial def flattenOr : Expr → List Expr

/-- Rebuild OR chain from list -/
def unflattenOr : List Expr → Option Expr

/-- Structural comparison for expressions (more stable than toString repr) -/
partial def exprStructuralCmp : Expr → Expr → Ordering
```

**Why these matter:**
- `flattenAnd`/`unflattenAnd`: PR A needs these for sorting conjuncts; PR B needs them to split predicates for pushdown
- `getReferencedColumns`: PR B needs this for `canPushPastProjection`; PR C needs it for edge detection
- `exprStructuralCmp`: PR A can use this instead of `toString (repr e)` for deterministic ordering

### Function Signature Concerns

| Function | Current Signature | Concern |
|----------|------------------|---------|
| `optimizeFromClause` | `(predicate : Option Expr) : FromClause → FromClause × Option Expr` | Plan's `pushPredicateDown` has different signature. **Decision:** Keep both - `optimizeFromClause` is internal, `pushPredicateDown` is the new public API |
| `normalizeExpr` | `Expr → Expr` | Already exists in Equiv.lean. **Decision:** Plan's `normalizeExprCanonical` is intentionally separate (different purpose - see clarification below) |

### Clarification: `normalizeExpr` vs `normalizeExprCanonical`

- **`normalizeExpr` (existing)**: Reorders commutative operands + eliminates double negation. Used by `syntacticEquiv` for equality checking.
- **`normalizeExprCanonical` (PR A)**: More comprehensive - flattens AND/OR chains, applies weight-based ordering (literals < columns < complex), ensures idempotency. Used for optimization matching.

These serve different purposes and should coexist.

---

## Lessons Learned from PR #1

1. **Function signatures matter upfront**: `pushPredicateDown` needed to return remaining predicates, but this was discovered late
2. **Join reordering state tracking was bolted-on**: The `containedTables` field was added as a fix rather than designed in
3. **Axioms should match implementation**: Several axioms were tautological or didn't reflect actual semantics
4. **Smaller PRs are better**: Three major features in one PR made review difficult

## Proposed Approach: Four Separate PRs

### PR 0: Shared Utilities (Prerequisite, Low Risk)

**Scope**: Common utilities needed by PRs A, B, and C.

**Design**:
```lean
-- In a new file: SqlEquiv/OptimizerUtils.lean

/-- Extract all column references from an expression -/
partial def getReferencedColumns : Expr → List ColumnRef
  | .col c => [c]
  | .binOp _ l r => getReferencedColumns l ++ getReferencedColumns r
  | .unaryOp _ e => getReferencedColumns e
  | .func _ args => args.flatMap getReferencedColumns
  | .agg _ (some e) _ => getReferencedColumns e
  | .case branches else_ =>
    branches.flatMap (fun (c, r) => getReferencedColumns c ++ getReferencedColumns r) ++
    (else_.map getReferencedColumns |>.getD [])
  | .inList e _ vals => getReferencedColumns e ++ vals.flatMap getReferencedColumns
  | .between e lo hi => getReferencedColumns e ++ getReferencedColumns lo ++ getReferencedColumns hi
  | _ => []

/-- Flatten nested ANDs: (a AND (b AND c)) → [a, b, c] -/
partial def flattenAnd : Expr → List Expr
  | .binOp .and l r => flattenAnd l ++ flattenAnd r
  | e => [e]

/-- Rebuild AND chain from list (right-associative) -/
def unflattenAnd : List Expr → Option Expr
  | [] => none
  | [e] => some e
  | e :: es => (unflattenAnd es).map (Expr.binOp .and e ·)

/-- Flatten nested ORs: (a OR (b OR c)) → [a, b, c] -/
partial def flattenOr : Expr → List Expr
  | .binOp .or l r => flattenOr l ++ flattenOr r
  | e => [e]

/-- Rebuild OR chain from list -/
def unflattenOr : List Expr → Option Expr
  | [] => none
  | [e] => some e
  | e :: es => (unflattenOr es).map (Expr.binOp .or e ·)

/-- Structural comparison for deterministic ordering -/
partial def exprStructuralCmp : Expr → Expr → Ordering
  -- Implementation: compare constructors first, then recursively compare fields
  -- Literals < Columns < BinOps < UnaryOps < Functions < etc.
```

**Axioms**: None needed (these are pure structural utilities).

**Tests**: Roundtrip (flatten then unflatten), column extraction correctness.

**Files to create**:
- `SqlEquiv/OptimizerUtils.lean` - new shared utilities
- Update `SqlEquiv/Basic.lean` to export it

---

### PR A: Expression Normalization (Low Risk)

**Scope**: Canonical ordering of commutative expressions for better matching.

**Dependencies**: PR 0 (uses `flattenAnd`, `flattenOr`, `unflattenAnd`, `unflattenOr`, `exprStructuralCmp`)

**Design**:
```lean
/-- Weight-based ordering: literals < columns < complex expressions -/
def exprWeight : Expr → Nat
  | .lit _ => 0
  | .col _ => 1
  | .binOp _ _ _ => 2
  | .unaryOp _ _ => 2
  | .func _ _ => 3
  | .agg _ _ _ => 4
  | _ => 5

/-- Total ordering on expressions for canonical form -/
def exprCompare : Expr → Expr → Ordering :=
  -- Primary: compare by weight
  -- Secondary: use exprStructuralCmp from PR 0 (replaces toString repr)
  fun e1 e2 =>
    match compare (exprWeight e1) (exprWeight e2) with
    | .eq => exprStructuralCmp e1 e2
    | ord => ord

/-- Normalize to canonical form. Idempotent: normalize (normalize e) = normalize e -/
partial def normalizeExprCanonical : Expr → Expr
  | .binOp .and l r =>
    -- Use flattenAnd from PR 0, sort, rebuild with unflattenAnd
    let conjuncts := (flattenAnd (.binOp .and l r)).map normalizeExprCanonical
    let sorted := conjuncts.toArray.qsort (exprCompare · · == .lt) |>.toList
    unflattenAnd sorted |>.getD (.lit (.bool true))
  | .binOp .or l r =>
    -- Similar for OR
    let disjuncts := (flattenOr (.binOp .or l r)).map normalizeExprCanonical
    let sorted := disjuncts.toArray.qsort (exprCompare · · == .lt) |>.toList
    unflattenOr sorted |>.getD (.lit (.bool false))
  -- ... other commutative ops (add, mul, eq) ...
  | e => e  -- Non-commutative: just recurse
```

**Key decisions**:
- **Use `exprStructuralCmp` from PR 0** instead of `toString (repr e)` (more stable)
- Flatten AND/OR chains, sort, rebuild using PR 0 utilities
- Keep separate from existing `normalizeExpr` in Equiv.lean (different purpose - see clarification above)

**Axiom**:
```lean
axiom normalizeExprCanonical_equiv (e : Expr) : normalizeExprCanonical e ≃ₑ e
```

**Tests**: Idempotency, commutativity preservation, deterministic ordering.

---

### PR B: Predicate Pushdown (Medium Risk)

**Scope**: Push WHERE predicates into JOINs and subqueries.

**Dependencies**: PR 0 (uses `getReferencedColumns`, `flattenAnd`)

**Relationship to existing code**:
- Existing `optimizeFromClause` (Optimizer.lean:276) is a simpler internal function that doesn't do real pushdown
- New `pushPredicateDown` is the proper implementation with `PushdownResult`
- Existing axioms `filter_join_left`/`filter_join_right` (Equiv.lean) already support this semantically
- Reuse existing `exprReferencesOnlyTable`, `exprReferencesOnlyFrom`, `hasAggregate`

**Design** (correct from the start):
```lean
/-- Result of attempting to push a predicate down.
    - pushedFrom: the transformed FROM clause
    - remaining: predicate that couldn't be pushed (must stay in WHERE) -/
structure PushdownResult where
  pushedFrom : FromClause
  remaining : Option Expr
  deriving Repr

/-- Push predicate as deep as possible into FROM clause -/
def pushPredicateDown (pred : Expr) (from_ : FromClause) : PushdownResult
```

**Safety checks** (call before pushing):
```lean
/-- Can push predicate past SELECT projection?
    Uses getReferencedColumns (PR 0) to check column availability -/
def canPushPastProjection (pred : Expr) (items : List SelectItem) : Bool :=
  let predCols := getReferencedColumns pred  -- from PR 0
  let availableCols := items.filterMap getSelectItemAlias
  predCols.all (fun c => availableCols.contains c.column)

/-- Can push predicate past GROUP BY?
    Uses hasAggregate (existing in Semantics.lean) -/
def canPushPastGroupBy (pred : Expr) (groupBy : List Expr) : Bool :=
  !hasAggregate pred &&  -- existing utility
  (getReferencedColumns pred).all (fun c => groupBy.any (exprRefersToColumn c))

/-- Can push to left side of join? -/
def canPushLeftThroughJoin (jtype : JoinType) : Bool :=
  match jtype with
  | .inner | .cross | .left => true
  | .right | .full => false  -- might filter out NULLs incorrectly

/-- Can push to right side of join? -/
def canPushRightThroughJoin (jtype : JoinType) : Bool :=
  match jtype with
  | .inner | .cross | .right => true
  | .left | .full => false
```

**Behavior by FROM type**:
| FROM Type | Behavior |
|-----------|----------|
| `.table t` | Can't push; return `remaining = some pred` |
| `.subquery sel alias` | Push into subquery's WHERE if safe; else `remaining = some pred` |
| `.join left jtype right on_` | Push to appropriate side or add to ON; recurse |

**Axiom**:
```lean
/-- Pushdown preserves semantics: evaluating pushed FROM + filtering by remaining
    equals filtering original FROM by full predicate -/
axiom pushdown_preserves_semantics (pred : Expr) (from_ : FromClause) :
  let result := pushPredicateDown pred from_
  ∀ db, filterByRemaining db (evalFrom db result.pushedFrom) result.remaining =
        (evalFrom db from_).filter (evalPredicate db pred)
```

**Tests**: Base table preservation, subquery pushdown, outer join safety, remaining predicate handling.

---

### PR C: Join Reordering (Higher Risk)

**Scope**: Cost-based reordering of INNER/CROSS joins.

**Dependencies**: PR 0 (uses `getReferencedColumns` for edge detection)

**Relationship to existing code**:
- Existing axioms in Equiv.lean: `join_assoc`, `join_comm`, `cross_join_assoc`, `cross_join_comm`
- Existing `getFromClauseTableNames` (Equiv.lean:1201) - similar to `originalTables` but for analysis, not tracking
- No existing implementation of actual reordering

**Design** (proper state tracking from the start):
```lean
/-- A node in the join graph. Tracks all original tables it represents. -/
structure JoinNode where
  /-- Original table (for single-table nodes) or synthetic name (for combined) -/
  table : TableRef
  /-- Estimated row count -/
  estimatedRows : Nat
  /-- All original table names contained in this node (for edge matching) -/
  originalTables : List String
  deriving Repr, BEq

/-- Initialize a leaf node from a table -/
def JoinNode.leaf (t : TableRef) : JoinNode :=
  { table := t, estimatedRows := defaultCardinality, originalTables := [getTableName t] }

/-- Combine two nodes after joining them -/
def JoinNode.combine (n1 n2 : JoinNode) (cost : Nat) : JoinNode :=
  { table := ⟨"__combined__", some s!"{n1.table.name}_{n2.table.name}"⟩
  , estimatedRows := cost
  , originalTables := n1.originalTables ++ n2.originalTables }
```

**Edge matching** (uses `originalTables`):
```lean
def edgeConnects (edge : JoinEdge) (n1 n2 : JoinNode) : Bool :=
  (n1.originalTables.contains edge.leftTable && n2.originalTables.contains edge.rightTable) ||
  (n1.originalTables.contains edge.rightTable && n2.originalTables.contains edge.leftTable)
```

**Safety gate**:
```lean
/-- Only reorder if all joins are INNER/CROSS -/
def canReorderJoins (from_ : FromClause) : Bool := hasOnlyInnerJoins from_
```

**Algorithm**: Greedy selection of cheapest join pair at each step.

**Axiom**:
```lean
axiom join_reorder_preserves_semantics (from_ : FromClause) :
  canReorderJoins from_ →
  ∀ db, evalFrom db (reorderJoins from_) = evalFrom db from_
```

**Tests**: Edge matching with combined nodes, outer join rejection, cost estimation.

---

## Implementation Order

```
PR 0 (Shared Utilities)
    │
    ├──► PR A (Expression Normalization) ─────┐
    │                                         │
    ├──► PR B (Predicate Pushdown) ───────────┼──► Integration PR
    │                                         │
    └──► PR C (Join Reordering) ──────────────┘
```

1. **PR 0 (Shared Utilities)**: Prerequisite for all others, very low risk, creates `OptimizerUtils.lean`
2. **PR A (Expression Normalization)**: Depends on PR 0, low risk
3. **PR B (Predicate Pushdown)**: Depends on PR 0, medium complexity
4. **PR C (Join Reordering)**: Depends on PR 0, highest complexity

**Note**: PRs A, B, C can be developed in parallel after PR 0 merges.

## Integration: `optimizeSelectAdvanced`

After all three PRs are merged:
```lean
def optimizeSelectAdvanced (sel : SelectStmt) : SelectStmt :=
  -- 1. Basic optimization (existing)
  let sel1 := optimizeSelectStmt sel

  -- 2. Normalize WHERE for better matching
  let where' := sel1.whereClause.map normalizeExprCanonical

  -- 3. Reorder joins if safe (PR C)
  let from' := sel1.fromClause.map fun f =>
    if canReorderJoins f then reorderJoins f else f

  -- 4. Push predicates down (PR B)
  let (from'', remainingWhere) := match from', where' with
    | some f, some w =>
      let result := pushPredicateDown w f
      (some result.pushedFrom, result.remaining)
    | f, w => (f, w)

  -- 5. Reconstruct
  SelectStmt.mk sel1.distinct sel1.items from'' remainingWhere
               sel1.groupBy sel1.having sel1.orderBy sel1.limitVal sel1.offsetVal
```

## Success Criteria

- [ ] PR 0 merged first with shared utilities
- [ ] Each PR passes CI independently
- [ ] Each PR has focused, comprehensive tests
- [ ] No function signature changes after initial implementation (see table above)
- [ ] Axioms accurately describe implementation behavior
- [ ] Code is reviewable in one pass (no accumulated patches)
- [ ] Existing utilities (`hasAggregate`, `exprReferencesOnlyFrom`, etc.) are reused, not duplicated

## Comparison with PR #1

| Aspect | PR #1 | New Approach |
|--------|-------|--------------|
| PRs | 1 large | 4 focused (PR 0 + A/B/C) |
| Shared utilities | Duplicated/inline | Centralized in `OptimizerUtils.lean` |
| `pushPredicateDown` return | Changed mid-review | Correct from start |
| Join node tracking | `containedTables` patch | `originalTables` designed in |
| Axiom accuracy | Fixed multiple times | Match implementation |
| Reuse of existing code | Missed opportunities | Leverages existing utilities |
| Reviewability | Required 10+ rounds | Should be 1-2 rounds each |

## Function Signature Stability

To avoid signature changes mid-review:

| Function | Signature | Stable? |
|----------|-----------|---------|
| `getReferencedColumns` | `Expr → List ColumnRef` | ✓ Simple, unlikely to change |
| `flattenAnd/Or` | `Expr → List Expr` | ✓ Straightforward |
| `unflattenAnd/Or` | `List Expr → Option Expr` | ✓ Returns Option for empty list |
| `exprStructuralCmp` | `Expr → Expr → Ordering` | ✓ Standard comparison signature |
| `normalizeExprCanonical` | `Expr → Expr` | ✓ Same as existing `normalizeExpr` |
| `PushdownResult` | `{ pushedFrom : FromClause, remaining : Option Expr }` | ✓ Designed correctly upfront |
| `pushPredicateDown` | `Expr → FromClause → PushdownResult` | ✓ Non-optional pred, returns struct |
| `JoinNode` | `{ table, estimatedRows, originalTables }` | ✓ All fields designed in |

**Enforcement**: Each PR should include a "Public API" section listing exported functions with signatures. Reviewers should flag any signature changes.

## Next Steps

1. Create branch `feature/optimizer-utils` and implement PR 0
2. After PR 0 merges, create branches for PRs A, B, C (can be parallel)
   - `feature/expr-normalization` for PR A
   - `feature/predicate-pushdown` for PR B
   - `feature/join-reordering` for PR C
3. After all merge, create `feature/optimizer-integration` for the final `optimizeSelectAdvanced`
4. Close PR #1 or cherry-pick any valuable tests
