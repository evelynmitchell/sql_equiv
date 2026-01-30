# Advanced Query Optimizer Redesign Plan

## Overview

This document outlines a cleaner implementation plan for advanced query optimization features: join reordering, expression normalization, and predicate pushdown. This replaces the approach in PR #1 which accumulated too many patches during review.

## Lessons Learned from PR #1

1. **Function signatures matter upfront**: `pushPredicateDown` needed to return remaining predicates, but this was discovered late
2. **Join reordering state tracking was bolted-on**: The `containedTables` field was added as a fix rather than designed in
3. **Axioms should match implementation**: Several axioms were tautological or didn't reflect actual semantics
4. **Smaller PRs are better**: Three major features in one PR made review difficult

## Proposed Approach: Three Separate PRs

### PR A: Expression Normalization (Low Risk)

**Scope**: Canonical ordering of commutative expressions for better matching.

**Design**:
```lean
/-- Weight-based ordering: literals < columns < complex expressions -/
def exprWeight : Expr → Nat

/-- Total ordering on expressions for canonical form -/
def exprCompare : Expr → Expr → Ordering

/-- Normalize to canonical form. Idempotent: normalize (normalize e) = normalize e -/
def normalizeExprCanonical : Expr → Expr
```

**Key decisions**:
- Use `toString (repr e)` for structural comparison fallback (deterministic)
- Flatten AND/OR chains, sort, rebuild
- Keep separate from the existing `normalizeExpr` in Equiv.lean (different purpose)

**Axiom**:
```lean
axiom normalizeExprCanonical_equiv (e : Expr) : normalizeExprCanonical e ≃ₑ e
```

**Tests**: Idempotency, commutativity preservation, deterministic ordering.

---

### PR B: Predicate Pushdown (Medium Risk)

**Scope**: Push WHERE predicates into JOINs and subqueries.

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
def canPushPastProjection (pred : Expr) (items : List SelectItem) : Bool
def canPushPastGroupBy (pred : Expr) (groupBy : List Expr) : Bool
def canPushLeftThroughJoin (jtype : JoinType) : Bool
def canPushRightThroughJoin (jtype : JoinType) : Bool
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

1. **PR A (Expression Normalization)**: Independent, low risk, useful immediately
2. **PR B (Predicate Pushdown)**: Depends on nothing, medium complexity
3. **PR C (Join Reordering)**: Most complex, benefits from PR B being stable

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

- [ ] Each PR passes CI independently
- [ ] Each PR has focused, comprehensive tests
- [ ] No function signature changes after initial implementation
- [ ] Axioms accurately describe implementation behavior
- [ ] Code is reviewable in one pass (no accumulated patches)

## Comparison with PR #1

| Aspect | PR #1 | New Approach |
|--------|-------|--------------|
| PRs | 1 large | 3 focused |
| `pushPredicateDown` return | Changed mid-review | Correct from start |
| Join node tracking | `containedTables` patch | `originalTables` designed in |
| Axiom accuracy | Fixed multiple times | Match implementation |
| Reviewability | Required 10+ rounds | Should be 1-2 rounds each |

## Next Steps

1. Create branch `feature/expr-normalization` and implement PR A
2. After PR A merges, create `feature/predicate-pushdown` for PR B
3. After PR B merges, create `feature/join-reordering` for PR C
4. Close PR #1 or cherry-pick any valuable tests
