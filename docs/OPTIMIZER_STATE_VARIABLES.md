# Optimizer State Variables (Cleanroom Specification)

This document defines all state variables in the optimizer system for formal verification purposes.

---

## Core AST State (Existing - from Ast.lean)

| Variable | Type | Description | Mutability |
|----------|------|-------------|------------|
| `Expr` | Inductive | Expression AST (lit, col, binOp, unaryOp, func, agg, case, etc.) | Immutable |
| `SelectStmt` | Structure | Full SELECT statement (distinct, items, from, where, groupBy, having, orderBy, limit, offset) | Immutable |
| `FromClause` | Inductive | FROM clause: `.table`, `.subquery`, `.join` | Immutable |
| `ColumnRef` | Structure | `{ table : Option String, column : String }` | Immutable |
| `TableRef` | Structure | `{ name : String, alias : Option String }` | Immutable |
| `WindowSpec` | Inductive | `WindowSpec.mk (partitionBy : List Expr) (orderBy : List OrderByItem)` | Immutable |
| `JoinType` | Inductive | `.inner`, `.left`, `.right`, `.full`, `.cross` | Immutable |

---

## PR 0: Shared Utilities (New - Derived State)

| Variable | Type | Description | Derived From |
|----------|------|-------------|--------------|
| `referencedColumns` | `List ColumnRef` | Columns referenced in an expression | `Expr` |
| `conjuncts` | `List Expr` | Flattened AND chain | `Expr` |
| `disjuncts` | `List Expr` | Flattened OR chain | `Expr` |

---

## PR A: Expression Normalization (New)

| Variable | Type | Description | Invariant |
|----------|------|-------------|-----------|
| `exprWeight` | `Nat` | Ordering weight (0=lit, 1=col, 2=binOp, ...) | `0 <= weight <= 5` |
| `normalizedExpr` | `Expr` | Canonicalized expression | `normalizedExpr ≃ₑ originalExpr` |

---

## PR B: Predicate Pushdown (New)

| Variable | Type | Description | Invariant |
|----------|------|-------------|-----------|
| `PushdownResult.pushedFrom` | `FromClause` | Transformed FROM with pushed predicates | Semantically equivalent when combined with `remaining` |
| `PushdownResult.remaining` | `Option Expr` | Predicates that couldn't be pushed | Must stay in WHERE clause |
| `canPush` | `Bool` | Safety check result | `true` -> pushdown is semantics-preserving |

---

## PR C: Join Reordering (New)

| Variable | Type | Description | Invariant |
|----------|------|-------------|-----------|
| `JoinNode.table` | `TableRef` | Original or synthetic table reference | - |
| `JoinNode.estimatedRows` | `Nat` | Cardinality estimate | `>= 0` |
| `JoinNode.originalTables` | `List String` | All original table names in this node | Non-empty, preserved through combines |
| `JoinEdge.leftTable` | `String` | Left side of join predicate | Must exist in some node |
| `JoinEdge.rightTable` | `String` | Right side of join predicate | Must exist in some node |
| `JoinEdge.predicate` | `Expr` | The join condition | - |
| `JoinEdge.selectivity` | `Float` | Estimated selectivity | `0.0 <= sel <= 1.0` |
| `joinGraph.nodes` | `List JoinNode` | Current nodes in graph | Decreases by 1 each iteration |
| `joinGraph.edges` | `List JoinEdge` | Available join predicates | Edges matching combined nodes are consumed |

---

## Global Optimization State

| Variable | Type | Description | Transition |
|----------|------|-------------|------------|
| `optimizationPhase` | Enum | Current phase | `Basic -> Normalize -> Reorder -> Pushdown -> Done` |
| `inputStmt` | `SelectStmt` | Original statement | Read-only |
| `outputStmt` | `SelectStmt` | Optimized statement | `outputStmt ≃ₛ inputStmt` |

---

## State Transition Diagram

```
┌─────────────┐
│ inputStmt   │
└──────┬──────┘
       │ optimizeSelectStmt (existing)
       v
┌─────────────┐
│ sel1        │  (basic optimizations applied)
└──────┬──────┘
       │ normalizeExprCanonical (PR A)
       v
┌─────────────┐
│ sel2        │  (WHERE normalized)
└──────┬──────┘
       │ reorderJoins (PR C) if canReorderJoins
       v
┌─────────────┐
│ sel3        │  (joins reordered)
└──────┬──────┘
       │ pushPredicateDown (PR B)
       v
┌─────────────┐
│ outputStmt  │  (predicates pushed, remaining in WHERE)
└─────────────┘
```

---

## Key Invariants

1. **Semantic Preservation**: At every phase transition, `output ≃ input`
2. **Termination**: Each phase processes finite AST structures
3. **Idempotency**: `normalizeExprCanonical (normalizeExprCanonical e) = normalizeExprCanonical e`
4. **Safety Gates**: `canReorderJoins` and `canPush*` functions prevent unsafe transformations
5. **Original Table Tracking**: `JoinNode.originalTables` is always non-empty and preserved through `combine`

---

## Related Documents

- [OPTIMIZER_REDESIGN_PLAN.md](./OPTIMIZER_REDESIGN_PLAN.md) - Implementation plan and design details
