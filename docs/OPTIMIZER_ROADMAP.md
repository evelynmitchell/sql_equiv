# SQL Equivalence Optimizer Roadmap

This document provides a comprehensive roadmap for optimizer development, from current work through long-term enhancements.

---

## Overview

The optimizer development follows a phased approach, building increasingly sophisticated transformations while maintaining formal verification as a first-class concern.

```
Phase 1: Foundation (COMPLETE)
    PR 0: Shared Utilities ✓
    PR A: Expression Normalization ✓

Phase 2: Core Optimizations (IN PROGRESS)
    PR B: Predicate Pushdown (PR #7)
    PR C: Join Reordering (PR #8)
    Integration PR

Phase 3: Cost Model Enhancement
    Advanced Cost Estimation
    Statistics Collection

Phase 4: Advanced Transformations
    Aggregate Pushdown
    Subquery Flattening
    Window Function Optimization

Phase 5: Plan Space Expansion
    Dynamic Programming Join Optimizer

Phase 6: Physical Optimization
    Partition Pruning
    Materialized View Recognition
```

---

## Phase 1: Foundation (COMPLETE)

### PR 0: Shared Utilities ✓
- `flattenAnd`/`unflattenAnd` - AND chain manipulation
- `flattenOr`/`unflattenOr` - OR chain manipulation
- `getReferencedColumns` - column reference extraction
- `exprStructuralCmp` - deterministic expression comparison

### PR A: Expression Normalization ✓
- `normalizeExprCanonical` - canonical expression ordering
- Weight-based comparison (literals < columns < complex)
- Idempotent transformation

---

## Phase 2: Core Optimizations (IN PROGRESS)

### PR B: Predicate Pushdown
**Status:** PR #7 open, under review
**Spec:** [OPTIMIZER_REDESIGN_PLAN.md](./OPTIMIZER_REDESIGN_PLAN.md#pr-b-predicate-pushdown-medium-risk)

Push WHERE predicates closer to data sources to reduce intermediate result sizes.

### PR C: Join Reordering
**Status:** PR #8 open, under review
**Spec:** [OPTIMIZER_REDESIGN_PLAN.md](./OPTIMIZER_REDESIGN_PLAN.md#pr-c-join-reordering-higher-risk)

Reorder INNER/CROSS joins using greedy cost-based selection.

### Integration PR
**Status:** Pending PR B & C merge
**Spec:** [OPTIMIZER_REDESIGN_PLAN.md](./OPTIMIZER_REDESIGN_PLAN.md#integration-optimizeselectadvanced)

Combine all optimizations into `optimizeSelectAdvanced`.

---

## Phase 3: Cost Model Enhancement

### Advanced Cost Estimation
**Spec:** [specs/ADVANCED_COST_ESTIMATION.md](./specs/ADVANCED_COST_ESTIMATION.md)

Replace hardcoded cardinality estimates with statistics-based cost model.

| Aspect | Current | Target |
|--------|---------|--------|
| Table cardinality | `defaultCardinality := 1000` | Actual row counts |
| Join selectivity | `0.1` constant | Histogram-based estimation |
| Predicate selectivity | Not estimated | Column statistics |

### Statistics Collection
**Spec:** Included in Advanced Cost Estimation

Infrastructure for gathering and maintaining table/column statistics.

---

## Phase 4: Advanced Transformations

### Aggregate Pushdown
**Spec:** [specs/AGGREGATE_PUSHDOWN.md](./specs/AGGREGATE_PUSHDOWN.md)

Push GROUP BY aggregations below joins when safe, reducing rows before joining.

```sql
-- Before
SELECT dept, SUM(salary) FROM employees e JOIN departments d ON e.dept_id = d.id GROUP BY dept

-- After (conceptual)
SELECT dept, total FROM (SELECT dept_id, SUM(salary) as total FROM employees GROUP BY dept_id) e
JOIN departments d ON e.dept_id = d.id
```

### Subquery Flattening
**Spec:** [specs/SUBQUERY_FLATTENING.md](./specs/SUBQUERY_FLATTENING.md)

Convert subqueries to joins for better optimization opportunities.

| Subquery Type | Transformation |
|---------------|----------------|
| Uncorrelated IN | Semi-join |
| Uncorrelated NOT IN | Anti-join |
| Uncorrelated EXISTS | Semi-join |
| Scalar subquery | Left join with LIMIT 1 semantics |
| Correlated | Decorrelation + join |

### Window Function Optimization
**Spec:** [specs/WINDOW_FUNCTION_OPTIMIZATION.md](./specs/WINDOW_FUNCTION_OPTIMIZATION.md)

Optimize window function evaluation order and predicate interaction.

---

## Phase 5: Plan Space Expansion

### Dynamic Programming Join Optimizer
**Spec:** [specs/DP_JOIN_OPTIMIZER.md](./specs/DP_JOIN_OPTIMIZER.md)

Replace greedy join ordering with dynamic programming to explore more plan permutations.

| Approach | Plans Explored | Optimal? |
|----------|---------------|----------|
| Greedy (current) | O(n²) | No (~70-80% of optimal) |
| DP (proposed) | O(3ⁿ) | Yes (for bushy trees) |

---

## Phase 6: Physical Optimization

### Partition Pruning
**Spec:** [specs/PARTITION_PRUNING.md](./specs/PARTITION_PRUNING.md)

Eliminate partitions based on query predicates.

```sql
-- Given: sales PARTITIONED BY (year)
SELECT * FROM sales WHERE year = 2024
-- Prune: Only scan year=2024 partition
```

### Materialized View Recognition
**Spec:** [specs/MATERIALIZED_VIEW_RECOGNITION.md](./specs/MATERIALIZED_VIEW_RECOGNITION.md)

Detect when query subexpressions can be satisfied by existing materialized views.

---

## Dependency Graph

```
                    ┌──────────────────┐
                    │  PR 0: Utilities │ ✓
                    └────────┬─────────┘
                             │
            ┌────────────────┼────────────────┐
            │                │                │
            ▼                ▼                ▼
    ┌───────────────┐ ┌─────────────┐ ┌───────────────┐
    │ PR A: Normalize│ │ PR B: Push  │ │ PR C: Reorder │
    │       ✓        │ │   down      │ │    joins      │
    └───────────────┘ └──────┬──────┘ └───────┬───────┘
                             │                │
                             └───────┬────────┘
                                     │
                                     ▼
                         ┌───────────────────────┐
                         │   Integration PR      │
                         └───────────┬───────────┘
                                     │
                    ┌────────────────┼────────────────┐
                    │                │                │
                    ▼                ▼                ▼
          ┌─────────────┐   ┌───────────────┐   ┌─────────────┐
          │  Advanced   │   │   Aggregate   │   │  Subquery   │
          │Cost Estimate│   │   Pushdown    │   │  Flattening │
          └──────┬──────┘   └───────────────┘   └─────────────┘
                 │
                 ▼
        ┌────────────────┐
        │  DP Join Opt   │
        └────────────────┘
                 │
        ┌────────┴────────┐
        │                 │
        ▼                 ▼
┌───────────────┐  ┌──────────────┐
│  Partition    │  │ Materialized │
│   Pruning     │  │    Views     │
└───────────────┘  └──────────────┘
```

---

## Verification Strategy

Each phase maintains the verification approach from the foundation:

1. **Axiom-first**: State correctness properties as axioms
2. **Test thoroughly**: Property-based testing in parallel
3. **Prove incrementally**: Replace axioms with proofs as time permits

See [OPTIMIZER_VERIFICATION_PLAN.md](./OPTIMIZER_VERIFICATION_PLAN.md) for detailed proof strategies.

---

## Estimated Effort

| Phase | Features | Est. Implementation | Est. Verification |
|-------|----------|---------------------|-------------------|
| 1 | Foundation | ✓ Complete | 2-3 days |
| 2 | Core Optimizations | 2 weeks | 2 weeks |
| 3 | Cost Model | 1 week | 1 week |
| 4 | Advanced Transforms | 3 weeks | 3 weeks |
| 5 | DP Optimizer | 1 week | 2 weeks |
| 6 | Physical Opts | 2 weeks | 2 weeks |

**Total estimated:** ~10 weeks implementation + ~10 weeks verification

---

## Success Metrics

### Correctness
- All transformations preserve query semantics
- Formal proofs for core transformations
- No regressions in test suite

### Performance
- Measurable improvement on Spider benchmark queries
- Optimizer itself runs in reasonable time (< 100ms for typical queries)

### Maintainability
- Each feature in separate module
- Clear interfaces between components
- Comprehensive documentation

---

## References

- [OPTIMIZER_REDESIGN_PLAN.md](./OPTIMIZER_REDESIGN_PLAN.md) - Phase 2 detailed design
- [OPTIMIZER_VERIFICATION_PLAN.md](./OPTIMIZER_VERIFICATION_PLAN.md) - Formal verification strategy
- [OPTIMIZER_STATE_VARIABLES.md](./OPTIMIZER_STATE_VARIABLES.md) - State variable specifications
- Individual feature specs in [specs/](./specs/)
