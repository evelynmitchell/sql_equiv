# Impact of Removing the Optimizer on Equivalence Proving

> **Historical snapshot.** Axiom/theorem counts in this document are as of when it was written. As of 25 Nov 2026 the codebase has **0 axioms** (all proved since PR #173) and **714 theorems**; run `python3 tools/count_axioms_theorems.py` for the live count. This is the *pre-removal* analysis: the optimizer it discusses was removed in PR #156, with the predicted zero impact on the equivalence proofs.

## Summary

The optimizer (`SqlEquiv/Optimizer.lean` and related modules) can be removed
with **zero impact** on the equivalence proof infrastructure. The dependency
is strictly one-directional: the optimizer imports and consumes equivalence
definitions, but equivalence never imports or references the optimizer.

## Dependency Graph

```
 Ast ──────────┐
               ▼
          Semantics
               │
               ▼
       Equiv (Defs, ValueLemmas, ExprAxioms,
              Decidable, Comparison, SetBagLemmas,
              StatementAxioms)
               │
               ▼                      ◀── one-way dependency
   ┌───────────┴───────────────┐
   │  Optimizer.lean           │
   │  OptimizerUtils.lean      │
   │  ExprNormalization.lean   │
   │  PredicatePushdown.lean   │
   │  JoinReordering.lean      │
   └───────────────────────────┘
```

The Equiv module's imports are:

| File | Imports |
|------|---------|
| `Equiv/Defs.lean` | `Ast`, `Semantics` |
| `Equiv/ValueLemmas.lean` | `Equiv.Defs` |
| `Equiv/ExprAxioms.lean` | `Equiv.Defs`, `Equiv.ValueLemmas` |
| `Equiv/Decidable.lean` | `Equiv.Defs`, `Equiv.ExprAxioms` |
| `Equiv/Comparison.lean` | `Equiv.Defs`, `Equiv.ValueLemmas`, `Equiv.Decidable`, `Equiv.SetBagLemmas` |
| `Equiv/SetBagLemmas.lean` | `Equiv.Defs` |
| `Equiv/StatementAxioms.lean` | `Equiv.Defs`, `Equiv.SetBagLemmas` |

No file under `Equiv/` imports `Optimizer`, `OptimizerUtils`, `ExprNormalization`,
`PredicatePushdown`, or `JoinReordering`.

## What the Equivalence Framework Proves (Without the Optimizer)

The `Equiv/` module contains **311 theorems** and **13 axioms** covering:

### Expression-level (42 theorems in ExprAxioms)
- Commutativity: `and_comm`, `or_comm`, `add_comm`, `mul_comm`, `eq_comm`
- Associativity: `and_assoc`, `or_assoc`
- De Morgan: `not_and`, `not_or`, `or_not_not`, `and_not_not`
- Distributivity: `and_or_distrib_left/right`, `or_and_distrib_left/right`
- Absorption: `and_absorb_or`, `or_absorb_and`
- Identity: `and_true`, `or_false`, `and_false`, `or_true` (+ commuted variants)
- Idempotence: `and_self`, `or_self`
- Complement: `and_not_self`, `or_not_self`
- Double negation: `not_not`
- Congruence: `binOp_congr`, `unaryOp_congr`
- WHERE simplification: `where_true_elim`, `where_false_empty`

### Value-level (37 theorems in ValueLemmas)
- `evalBinOp_and_comm`, `evalBinOp_or_comm`, `evalBinOp_add_comm`, etc.
- `evalBinOp_and_assoc`, `evalBinOp_or_assoc`, etc.
- Short-circuit proofs: `evalBinOp_and_false_right`, `evalBinOp_or_true_right`
- Algebraic identities at the `Option Value` level

### Statement-level (64 theorems in StatementAxioms)
- SET operations: `union_all_comm`, `union_comm`, `union_assoc`, `intersect_assoc`, `intersect_comm`, `union_idempotent`, `union_empty_right`, `except_self_empty`, `intersect_empty_right`
- Distributivity: `union_intersect_distrib`, `intersect_union_distrib`
- JOIN properties: `inner_join_true_is_cross`, `inner_join_false_empty`, `cross_join_cardinality`, `cross_join_cardinality_comm`, `inner_join_cardinality_le`, `left_join_cardinality_ge`, `right_join_cardinality_ge`, `cross_join_assoc_cardinality`, `inner_join_to_where`, `left_join_preserves_left`, `right_join_preserves_right`, `inner_subset_cross`, `left_join_filter_null_is_inner`
- Subquery: `exists_empty_false`, `exists_nonempty_true`, `not_not_exists`, `in_empty_subquery_false`, `not_in_empty_subquery_true`, `scalar_subquery_empty_null`, `exists_as_count_gt_zero`, `exists_monotonic`, `in_singleton_subquery`
- LIMIT/OFFSET: `limit_zero_empty`, `limit_upper_bound`, `limit_monotonic`, `offset_zero_identity`, `offset_too_large_empty`, `consecutive_pages`, `pagination_upper_bound`, etc.

### Equivalence relations (20 theorems in Defs)
- Reflexivity, symmetry, transitivity for all 6 equivalence relations (`≃ₑ`, `≃ₛ`, `≃ᵩ`, `≃ᵇ`, `≃ˢ`, `≃`)
- Coercion: `QueryEquiv.toBagEquiv`, `QueryBagEquiv.toSetEquiv`

### Other (148 theorems across Decidable, Comparison, SetBagLemmas)
- String/LIKE pattern matching, BETWEEN expansion, comparison normalization
- List-level permutation and set membership lemmas
- Decidable equivalence for syntactic checks

All of the above are self-contained. None reference any optimizer function.

## What the Optimizer Contributes

The optimizer files contain:

### 3 axioms (in Optimizer.lean)
```lean
axiom optimizeExpr_equiv (e : Expr) : optimizeExpr e ≃ₑ e
axiom optimizeSelectStmt_equiv (s : SelectStmt) : optimizeSelectStmt s ≃ₛ s
axiom optimize_equiv (s : Stmt) : optimize s ≃ s
```

These claim the optimizer output is equivalent to its input. They are
*consumers* of `≃ₑ`, `≃ₛ`, and `≃`, not definitions of them.

### 6 derived theorems (in Optimizer.lean)
- `where_true_elim_correct`, `where_false_preserves_equiv`
- `double_neg_elim_correct`, `constant_fold_correct`
- `and_false_correct`, `or_true_correct`

All 6 are derived by combining the optimizer axioms with theorems already
proven independently in `Equiv/ExprAxioms.lean` (e.g. `and_false`, `or_true`,
`not_not`). The underlying algebraic facts are already proven; these theorems
just compose them with the optimizer soundness claim.

### Rewrite functions (~500 lines)
- `foldArithmetic`, `foldComparison`, `foldLogical` (constant folding)
- `applyDeMorgan`, `eliminateDoubleNegation`, `applyIdentityLaws` (boolean simplification)
- `applyIdempotentLaws`, `applyComplementLaws`, `simplifyArithmetic`
- `optimizeExpr`, `optimizeSelectStmt`, `optimize` (recursive traversals)
- `CostFactors`, `estimateCost`, `generateReport` (cost model)

### Satellite modules
- `OptimizerUtils.lean`: shared utilities (column extraction, expression flattening)
- `ExprNormalization.lean`: canonical ordering
- `PredicatePushdown.lean`: WHERE-into-JOIN pushdown
- `JoinReordering.lean`: cost-based join order

## Concrete Impact of Removal

| Aspect | Impact |
|--------|--------|
| Equivalence definitions (`≃ₑ`, `≃ₛ`, `≃ᵩ`, `≃ᵇ`, `≃ˢ`, `≃`) | None |
| Expression-level theorems (311 in Equiv/) | None |
| Statement-level theorems (SET, JOIN, subquery, LIMIT) | None |
| Value-level lemmas | None |
| Decidable equivalence checking | None |
| Comparison/normalization proofs | None |
| 3 optimizer soundness axioms | Lost |
| 6 optimizer-specific derived theorems | Lost |
| Rewrite functions and cost model | Lost |
| Build time | Reduced (fewer files to compile) |

### What is lost

1. **The claim that the optimizer preserves semantics** (3 axioms). These are
   currently unproven (`axiom`, not `theorem`), so their removal does not weaken
   any proven result.

2. **6 derived theorems** that compose optimizer axioms with Equiv theorems.
   Since these depend on unproven axioms, they carry no more proof-theoretic
   weight than the axioms themselves.

3. **Executable optimization** — the ability to transform queries at runtime.
   This is a practical feature, not a proof artifact.

### What is preserved

Everything that constitutes the formal equivalence framework:
- All 6 equivalence relation definitions
- All 311 proven theorems
- All 13 axioms in the Equiv module (JOIN commutativity/associativity,
  subquery unnesting, etc.)
- The complete algebraic theory of SQL boolean expressions
- The complete theory of SET operations, JOINs, subqueries, and pagination

## Required Code Changes for Removal

1. **`SqlEquiv.lean`** (root): Remove `import SqlEquiv.Optimizer`
2. **Delete files**: `Optimizer.lean`, `OptimizerUtils.lean`, `ExprNormalization.lean`,
   `PredicatePushdown.lean`, `JoinReordering.lean`
3. **Update `lakefile.lean`**: Remove any optimizer-specific lean_lib or lean_exe entries
   if present
4. **Tests**: Remove or migrate `Test/OptimizerTest.lean` and
   `LSpecTests/QueryOptimizer.lean`
5. **`SqlEquiv/Basic.lean`**: Remove `import SqlEquiv.OptimizerUtils` and any
   re-exports of optimizer symbols

No changes needed to any file under `Equiv/`, `Ast.lean`, `Semantics.lean`,
`SemanticsBase.lean`, `SemanticsCore.lean`, `Parser.lean`, `Pretty.lean`, or
`Tactics.lean`.

## Conclusion

The equivalence proof infrastructure is architecturally independent from the
optimizer. Removing the optimizer would delete executable optimization
capabilities and 3 unproven axioms, but would not invalidate, weaken, or
require changes to any equivalence theorem. The formal guarantees of the
project would be strictly unchanged.
