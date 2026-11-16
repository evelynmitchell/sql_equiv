# Typed core inventory: `SqlEquiv` laws → `SqlCore`

This is the inventory that phase 5 (#294) of the [typed core plan](TYPED_CORE_PLAN.md) asks for. It
lists every `theorem` declared in the four `SqlEquiv` equivalence files below and says what became
of it in the typed core `SqlCore`. The typed laws are the ones in `SqlCore/Scalar.lean`,
`Truth.lean`, `Preconditions.lean`, `Equiv.lean`, `QueryEquiv.lean` and `QueryLaws.lean`, re-derived
from cslib-frontier at `e78796a1` (`CslibFrontier/Languages/SQL/{Equiv,QueryEquiv,QueryLaws}.lean`).
None of the four files declares an `axiom` or a `lemma`.

The typed core covers the following fragment:

- **Scalar expressions:** int, text, bool and exact decimal values, `NULL`, unary and binary
  operators, `IN` over a list of literals, and `CASE`.
- **Queries:** table, `WHERE` (`select`), `SELECT` list (`project`), inner join `ON θ`,
  `UNION ALL` and `DISTINCT`.

Side conditions quantify over rows that conform to a typing context `Γ`. Where possible they are
decidable checks: `e.typeOf Γ = some τ`, `Expr.IsSafe`, `Expr.IsSafePredicate` and `q.typeOf = some Γ`.
`NULL` is `none`. Errors are strict: there is no short-circuit, and the first failure fails the
whole expression or query. Equivalence observes `Except.toOption`, so it sees whether evaluation
succeeds and with what result, but not which error is raised.

**Legend** (the Category column):

- `counterpart`: a `SqlCore` theorem states the same law. Any hypothesis it adds is named in the
  row.
- `decidable check`: the same law, where a semantic `SqlEquiv` hypothesis became a decidable
  typed check. The row names both. The map from hypothesis to check is in
  `SqlCore/Preconditions.lean`.
- `counterpart?`: probably the same law, but the match is not exact. The row says why.
- `not carried over`: the row gives the reason. Rows marked *phase 7* are planned for the
  certified simplifier and decision procedure (#296). Rows marked *phase 8* are planned for
  features beyond the frontier (#297).

In the tables, a name written without a namespace is in `SqlCore`. `Expr.Equiv.x` stands for
`SqlCore.Expr.Equiv.x`, and `Query.x` stands for `SqlCore.Query.x`.

**Other equivalence files (not inventoried):** `SqlEquiv/Equiv/` also contains the following files.

| File | Declarations | Contents |
|---|---|---|
| `Comparison.lean` | 206 | NULL laws, comparison laws, predicate pushdown |
| `ValueLemmas.lean` | 51 | value-level operator laws; their typed counterparts are the operator laws in `SqlCore/Scalar.lean` |
| `Decidable.lean` | 43 | `DecidableEq`, ground-term detection, reference helpers |
| `StatementChecker.lean` | 0 | the certified statement checkers |

`Comparison.lean` clearly contains equivalence laws, and it needs its own inventory.

## `SqlEquiv/Equiv/Defs.lean` (21 theorems, 0 private)

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `expr_equiv_refl` | counterpart | `Expr.Equiv.refl` (over the rows of `Γ`) |
| `expr_equiv_symm` | counterpart | `Expr.Equiv.symm` |
| `expr_equiv_trans` | counterpart | `Expr.Equiv.trans` (also the `Trans` instance and `Expr.equivSetoid`) |
| `ExprEquiv.toEmptyDb` | not carried over | Artefact of the untyped representation: typed `Expr` has no subqueries, so evaluation takes no database and `≃ₑ` and `≃ₑ₀` coincide |
| `select_equiv_refl` | counterpart | `Query.Equiv.refl .ordered`; the `SelectStmt`/`Query` split is an AST artefact, and typed `Query` is one type |
| `select_equiv_symm` | counterpart | `Query.Equiv.symm` at `.ordered` |
| `select_equiv_trans` | counterpart | `Query.Equiv.trans` at `.ordered` |
| `query_equiv_refl` | counterpart | `Query.Equiv.refl` at `.ordered` |
| `query_equiv_symm` | counterpart | `Query.Equiv.symm` at `.ordered` |
| `query_equiv_trans` | counterpart | `Query.Equiv.trans` at `.ordered` |
| `query_bag_equiv_refl` | counterpart | `Query.Equiv.refl` at `.bag` |
| `query_bag_equiv_symm` | counterpart | `Query.Equiv.symm` at `.bag` |
| `query_bag_equiv_trans` | counterpart | `Query.Equiv.trans` at `.bag` |
| `query_set_equiv_refl` | counterpart | `Query.Equiv.refl` at `.set` |
| `query_set_equiv_symm` | counterpart | `Query.Equiv.symm` at `.set` |
| `query_set_equiv_trans` | counterpart | `Query.Equiv.trans` at `.set` |
| `QueryEquiv.toBagEquiv` | counterpart | `Query.Equiv.mono` (`ordered ≤ bag`), or `Query.Equiv.of_ordered` |
| `QueryBagEquiv.toSetEquiv` | counterpart | `Query.Equiv.mono` (`bag ≤ set`) |
| `stmt_equiv_refl` | not carried over | `Stmt` includes DML, which is outside the fragment (phase 8); for queries, see `Query.Equiv.refl` |
| `stmt_equiv_symm` | not carried over | `Stmt`/DML is outside the fragment (phase 8) |
| `stmt_equiv_trans` | not carried over | `Stmt`/DML is outside the fragment (phase 8) |

## `SqlEquiv/Equiv/ExprAxioms.lean` (60 theorems, 0 private)

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `and_comm` | counterpart | `Expr.Equiv.binary_comm` with `evalBinOp_and_comm`; there is no hypothesis on either side |
| `or_comm` | counterpart | `Expr.Equiv.binary_comm` with `evalBinOp_or_comm` |
| `add_comm` | counterpart | `Expr.Equiv.binary_comm` with `evalBinOp_add_comm` |
| `mul_comm` | counterpart | `Expr.Equiv.binary_comm` with `evalBinOp_mul_comm` |
| `not_not_bool` | counterpart | `evalUnOp_not_not` (datum level, `d.HasType .bool`, NULL included); `Truth.not_not` |
| `not_not` | decidable check | `Expr.Equiv.not_not`: `isBoolValued` becomes `p.typeOf Γ = some .bool` |
| `eq_comm` | counterpart | `Expr.Equiv.binary_comm` with `CmpOp.eval_eq_comm` (or `evalBinOp_cmp_swap .eq`) |
| `and_assoc` | not carried over | Phase 7: no `Expr.Equiv` statement yet. `inf_assoc` on `Truth` gives it, and it needs no side condition because both sides evaluate `a`, `b` and `c` |
| `or_assoc` | not carried over | Phase 7: no `Expr.Equiv` statement yet. `sup_assoc` on `Truth` gives it, with no side condition |
| `not_and` | counterpart | `not_evalBinOp_and` (operator level, every datum); the `isBoolValued` hypotheses are dropped; the `Expr` lift is not stated |
| `not_or` | counterpart | `not_evalBinOp_or` (operator level); the `isBoolValued` hypotheses are dropped |
| `and_or_distrib_left` | not carried over | Phase 7: no `Expr.Equiv` statement. `Truth` is a distributive lattice (`inf_sup_left`), and no condition is needed because both sides evaluate every operand |
| `and_or_distrib_right` | not carried over | Phase 7: as `and_or_distrib_left` (`inf_sup_right`) |
| `or_and_distrib_left` | not carried over | Phase 7: as `and_or_distrib_left` (`sup_inf_left`) |
| `or_and_distrib_right` | not carried over | Phase 7: as `and_or_distrib_left` (`sup_inf_right`) |
| `and_absorb_or` | not carried over | Phase 7: `inf_sup_self` on `Truth`. The `Expr` law would need `IsSafePredicate b`, because the right side drops `b` |
| `or_absorb_and` | not carried over | Phase 7: `sup_inf_self` on `Truth`. The `Expr` law would need `IsSafePredicate b` |
| `and_true` | decidable check | `Expr.Equiv.and_true`: `isBoolValued` becomes `typeOf Γ = some .bool` |
| `or_false` | decidable check | `Expr.Equiv.or_false`: `isBoolValued` becomes `typeOf Γ = some .bool` |
| `and_false` | counterpart | `Expr.Equiv.and_false`; it gains `IsSafePredicate p`, because strict errors mean there is no short-circuit |
| `or_true` | counterpart | `Expr.Equiv.or_true`; it gains `IsSafePredicate p` (strict errors) |
| `where_true_elim` | counterpart | `Query.select_true` (ordered, no condition) |
| `where_false_empty` | not carried over | Phase 7 (simplifier `WHERE FALSE` folding): there is no `select (lit false)` law. The no-aggregate hypothesis disappears, because aggregates are outside the fragment |
| `normalizeExpr_lit` | not carried over | Phase 7: equation lemma of `SqlEquiv`'s `normalizeExpr`, which the certified `Expr.simplify`/`Expr.equiv_simplify` replaces |
| `normalizeExpr_col` | not carried over | Phase 7: `normalizeExpr` equation lemma, replaced by `Expr.simplify` |
| `normalizeExpr_countStar` | not carried over | Outside the fragment (aggregates) and a `normalizeExpr` equation lemma; phase 8 |
| `normalizeExpr_windowFn` | not carried over | Outside the fragment (window functions); phase 8 |
| `normalizeExpr_exists` | not carried over | Outside the fragment (EXISTS subqueries); phase 8 |
| `normalizeExpr_subquery` | not carried over | Outside the fragment (scalar subqueries); phase 8 |
| `normalizeExpr_unaryOp` | not carried over | Phase 7: `normalizeExpr` equation lemma, replaced by `Expr.simplify` |
| `normalizeExpr_inSubquery` | not carried over | Outside the fragment (IN subqueries); phase 8 |
| `normalizeExpr_between` | not carried over | Outside the fragment (`BETWEEN`); phase 8 |
| `normalizeExpr_binOp_other` | not carried over | Phase 7: `normalizeExpr` equation lemma, replaced by `Expr.simplify` |
| `normalizeExpr_binOp_and` | not carried over | Phase 7: commutative operand sorting for `syntacticEquiv`, replaced by the simplifier and decision procedure |
| `normalizeExpr_binOp_or` | not carried over | Phase 7: as `normalizeExpr_binOp_and` |
| `normalizeExpr_binOp_add` | not carried over | Phase 7: as `normalizeExpr_binOp_and` |
| `normalizeExpr_binOp_mul` | not carried over | Phase 7: as `normalizeExpr_binOp_and` |
| `normalizeExpr_func` | not carried over | Outside the fragment (scalar functions such as COALESCE and UPPER); phase 8 |
| `normalizeExpr_agg` | not carried over | Outside the fragment (aggregates); phase 8 |
| `normalizeExpr_case` | not carried over | Phase 7: `normalizeExpr` equation lemma (typed `CASE` is binary `caseWhen`), replaced by `Expr.simplify` |
| `normalizeExpr_inList` | not carried over | Phase 7: `normalizeExpr` equation lemma (typed `IN` lists are literals), replaced by `Expr.simplify` |
| `expr_equiv_subst` | counterpart | The definition of `Expr.Equiv` (`h r hr`, on `toOption`) and `Expr.Equiv.evalTruth`. This is not `Expr.Equiv.subst`, which is about substitution |
| `true_and` | decidable check | `Expr.Equiv.true_and`: `isBoolValued` becomes `typeOf Γ = some .bool` |
| `false_or` | decidable check | `Expr.Equiv.false_or`: `isBoolValued` becomes `typeOf Γ = some .bool` |
| `false_and` | counterpart | `Expr.Equiv.false_and`; it gains `IsSafePredicate p` (strict errors) |
| `true_or` | counterpart | `Expr.Equiv.true_or`; it gains `IsSafePredicate p` (strict errors) |
| `and_self` | not carried over | Phase 7: `inf_idem` on `Truth`. The `Expr` law would need `typeOf Γ = some .bool` |
| `or_self` | not carried over | Phase 7: `sup_idem` on `Truth`. The `Expr` law would need `typeOf Γ = some .bool` |
| `and_not_self` | not carried over | False under three-valued logic (`NULL AND NOT NULL` is `NULL`; `Truth.unknown_inf_not_unknown`). It needs `IsTwoValued`, which is semantic, not decidable |
| `or_not_self` | not carried over | False under three-valued logic (`Truth.unknown_sup_not_unknown`). It needs `IsTwoValued`, which is not decidable |
| `not_self_and` | not carried over | False under three-valued logic, as `and_not_self` |
| `not_self_or` | not carried over | False under three-valued logic, as `or_not_self` |
| `or_not_not` | counterpart | `not_evalBinOp_and`, read right to left (operator level, no hypothesis) |
| `and_not_not` | counterpart | `not_evalBinOp_or`, read right to left (operator level, no hypothesis) |
| `or_and_factor_left` | not carried over | Phase 7: reverse of `and_or_distrib_left` (`inf_sup_left` on `Truth`) |
| `and_or_factor_left` | not carried over | Phase 7: reverse of `or_and_distrib_left` (`sup_inf_left` on `Truth`) |
| `binOp_congr` | counterpart | `Expr.Equiv.binary` |
| `unaryOp_congr` | counterpart | `Expr.Equiv.unary` |
| `binOp_congr_left` | counterpart | `Expr.Equiv.binary` with `Expr.Equiv.refl` |
| `binOp_congr_right` | counterpart | `Expr.Equiv.binary` with `Expr.Equiv.refl` |

## `SqlEquiv/Equiv/StatementAxioms.lean` (100 theorems: 75 public, 25 private)

### Set operations

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `union_all_length` | not carried over | Subsumed: `Query.eval_unionAll` with `List.length_append` |
| `except_self_empty` | not carried over | Outside the fragment (`EXCEPT`); phase 8 |
| `intersect_empty_right` | not carried over | Outside the fragment (`INTERSECT`); phase 8 |
| `intersect_idempotent` | not carried over | Outside the fragment (`INTERSECT`); phase 8 |
| `union_all_comm` | counterpart | `Query.unionAll_comm` (bag) |
| `union_comm` | not carried over | Outside the fragment (dedup `UNION`); phase 8. It is derivable as `DISTINCT` of `unionAll_comm` via `Query.Equiv.distinct` |
| `union_assoc` | not carried over | Outside the fragment (dedup `UNION`); phase 8 |
| `intersect_assoc` | not carried over | Outside the fragment (`INTERSECT`); phase 8 |
| `intersect_comm` | not carried over | Outside the fragment (`INTERSECT`); phase 8 |
| `union_idempotent` | counterpart? | `Query.distinct_unionAll_self`, if `UNION` is read as `DISTINCT (UNION ALL)`. The typed law keeps the `DISTINCT` on the right (ordered), while `SqlEquiv` drops it (set level) |
| `union_empty_right` | not carried over | Outside the fragment (dedup `UNION`); phase 8 |
| `union_intersect_distrib` | not carried over | Outside the fragment (`UNION`/`INTERSECT`); phase 8 |
| `intersect_union_distrib` | not carried over | Outside the fragment (`UNION`/`INTERSECT`); phase 8 |

### Joins

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `inner_join_true_is_cross` | not carried over | Artefact of the untyped AST: there is no separate `CROSS` constructor, and a cross join is `join (lit (.bool true))` by definition |
| `inner_join_false_empty` | not carried over | Phase 7 (folding `ON FALSE`): no typed law, and the result is empty only when both inputs succeed |
| `left_join_false_all_left` | not carried over | Outside the fragment (outer joins); phase 8 |
| `cross_join_cardinality` | not carried over | Subsumed: `Query.eval_join`, `Expr.filterRows_true`, `Row.product` and `List.length_product` |
| `cross_join_cardinality_comm` | not carried over | Subsumed: `Query.join_comm` (bag), whose `List.Perm` preserves length |
| `inner_join_cardinality_le` | not carried over | Subsumed: `Query.eval_join` (`filterRows` keeps a sublist of `Row.product`) with `List.length_product`; exact equijoin counts are in frontier `JoinSize.lean`, which is not ported |
| `left_join_cardinality_ge` | not carried over | Outside the fragment (outer joins); phase 8 |
| `right_join_cardinality_ge` | not carried over | Outside the fragment (outer joins); phase 8 |
| `inner_join_empty_left` | not carried over | Subsumed: `Query.eval_join` with `List.nil_product` (under strict errors, the other input must still succeed) |
| `inner_join_empty_right` | not carried over | Subsumed: `Query.eval_join` with `List.product_nil` |
| `cross_join_empty_left` | not carried over | Subsumed: as `inner_join_empty_left` (a cross join is `join (lit true)`) |
| `cross_join_empty_right` | not carried over | Subsumed: as `inner_join_empty_right` |
| `cross_join_assoc_cardinality` | not carried over | Subsumed: `Query.eval_join` with `List.length_product` and `Nat.mul_assoc`; join associativity itself is phase 7 |
| `inner_join_to_where` | counterpart | `Query.select_join_true` (`WHERE θ` over a cross join is `JOIN ON θ`, ordered, with no condition) |
| `left_join_preserves_left` | not carried over | Outside the fragment (outer joins); phase 8 |
| `right_join_preserves_right` | not carried over | Outside the fragment (outer joins); phase 8 |
| `inner_subset_cross` | not carried over | Subsumed: `Query.eval_join` (`filterRows` is a sublist of `Row.product`), as `inner_join_cardinality_le` |
| `left_join_filter_null_is_inner` | not carried over | Outside the fragment (outer joins) and an artefact of name lookup (`find?` on column names); phase 8 |

### Subqueries

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `exists_empty_false` | not carried over | Outside the fragment (`EXISTS`); phase 8 (correlated-subquery prototype) |
| `not_exists_empty_true` | not carried over | Outside the fragment (`EXISTS`); phase 8 |
| `exists_nonempty_true` | not carried over | Outside the fragment (`EXISTS`); phase 8 |
| `not_exists_nonempty_false` | not carried over | Outside the fragment (`EXISTS`); phase 8 |
| `not_not_exists` | not carried over | Outside the fragment (`EXISTS`); phase 8 |
| `in_empty_subquery_false` | not carried over | Outside the fragment (IN subquery); phase 8. The literal-list analogue is `Expr.Equiv.inList_nil` (`IsSafe e`) |
| `not_in_empty_subquery_true` | not carried over | Outside the fragment (NOT IN subquery); phase 8 |
| `scalar_subquery_empty_null` | not carried over | Outside the fragment (scalar subquery); phase 8 |
| `exists_as_count_gt_zero` | not carried over | Outside the fragment (`EXISTS` and `COUNT`); phase 8 |
| `not_exists_as_count_eq_zero` | not carried over | Outside the fragment (`EXISTS` and `COUNT`); phase 8 |
| `in_subquery_as_exists` | not carried over | Outside the fragment (IN subquery, `EXISTS`); phase 8 |
| `not_in_subquery_as_not_exists` | not carried over | Outside the fragment (NOT IN subquery); phase 8 |
| `subquery_limit_one` | not carried over | Outside the fragment (subquery, `LIMIT`); phase 8 |
| `scalar_subquery_is_first` | not carried over | Outside the fragment (scalar subquery); phase 8 |
| `exists_monotonic` | not carried over | Outside the fragment (`EXISTS`); phase 8 |
| `subquery_where_true` | not carried over | Outside the fragment (subquery); phase 8. Its `WHERE TRUE` part is `Query.select_true` |
| `subquery_where_false` | not carried over | Outside the fragment (subquery, aggregates); phase 8 |
| `in_singleton_subquery` | not carried over | Outside the fragment (IN subquery); phase 8. The literal-list analogue is `Expr.Equiv.inList_singleton` |
| `evalExprWithDb_qcol_append_comm` | not carried over | Artefact of name lookup (qualified column order in an appended row); typed columns are positions (`Expr.eval_rename_castAdd`/`natAdd`) |
| `join_match_implies_in_subquery` | not carried over | Outside the fragment (IN subquery decorrelation); phase 8 |
| `not_in_subquery_unnest_to_antijoin` | not carried over | Outside the fragment (NOT IN subquery, anti-join); phase 8 |
| `in_subquery_implies_join_match` | not carried over | Outside the fragment (IN subquery decorrelation); phase 8 |
| `in_subquery_unnest_to_join` | not carried over | Outside the fragment (IN subquery unnesting); phase 8 |

### ORDER BY, LIMIT and OFFSET

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `order_by_preserves_count` | not carried over | Outside the fragment (`ORDER BY`); phase 8 |
| `order_by_length_invariant` | not carried over | Outside the fragment (`ORDER BY`); phase 8 |
| `limit_zero_empty` | not carried over | Outside the fragment (`LIMIT`); phase 8 |
| `limit_upper_bound` | not carried over | Outside the fragment (`LIMIT`); phase 8 |
| `limit_none_all_rows` | not carried over | Outside the fragment (`LIMIT`); phase 8 |
| `limit_monotonic` | not carried over | Outside the fragment (`LIMIT`); phase 8 |
| `limit_one_singleton` | not carried over | Outside the fragment (`LIMIT`); phase 8 |
| `offset_zero_identity` | not carried over | Outside the fragment (`OFFSET`); phase 8 |
| `offset_too_large_empty` | not carried over | Outside the fragment (`OFFSET`); phase 8 |
| `offset_reduces_count` | not carried over | Outside the fragment (`OFFSET`); phase 8 |
| `offset_monotonic` | not carried over | Outside the fragment (`OFFSET`); phase 8 |
| `limit_offset_compose` | not carried over | Outside the fragment (`LIMIT`/`OFFSET`); phase 8 |
| `offset_limit_zero_empty` | not carried over | Outside the fragment (`LIMIT`/`OFFSET`); phase 8 |
| `pagination_upper_bound` | not carried over | Outside the fragment (`LIMIT`/`OFFSET`); phase 8 |
| `pagination_identity` | not carried over | Outside the fragment (`LIMIT`/`OFFSET`); phase 8 |
| `consecutive_pages` | not carried over | Outside the fragment (`LIMIT`/`OFFSET`); phase 8 |
| `order_limit_deterministic` | not carried over | Outside the fragment (`ORDER BY`/`LIMIT`); phase 8 |

### WHERE congruence

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `select_where_congr` | counterpart | `Query.Equiv.select_expr`; it gains `q.typeOf = some Γ` (decidable), and `p ≃ q` holds in `Γ` |
| `selectWithContext_where_congr` | not carried over | Outside the fragment (correlated subqueries, outer row); phase 8 |
| `exists_where_congr` | not carried over | Outside the fragment (`EXISTS`); phase 8 |
| `inSubquery_where_congr` | not carried over | Outside the fragment (IN subquery); phase 8 |

### Private helpers (25)

All 25 private helpers are `not carried over`. Each one serves a public theorem that was not
carried over. They fall into these groups:

- **List lemmas:** `List.filterMap_none`, `List.flatMap_const_nil`, `List.filterMap_some_comp`,
  `List.length_flatMap_const`, `List.length_flatMap_le`, `List.length_flatMap_ge_length`,
  `exists_mem_flatMap_of_length_ge_one`, `flatMap_length_eq_of_forall`,
  `List.any_eq_not_isEmpty_filter`, `List.isEmpty_map`, `List.any_map`,
  `list_filter_map_eq_flatMap`, `list_filter_map_of_flatMap`, `list_flatMap_congr_mem` and
  `take_add_eq`. These are proof plumbing for the join, subquery and pagination proofs. The typed
  core uses Mathlib's `List` library and `SqlCore/Foundations/ListProduct.lean` instead.
- **Outer-join body lemmas:** `left_join_body_length_ge_one`, `right_join_body_length_ge_one`,
  `filter_pred_false_on_null_mapped`, `isNullValue_lookupCI_nullPad` and `filter_null_pad_empty`.
  Outer joins and NULL padding are outside the fragment (phase 8).
- **Name-lookup lemmas:** `lookupCI_append_none_left` and `lookupCI_append_none_right`. These are
  an artefact of case-insensitive name lookup, which positional columns do not need.
- **`SelectStmt` field-shape lemmas:** `evalSelect_SN`, `evalSelect_S0` and `evalSelect_0N`.
  They are needed only for `LIMIT`/`OFFSET` (phase 8).

## `SqlEquiv/Equiv/SetBagLemmas.lean` (11 theorems, 0 private)

These are list lemmas about `List.eraseDups`, which keeps the first occurrence of each element.
The typed core's `DISTINCT` uses Mathlib's `List.dedup`, which keeps the last occurrence, so these
lemmas are replaced by Mathlib lemmas rather than carried over.

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `perm_ext_iff_of_nodup` | not carried over | Subsumed by Mathlib `List.perm_ext_iff_of_nodup` |
| `mem_eraseDups` | not carried over | Subsumed by Mathlib `List.mem_dedup` |
| `nodup_eraseDups` | not carried over | Subsumed by Mathlib `List.nodup_dedup` |
| `Perm_eraseDups` | not carried over | Subsumed by Mathlib `List.Perm.dedup`; at query level, `EquivLevel.Rel.perm_dedup` |
| `filter_eraseDups` | not carried over | Subsumed by `List.dedup_filter` (`SqlCore/Foundations/ListDedup.lean`) |
| `eraseDups_eq_self_of_nodup` | not carried over | Subsumed by Mathlib `List.dedup_eq_self` |
| `eraseDups_eraseDups` | not carried over | Subsumed by Mathlib `List.dedup_idem`; at query level, `Query.distinct_distinct` |
| `contains_filter` | not carried over | Artefact of the untyped representation (`BEq`/`contains`, used by `INTERSECT`); the typed core uses `DecidableEq` and `List.mem_filter` |
| `contains_eraseDups` | not carried over | Artefact (`contains` on `BEq`); `List.mem_dedup` covers it |
| `mem_filter_contains` | not carried over | Artefact (`contains`-based `INTERSECT`/`EXCEPT`, which are phase 8); `List.mem_filter` covers it |
| `mem_eraseDups_append` | not carried over | Subsumed by `List.mem_dedup` with `List.mem_append` |

## Summary

| File | Theorems | counterpart | counterpart? | decidable check | not carried over: phase 7 | not carried over: phase 8 | not carried over: other reason |
|---|---|---|---|---|---|---|---|
| `Defs.lean` | 21 | 17 | 0 | 0 | 0 | 3 | 1 |
| `ExprAxioms.lean` | 60 | 20 | 0 | 5 | 23 | 8 | 4 |
| `StatementAxioms.lean` (public) | 75 | 3 | 1 | 0 | 1 | 58 | 12 |
| `StatementAxioms.lean` (private) | 25 | 0 | 0 | 0 | 0 | 8 | 17 |
| `SetBagLemmas.lean` | 11 | 0 | 0 | 0 | 0 | 0 | 11 |
| **Total** | **192** | **40** | **1** | **5** | **24** | **77** | **45** |

In the summary, the "other reason" column covers three kinds of row: subsumed by a general lemma,
artefact of the untyped representation, and false under three-valued logic. The four `ExprAxioms`
complement laws (`and_not_self` and its siblings) are the only rows that are false under
three-valued logic. Of the 25 private helpers, the 8 outer-join and pagination helpers count as
phase 8, and the 17 list and name-lookup helpers count as other.
