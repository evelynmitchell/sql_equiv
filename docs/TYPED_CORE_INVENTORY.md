# Typed core inventory: `SqlEquiv` laws → `SqlCore`

This is the inventory that phase 5 (#294) of the [typed core plan](TYPED_CORE_PLAN.md) asks for. It
lists every `theorem` declared in six `SqlEquiv` equivalence files (`Defs`, `ExprAxioms`,
`StatementAxioms`, `SetBagLemmas`, `ValueLemmas` and `Comparison`), and it says what became of
each one in the typed core `SqlCore`. The typed laws are the ones in `SqlCore/Scalar.lean`,
`Truth.lean`, `Preconditions.lean`, `Equiv.lean`, `QueryEquiv.lean` and `QueryLaws.lean`, re-derived
from cslib-frontier at `e78796a1` (`CslibFrontier/Languages/SQL/{Equiv,QueryEquiv,QueryLaws}.lean`).
None of the six files declares an `axiom` or a `lemma`. `Decidable.lean` is covered by a
paragraph, plus one row for the one law it states.

The typed core covers the following fragment:

- **Scalar expressions:** int, text, bool and exact decimal values, `NULL`, unary and binary
  operators, `IN` over a list of literals, and `CASE`.
- **Queries:** table, `WHERE` (`select`), `SELECT` list (`project`), inner join `ON θ`,
  `UNION ALL` and `DISTINCT`; since phase 8, `GROUP BY` with aggregates (#313), `ORDER BY`,
  `LIMIT` and `OFFSET` (#318), `INTERSECT`/`EXCEPT` (#322), and uncorrelated subqueries (#329).

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

**Other files:** `SqlEquiv/Equiv/StatementChecker.lean` declares no theorems. Its certified
statement checkers are phase 7 infrastructure.

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
| `and_assoc` | counterpart | `Expr.Equiv.and_assoc`; the `isBoolValued` hypotheses are dropped (no hypothesis, because both sides evaluate every operand) |
| `or_assoc` | counterpart | `Expr.Equiv.or_assoc`; the `isBoolValued` hypotheses are dropped |
| `not_and` | counterpart | `Expr.Equiv.not_and`; the `isBoolValued` hypotheses are dropped (Kleene De Morgan, `not_evalBinOp_and`) |
| `not_or` | counterpart | `Expr.Equiv.not_or`; the `isBoolValued` hypotheses are dropped (`not_evalBinOp_or`) |
| `and_or_distrib_left` | counterpart | `Expr.Equiv.and_or_distrib_left`; the `isBoolValued` hypotheses are dropped |
| `and_or_distrib_right` | counterpart | `Expr.Equiv.and_or_distrib_left` composed with `Expr.Equiv.binary_comm` (`evalBinOp_and_comm`) and congruence |
| `or_and_distrib_left` | counterpart | `Expr.Equiv.or_and_distrib_left`; the `isBoolValued` hypotheses are dropped |
| `or_and_distrib_right` | counterpart | `Expr.Equiv.or_and_distrib_left` composed with `Expr.Equiv.binary_comm` (`evalBinOp_or_comm`) and congruence |
| `and_absorb_or` | decidable check | `Expr.Equiv.and_or_absorb`: `isBoolValued a` becomes `a.typeOf Γ = some .bool`, and `isBoolValued b` becomes `b.IsSafePredicate Γ` |
| `or_absorb_and` | decidable check | `Expr.Equiv.or_and_absorb`: `typeOf Γ = some .bool` for `a`, `IsSafePredicate Γ` for `b` |
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
| `and_self` | decidable check | `Expr.Equiv.and_self`: `isBoolValued` becomes `a.typeOf Γ = some .bool` |
| `or_self` | decidable check | `Expr.Equiv.or_self`: `isBoolValued` becomes `a.typeOf Γ = some .bool` |
| `and_not_self` | not carried over | False under three-valued logic (`NULL AND NOT NULL` is `NULL`; `Truth.unknown_inf_not_unknown`). It needs `IsTwoValued`, which is semantic, not decidable |
| `or_not_self` | not carried over | False under three-valued logic (`Truth.unknown_sup_not_unknown`). It needs `IsTwoValued`, which is not decidable |
| `not_self_and` | not carried over | False under three-valued logic, as `and_not_self` |
| `not_self_or` | not carried over | False under three-valued logic, as `or_not_self` |
| `or_not_not` | counterpart | `(Expr.Equiv.not_and).symm` (no hypothesis) |
| `and_not_not` | counterpart | `(Expr.Equiv.not_or).symm` (no hypothesis) |
| `or_and_factor_left` | counterpart | `(Expr.Equiv.and_or_distrib_left).symm`; the hypotheses are dropped |
| `and_or_factor_left` | counterpart | `(Expr.Equiv.or_and_distrib_left).symm`; the hypotheses are dropped |
| `binOp_congr` | counterpart | `Expr.Equiv.binary` |
| `unaryOp_congr` | counterpart | `Expr.Equiv.unary` |
| `binOp_congr_left` | counterpart | `Expr.Equiv.binary` with `Expr.Equiv.refl` |
| `binOp_congr_right` | counterpart | `Expr.Equiv.binary` with `Expr.Equiv.refl` |

## `SqlEquiv/Equiv/StatementAxioms.lean` (100 theorems: 75 public, 25 private)

### Set operations

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `union_all_length` | not carried over | Subsumed: `Query.eval_unionAll` with `List.length_append` |
| `except_self_empty` | counterpart | `Query.eval_difference_self`: `q EXCEPT q` evaluates to no rows, or fails as `q` does |
| `intersect_empty_right` | counterpart | `Query.eval_intersect_of_eval_eq_nil` (any empty right side, not only `WHERE FALSE`) |
| `intersect_idempotent` | counterpart | `Query.intersect_self`: `q INTERSECT q` is `DISTINCT q` (ordered); `SqlEquiv`'s set-level form follows, since `DISTINCT q` is set-equivalent to `q` |
| `union_all_comm` | counterpart | `Query.unionAll_comm` (bag) |
| `union_comm` | not carried over | Outside the fragment (dedup `UNION`); phase 8. It is derivable as `DISTINCT` of `unionAll_comm` via `Query.Equiv.distinct` |
| `union_assoc` | not carried over | Outside the fragment (dedup `UNION`); phase 8 |
| `intersect_assoc` | counterpart | `Query.intersect_assoc` (ordered: both sides evaluate the inputs in the same order) |
| `intersect_comm` | counterpart | `Query.intersect_comm` (bag; `SqlEquiv` states it at the set level) |
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
| `in_empty_subquery_false` | not carried over | `IN` subqueries are in the fragment since phase 8f (`Query.attach`, `SubKind.inSub`); the law is not stated yet (examples in `SubqueryExamples`). The literal-list analogue is `Expr.Equiv.inList_nil` (`IsSafe e`) |
| `not_in_empty_subquery_true` | not carried over | `NOT IN` subqueries are in the fragment since phase 8f; the law is not stated yet |
| `scalar_subquery_empty_null` | not carried over | Scalar subqueries are in the fragment since phase 8f; an empty one gives `NULL` (`scalarOf`, `SubqueryExamples`), but the law is not stated yet |
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
| `order_by_preserves_count` | counterpart | `Query.perm_of_eval_orderBy`: the sorted rows are a permutation of the input, hence as many |
| `order_by_length_invariant` | counterpart | `Query.perm_of_eval_orderBy`: every sort permutes the same input rows |
| `limit_zero_empty` | counterpart | `Query.eval_limit_zero` (any offset) |
| `limit_upper_bound` | counterpart | `Query.length_le_of_eval_limit` |
| `limit_none_all_rows` | counterpart | `Query.eval_limit` with no count (the rows after the offset); `Query.limit_none_zero` with no offset |
| `limit_monotonic` | counterpart? | `Query.limit_limit` with `m ≤ n` and no offsets: `LIMIT m` over `LIMIT n` is `LIMIT m`, so the shorter result is a prefix of the longer |
| `limit_one_singleton` | counterpart | `Query.length_le_of_eval_limit` with `c = 1` |
| `offset_zero_identity` | counterpart | `Query.limit_none_zero` (ordered) |
| `offset_too_large_empty` | counterpart | `Query.length_of_eval_offset`: the length is `rs'.length - o = 0` |
| `offset_reduces_count` | counterpart | `Query.length_of_eval_offset` |
| `offset_monotonic` | counterpart | `Query.length_of_eval_offset` (`rs'.length - o` is antitone in `o`) |
| `limit_offset_compose` | counterpart | `Query.eval_limit` (definitional: drop the offset, then take the count); `Query.limit_offset_offset` for nested offsets |
| `offset_limit_zero_empty` | counterpart | `Query.eval_limit_zero` |
| `pagination_upper_bound` | counterpart | `Query.length_le_of_eval_limit` |
| `pagination_identity` | counterpart? | `Query.eval_limit` with `List.take_length`; no separate theorem, since the count depends on the instance |
| `consecutive_pages` | counterpart | `Query.eval_limit_pages` |
| `order_limit_deterministic` | counterpart | `Query.eval_limit` over `Query.orderBy` (evaluation is a function; the sort is stable, registry T14) |

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

## `SqlEquiv/Equiv/ValueLemmas.lean` (51 theorems: 50 public, 1 private)

These are value-level operator laws over `Option Value`, where an error is `none` and NULL is `.null t`. Their typed counterparts are datum-level laws in `SqlCore/Scalar.lean`, where an error is an `Except` and NULL is `none`, and lattice laws on `Truth`. `Truth` is a `LinearOrder`, so it is a distributive lattice, and Mathlib's `inf_assoc`, `inf_idem`, `inf_sup_left` and similar laws apply to it.

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `evalBinOp_and_comm` | counterpart | `evalBinOp_and_comm` (every datum) |
| `evalBinOp_or_comm` | counterpart | `evalBinOp_or_comm` |
| `evalBinOp_add_comm` | counterpart | `evalBinOp_add_comm` |
| `evalBinOp_mul_comm` | counterpart | `evalBinOp_mul_comm` |
| `Int.beq_comm` | not carried over | Artefact: `BEq` helper for untyped `Value.eq`; typed comparison is `Value.cmp` (`Value.cmp_swap`) |
| `String.beq_comm` | not carried over | Artefact: `BEq` helper, as `Int.beq_comm` |
| `Bool.beq_comm` | not carried over | Artefact: `BEq` helper, as `Int.beq_comm` |
| `evalBinOp_eq_comm` | counterpart | `CmpOp.eval_eq_comm` (or `evalBinOp_cmp_swap .eq`) |
| `evalBinOp_and_false_right` | counterpart | `evalBinOp_and_false`; it gains `a.HasType .bool`, because strict errors mean there is no short-circuit |
| `evalBinOp_and_false_left` | counterpart | `evalBinOp_and_comm` with `evalBinOp_and_false` (`HasType .bool`) |
| `evalBinOp_or_true_right` | counterpart | `evalBinOp_or_true`; it gains `HasType .bool` (no short-circuit) |
| `evalBinOp_or_true_left` | counterpart | `evalBinOp_or_comm` with `evalBinOp_or_true` |
| `evalBinOp_and_true_right` | counterpart | `evalBinOp_and_true` (bool datum, NULL included) |
| `evalBinOp_or_false_right` | counterpart | `evalBinOp_or_false` |
| `evalBinOp_and_idem` | counterpart | `inf_idem` on `Truth` |
| `evalBinOp_or_idem` | counterpart | `sup_idem` on `Truth` |
| `evalUnaryOp_not_bool` | counterpart | `Truth.ofBool_not` (`evalUnOp .not` is `Truth.not` through `toTruth`) |
| `evalBinOp_and_not_self` | not carried over | False under three-valued logic for `unknown` (`Truth.unknown_inf_not_unknown`); the `Bool` case is `Bool.and_not_self` via `Truth.ofBool_and` |
| `evalBinOp_or_not_self` | not carried over | False under three-valued logic for `unknown` (`Truth.unknown_sup_not_unknown`) |
| `evalBinOp_and_true_left` | counterpart | `evalBinOp_and_comm` with `evalBinOp_and_true` |
| `evalBinOp_or_false_left` | counterpart | `evalBinOp_or_comm` with `evalBinOp_or_false` |
| `evalBinOp_and_assoc` | counterpart | `inf_assoc` on `Truth` |
| `evalBinOp_or_assoc` | counterpart | `sup_assoc` on `Truth` |
| `evalBinOp_and_absorb_or` | counterpart | `inf_sup_self` on `Truth` |
| `evalBinOp_or_absorb_and` | counterpart | `sup_inf_self` on `Truth` |
| `evalUnaryOp_not_and` | counterpart | `not_evalBinOp_and`, or `Truth.not_inf` |
| `evalUnaryOp_not_or` | counterpart | `not_evalBinOp_or`, or `Truth.not_sup` |
| `evalUnaryOp_not_or_bnn` | counterpart | `not_evalBinOp_or`; the bool-or-NULL-or-error hypothesis is dropped (every datum) |
| `evalUnaryOp_not_and_bnn` | counterpart | `not_evalBinOp_and`; the hypothesis is dropped |
| `evalBinOp_eq_isBoolOrNullOrNone` | not carried over | Artefact: a typed comparison returns `Truth` by its type (`CmpOp.eval : … → Except EvalError Truth`) |
| `evalBinOp_ge_isBoolOrNullOrNone` | not carried over | Artefact, as `evalBinOp_eq_isBoolOrNullOrNone` |
| `evalBinOp_le_isBoolOrNullOrNone` | not carried over | Artefact, as `evalBinOp_eq_isBoolOrNullOrNone` |
| `evalBinOp_or_preserves_bnn` | not carried over | Artefact: `OR` returns `Truth.toDatum`, which is bool-typed (`Truth.toDatum_hasType`) |
| `evalBinOp_and_or_distrib` | counterpart | `inf_sup_left` on `Truth` |
| `evalBinOp_and_or_distrib_right` | counterpart | `inf_sup_right` on `Truth` |
| `evalBinOp_or_and_distrib` | counterpart | `sup_inf_left` on `Truth` |
| `evalBinOp_or_and_distrib_right` | counterpart | `sup_inf_right` on `Truth` |
| `Value.eq_comm` | counterpart | `CmpOp.eval_eq_comm` / `Value.cmp_swap` |
| `eq_true_of_evalBinOp_eq` | counterpart | `CmpOp.eval_eq_ok_true_iff` (operands of a common type) |
| `evalBinOp_eq_of_eq_true` | counterpart | `CmpOp.eval_eq_ok_true_iff`, right to left |
| `Value.eq_some_true_not_null_left` | not carried over | Artefact: NULL is not a `Value` in the typed core (it is `none`, and `CmpOp.eval_none_left` gives `unknown`) |
| `Value.eq_some_true_not_null_right` | not carried over | Artefact, as `Value.eq_some_true_not_null_left` (`CmpOp.eval_none_right`) |
| `Option.beq_some_true_iff` | not carried over | Artefact: `BEq` on `Option Bool`; the typed core uses `Truth.isTrue_iff` |
| `Value.toTrilean_ofTrilean` | counterpart | `Datum.toTruth_toDatum` |
| `Trilean.toOptionValue_isBoolOrNull` | counterpart | `Truth.toDatum_hasType` |
| `evalBinOp_and_as_trilean` | not carried over | Subsumed by definition: typed `evalBinOp .and` is `⊓` through `Datum.toTruth` |
| `evalBinOp_or_as_trilean` | not carried over | Subsumed by definition (`⊔` through `toTruth`) |
| `evalUnaryOp_not_as_trilean` | not carried over | Subsumed by definition (`Truth.not` through `toTruth`) |
| `evalUnaryOp_not_not_via_trilean` | counterpart | `evalUnOp_not_not` (`HasType .bool`); the typed-NULL caveat disappears |
| `mismatched_types_error` | not carried over | Replaced by static typing: well-typed expressions never raise `typeMismatch` (`Expr.eval_ne_typeMismatch`) |

The private helper `isBoolOrNull_some_elim` is `not carried over`. It is an artefact of the
untyped bool-or-NULL predicate, and the typed core uses `Datum.exists_toTruth_eq_ok_iff`.

## `SqlEquiv/Equiv/Comparison.lean` (202 theorems: 149 public, 53 private)

A grep for `theorem` finds 206 lines in this file. Four of them are doc-comment lines, which leaves 202 declarations. None of them is an `axiom`.

### Query rewrites (pushdown, joins, filters)

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `filter_join_left` | decidable check | `Query.select_join_left`: the semantic "filter ignores the right row" becomes `p : Expr n` renamed by `Fin.castAdd`, plus `IsSafePredicate` of `p` and `θ` |
| `filter_join_right` | decidable check | `Query.select_join_right`: as `filter_join_left`, with `Fin.natAdd` |
| `filter_pushdown_table` | not carried over | Artefact: the typed core has no derived-table/alias wrapper, so both sides are the same `select p (table t)` |
| `join_assoc` | not carried over | Phase 7 (join reordering): there is no typed `join_assoc` |
| `cross_join_assoc` | not carried over | Phase 7: as `join_assoc` (cross join is `join (lit true)`) |
| `join_comm` | counterpart | `Query.join_comm` (bag); the semantic condition hypothesis becomes explicit renaming `θ.rename finAddFlip` |
| `cross_join_comm` | counterpart | `Query.join_comm` with `θ = lit true` (bag, which is stronger than the membership up to column permutation stated here) |
| `project_join` | deleted (#307) | Vacuous: both sides are syntactically identical; there is no typed law to match |
| `project_star_identity` | deleted (#307) | Vacuous: both sides are identical; the intended law is `Query.project_col` |
| `filter_and` | counterpart | `Query.select_select`; it gains `IsSafePredicate` of the outer predicate (strict errors) |
| `filter_commute` | counterpart | `Query.select_comm`; it gains `IsSafePredicate` of both predicates |
| `filter_idempotent` | counterpart | `Query.select_select` composed with `Query.Equiv.select_expr` and `Expr.Equiv.and_self` (`IsSafePredicate p`) |
| `filter_true_elim'` | counterpart | `Query.select_true` |
| `filter_false_empty'` | not carried over | Phase 7: as `where_false_empty` |
| `filter_project_commute` | deleted (#307) | Vacuous: both sides are identical; the intended law is `Query.select_project` |
| `push_filter_project_through_join` | deleted (#307) | Vacuous: both sides are identical; the intended laws are `Query.select_join_left` and `Query.select_project` |

### NULL laws

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `is_null_on_null` | not carried over | Subsumed by definition (`evalUnOp .isNull none` reduces by `rfl`); the typed-NULL argument `t` is an artefact |
| `is_null_on_none` | not carried over | Artefact: an error (`none`) has no typed analogue; a typed error propagates |
| `is_null_on_int` | not carried over | Subsumed by definition (`evalUnOp .isNull (some v)` reduces by `rfl`) |
| `is_null_on_string` | not carried over | Subsumed by definition, as `is_null_on_int` |
| `is_null_on_bool` | not carried over | Subsumed by definition, as `is_null_on_int` |
| `is_not_null_on_null` | not carried over | Subsumed by definition (`rfl`), with the typed-NULL argument as an artefact |
| `is_not_null_on_none` | not carried over | Artefact: an error has no typed analogue |
| `is_not_null_on_int` | not carried over | Subsumed by definition (`rfl`) |
| `is_not_null_on_string` | not carried over | Subsumed by definition (`rfl`) |
| `is_not_null_on_bool` | not carried over | Subsumed by definition (`rfl`) |
| `is_null_is_not_null_complement` | counterpart | `not_evalUnOp_isNull` |
| `null_add_left` | counterpart | `evalBinOp_arith_null_left .add`; it gains `IsNumeric` of the other operand (text is a type error) |
| `null_add_right` | counterpart | `evalBinOp_arith_null_right .add` (`IsNumeric`) |
| `null_sub_left` | counterpart | `evalBinOp_arith_null_left .sub` (`IsNumeric`) |
| `null_sub_right` | counterpart | `evalBinOp_arith_null_right .sub` (`IsNumeric`) |
| `null_mul_left` | counterpart | `evalBinOp_arith_null_left .mul` (`IsNumeric`) |
| `null_mul_right` | counterpart | `evalBinOp_arith_null_right .mul` (`IsNumeric`) |
| `null_div_left` | counterpart | `evalBinOp_arith_null_left .div` (`IsNumeric`) |
| `null_div_right` | counterpart | `evalBinOp_arith_null_right .div` (`IsNumeric`; `1 / NULL` is `NULL`) |
| `null_eq_left` | counterpart | `CmpOp.eval_none_left` (`unknown`, every datum) |
| `null_eq_right` | counterpart | `CmpOp.eval_none_right` |
| `null_ne_left` | counterpart | `CmpOp.eval_none_left` |
| `null_ne_right` | counterpart | `CmpOp.eval_none_right` |
| `null_lt_left` | counterpart | `CmpOp.eval_none_left` |
| `null_lt_right` | counterpart | `CmpOp.eval_none_right` |
| `false_and_null` | counterpart | `Truth.false_inf` |
| `null_and_false` | counterpart | `Truth.inf_false` (also `evalBinOp_and_false`) |
| `true_and_null` | counterpart | `Truth.true_inf` |
| `null_and_true` | counterpart | `Truth.inf_true` |
| `true_or_null` | counterpart | `Truth.true_sup` |
| `null_or_true` | counterpart | `Truth.sup_true` |
| `false_or_null` | counterpart | `Truth.false_sup` |
| `null_or_false` | counterpart | `Truth.sup_false` |
| `null_and_null` | counterpart | `inf_idem` at `unknown` |
| `null_or_null` | counterpart | `sup_idem` at `unknown` |

### Three-valued logic (`Trilean`)

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `trilean_not_not` | counterpart | `Truth.not_not` |
| `trilean_and_comm` | counterpart | `inf_comm` on `Truth` |
| `trilean_or_comm` | counterpart | `sup_comm` on `Truth` |
| `trilean_and_true` | counterpart | `Truth.inf_true` |
| `trilean_or_false` | counterpart | `Truth.sup_false` |
| `trilean_and_false` | counterpart | `Truth.inf_false` |
| `trilean_or_true` | counterpart | `Truth.sup_true` |
| `trilean_de_morgan_and` | counterpart | `Truth.not_inf` |
| `trilean_de_morgan_or` | counterpart | `Truth.not_sup` |
| `trilean_and_assoc` | counterpart | `inf_assoc` on `Truth` |
| `trilean_or_assoc` | counterpart | `sup_assoc` on `Truth` |
| `trilean_and_self` | counterpart | `inf_idem` on `Truth` |
| `trilean_or_self` | counterpart | `sup_idem` on `Truth` |
| `trilean_ofBool_toBool` | counterpart | `Truth.isTrue_ofBool` (`Truth` has `isTrue` rather than `toBool`) |
| `evalBinOp_and_comm_via_trilean` | counterpart | `evalBinOp_and_comm`, without the bool-or-NULL hypothesis |
| `evalBinOp_or_comm_via_trilean` | counterpart | `evalBinOp_or_comm`, without the hypothesis |

### COALESCE, NULLIF and value nullness

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `isNullValue_none` | not carried over | Artefact: the `isNullValue` helper on `Option Value`; a typed NULL is `none` (`Option.isNone`) |
| `isNullValue_null` | not carried over | Artefact, as `isNullValue_none` |
| `isNullValue_int` | not carried over | Artefact, as `isNullValue_none` |
| `isNullValue_string` | not carried over | Artefact, as `isNullValue_none` |
| `isNullValue_bool` | not carried over | Artefact, as `isNullValue_none` |
| `coalesce_null_left_nonnull` | not carried over | Outside the fragment (`COALESCE`); phase 8 |
| `coalesce_int_left` | not carried over | Outside the fragment (`COALESCE`); phase 8 |
| `coalesce_string_left` | not carried over | Outside the fragment (`COALESCE`); phase 8 |
| `coalesce_bool_left` | not carried over | Outside the fragment (`COALESCE`); phase 8 |
| `coalesce_single_int` | not carried over | Outside the fragment (`COALESCE`); phase 8 |
| `coalesce_single_string` | not carried over | Outside the fragment (`COALESCE`); phase 8 |
| `coalesce_single_bool` | not carried over | Outside the fragment (`COALESCE`); phase 8 |
| `coalesce_single_null` | not carried over | Outside the fragment (`COALESCE`); phase 8 |
| `coalesce_empty` | not carried over | Outside the fragment (`COALESCE`); phase 8 |
| `nullif_same_int` | not carried over | Outside the fragment (`NULLIF`); phase 8 |
| `nullif_diff_int` | not carried over | Outside the fragment (`NULLIF`); phase 8 |
| `value_null_or_not_null` | not carried over | Subsumed: a `Datum` is an `Option`, so it is `none` or `some` (`Option.eq_none_or_eq_some`) |
| `value_is_null_complement` | counterpart | `not_evalUnOp_isNull` (`IS NULL` is the negation of `IS NOT NULL`) |
| `typed_null_same_nullness` | not carried over | Artefact of typed-NULL bookkeeping (`.null t`); a typed NULL is untyped `none` |

### Aggregates

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `count_star_nonneg` | not carried over | Outside the fragment (aggregates: `COUNT(*)`); phase 8 |
| `count_star_empty` | not carried over | Outside the fragment (aggregates); phase 8 |
| `count_star_singleton` | not carried over | Outside the fragment (aggregates); phase 8 |
| `count_after_filter_le` | not carried over | Subsumed by `List.length_filter_le` |
| `sum_empty` | not carried over | Outside the fragment (aggregates: `SUM`); phase 8 |
| `sum_singleton` | not carried over | Outside the fragment (aggregates); phase 8 |
| `sum_add_zero` | not carried over | Outside the fragment (aggregates); phase 8 |
| `min_singleton` | not carried over | Outside the fragment (aggregates: `MIN`); phase 8 |
| `max_singleton` | not carried over | Outside the fragment (aggregates: `MAX`); phase 8 |
| `min_le_elem` | not carried over | Outside the fragment (aggregates); phase 8 |
| `max_ge_elem` | not carried over | Outside the fragment (aggregates); phase 8 |
| `distinct_count_le` | not carried over | Outside the fragment (`COUNT(DISTINCT …)`); phase 8 |
| `distinct_idempotent` | not carried over | Subsumed by Mathlib `List.dedup_idem` (at query level, `Query.distinct_distinct`) |
| `count_distinct_le_count` | not carried over | Outside the fragment (`COUNT(DISTINCT …)`); phase 8 |

### CASE, arithmetic, IN and BETWEEN

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `case_when_true` | counterpart | `Expr.Equiv.caseWhen_true` |
| `case_when_false` | counterpart | `Expr.Equiv.caseWhen_false` |
| `case_when_false_no_else` | counterpart | `Expr.Equiv.caseWhen_false` with `b = null τ` (typed `CASE` always has an `ELSE`; a missing one is `NULL`) |
| `case_empty_else` | not carried over | Artefact of the n-ary `CASE` AST: typed `caseWhen` has exactly one branch, and the phase 6 bridge lowers lists of branches |
| `case_empty_no_else` | not carried over | Artefact, as `case_empty_else` |
| `filter_and_eq_filter_filter` | not carried over | Subsumed by `List.filter_filter` |
| `filter_comm` | not carried over | Subsumed by `List.filter_filter` with `Bool.and_comm` |
| `predicate_pushdown` | counterpart | `Query.select_select`; it gains `IsSafePredicate q` (strict errors) |
| `expr_add_zero` | decidable check | `Expr.Equiv.add_zero`: `isIntValued` becomes `typeOf Γ = some .int` (NULL now allowed) |
| `expr_zero_add` | decidable check | `Expr.Equiv.zero_add` (`typeOf Γ = some .int`) |
| `expr_mul_one` | decidable check | `Expr.Equiv.mul_one` (`typeOf Γ = some .int`) |
| `expr_one_mul` | decidable check | `Expr.Equiv.one_mul` (`typeOf Γ = some .int`) |
| `expr_mul_zero` | not carried over | False for a NULL integer (`NULL * 0` is `NULL`); `isIntValued` excludes NULL, but nullability is not typed, so there is no decidable check |
| `expr_zero_mul` | not carried over | False for a NULL integer, as `expr_mul_zero` |
| `expr_sub_zero` | decidable check | `Expr.Equiv.sub_zero` (`typeOf Γ = some .int`) |
| `in_empty_false` | counterpart | `Expr.Equiv.inList_nil`; it gains `IsSafe e` (strict errors) |
| `not_in_empty_true` | counterpart | `Expr.Equiv.unary .not` applied to `Expr.Equiv.inList_nil` (`IsSafe e`); `NOT IN` is `NOT (… IN …)` |
| `in_singleton` | counterpart | `Expr.Equiv.inList_singleton` (list elements are literal datums, not expressions) |
| `not_in_singleton` | counterpart | `Expr.Equiv.inList_singleton` under `unary .not`, then `Expr.Equiv.not_cmp .eq` |
| `in_pair` | counterpart | `Datum.inList_cons` twice with `Datum.inList_nil` and `Truth.false_sup` (datum level, literal elements) |
| `not_in_pair` | counterpart | As `in_pair`, then `Truth.not_sup` and `CmpOp.eval_negate` |
| `in_list_or_expansion` | counterpart | Definition of `Datum.inList` (Kleene `OR` of `=` from `FALSE`) and `Datum.inList_cons` (datum level, literal elements) |
| `not_in_list_and_expansion` | counterpart | As `in_list_or_expansion`, then `Truth.not_sup` and `CmpOp.eval_negate` |
| `between_expansion` | not carried over | Outside the fragment (`BETWEEN`); phase 8 |
| `between_reflexive` | not carried over | Outside the fragment (`BETWEEN`); phase 8 |

### LIKE and string functions

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `like_match_all` | counterpart | `likeText_pct`: `s LIKE '%'` holds for every text; on datums `evalBinOp (.like ci)` unfolds to it, and `NULL` gives `NULL`. Typing replaces `isStringOrNull` |
| `like_empty_pattern` | counterpart | `likeText_empty_iff`: `s LIKE ''` holds exactly for `''` |
| `like_self` | counterpart | `likeText_self`: every text matches itself (`%` and `_` match themselves), in either case mode |
| `concat_empty_left` | not carried over | Outside the fragment (string functions: `CONCAT`); phase 8. `isStringOrUntypedNullValued` would become `IsText` |
| `concat_empty_right` | not carried over | Outside the fragment (`CONCAT`); phase 8 |
| `length_concat` | not carried over | Outside the fragment (`LENGTH`, `CONCAT`); phase 8 |
| `upper_idempotent` | not carried over | Outside the fragment (`UPPER`); phase 8 |
| `lower_idempotent` | not carried over | Outside the fragment (`LOWER`); phase 8 |
| `upper_lower_upper` | not carried over | Outside the fragment (`UPPER`/`LOWER`); phase 8 |
| `lower_upper_lower` | not carried over | Outside the fragment (`UPPER`/`LOWER`); phase 8 |
| `length_empty` | not carried over | Outside the fragment (`LENGTH`); phase 8 |

### Comparisons

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `eq_reflexive` | not carried over | Phase 7: datum level is `Value.cmp_self`. There is no `Expr.Equiv` statement, and `evaluable` would become `IsSafe` |
| `ne_irreflexive` | not carried over | Phase 7: as `eq_reflexive` |
| `not_eq_is_ne` | counterpart | `Expr.Equiv.not_cmp .eq` (no hypothesis) |
| `not_ne_is_eq` | counterpart | `Expr.Equiv.not_cmp .ne` |
| `not_lt_is_ge` | counterpart | `Expr.Equiv.not_cmp .lt` |
| `not_le_is_gt` | counterpart | `Expr.Equiv.not_cmp .le` |
| `not_gt_is_le` | counterpart | `Expr.Equiv.not_cmp .gt` |
| `not_ge_is_lt` | counterpart | `Expr.Equiv.not_cmp .ge` |
| `not_between_expansion` | not carried over | Outside the fragment (`BETWEEN`); phase 8 |
| `lt_flip` | counterpart | `evalBinOp_cmp_swap .lt` (operator level; the `Expr` lift is `Expr.Equiv.of_eval_eq` up to `toOption`) |
| `le_flip` | counterpart | `evalBinOp_cmp_swap .le` |
| `gt_flip` | counterpart | `evalBinOp_cmp_swap .gt` |
| `ge_flip` | counterpart | `evalBinOp_cmp_swap .ge` |

### Private helpers (53)

All 53 private helpers are `not carried over`. They fall into these groups:

- **Phase 8, `COALESCE`/`NULLIF` (2):** `coalesce_toUpper` and `nullif_toUpper`.
- **Phase 8, aggregates (4):** `foldl_min_le_init`, `foldl_min_le_of_mem`, `init_le_foldl_max` and
  `le_foldl_max_of_mem`.
- **Subsumed, `LIKE` (7):** `simpleLike_pct`, `simpleLike_empty`, `evalBinOp_like_empty_eq_eq`,
  `isPrefixOf_append`, `dropLast_isPrefixOf`, `stringContains_go_of_prefix_at` and
  `simpleLike_self`. They were helpers of `SqlEquiv`'s `simpleLike`; the typed matcher's
  laws are `likeText_pct`, `likeText_empty_iff` and `likeText_self` (phase 8c). Since #323
  `SqlEquiv` uses a port of that matcher (`likeMatch`), and its helpers are ports of the typed
  ones (`likeMatch_pct`, `likeMatch_empty`, `likeMatch_self` and their `likePat*` lemmas).
- **Phase 8, string functions (18):**
  - `CONCAT`/`LENGTH`: `evalFunc_concat_empty_left`, `evalFunc_concat_empty_right` and
    `evalFunc_length_concat`.
  - `Char`: `char_toUpper_toNat`, `char_toLower_toNat`, `char_ext_toNat`,
    `char_toUpper_toLower_toUpper`, `char_toLower_toUpper_toLower`, `char_toUpper_idem` and
    `char_toLower_idem`.
  - `String`: `string_toUpper_idem`, `string_toLower_idem`, `string_toUpper_toLower_toUpper` and
    `string_toLower_toUpper_toLower`.
  - `evalFunc`: `evalFunc_upper_idem`, `evalFunc_lower_idem`, `evalFunc_upper_lower_upper` and
    `evalFunc_lower_upper_lower`.
- **Subsumed by `CmpOp.eval_negate` / `evalBinOp_cmp_negate` (12):** `not_map_bool_eq`,
  `evalUnaryOp_not_eq`, `not_map_bool_cancel`, `not_map_ordering_eq_lt`, `not_map_ordering_ne_gt`,
  `not_map_ordering_eq_gt`, `not_map_ordering_ne_lt`, `evalUnaryOp_not_ne`, `evalUnaryOp_not_lt`,
  `evalUnaryOp_not_le`, `evalUnaryOp_not_gt` and `evalUnaryOp_not_ge`.
- **Subsumed by `Value.cmp_swap` / `CmpOp.eval_swap` (5):** `compare_swap_gen`,
  `ordering_lt_eq_swap_gt`, `ordering_ne_gt_eq_swap_ne_lt`, `evalBinOp_lt_eq_gt_flip` and
  `evalBinOp_le_eq_ge_flip`.
- **Subsumed by `Datum.inList_cons` and the definition of `Datum.inList` (4):** `or_false_map_bool`,
  `evalBinOp_or_false_left_eq`, `eval_foldl_or_eq` and `not_foldl_or_eq_is_foldl_and_ne`.
- **Subsumed by Mathlib `List.dedup_eq_self` (1):** `nodup_implies_eraseDups_eq`.

That is 31 helpers in phase 8 and 22 subsumed.

## `SqlEquiv/Equiv/Decidable.lean` (not inventoried row by row)

`Decidable.lean` is decision-procedure infrastructure. It contains the following, and its
counterpart is phase 7 (#296):

- **Generated decidable equality:** `DecidableEq` deciders and their `_eq_true_iff` lemmas.
- **Ground and closed detection:** `isGround`/`isClosed` and the lemmas that ground or closed
  expressions do not depend on the database or row. Typed `Expr` has no database dependence;
  constant folding is `Expr.Equiv.of_eval_eq_ok`.
- **Decider soundness:** `decideExprEquiv_sound`, `decideGroundExprEquiv_sound` and
  `syntacticEquiv_implies_equiv`.
- **Table-reference helpers:** `exprReferencesOnlyFrom` and similar. Typed columns are positions,
  so these are not needed.
- **`sizeOf` and `foldl` helpers.**

One declaration in it states a law:

| SqlEquiv theorem | Category | Typed counterpart / reason |
|---|---|---|
| `normalizeExpr_equiv` | not carried over | Phase 7: the soundness of `SqlEquiv`'s normaliser (`e ≃ₑ normalizeExpr e`); its counterpart is the certificate `Expr.equiv_simplify` of the frontier's `Expr.simplify` (`Simplify.lean`, not yet ported) |

## Summary

| File | Theorems | counterpart | counterpart? | decidable check | not carried over: phase 7 | not carried over: phase 8 | not carried over: other reason |
|---|---|---|---|---|---|---|---|
| `Defs.lean` | 21 | 17 | 0 | 0 | 0 | 3 | 1 |
| `ExprAxioms.lean` | 60 | 28 | 0 | 9 | 11 | 8 | 4 |
| `StatementAxioms.lean` (public) | 75 | 23 | 3 | 0 | 1 | 36 | 12 |
| `StatementAxioms.lean` (private) | 25 | 0 | 0 | 0 | 0 | 8 | 17 |
| `SetBagLemmas.lean` | 11 | 0 | 0 | 0 | 0 | 0 | 11 |
| `ValueLemmas.lean` (public) | 50 | 34 | 0 | 0 | 0 | 0 | 16 |
| `ValueLemmas.lean` (private) | 1 | 0 | 0 | 0 | 0 | 0 | 1 |
| `Comparison.lean` (public) | 149 | 73 | 0 | 7 | 5 | 34 | 30 |
| `Comparison.lean` (private) | 53 | 0 | 0 | 0 | 0 | 24 | 29 |
| `Decidable.lean` (law rows only) | 1 | 0 | 0 | 0 | 1 | 0 | 0 |
| **Total** | **446** | **175** | **3** | **16** | **18** | **113** | **121** |

Phase 8b (#318) moved the 17 `ORDER BY`/`LIMIT`/`OFFSET` rows from phase 8 to counterparts in
`SqlCore/QueryLaws.lean`. Phase 8c (#322) moved 5 `INTERSECT`/`EXCEPT` rows and 3 `LIKE` rows to
counterparts, and the 7 private `simpleLike` helpers to "subsumed".

The "other reason" column covers three kinds of row: subsumed by a general lemma or by a
definition, artefact of the untyped representation (vacuous statements included), and false
under three-valued logic or for NULL. These rows are false under three-valued logic or for
NULL:

- the four `ExprAxioms` complement laws;
- `evalBinOp_and_not_self` and `evalBinOp_or_not_self` in `ValueLemmas`;
- `expr_mul_zero` and `expr_zero_mul` in `Comparison`.

The private helpers are counted from their grouped lists:

| File | Phase 8 | Other |
|---|---|---|
| `StatementAxioms` | 8 (outer join, pagination) | 17 (lists, name lookup) |
| `Comparison` | 24 (`COALESCE`, aggregates, string functions) | 29 (subsumed comparison, `IN` and `simpleLike` helpers) |
| `ValueLemmas` | 0 | 1 (artefact) |

The `ExprAxioms` laws for associativity, De Morgan, distributivity, idempotence and absorption
map to the expression-level laws `Expr.Equiv.and_assoc`, `or_assoc`, `not_and`, `not_or`,
`and_or_distrib_left`, `or_and_distrib_left`, `and_self`, `or_self`, `and_or_absorb` and
`or_and_absorb`. These laws are being added to `SqlCore/Equiv.lean` in this phase.
