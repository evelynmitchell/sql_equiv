# Plan for Proving Semantic Preservation Axioms

This document outlines a phased approach to replacing axioms with proven theorems in the sql_equiv codebase.

## Current State

### Target Axioms (Issue #11)

**PredicatePushdown:**
```lean
axiom pushdown_preserves_semantics (db : Database) (pred : Expr) (from_ : FromClause) :
  let result := pushPredicateDown pred from_
  filterRows db (evalFrom db result.pushedFrom) result.remaining =
  filterRows db (evalFrom db from_) (some pred)
```

**JoinReordering:**
```lean
axiom join_reorder_preserves_forward (db : Database) (from_ : FromClause) :
  canReorderJoins from_ →
  ∀ row ∈ evalFrom db (reorderJoins from_),
    ∃ row2 ∈ evalFrom db from_, (∀ p, p ∈ row ↔ p ∈ row2)

axiom join_reorder_preserves_backward (db : Database) (from_ : FromClause) :
  canReorderJoins from_ →
  ∀ row ∈ evalFrom db from_,
    ∃ row2 ∈ evalFrom db (reorderJoins from_), (∀ p, p ∈ row ↔ p ∈ row2)
```

### Axiom Dependency Hierarchy

```
Level 4: Optimizer Axioms (target)
├── pushdown_preserves_semantics
└── join_reorder_preserves_*
         ↓ depends on
Level 3: Filter/Projection Axioms
├── filter_join_left
├── filter_join_right
├── filter_pushdown_table
└── filter_and
         ↓ depends on
Level 2: Join Algebra Axioms
├── join_comm_full
├── join_assoc
├── cross_join_comm
└── cross_join_assoc
         ↓ depends on
Level 1: Boolean/Expression Axioms
├── evalBinOp_and_assoc
├── evalBinOp_or_assoc
├── and_comm, or_comm
└── Value.eq properties
         ↓ depends on
Level 0: Semantic Model
├── evalExprWithDb
├── evalFrom
└── evalSelect
```

### Semantic Model (Level 0)

```lean
abbrev Row := List (String × Value)
abbrev Table := List Row
abbrev Database := String → Table

-- Key evaluation functions (already implemented)
def evalExprWithDb : Database → Row → Expr → Option Value
def evalFrom : Database → FromClause → Table
def evalSelect : Database → SelectStmt → Table
```

---

## Phased Approach

### Phase 1: Foundation - Value and Boolean Properties -- COMPLETED

**Goal:** Prove properties about value comparison and boolean operations.

**Axioms proved (22 total, all compile and build successfully):**
- `evalBinOp_and_assoc` - AND is associative (proven via exhaustive 6x6x6 case analysis with `simp [evalBinOp]`)
- `evalBinOp_or_assoc` - OR is associative (proven via exhaustive 6x6x6 case analysis with `simp [evalBinOp]`)
- `evalBinOp_and_or_distrib_left` - AND distributes over OR (proven via exhaustive 6x6x6 case analysis with `simp [evalBinOp]`)
- `evalBinOp_or_and_distrib_left` - OR distributes over AND (proven via exhaustive 6x6x6 case analysis with `simp [evalBinOp]`)
- `coalesce_int_left`, `coalesce_string_left`, `coalesce_bool_left`
- `coalesce_single_int`, `coalesce_single_string`, `coalesce_single_bool`
- `coalesce_single_null`, `coalesce_empty`
- `nullif_same_int`, `nullif_diff_int`
- `min_singleton`, `max_singleton`
- `distinct_count_le`, `distinct_idempotent`, `count_distinct_le_count`
- `filter_and_eq_filter_filter`, `filter_comm`

**Removed (was unsound):**
- `coalesce_null_left` - deleted; was unsound for null second argument (see Known Soundness Issues). Replaced by `coalesce_null_left_nonnull`.

**Approach used:**
1. Exhaustive case analysis on all `Option Value` constructor triples (for associativity/distributivity)
2. `simp` with `evalFunc`/`isNullValue` unfolding (for COALESCE/NULLIF)
3. Standard library lemmas (for list properties)
4. Induction on list structure (for filter properties)

---

### Phase 1b: Expression-Level Axioms (~35 axioms) -- NEXT

**Goal:** Prove the remaining expression-level axioms that use `≃ₑ` (ExprEquiv).
These all follow the same pattern: unfold `evalExprWithDb`, case-split on the
evaluated values, then close with `simp`/`rfl`. They are independent of each
other and of later phases.

**Approach:** For each axiom of the form `theorem foo : lhs ≃ₑ rhs`, introduce
`row`, unfold `evalExpr`, and use `simp [evalExprWithDb, evalBinOp, evalUnaryOp]`
with case analysis on the evaluated sub-expressions.

**Arithmetic identities (7 axioms):**
- `expr_add_zero`, `expr_zero_add`, `expr_mul_one`, `expr_one_mul`,
  `expr_mul_zero`, `expr_zero_mul`, `expr_sub_zero`

**Boolean identities (7 axioms):**
- `not_not`, `and_true`, `or_false`, `and_self`, `or_self`,
  `and_not_self`, `or_not_self`

**Boolean absorption (2 axioms):**
- `and_absorb_or`, `or_absorb_and`

**Comparison operators (14 axioms):**
- `eq_reflexive`, `ne_irreflexive`, `eq_comm` (already a theorem, just used by later axioms)
- `not_eq_is_ne`, `not_ne_is_eq`, `not_lt_is_ge`, `not_le_is_gt`,
  `not_gt_is_le`, `not_ge_is_lt`
- `lt_flip`, `le_flip`, `gt_flip`, `ge_flip`

**CASE expressions (5 axioms):**
- `case_when_true`, `case_when_false`, `case_when_false_no_else`,
  `case_empty_else`, `case_empty_no_else`

**Estimated complexity:** Easy -- mostly mechanical `simp`/`rfl` proofs.

---

### Phase 1c: IN / BETWEEN / LIKE Axioms (~11 axioms)

**Goal:** Prove expression-level axioms involving IN lists, BETWEEN, and LIKE.

**IN/NOT IN (8 axioms):**
- `in_empty_false`, `not_in_empty_true` -- trivial (empty list)
- `in_singleton`, `not_in_singleton` -- single-element expansion
- `in_pair`, `not_in_pair` -- two-element expansion
- `in_list_or_expansion`, `not_in_list_and_expansion` -- general list induction

**BETWEEN (3 axioms):**
- `between_expansion`, `between_reflexive`, `not_between_expansion`

**LIKE (3 axioms):**
- `like_match_all`, `like_empty_pattern`, `like_self`
  (harder -- depends on `simpleLike` pattern matching semantics)

**Estimated complexity:** Easy-Medium.

---

### Phase 1d: String/Function Axioms (~7 axioms)

**Goal:** Prove string concatenation and function idempotence axioms.

- `concat_empty_left`, `concat_empty_right` -- concat identity
- `upper_idempotent`, `lower_idempotent` -- function idempotence
- `upper_lower_upper`, `lower_upper_lower` -- function composition
- `length_empty` -- length of empty string

**Estimated complexity:** Easy -- unfold `evalFunc` and `simp`.

---

### Phase 2: Statement-Level Filter/WHERE Axioms (~7 axioms)

**Goal:** Prove axioms about WHERE clause behavior at the `evalSelect`/`evalStmt` level.

**Target axioms:**
- `where_true_elim` -- WHERE TRUE is identity
- `where_false_empty` -- WHERE FALSE produces empty result
- `filter_and` -- WHERE (p AND q) = WHERE p then WHERE q
- `filter_commute` -- WHERE p then WHERE q = WHERE q then WHERE p
- `filter_idempotent` -- WHERE p then WHERE p = WHERE p
- `filter_false_empty'` -- variant of WHERE FALSE
- `predicate_pushdown` -- WHERE pushdown for single table

**Approach:** Unfold `evalSelect`/`evalStmt`, reason about `List.filter`.

**Estimated complexity:** Medium -- requires understanding `evalSelect` structure.

---

### Phase 3: Aggregate/Distinct/List Axioms (~4 axioms)

**Target axioms:**
- `min_le_elem`, `max_ge_elem` -- list fold properties (induction on list)
- `distinct_count_le`, `distinct_idempotent` -- `List.eraseDups` properties

**Estimated complexity:** Medium -- standard list induction.

---

### Phase 4: Set Operations (UNION/INTERSECT/EXCEPT) (~13 axioms)

**Goal:** Prove commutativity, associativity, idempotence, and distributivity
of set operations.

**Commutativity (3):** `union_comm`, `union_all_comm`, `intersect_comm`
**Associativity (2):** `union_assoc`, `intersect_assoc`
**Idempotence (2):** `union_idempotent`, `intersect_idempotent`
**Identity/absorption (3):** `except_self_empty`, `union_empty_right`, `intersect_empty_right`
**Cardinality (1):** `union_all_length`
**Distributivity (2):** `union_intersect_distrib`, `intersect_union_distrib`

**Approach:** Unfold `evalQuery`, reason about list dedup/append/filter.

**Estimated complexity:** Medium -- list reasoning, but no join semantics needed.

---

### Phase 5: ORDER BY / LIMIT / OFFSET Axioms (~14 axioms)

**Goal:** Prove properties of ORDER BY, LIMIT, and OFFSET.

**ORDER BY (6):** `order_by_preserves_count`, `order_by_empty_identity`,
  `order_by_idempotent`, `order_by_last_wins`, `order_by_reverse`,
  `order_limit_deterministic`

**LIMIT/OFFSET (8):** `limit_zero_empty`, `limit_upper_bound`,
  `limit_none_all_rows`, `limit_monotonic`, `limit_one_singleton`,
  `offset_zero_identity`, `offset_too_large_empty`, `offset_reduces_count`,
  `offset_monotonic`, `limit_offset_compose`, `offset_limit_zero_empty`,
  `pagination_upper_bound`, `pagination_identity`, `consecutive_pages`

**Approach:** These reduce to `List.take`/`List.drop`/`List.length` lemmas.

**Estimated complexity:** Easy-Medium.

---

### Phase 6: Join Axioms (~21 axioms)

**Goal:** Prove join commutativity, associativity, cardinality bounds,
and empty-table behavior.

**Empty table (4 -- easy):** `inner_join_empty_left`, `inner_join_empty_right`,
  `cross_join_empty_left`, `cross_join_empty_right`

**Trivial conditions (2 -- easy):** `inner_join_true_is_cross`, `inner_join_false_empty`

**Cardinality (5 -- medium):** `cross_join_cardinality`, `cross_join_cardinality_comm`,
  `cross_join_assoc_cardinality`, `inner_join_cardinality_le`,
  `left_join_cardinality_ge`, `right_join_cardinality_ge`

**Semantics (5 -- hard):** `join_comm`, `join_comm_full`, `cross_join_comm`,
  `join_assoc`, `cross_join_assoc`

**Advanced (5 -- hard):** `inner_join_to_where`, `left_join_preserves_left`,
  `right_join_preserves_right`, `inner_subset_cross`,
  `left_join_filter_null_is_inner`, `left_join_false_all_left`

**Approach:** Unfold `evalFrom` join cases, reason about row merging and
list comprehension. The commutativity/associativity proofs require showing
row merging is commutative/associative (modulo column ordering).

**Estimated complexity:** Medium-Hard.

---

### Phase 7: Subquery / EXISTS / IN Axioms (~17 axioms)

**Goal:** Prove subquery evaluation properties.

**Simple/empty (6 -- easy):** `exists_empty_false`, `not_exists_empty_true`,
  `exists_nonempty_true`, `not_exists_nonempty_false`, `not_not_exists`,
  `scalar_subquery_empty_null`

**Subquery WHERE (2 -- easy):** `subquery_where_true`, `subquery_where_false`

**Equivalences (4 -- medium):** `exists_as_count_gt_zero`,
  `not_exists_as_count_eq_zero`, `subquery_limit_one`, `scalar_subquery_is_first`

**Advanced (5 -- hard):** `in_subquery_as_exists`, `not_in_subquery_as_not_exists`,
  `uncorrelated_subquery_independent`, `in_singleton_subquery`,
  `correlated_subquery_uses_context`, `exists_monotonic`

**Unnesting (4 -- hard):** `in_subquery_unnest_to_join`,
  `not_in_subquery_unnest_to_antijoin`, `in_subquery_implies_join_match`,
  `join_match_implies_in_subquery`

**Estimated complexity:** Medium-Hard.

---

### Phase 8: Expression Evaluation Helper Lemmas

**Goal:** Prove helper properties needed by harder axioms in Phases 6-7.

**Target lemmas:**
- `normalizeExpr_equiv` -- normalization preserves semantics
- `syntacticEquiv_implies_equiv` -- syntactic equivalence implies semantic
- `ground_expr_eval_independent` -- ground expressions don't depend on row
- `decideGroundExprEquiv_sound` -- ground equivalence decision procedure is sound

**Approach:** Structural induction on `Expr`.

**Estimated complexity:** Medium-High.

---

### Phase 9: Filter Pushdown Through Joins

**Goal:** Prove predicates can be pushed into join operands.

**Target axioms:**
- `filter_join_left`, `filter_join_right`, `filter_pushdown_table`

**Approach:** Use column reference tracking from `exprReferencesOnlyFrom`,
show filter evaluation only depends on referenced columns.

**Estimated complexity:** High.

---

### Phase 10: Optimizer Correctness (Final Target)

**Goal:** Prove the top-level optimizer axioms from Issue #11.

**Target axioms (not in Equiv.lean -- in Optimizer modules):**
- `pushdown_preserves_semantics`
- `join_reorder_preserves_forward`
- `join_reorder_preserves_backward`

**Strategy:** Compose lemmas from all prior phases.

**Estimated complexity:** High -- ties everything together.

---

## Remaining Axiom Count by Phase

| Phase | Description | Axioms | Difficulty |
|-------|-------------|--------|------------|
| 1 | Value/Boolean properties | 0 (done) | -- |
| 1b | Expression-level (bool, arith, cmp, CASE) | ~35 | Easy |
| 1c | IN / BETWEEN / LIKE | ~11 | Easy-Medium |
| 1d | String/Function | ~7 | Easy |
| 2 | Statement-level filter/WHERE | ~7 | Medium |
| 3 | Aggregate/Distinct | ~4 | Medium |
| 4 | Set operations | ~13 | Medium |
| 5 | ORDER BY / LIMIT / OFFSET | ~14 | Easy-Medium |
| 6 | Join axioms | ~21 | Medium-Hard |
| 7 | Subquery / EXISTS / IN | ~17 | Medium-Hard |
| 8 | Expression evaluation helpers | ~4 | Medium-High |
| 9 | Filter pushdown through joins | ~3 | High |
| 10 | Optimizer correctness | ~3 | High |
| | **Total remaining** | **~152** | |

## Implementation Order (with GitHub Issues)

Work the waves in order. Issues within a wave are independent and can be
done in parallel.

### Wave 1 -- Expression-level boolean/arithmetic/comparison (easiest, highest ROI)

All mechanical `simp`/`rfl` proofs. No dependencies between them.

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 1 | [#46](https://github.com/evelynmitchell/sql_equiv/issues/46) | `not_not` (double negation) | 1 | Easy |
| 2 | [#48](https://github.com/evelynmitchell/sql_equiv/issues/48) | `and_true`, `or_false` (identity) | 2 | Easy |
| 3 | [#47](https://github.com/evelynmitchell/sql_equiv/issues/47) | `and_absorb_or`, `or_absorb_and` (absorption) | 2 | Easy |
| 4 | [#49](https://github.com/evelynmitchell/sql_equiv/issues/49) | `and_self`, `or_self` (idempotent) | 2 | Easy (check soundness) |
| 5 | [#50](https://github.com/evelynmitchell/sql_equiv/issues/50) | `and_not_self`, `or_not_self` (complement) | 2 | Easy (check soundness) |
| 6 | [#57](https://github.com/evelynmitchell/sql_equiv/issues/57) | Arithmetic identities (x+0, x*1, etc.) | 7 | Easy (check soundness) |
| 7 | [#54](https://github.com/evelynmitchell/sql_equiv/issues/54) | Comparison negation rules | 6 | Easy |
| 8 | [#55](https://github.com/evelynmitchell/sql_equiv/issues/55) | Comparison flip rules | 4 | Easy |
| 9 | [#56](https://github.com/evelynmitchell/sql_equiv/issues/56) | `eq_reflexive`, `ne_irreflexive` | 2 | Easy-Medium |
| 10 | [#61](https://github.com/evelynmitchell/sql_equiv/issues/61) | CASE/WHEN simplification | 5 | Easy |

### Wave 2 -- IN/BETWEEN/LIKE/String (still expression-level)

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 11 | [#58](https://github.com/evelynmitchell/sql_equiv/issues/58) | IN list expansion | 6 | Easy-Medium |
| 12 | [#59](https://github.com/evelynmitchell/sql_equiv/issues/59) | BETWEEN expansion | 3 | Easy |
| 13 | [#60](https://github.com/evelynmitchell/sql_equiv/issues/60) | LIKE pattern rules | 3 | Medium |
| 14 | [#62](https://github.com/evelynmitchell/sql_equiv/issues/62) | String function properties | 7 | Easy |

### Wave 3 -- Statement-level, no join dependency (can parallel with Wave 2)

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 15 | [#51](https://github.com/evelynmitchell/sql_equiv/issues/51) | `where_true_elim`, `where_false_empty` | 2 | Medium |
| 16 | [#72](https://github.com/evelynmitchell/sql_equiv/issues/72) | Filter composition rules | 4 | Medium |
| 17 | [#82](https://github.com/evelynmitchell/sql_equiv/issues/82) | Aggregate properties | 4 | Medium |
| 18 | [#79](https://github.com/evelynmitchell/sql_equiv/issues/79) | ORDER BY properties | 5 | Easy-Medium |
| 19 | [#80](https://github.com/evelynmitchell/sql_equiv/issues/80) | LIMIT properties | 5 | Easy-Medium |
| 20 | [#81](https://github.com/evelynmitchell/sql_equiv/issues/81) | OFFSET/pagination | 5 | Easy-Medium |
| 21 | [#63](https://github.com/evelynmitchell/sql_equiv/issues/63) | Set operation commutativity | 3 | Medium |
| 22 | [#64](https://github.com/evelynmitchell/sql_equiv/issues/64) | Set operation assoc/distrib | 4 | Medium |
| 23 | [#65](https://github.com/evelynmitchell/sql_equiv/issues/65) | Set operation edge cases | 5 | Medium |

### Wave 4 -- Helper lemmas

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 24 | [#52](https://github.com/evelynmitchell/sql_equiv/issues/52) | Normalization equivalence | 2 | Medium-High |
| 25 | [#53](https://github.com/evelynmitchell/sql_equiv/issues/53) | Ground expr independence | 2 | Medium-High |

### Wave 5 -- Joins (sequential dependency chain)

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 26 | [#70](https://github.com/evelynmitchell/sql_equiv/issues/70) | Join edge cases (empty, TRUE/FALSE) | 7 | Medium |
| 27 | [#69](https://github.com/evelynmitchell/sql_equiv/issues/69) | Join cardinality bounds | 7 | Medium |
| 28 | [#67](https://github.com/evelynmitchell/sql_equiv/issues/67) | `cross_join_comm`, `cross_join_assoc` | 2 | Medium-Hard |
| 29 | [#66](https://github.com/evelynmitchell/sql_equiv/issues/66) | `join_comm`, `join_comm_full` | 2 | Hard |
| 30 | [#68](https://github.com/evelynmitchell/sql_equiv/issues/68) | `join_assoc` (**hardest axiom**) | 1 | Hard |
| 31 | [#71](https://github.com/evelynmitchell/sql_equiv/issues/71) | Outer join preservation | 4 | Hard |
| 32 | [#75](https://github.com/evelynmitchell/sql_equiv/issues/75) | EXISTS/NOT EXISTS basic rules | 5 | Medium |
| 33 | [#76](https://github.com/evelynmitchell/sql_equiv/issues/76) | IN subquery rules | 5 | Medium |
| 34 | [#78](https://github.com/evelynmitchell/sql_equiv/issues/78) | Scalar/correlated subquery | 8 | Medium-Hard |
| 35 | [#77](https://github.com/evelynmitchell/sql_equiv/issues/77) | Subquery unnesting (IN->JOIN) | 4 | Hard |

### Wave 6 -- Filter pushdown + optimizer (final target)

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 36 | [#73](https://github.com/evelynmitchell/sql_equiv/issues/73) | Filter pushdown through joins | 3 | High |
| 37 | [#74](https://github.com/evelynmitchell/sql_equiv/issues/74) | `predicate_pushdown` (optimizer) | 1 | High |

---


## Infrastructure Axioms (Semantics.lean)

When proving equivalence axioms in `Equiv.lean`, we often need to "unfold"
`evalExprWithDb` (a `partial def` that Lean cannot reduce). We add
**infrastructure axioms** to `Semantics.lean` that assert the definitional
unfolding equations. These are not SQL equivalences themselves — they are
bridges that let proofs access the evaluation semantics.

| Axiom | Added for | Purpose |
|-------|-----------|---------|
| `evalExprWithDb_lit` | (pre-existing) | Unfold literal evaluation |
| `evalExprWithDb_binOp` | (pre-existing) | Unfold binary op evaluation |
| `evalExprWithDb_unaryOp` | (pre-existing) | Unfold unary op evaluation |
| `evalExprWithDb_case` | #61 CASE/WHEN | Unfold CASE expression to `evalCase` |
| `evalCase_nil_some` | #61 CASE/WHEN | Empty branches with ELSE |
| `evalCase_nil_none` | #61 CASE/WHEN | Empty branches, no ELSE → NULL |
| `evalCase_cons_true` | #61 CASE/WHEN | True condition → return result |
| `evalCase_cons_false` | #61 CASE/WHEN | False condition → skip to rest |
| `evalExprWithDb_func` | #62 String functions | Unfold function call to `evalFunc` |
| `evalExprWithDb_between` | #59 BETWEEN | Unfold BETWEEN expression |

New infrastructure axioms should be added to this table as they are created.
All infrastructure axioms have runtime tests in `Test/AxiomCoverageTest.lean`.

---

## Known Soundness Issues

### `coalesce_null_left` was unsound (removed)

The axiom `coalesce_null_left` has been **deleted** from the codebase. It
claimed `COALESCE(NULL, x) = x` for all `x`, but this was false when `x` is
itself a null value (`some (.null _)`).

The `evalFunc` implementation uses `List.find?` to locate the first non-null
argument. When both arguments are null, `find?` returns `none`, but the axiom
claimed the result is `some (.null _)`. In Lean's type system, `none ≠ some _`,
so the axiom introduced an inconsistency from which `False` could be derived.

**Resolution:** The axiom has been removed entirely. The sound replacement is
`coalesce_null_left_nonnull`, which adds the precondition
`isNullValue v = false`. The `sql_rw_null` tactic now uses the sound version.

**Why it was removed rather than kept:** Keeping an unsound axiom "for backwards
compatibility" is dangerous in a proof assistant — any proof depending on it is
silently invalid, and the axiom could be applied accidentally via tactics.
Deleting it forces any downstream code to use the sound version, making
unsoundness a compile error rather than a silent bug.

**Root cause:** The distinction between `none` (evaluation failure / no value)
and `some (.null _)` (a SQL NULL was produced) is easy to overlook when writing
axioms that quantify over `Option Value`. All such axioms should be audited
to ensure they handle both cases correctly.

**Recommendation:** When writing new axioms over `Option Value`, always check
five representative values: `some (.int _)`, `some (.string _)`, `some (.bool _)`,
`some (.null _)`, and `none`.

---

## Known Evaluator Limitations

### Double-qualification of column names in subquery wrapping

The `evalFrom` function qualifies column names at each level of nesting:
- `.table ⟨"users", some "u"⟩` produces columns like `u.id`, `u.age`
- `.subquery sel "filtered_a"` takes the output of `evalSelect` and prefixes
  every column with `filtered_a.`, producing `filtered_a.u.id`, `filtered_a.u.age`

This double-qualification breaks the `filter_join_left` and `filter_join_right`
axioms at the evaluator level. These axioms rewrite:
```
SELECT * FROM (A JOIN B ON cond) WHERE filter
```
into:
```
SELECT * FROM (SELECT * FROM A WHERE filter) AS filtered_a JOIN B ON cond
```

After the rewrite, the join condition still references `u.id` (the original
alias), but the subquery-wrapped columns are now named `filtered_a.u.id`.
The `getQualified` lookup for `u.id` fails because no column has that exact
name — the evaluator does not strip or flatten nested qualifiers.

**Impact on testing:** The axiom coverage tests for `filter_join_left` and
`filter_join_right` work around this by testing the semantic property directly
via `evalFrom` (filter-then-join vs join-then-filter) rather than comparing
`evalSelect` on both sides of the axiom's rewrite.

**Impact on proving:** When proving these axioms (Phase 6), the proof will need
to account for column renaming through subquery boundaries. Options:
1. Fix `evalFrom`'s `.subquery` case to strip existing qualifiers before
   re-qualifying (so `u.id` becomes `filtered_a.id`, not `filtered_a.u.id`)
2. Make `getQualified` aware of nested qualifiers (match on suffix)

3. Redefine the axioms to use `evalFrom`-level filter pushdown (avoiding
   `evalSelect` subquery wrapping entirely)

Option 1 is likely the cleanest fix — `evalSelect` already projects columns
via `SelectItem`, so the subquery output should have unqualified column names
that then get a single qualifier from the outer `evalFrom`.

---

## Open Questions

1. **Row representation:** Should we use `List (String × Value)` or a more structured type?
2. **NULL handling:** Three-valued logic adds complexity - start with two-valued subset?
3. **Column ordering:** Do we need to prove rows are equal as sets or as ordered lists?
4. **Termination:** Some proofs may need well-founded recursion arguments.
5. **Option Value soundness audit:** The unsound `coalesce_null_left` axiom has been removed, but other axioms quantifying over `Option Value` may have similar `none` vs `some (.null _)` confusion. A systematic audit is still recommended.

---

## Parallelization

These phase groups are independent and can be worked on in parallel:
- **Group A:** Phases 1b, 1c, 1d (expression-level, no dependencies)
- **Group B:** Phases 4, 5 (set operations, LIMIT/OFFSET -- independent of joins)
- **Group C:** Phases 2, 3 (aggregate/distinct, filter/WHERE)
- **Group D:** Phases 6, 7, 8, 9, 10 (joins, subqueries, optimizer -- sequential dependency chain)
