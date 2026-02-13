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

### Phase 1b: Expression-Level Axioms (~35 axioms) -- COMPLETE

**Goal:** Prove the remaining expression-level axioms that use `≃ₑ` (ExprEquiv).
These all follow the same pattern: unfold `evalExprWithDb`, case-split on the
evaluated values, then close with `simp`/`rfl`. They are independent of each
other and of later phases.

**Approach:** For each axiom of the form `theorem foo : lhs ≃ₑ rhs`, introduce
`row`, unfold `evalExpr`, and use `simp [evalExprWithDb, evalBinOp, evalUnaryOp]`
with case analysis on the evaluated sub-expressions.

**Arithmetic identities (7 axioms) — PROVED (PR #93):**
- `expr_add_zero`, `expr_zero_add`, `expr_mul_one`, `expr_one_mul`,
  `expr_mul_zero`, `expr_zero_mul`, `expr_sub_zero`
- Required `Expr.isIntValued` precondition (see Batch 3 in PROVING_LOG.md)

**Boolean identities (7 axioms) — PROVED (PR #104):**
- `not_not`, `and_true`, `or_false`, `and_self`, `or_self`,
  `and_not_self`, `or_not_self`
- Required `Expr.isBoolValued` precondition

**Boolean absorption (2 axioms) — PROVED (PR #104):**
- `and_absorb_or`, `or_absorb_and`
- Required `Expr.isBoolValued` precondition

**Comparison operators (14 axioms) — PROVED:**
- `eq_reflexive`, `ne_irreflexive` — proved with `Expr.evaluable` precondition (PR #92)
- `eq_comm` (already a theorem, just used by later axioms)
- `not_eq_is_ne`, `not_ne_is_eq`, `not_lt_is_ge`, `not_le_is_gt`,
  `not_gt_is_le`, `not_ge_is_lt` — proved (PR #85)
- `lt_flip`, `le_flip`, `gt_flip`, `ge_flip` — proved (PR #85)

**CASE expressions (5 axioms) — PROVED (PR #85):**
- `case_when_true`, `case_when_false`, `case_when_false_no_else`,
  `case_empty_else`, `case_empty_no_else`

**Estimated complexity:** Easy -- mostly mechanical `simp`/`rfl` proofs.

---

### Phase 1c: IN / BETWEEN / LIKE Axioms (~11 axioms)

**Goal:** Prove expression-level axioms involving IN lists, BETWEEN, and LIKE.

**IN/NOT IN (8 axioms) — ALL PROVED:**
- `in_empty_false` — **PROVED** (PR #112, reproved in PR #125; `evaluable` precondition dropped)
- `not_in_empty_true` — **PROVED** (PR #112, reproved in PR #125; `evaluable` precondition dropped)
- `in_singleton`, `not_in_singleton` — **PROVED** (PR #126) via foldl+evalBinOp semantics
- `in_pair`, `not_in_pair` — **PROVED** (PR #126) via foldl+evalBinOp + De Morgan
- `in_list_or_expansion`, `not_in_list_and_expansion` — **PROVED** (PR #126) via foldl induction

**BETWEEN (3 axioms) — ALL PROVED:**
- `between_reflexive` — proved (PR #86, restored in PR #102)
- `between_expansion` — **PROVED** (PR #109)
- `not_between_expansion` — **PROVED** (PR #109)

**LIKE (3 axioms) — 2 proved, 1 remaining:**
- `like_empty_pattern` — proved (PR #86, restored in PR #102)
- `like_match_all` — **PROVED** (PR #111) with `isStringOrNull` precondition
- `like_self` — **PROVED** (PR #134) via `simpleLike` refactoring to list ops

**Estimated complexity:** Easy-Medium.

---

### Phase 1d: String/Function Axioms (~7 axioms)

**Goal:** Prove string concatenation and function idempotence axioms.

- `concat_empty_left`, `concat_empty_right` -- concat identity — **PROVED** (PR #107)
- `upper_idempotent`, `lower_idempotent` -- function idempotence — **PROVED** (PR #105)
- `upper_lower_upper`, `lower_upper_lower` -- function composition — **PROVED** (PR #105)
- `length_empty` -- length of empty string — proved (PR #86, restored in PR #102)
- `length_concat` -- length of concatenation — **PROVED** (PR #109)

**Estimated complexity:** Easy -- unfold `evalFunc` and `simp`.

---

### Phase 2: Statement-Level Filter/WHERE Axioms (~7 axioms) -- PARTIALLY COMPLETED

**Goal:** Prove axioms about WHERE clause behavior at the `evalSelect`/`evalStmt` level.

**Target axioms:**
- `where_true_elim` -- WHERE TRUE is identity — **PROVED** (via `evalSelect_where_congr`)
- `where_false_empty` -- WHERE FALSE produces empty result — **PROVED** (with `h_no_agg` precondition, via `evalSelect_filter_all_false`)
- `filter_false_empty'` -- variant of WHERE FALSE — **PROVED** (delegates to `where_false_empty`)
- `filter_and` -- WHERE (p AND q) = WHERE p then WHERE q — **BLOCKED** (evalFrom .subquery double-qualification bug)
- `filter_commute` -- WHERE p then WHERE q = WHERE q then WHERE p — **BLOCKED** (same)
- `filter_idempotent` -- WHERE p then WHERE p = WHERE p — **BLOCKED** (same)
- `predicate_pushdown` -- WHERE pushdown for single table — **BLOCKED** (evalExpr vs evalExprWithDb gap)

**Infrastructure axioms added:**
- `evalSelect_where_congr` — if two WHERE clauses produce the same filtering, evalSelect produces the same result
- `evalSelect_filter_all_false` — WHERE that rejects all rows produces empty result (when no aggregates)

**Soundness fixes:**
- `where_false_empty` and `filter_false_empty'` were unsound for aggregate queries (e.g., `SELECT COUNT(*) ... WHERE FALSE` produces 1 row, not 0). Added `h_no_agg : selectHasAggregate items = false` precondition.

**Blocked axioms:**
- `filter_and`, `filter_commute`, `filter_idempotent`: blocked by evalFrom .subquery double-qualification bug — subquery wrapping causes columns like `t.col` to become `inner.t.col`, so the outer WHERE can't find them.
- `predicate_pushdown`: blocked by `evalExpr` vs `evalExprWithDb` gap — the external filter uses `evalExpr` (no db context) while `evalSelect` internally uses `evalExprWithDb db`. Could be proved with a `q.hasNoSubquery` precondition.

**Approach used:** Infrastructure axioms capturing evalSelect's WHERE clause behavior, then theorem proofs using those axioms.

---

### Phase 3: Aggregate/Distinct/List Axioms (~4 axioms)

**Target axioms:**
- `min_le_elem`, `max_ge_elem` -- list fold properties (induction on list)
- `distinct_count_le`, `distinct_idempotent` -- `List.eraseDups` properties

**Estimated complexity:** Medium -- standard list induction.

---

### Phase 4: Set Operations (UNION/INTERSECT/EXCEPT) — 13 proved, 0 unsound

**Status:** COMPLETE

**Proved under exact equality ≃ᵩ (5 theorems):**
- `union_all_length` — `List.length_append`
- `except_self_empty` — `List.filter_eq_nil_iff` + `List.contains_iff_mem`
- `intersect_empty_right` — `evalSelect_filter_all_false` for empty select
- `intersect_idempotent` — `List.filter_eq_self` + `List.contains_iff_mem`
- `intersect_assoc` — `List.filter_filter` + `List.filter_congr` + Bool case analysis

**Proved under bag equivalence ≃ᵇ (3 theorems):**
- `union_all_comm` — `List.perm_append_comm`
- `union_comm` — `Perm_eraseDups` + `List.perm_append_comm`
- `union_assoc` — `perm_ext_iff_of_nodup` + `nodup_eraseDups` + `or_assoc`

**Proved under set equivalence ≃ˢ (5 theorems):**
- `intersect_comm` — `mem_filter_contains` + `And.comm`
- `union_idempotent` — `mem_eraseDups` + `List.mem_append` + `Or.elim id id`
- `union_empty_right` — `mem_eraseDups` + `evalSelect_filter_all_false`
- `union_intersect_distrib` — `mem_eraseDups_append` + `mem_filter_contains` + `or_and_left`
- `intersect_union_distrib` — `mem_filter_contains` + `mem_eraseDups_append` + `and_or_left`

**Equivalence hierarchy:** `≃ᵩ` (exact list equality) → `≃ᵇ` (bag/Perm) → `≃ˢ` (set/membership).
Defined in `Defs.lean`; helper lemmas in `SetBagLemmas.lean`.

**Infrastructure added:** `evalQuery_simple`, `evalQuery_compound` (decompose `evalQuery`)
**Dependencies added:** `LawfulBEq` for `SqlType` and `Value` (derived via `ReflBEq` + `LawfulBEq`)

---

### Phase 5: ORDER BY / LIMIT / OFFSET Axioms (~18 axioms)

**Goal:** Prove properties of ORDER BY, LIMIT, and OFFSET.

**16 proved (PR #115), 2 remaining axioms:**

**ORDER BY (5 total, 3 proved, 2 axioms):**
- Proved: `order_by_preserves_count`, `order_by_length_invariant`, `order_limit_deterministic`
- Axioms: `order_by_idempotent`, `order_by_reverse`

**LIMIT/OFFSET (12):** `limit_zero_empty`, `limit_upper_bound`,
  `limit_none_all_rows`, `limit_monotonic`, `limit_one_singleton`,
  `offset_zero_identity`, `offset_too_large_empty`, `offset_reduces_count`,
  `offset_monotonic`, `limit_offset_compose`, `offset_limit_zero_empty`,
  `pagination_upper_bound`, `pagination_identity`, `consecutive_pages`

**Approach:** Infrastructure axioms `evalSelect_limit_offset` and
`evalSelect_orderBy_length` in Semantics.lean decompose `evalSelect` into
`List.take`/`List.drop`/`List.length` reasoning. Helper lemmas specialize
for concrete `Option` values to avoid rewrite ambiguity.

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

### Phase 7: Subquery / EXISTS / IN Axioms (~17 axioms, 4 proved)

**Goal:** Prove subquery evaluation properties.

**Simple/empty (6 -- easy, 4 proved):** `exists_empty_false` (**PROVED**, PR #135),
  `not_exists_empty_true` (**PROVED**, PR #135),
  `exists_nonempty_true` (**PROVED**, PR #135),
  `not_exists_nonempty_false` (**PROVED**, PR #135), `not_not_exists`,
  `scalar_subquery_empty_null`

**Subquery WHERE (2 -- easy):** `subquery_where_true`, `subquery_where_false`

**Equivalences (4 -- medium):** `exists_as_count_gt_zero`,
  `not_exists_as_count_eq_zero`, `subquery_limit_one`, `scalar_subquery_is_first`

**Advanced (4 -- hard):** `in_subquery_as_exists`, `not_in_subquery_as_not_exists`,
  `uncorrelated_subquery_independent`, `in_singleton_subquery`,
  `exists_monotonic`

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

**Current totals**: 47 axioms remaining (34 in Equiv/, 13 in infrastructure files), 418 theorems proved (89.9%).
Axiom ratchet: 47 (in `tools/axiom_count_minimum.txt`).
Run `python3 tools/count_axioms_theorems.py -v` for a live per-file breakdown (includes `private theorem` declarations).

| Phase | Description | Proved | Remaining | Difficulty |
|-------|-------------|--------|-----------|------------|
| 1 | Value/Boolean properties | 22 | 0 (done) | -- |
| 1b | Expression-level (bool, arith, cmp, CASE) | ~35 | 0 (done) | -- |
| 1c | IN / BETWEEN / LIKE | 13 | 0 (done) | -- |
| 1d | String/Function | 8 | 0 (done) | -- |
| 2 | Statement-level filter/WHERE | 3 | ~4 | Medium |
| 3 | Aggregate/Distinct | 0 | ~4 | Medium |
| 4 | Set operations | 0 | ~13 | Medium |
| 5 | ORDER BY / LIMIT / OFFSET | 16 | 2 | Easy-Medium |
| 6 | Join axioms | 0 | ~21 | Medium-Hard |
| 7 | Subquery / EXISTS / IN | 4 | ~13 | Medium-Hard |
| 8 | Expression evaluation helpers | 1 | ~3 | Medium-High |
| 9 | Filter pushdown through joins | 0 | ~3 | High |
| 10 | Optimizer correctness | 0 | ~3 | High |
| infra | Infrastructure (Semantics.lean) | 21 | 5 (5 bridge axioms — irreducible) | N/A |
| runtime | Optimizer/Normalization/Pushdown | 0 | 8 | N/A |
| | **Total** | **~106** | **~83** | |

**Note:** 3 proofs from PR #86 (`between_reflexive`, `like_empty_pattern`,
`length_empty`) were lost during the Equiv.lean → submodule split but have
been restored in PR #102.

## Implementation Order (with GitHub Issues)

Work the waves in order. Issues within a wave are independent and can be
done in parallel.

### Wave 1 -- Expression-level boolean/arithmetic/comparison (easiest, highest ROI)

Sound axioms are mechanical `simp`/`rfl` proofs. Unsound axioms need a design
decision first (see "Unsound Axiom Strategy" below).

| Order | Issue | Description | Axioms | Status |
|:-----:|-------|-------------|:------:|--------|
| 1 | [#46](https://github.com/evelynmitchell/sql_equiv/issues/46) | `not_not` (double negation) | 1 | **Proved** (PR #104) — `isBoolValued` precondition |
| 2 | [#48](https://github.com/evelynmitchell/sql_equiv/issues/48) | `and_true`, `or_false` (identity) | 2 | **Proved** (PR #104) — `isBoolValued` precondition |
| 3 | [#47](https://github.com/evelynmitchell/sql_equiv/issues/47) | `and_absorb_or`, `or_absorb_and` (absorption) | 2 | **Proved** (PR #104) — `isBoolValued` precondition |
| 4 | [#49](https://github.com/evelynmitchell/sql_equiv/issues/49) | `and_self`, `or_self` (idempotent) | 2 | **Proved** (PR #104) — `isBoolValued` precondition |
| 5 | [#50](https://github.com/evelynmitchell/sql_equiv/issues/50) | `and_not_self`, `or_not_self` (complement) | 2 | **Proved** (PR #104) — `isBoolValued` precondition |
| 6 | [#57](https://github.com/evelynmitchell/sql_equiv/issues/57) | Arithmetic identities (x+0, x*1, etc.) | 7 | **Proved** (PR #93) — `isIntValued` precondition |
| 7 | [#54](https://github.com/evelynmitchell/sql_equiv/issues/54) | Comparison negation rules | 6 | **Proved** (PR #85) |
| 8 | [#55](https://github.com/evelynmitchell/sql_equiv/issues/55) | Comparison flip rules | 4 | **Proved** (PR #85) |
| 9 | [#56](https://github.com/evelynmitchell/sql_equiv/issues/56) | `eq_reflexive`, `ne_irreflexive` | 2 | **Proved** (PR #92) — `evaluable` precondition |
| 10 | [#61](https://github.com/evelynmitchell/sql_equiv/issues/61) | CASE/WHEN simplification | 5 | **Proved** (PR #85) |

### Wave 2 -- IN/BETWEEN/LIKE/String (still expression-level)

| Order | Issue | Description | Axioms | Status |
|:-----:|-------|-------------|:------:|--------|
| 11 | [#58](https://github.com/evelynmitchell/sql_equiv/issues/58) | IN list expansion | 8 | 8 **proved** (PR #112: empty cases; PR #126: singleton, pair, general expansion) |
| 12 | [#59](https://github.com/evelynmitchell/sql_equiv/issues/59) | BETWEEN expansion | 3 | 3 **proved** (PR #102: `between_reflexive`; PR #109: `between_expansion`, `not_between_expansion`) |
| 13 | [#60](https://github.com/evelynmitchell/sql_equiv/issues/60) | LIKE pattern rules | 3 | 3 **proved** (PR #102: `like_empty_pattern`; PR #111: `like_match_all`; PR #134: `like_self`) |
| 14 | [#62](https://github.com/evelynmitchell/sql_equiv/issues/62) | String function properties | 8 | 8 **proved** (PR #102: `length_empty`; PR #105: `upper/lower_idempotent`, `upper_lower_upper`, `lower_upper_lower`; PR #107: `concat_empty_left/right`; PR #109: `length_concat`) |

### Wave 3 -- Statement-level, no join dependency (can parallel with Wave 2)

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 15 | [#51](https://github.com/evelynmitchell/sql_equiv/issues/51) | `where_true_elim`, `where_false_empty` | 2 | **Proved** (PR #116) |
| 16 | [#72](https://github.com/evelynmitchell/sql_equiv/issues/72) | Filter composition rules | 4 | 1 **proved** (PR #116: `filter_false_empty'`); 3 blocked (subquery double-qualification) |
| 17 | [#82](https://github.com/evelynmitchell/sql_equiv/issues/82) | Aggregate properties | 4 | Medium |
| 18 | [#79](https://github.com/evelynmitchell/sql_equiv/issues/79) | ORDER BY properties | 5 | 3 **proved** (PR #115); 2 axioms |
| 19 | [#80](https://github.com/evelynmitchell/sql_equiv/issues/80) | LIMIT properties | 5 | **Proved** (PR #115) |
| 20 | [#81](https://github.com/evelynmitchell/sql_equiv/issues/81) | OFFSET/pagination | 5 | **Proved** (PR #115) |
| 21 | [#63](https://github.com/evelynmitchell/sql_equiv/issues/63) | Set operation commutativity | 3 | Medium |
| 22 | [#64](https://github.com/evelynmitchell/sql_equiv/issues/64) | Set operation assoc/distrib | 4 | Medium |
| 23 | [#65](https://github.com/evelynmitchell/sql_equiv/issues/65) | Set operation edge cases | 5 | Medium |

### Wave 4 -- Helper lemmas

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 24 | [#52](https://github.com/evelynmitchell/sql_equiv/issues/52) | Normalization equivalence | 2 | Medium-High |
| 25 | [#53](https://github.com/evelynmitchell/sql_equiv/issues/53) | Ground expr independence | 2 | 1 **proved** (PR #94), 1 kept as axiom (`partial def` limitation) |

### Wave 5 -- Joins (sequential dependency chain)

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 26 | [#70](https://github.com/evelynmitchell/sql_equiv/issues/70) | Join edge cases (empty, TRUE/FALSE) | 7 | Medium |
| 27 | [#69](https://github.com/evelynmitchell/sql_equiv/issues/69) | Join cardinality bounds | 7 | Medium |
| 28 | [#67](https://github.com/evelynmitchell/sql_equiv/issues/67) | `cross_join_comm`, `cross_join_assoc` | 2 | Medium-Hard |
| 29 | [#66](https://github.com/evelynmitchell/sql_equiv/issues/66) | `join_comm`, `join_comm_full` | 2 | Hard |
| 30 | [#68](https://github.com/evelynmitchell/sql_equiv/issues/68) | `join_assoc` (**hardest axiom**) | 1 | Hard |
| 31 | [#71](https://github.com/evelynmitchell/sql_equiv/issues/71) | Outer join preservation | 4 | Hard |
| 32 | [#75](https://github.com/evelynmitchell/sql_equiv/issues/75) | EXISTS/NOT EXISTS basic rules | 5 | 4 **proved** (PR #135: `exists_empty_false`, `not_exists_empty_true`, `exists_nonempty_true`, `not_exists_nonempty_false`); 1 axiom (`not_not_exists`) |
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

### PR #130: Non-partial core evaluators (70 → 63 axioms)

Split `Semantics.lean` into 3 files to work around `partial def` opacity:
- `SemanticsBase.lean` — type aliases, helpers, operator evaluators
- `SemanticsCore.lean` — non-partial `evalExprCore`/`evalFromCore` with WFR
  termination proofs and equational theorems proved via `simp [evalExprCore]`
- `Semantics.lean` — partial mutual block + bridge axioms + infrastructure theorems

**10 axioms converted to theorems** by proving equivalence through bridge axioms
to the non-partial core evaluators. **3 bridge axioms added** connecting
`partial def` functions to their non-partial mirrors. **5 more CASE axioms
converted** in PR #131 via foldl-evalCaseHelper equivalence (63 → 58).
**2 evalQuery axioms converted** in PR #132 via evalQueryCore bridge (58 → 57).
**4 evalSelect axioms converted** in PR #133 via evalSelectCore bridge (57 → 54).

All infrastructure axioms that described equational properties have been
eliminated. Only 5 bridge axioms remain — these are inherently needed because
`partial def` = `opaque` in Lean 4's kernel.

### Current status

| Name | Status | Purpose |
|------|--------|---------|
| `evalExprWithDb_eq_evalExprCore` | **bridge axiom** (PR #130) | Connect partial `evalExprWithDb` to non-partial `evalExprCore` |
| `evalCase_eq_evalCaseHelper` | **bridge axiom** (PR #130) | Connect partial `evalCase` to non-partial `evalCaseHelper` |
| `evalFrom_eq_evalFromCore` | **bridge axiom** (PR #130) | Connect partial `evalFrom` to non-partial `evalFromCore` |
| `evalExprWithDb_lit` | **theorem** (PR #130) | Unfold literal evaluation |
| `evalExprWithDb_binOp` | **theorem** (PR #130) | Unfold binary op evaluation |
| `evalExprWithDb_unaryOp` | **theorem** (PR #130) | Unfold unary op evaluation |
| `evalExprWithDb_func` | **theorem** (PR #130) | Unfold function call to `evalFunc` |
| `evalExprWithDb_between` | **theorem** (PR #130) | Unfold BETWEEN expression |
| `evalExprWithDb_inList` | **theorem** (PR #130) | Unfold IN list evaluation |
| `evalFrom_cross_join` | **theorem** (PR #130) | Unfold cross join evaluation |
| `evalFrom_inner_join` | **theorem** (PR #130) | Unfold inner join evaluation |
| `evalFrom_left_join` | **theorem** (PR #130) | Unfold left join evaluation |
| `evalFrom_right_join` | **theorem** (PR #130) | Unfold right join evaluation |
| `evalExprWithDb_exists` | **theorem** (PR #135) | Unfold EXISTS expression |
| `evalExprWithDb_case` | **theorem** (PR #131) | Unfold CASE expression to `evalCase` |
| `evalCase_nil_some` | **theorem** (PR #131) | Empty branches with ELSE |
| `evalCase_nil_none` | **theorem** (PR #131) | Empty branches, no ELSE → NULL |
| `evalCase_cons_true` | **theorem** (PR #131) | True condition → return result |
| `evalCase_cons_false` | **theorem** (PR #131) | False condition → skip to rest |
| `evalQuery_eq_evalQueryCore` | **bridge axiom** (PR #132) | Connect partial `evalQuery` to non-partial `evalQueryCore` |
| `evalSelect_eq_evalSelectCore` | **bridge axiom** (PR #133) | Connect partial `evalSelect` to non-partial `evalSelectCore` |
| `evalSelect_limit_offset` | **theorem** (PR #133) | Decompose evalSelect into take/drop |
| `evalSelect_orderBy_length` | **theorem** (PR #133) | ORDER BY preserves length |
| `evalSelect_where_congr` | **theorem** (PR #133) | Congruence: same filtering → same result |
| `evalSelect_filter_all_false` | **theorem** (PR #133) | Always-false filter → empty result (no agg) |
| `evalQuery_simple` | **theorem** (PR #132) | Decompose simple query evaluation |
| `evalQuery_compound` | **theorem** (PR #132) | Decompose compound query evaluation |

All infrastructure axioms have runtime tests in `Test/AxiomCoverageTest.lean`.

---

## Option 3: Null Semantics Fix (Adopted — PR #92, merged)

### Problem

The original `evalBinOp` and `evalUnaryOp` returned `none` for **both**:
1. SQL NULL propagation (correct: `NULL + 5 = NULL`)
2. Type errors/mismatches (wrong: `"hello" + 5 = error`)

This conflation made axioms like `eq_reflexive` unprovable: `NULL = NULL`
should produce `some (.null none)` (SQL NULL), but the evaluator returned
`none` (indistinguishable from an error).

### Solution

Changed `evalBinOp` and `evalUnaryOp` to return `some (.null none)` for
SQL null propagation in **arithmetic, comparison, unary, and string** operations.
AND/OR retain original semantics to preserve distributivity laws.

| Operation | Before | After |
|-----------|--------|-------|
| `NULL + 5` | `none` | `some (.null none)` |
| `NULL = 5` | `none` | `some (.null none)` |
| `NOT NULL` | `none` | `some (.null none)` |
| `NULL \|\| 'x'` | `none` | `some (.null none)` |
| `"hello" + 5` | `none` | `none` (unchanged, real error) |
| `NULL AND TRUE` | `none` | `none` (AND/OR unchanged) |

### Key Results

- **`eq_reflexive` (#56)**: Now a **theorem** (was axiom). Requires
  `Expr.evaluable` precondition (expression produces `some` value).
- **`ne_irreflexive` (#56)**: Now a **theorem** (was axiom). Same precondition.
- **Distributivity preserved**: AND/OR keep original semantics, so
  `evalBinOp_and_or_distrib_left` and `evalBinOp_or_and_distrib_left` unchanged.
- **Null propagation theorems updated**: `null_add_left` etc. now quantify over
  `Value` (not `Option Value`) and conclude `= some (.null none)`.
- **Comparison negation helpers**: Repaired with explicit null case splits
  (6 helpers, ~20 lines each).
- **All 195 runtime tests pass**.

### `Expr.evaluable` Precondition

```lean
def Expr.evaluable (e : Expr) : Prop :=
  ∀ row : Row, ∃ v : Value, evalExpr row e = some v
```

This excludes only error-producing expressions (missing columns, aggregates
without group context). All well-formed SQL in a valid context satisfies this.
It is a much milder precondition than a full type system.

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

## Unsound Axiom Strategy (Design Decision)

~20 axioms in Waves 1-2 are **unsound as stated** — they claim equivalences
for all expressions but only hold for specific types. Three prototypes were
built to compare approaches (PRs #87, #88, #89). See `PROVING_LOG.md` for
full details.

### The two problems

1. **Null/error conflation**: `evalBinOp` returns `none` for both SQL NULL
   propagation (correct behavior) and type errors (ill-formed expressions).
   This makes `eq_reflexive` unprovable: `NULL = NULL` gives `none` but the
   CASE expression gives `some (.null none)`.

2. **Type mismatches**: `NOT 5`, `"hello" + 0`, etc. return `none` but axioms
   claim they equal the original expression. These need type preconditions.

### Adopted path

**Step 1 — Fix null semantics (Option 3) — DONE (PR #92):**
Changed `evalBinOp`/`evalUnaryOp` to return `some (.null none)` for null
propagation, distinguishing it from `none` (errors). Results:
- `eq_reflexive` and `ne_irreflexive` proved with `Expr.evaluable` precondition
- All 7 arithmetic identities proved with `Expr.isIntValued` precondition (PR #93)
- Proof repair was manageable (~90 mechanical fixes)
- AND/OR kept original semantics to preserve distributivity laws

**Step 2 — Type preconditions (interim approach):**
Rather than a full type system (Option 2), we're using ad-hoc predicates:
- `Expr.evaluable` — expression always produces `some` value (for `eq_reflexive`)
- `Expr.isIntValued` — expression always produces `some (.int n)` (for arithmetic)
- `Expr.isBoolValued` — needed for boolean axioms (#46-50), not yet defined

A full `Expr.wellTyped` type system (Option 2, PR #88) remains the long-term
goal for composability, but the ad-hoc predicates are proving sufficient for
now and don't block progress.

**Optimizer guards mirror axiom preconditions (PRs #100-101):**
The optimizer now has runtime type guards that match the proof preconditions:
- `isDefinitelyBool` (allowlist) guards boolean rewrites — mirrors `isBoolValued`
- `isDefinitelyNonInt` (blocklist) guards arithmetic rewrites — mirrors `isIntValued`
This creates a virtuous cycle: the same type reasoning protects both the
optimizer (at runtime) and the axioms (in proofs).

### What this means for the wave plan

- **Waves 1-2 sound axioms** (#54, #55, #61): proved
- **Wave 1 #56** (`eq_reflexive`, `ne_irreflexive`): proved (PR #92)
- **Wave 1 #57** (arithmetic identities): proved (PR #93) with `isIntValued`
- **Waves 1-2 type-mismatch axioms** (#46-50, #60): need `isBoolValued`
  or `evaluable` preconditions; provable now with Option 3 semantics
- **#58 IN-list expansion**: all 8 proved (PR #112 + PR #126). Evaluator fixed by PR #125; proofs via foldl+evalBinOp semantics
- **Waves 3+**: unaffected by this design decision

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

## Known Regressions (all resolved)

### PR #86 proofs lost during Equiv.lean split — FIXED (PR #102)

**Date discovered:** 2026-02-09 | **Date fixed:** 2026-02-09
**Cause:** Commit 711581c split `SqlEquiv/Equiv.lean` (4105 lines) into 6
submodules. During the split, 3 theorem proofs from PR #86 were reverted to
axiom declarations, and their helper lemmas were dropped entirely.

**Affected axioms (all restored in PR #102):**
| Axiom | Helper lemmas | Status |
|-------|--------------|--------|
| `between_reflexive` | `evalBetween_reflexive` | Restored |
| `like_empty_pattern` | `simpleLike_empty`, `evalBinOp_like_empty_eq_eq` | Restored |
| `length_empty` | (inline proof) | Restored |

**Prevention:** When splitting large files, verify theorem/axiom counts
before and after the split match. A CI check comparing `grep -c "^axiom\|^theorem"`
counts would catch this automatically.

---

## Open Questions

1. **Row representation:** Should we use `List (String × Value)` or a more structured type?
2. ~~**NULL handling:** Three-valued logic adds complexity - start with two-valued subset?~~ **Resolved** — Option 3 null semantics adopted (PR #92).
3. **Column ordering:** Do we need to prove rows are equal as sets or as ordered lists?
4. **Termination:** ~~Some proofs may need well-founded recursion arguments. The `partial def` limitation blocks `ground_expr_eval_independent`.~~ **Partially resolved** — PR #130 introduced non-partial core evaluators (`evalExprCore`, `evalFromCore`) with WFR termination proofs. 10 infrastructure axioms converted to theorems. Remaining `partial def` limitations: evalSelect axioms (4), evalQuery axioms (2), plus 3 bridge axioms. CASE axioms (5) proved in PR #131.
5. ~~**Option Value soundness audit:** The unsound `coalesce_null_left` axiom has been removed, but other axioms quantifying over `Option Value` may have similar `none` vs `some (.null _)` confusion.~~ **Partially resolved** — Option 3 fixes `none` vs `some (.null _)` conflation. The `/audit` tool (PR #99) now catches unsound optimizer rewrites. Remaining unsound axioms are documented in PROVING_LOG.md.

---

## Parallelization

These phase groups are independent and can be worked on in parallel:
- **Group A:** Phases 1b, 1c, 1d (expression-level, no dependencies)
- **Group B:** Phases 4, 5 (set operations, LIMIT/OFFSET -- independent of joins)
- **Group C:** Phases 2, 3 (aggregate/distinct, filter/WHERE)
- **Group D:** Phases 6, 7, 8, 9, 10 (joins, subqueries, optimizer -- sequential dependency chain)

---

## Batteries Migration Sequencing

**Decision (2026-02-11):** Complete axiom proving work **before** the Batteries
migration (`docs/batteries-migration-plan.md`).

### Rationale

1. **Most remaining axioms won't benefit from Batteries.** The plan's own
   assessment: JOIN semantics, subquery semantics, evaluation axioms, and
   optimizer correctness are all SQL-domain-specific. Batteries helps with
   list permutation and boolean algebra — areas we've already covered.

2. **The migration is high-risk for existing proofs.** The `evalBinOp` →
   `nullPropBinOp` refactor (Phase 2 of the migration) is rated "High
   likelihood" to break ExprAxioms proofs. Better to do that rework once,
   after the axiom count is stable, rather than interleaving proof work
   with a structural refactor.

3. **The `alias` rename creates merge conflict surface.** It touches 15
   files / 89 occurrences. Any parallel proof branches would conflict.
   Easier to do the rename when there's no ongoing proof work.

4. **Caveat — avoid new exhaustive Value case-split proofs.** If an axiom
   requires a 36-arm Value case analysis, consider deferring it until after
   the `nullPropBinOp` refactor makes those proofs compositional. Most
   remaining axioms (joins, subqueries, WHERE pushdown) operate at the
   statement/table level, so this shouldn't come up often.

### Trigger for migration

Start the Batteries migration when:
- Axiom proving hits diminishing returns, OR
- New `Value` constructors (`float`, `datetime`, `decimal`) are needed, OR
- A specific axiom proof would benefit significantly from Batteries lemmas
