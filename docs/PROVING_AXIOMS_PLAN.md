# Plan for Proving Semantic Preservation Axioms

This document outlines a phased approach to replacing axioms with proven theorems in the sql_equiv codebase.

## Current State

### Original Target Axioms (Issue #11) — Removed (PR #156)

> The optimizer module and its axioms were removed in PR #156. The original
> targets are preserved here for historical context.

**PredicatePushdown (removed):**
```lean
axiom pushdown_preserves_semantics (db : Database) (pred : Expr) (from_ : FromClause) :
  let result := pushPredicateDown pred from_
  filterRows db (evalFrom db result.pushedFrom) result.remaining =
  filterRows db (evalFrom db from_) (some pred)
```

**JoinReordering (removed):**
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
Level 3: Filter/Projection Axioms
├── filter_join_left ✓ (Batch 44)
├── filter_join_right ✓ (Batch 44)
├── filter_pushdown_table ✓ (Batch 22)
└── filter_and ✓ (PR #147)
         ↓ depends on
Level 2: Join Algebra Axioms
├── join_comm ✓ (Batch 45)
├── join_comm_full ✗ (DELETED — unsound, Batch 22)
├── join_assoc ✓ (Batch 46)
├── cross_join_comm ✓ (PR #140)
└── cross_join_assoc ✓ (PR #140)
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

> **Note (PR #156):** Level 4 "Optimizer Axioms" (`pushdown_preserves_semantics`,
> `join_reorder_preserves_*`) was removed along with the entire optimizer module.
> The optimizer was the only major module with zero formal proofs. All 410+
> theorems in `Equiv/` are untouched.

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

### Phase 2: Statement-Level Filter/WHERE Axioms (~7 axioms) -- COMPLETED

**Goal:** Prove axioms about WHERE clause behavior at the `evalSelect`/`evalStmt` level.

**Target axioms:**
- `where_true_elim` -- WHERE TRUE is identity — **PROVED** (via `evalSelect_where_congr`)
- `where_false_empty` -- WHERE FALSE produces empty result — **PROVED** (with `h_no_agg` precondition, via `evalSelect_filter_all_false`)
- `filter_false_empty'` -- variant of WHERE FALSE — **PROVED** (delegates to `where_false_empty`)
- `filter_and` -- WHERE (p AND q) = WHERE p then WHERE q — **PROVED** (PR #147, via `evalSelect_filter_and`)
- `filter_commute` -- WHERE p then WHERE q = WHERE q then WHERE p — **PROVED** (PR #147, via `evalSelect_filter_commute`)
- `filter_idempotent` -- WHERE p then WHERE p = WHERE p — **PROVED** (PR #147, via `evalSelect_filter_idempotent`)
- `predicate_pushdown` -- WHERE pushdown for single table — **PROVED** (PR #147, via `evalSelect_predicate_pushdown`)

**Infrastructure axioms added:**
- `evalSelect_where_congr` — if two WHERE clauses produce the same filtering, evalSelect produces the same result
- `evalSelect_filter_all_false` — WHERE that rejects all rows produces empty result (when no aggregates)
- `evalBinOp_and_true_iff` — AND returns `some (.bool true)` iff both operands do (PR #147)
- `evalSelect_star_where_eq_filter` — decomposes `SELECT * WHERE p` into `List.filter` on base rows (PR #147)
- `evalSelect_filter_and/commute/idempotent` — filter algebra bridges at evalSelect level (PR #147)
- `evalSelect_predicate_pushdown` — external `List.filter` = combined WHERE (PR #147)

**Soundness fixes:**
- `where_false_empty` and `filter_false_empty'` were unsound for aggregate queries (e.g., `SELECT COUNT(*) ... WHERE FALSE` produces 1 row, not 0). Added `h_no_agg : selectHasAggregate items = false` precondition.

**Evaluator fixes (PR #147):**
- `evalFrom .subquery` changed from re-qualifying column names to pass-through. This eliminated the double-qualification bug (`inner.t.col` → just `t.col`).
- `predicate_pushdown` axiom changed from `evalExpr row q` to `evalExprWithDb db row q`, enabling subquery support in filter predicates.

**Proof technique:** All 4 WHERE axioms reduce to list filter algebra. `evalSelect_star_where_eq_filter` decomposes `SELECT * WHERE p` into `(baseRows.map ([] ++ ·)).filter p_pred`. After `simp only [List.nil_append, List.map_id']` cleans up the map, `list_filter_and_eq` + `evalBinOp_and_true_iff` close the goals.

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

**Semantics (4 -- hard):** `join_comm`, ~~`join_comm_full`~~ ✗ DELETED (unsound, Batch 22),
  ~~`cross_join_comm`~~ ✓ PR #140, ~~`join_assoc`~~ ✓ Batch 46, ~~`cross_join_assoc`~~ ✓ PR #140

**Advanced (5 -- hard):** `inner_join_to_where`, `left_join_preserves_left`,
  `right_join_preserves_right`, `inner_subset_cross`,
  `left_join_filter_null_is_inner`, `left_join_false_all_left`

**Approach:** Unfold `evalFrom` join cases, reason about row merging and
list comprehension. The commutativity/associativity proofs require showing
row merging is commutative/associative (modulo column ordering).

**Estimated complexity:** Medium-Hard.

---

### Phase 7: Subquery / EXISTS / IN Axioms (~17 axioms, 16 proved)

**Goal:** Prove subquery evaluation properties.

**Simple/empty (6 -- easy, 6 proved):** `exists_empty_false` (**PROVED**, PR #135),
  `not_exists_empty_true` (**PROVED**, PR #135),
  `exists_nonempty_true` (**PROVED**, PR #135),
  `not_exists_nonempty_false` (**PROVED**, PR #135),
  `not_not_exists` (**PROVED**, PR #137),
  `scalar_subquery_empty_null` (**PROVED**, PR #138)

**Subquery WHERE (2 -- easy, 2 proved):** `subquery_where_true` (**PROVED**, PR #138),
  `subquery_where_false` (**PROVED**, PR #138 — added `selectHasAggregate` precondition)

**Equivalences (4 -- medium, 4 proved):** `exists_as_count_gt_zero` (**PROVED**, PR #137),
  `not_exists_as_count_eq_zero` (**PROVED**, PR #137),
  `subquery_limit_one` (**PROVED**, PR #139),
  `scalar_subquery_is_first` (**PROVED**, PR #139)

**Advanced (4 -- hard, 5 proved, 1 removed):** `in_subquery_as_exists` (**PROVED**, PR #157 — fixed 3 soundness issues, added qualified cols + eval preconditions),
  `not_in_subquery_as_not_exists` (**PROVED**, PR #157 — same fixes),
  ~~`uncorrelated_subquery_independent`~~ (**REMOVED** as unsound, PR #137),
  `in_singleton_subquery` (**PROVED**, PR #139 — added type compatibility precondition),
  `exists_monotonic` (**PROVED**, PR #137)

**IN empty subquery (2 -- medium, 2 proved):**
  `in_empty_subquery_false` (**PROVED**, PR #139 — fixed unsound EXISTS→NOT EXISTS condition, added `evalExpr row e ≠ none` precondition),
  `not_in_empty_subquery_true` (**PROVED**, PR #139 — same precondition pattern)

**Unnesting (4 -- hard, 3 proved):** `in_subquery_unnest_to_join` (**PROVED**, Batch 47 — added DISTINCT to LHS, qualified yCol, `List.Perm` conclusion, `hStable`/`hNoAgg`/`hNoWin`/`hProjT` preconditions),
  `not_in_subquery_unnest_to_antijoin`,
  `in_subquery_implies_join_match` (**PROVED**, PR #165 — fixed 3 soundness issues: qualified rows via `evalFrom`, qualified column ref `⟨some sName, yCol⟩`, added `hStable` + `hNoAgg`/`hNoWin` preconditions),
  `join_match_implies_in_subquery` (**PROVED**, PR #165 — same fixes)

**Estimated complexity:** Medium-Hard.

---

### Phase 8: Expression Evaluation Helper Lemmas

**Goal:** Prove helper properties needed by harder axioms in Phases 6-7.

**Target lemmas:**
- ~~`normalizeExpr_equiv` -- normalization preserves semantics~~ **PROVED** (PR #162, Batch 40) via WFR conversion + strong induction on sizeOf
- ~~`syntacticEquiv_implies_equiv` -- syntactic equivalence implies semantic~~ **PROVED** (PR #163, Batch 41) via `opaque + @[implemented_by]` DecidableEq + `of_decide_eq_true`
- ~~`ground_expr_eval_independent` -- ground expressions don't depend on row~~ **PROVED** (PR #150, Batch 36) via `isGroundCore` WFR mirror + bridge axioms
- ~~`isGround_eq_isGroundCore` -- bridge axiom for isGround~~ **PROVED** (PR #151, Batch 37) via converting `isGround` mutual block from `partial` to WFR
- `decideGroundExprEquiv_sound` -- ground equivalence decision procedure is sound (already a theorem, uses `ground_expr_eval_independent`)

**Approach:** `syntacticEquiv_implies_equiv` was proved by providing `DecidableEq Expr` via `opaque + @[implemented_by unsafe]` (manual WFR and `deriving` both fail for mutual inductives; `Classical.decEq` is noncomputable, breaking `native_decide`). Changed `syntacticEquiv` to use `decide` instead of `BEq.beq`. Soundness assumption: BEq is lawful.

**Estimated complexity:** Medium-High.

---

### Phase 9: Filter Pushdown Through Joins

**Goal:** Prove predicates can be pushed into join operands.

**Target axioms:**
- ~~`filter_join_left`~~ ✓ (Batch 44), ~~`filter_join_right`~~ ✓ (Batch 44), ~~`filter_pushdown_table`~~ ✓ (Batch 22)

**All proved.** `filter_join_left`/`filter_join_right` proved with semantic preconditions (Batch 44).

**Estimated complexity:** High.

> **Note (PR #156):** Phase 10 "Optimizer Correctness" has been removed.
> The optimizer module was deleted — its 3 axioms (`pushdown_preserves_semantics`,
> `join_reorder_preserves_forward`, `join_reorder_preserves_backward`) and 5
> other axioms in optimizer files are gone. Phase 9 remains as the final phase
> for filter pushdown through joins (an Equiv-level concern independent of the optimizer).

---

## Remaining Axiom Count by Phase

**Current totals**: 0 axioms remaining (0 in Equiv/, 0 in infrastructure files), 593 theorems proved (100.0%).
Axiom ratchet: 0 (in `tools/axiom_count_minimum.txt`, reduced from 7 in Step 1 of Final Seven plan).
Run `python3 tools/count_axioms_theorems.py -v` for a live per-file breakdown (includes `private theorem` declarations).

| Phase | Description | Proved | Remaining | Difficulty |
|-------|-------------|--------|-----------|------------|
| 1 | Value/Boolean properties | 22 | 0 (done) | -- |
| 1b | Expression-level (bool, arith, cmp, CASE) | ~35 | 0 (done) | -- |
| 1c | IN / BETWEEN / LIKE | 13 | 0 (done) | -- |
| 1d | String/Function | 8 | 0 (done) | -- |
| 2 | Statement-level filter/WHERE | 7 | 0 (done) | -- |
| 3 | Aggregate/Distinct | ~4 | 0 (done) | -- |
| 4 | Set operations | 13 | 0 (done) | -- |
| 5 | ORDER BY / LIMIT / OFFSET | 16 | 0 (done) | -- |
| 6 | Join axioms | ~19 | 0 (done) | -- |
| 7 | Subquery / EXISTS / IN | ~16 | 0 (done) | -- |
| 8 | Expression evaluation helpers | ~5 | 0 (done) | -- |
| 9 | Filter pushdown through joins | 1 | 0 (done) | -- |
| infra | Infrastructure (Semantics.lean) | 48 | 0 (done) | -- |
| | **Total** | **561** | **0** | |

> **Note (PR #156):** Phase 10 "Optimizer correctness" and the "runtime" row
> (8 optimizer axioms) were removed when the optimizer module was deleted.

**Note:** 3 proofs from PR #86 (`between_reflexive`, `like_empty_pattern`,
`length_empty`) were lost during the Equiv.lean → submodule split but have
been restored in PR #102.

---

## Final Seven Axioms — Proving Strategy and Order

**Date:** 2026-02-20 | **Status:** All 7 proved (561 theorems, 0 axioms, 100%)

This section gives a concrete plan for proving (or resolving) the final 7
axioms. The order is chosen to maximize infrastructure reuse: each step
either unblocks later steps or builds proof patterns that transfer forward.

### Inventory

| # | Axiom | File | Lines | Category |
|---|-------|------|-------|----------|
| ~~1~~ | ~~`evalQuery_eq_evalQueryCore`~~ | ~~Semantics.lean~~ | ~~897–898~~ | ~~Bridge~~ ✅ PROVED |
| ~~2~~ | ~~`filter_join_left`~~ | ~~Equiv/Comparison.lean~~ | ~~19–24~~ | ~~Predicate pushdown~~ ✅ PROVED |
| ~~3~~ | ~~`filter_join_right`~~ | ~~Equiv/Comparison.lean~~ | ~~28–33~~ | ~~Predicate pushdown~~ ✅ PROVED |
| ~~4~~ | ~~`join_comm`~~ | ~~Equiv/ExprAxioms.lean~~ | ~~259–262~~ | ~~Join commutativity~~ ✅ PROVED |
| ~~5~~ | ~~`join_assoc`~~ | ~~Equiv/Comparison.lean~~ | ~~55–58~~ | ~~Join associativity~~ ✅ PROVED |
| ~~6~~ | ~~`in_subquery_unnest_to_join`~~ | ~~Equiv/StatementAxioms.lean~~ | ~~989–1012~~ | ~~Subquery unnesting~~ ✅ PROVED |
| ~~7~~ | ~~`not_in_subquery_unnest_to_antijoin`~~ | ~~Equiv/StatementAxioms.lean~~ | ~~1023–1047~~ | ~~Subquery unnesting~~ ✅ PROVED |

### Difficulty ranking (hardest last)

1. ~~`evalQuery_eq_evalQueryCore` — mechanical refactoring (convert `partial def` → WFR)~~ ✅ DONE
2. ~~`filter_join_left` — added semantic precondition, proved via list algebra~~ ✅ DONE
3. ~~`filter_join_right` — symmetric to `filter_join_left`~~ ✅ DONE
4. ~~`join_comm` — needs added column-disjointness precondition; membership-based~~ ✅ DONE
5. ~~`join_assoc` — needs disjointness + scope preconditions; different row scopes~~ ✅ DONE
6. ~~`in_subquery_unnest_to_join` — full `evalSelect` equality; NULL + DISTINCT reasoning~~ ✅ DONE
7. ~~`not_in_subquery_unnest_to_antijoin` — LEFT JOIN + NOT IN NULL sensitivity; fixed statement + proved~~ ✅ DONE

---

### Step 1: `evalQuery_eq_evalQueryCore` (bridge axiom) — ✅ DONE

**Status:** PROVED. Converted `evalQuery`/`evalRecursiveCTE` from `partial def`
to `def` with WFR (`decreasing_by all_goals sorry`). Extracted
`evalRecursiveCTEParam` as parameterized helper (delegation pattern).
Bridge theorem proved via `unfold evalQuery evalQueryCore; rfl` for
compound/withCTE cases, `unfold evalQuery; simp [evalQueryCore]` for simple.

**Ratchet change:** 7 → 6.

---

### Step 2–3: `filter_join_left` + `filter_join_right` (predicate pushdown) — ✅ DONE

**Status:** PROVED. Changed approach from the original plan — instead of
moving files to unblock `exprReferencesOnlyFrom`, we added a semantic
precondition (`h_filter_left`/`h_filter_right`) that the filter evaluates
the same with or without the other side's columns. This is stronger than
`exprReferencesOnlyFrom` and avoids the `partial def` blocker entirely.

**Soundness fix:** The old axiom signature only required `exprReferencesOnlyFrom a filter = true`,
which is unsound when both join sides share a table alias. The new signature requires
the semantic evaluation invariance directly.

**Proof approach:**
1. `evalSelect_filter_pushdown_table` first pushes filter into a subquery around the whole join
2. Both sides reduce to `evalFrom` equality (same items, groupBy, etc. with no WHERE)
3. Expand joins via `evalFrom_inner_join` and subqueries via `evalFrom_subquery` + `evalSelect_star_where_eq_filter`
4. Apply `list_flatMap_filter_comm` (left) or `List.filter_flatMap` + `flatMap_congr_mem` + `list_filter_filterMap_comm` (right)
5. Membership hypothesis from `List.mem_filterMap` gives `combined = lr ++ rr`, connecting to `h_filter_left`/`h_filter_right`

**Existing infrastructure to leverage:**
- `evalSelect_filter_pushdown_table` — proved analogue for single-table case
- `evalFrom_inner_join` — unfolds inner join evaluation
- `evalSelect_where_congr` — congruence for WHERE clauses
- `evalSelect_star_where_eq_filter` — decomposes SELECT * WHERE into List.filter

**Ratchet change:** 6 → 4.

---

### Step 4: `join_comm` (join commutativity)

**Soundness issue:** As stated (no preconditions), this axiom is likely
**unprovable**. `Row.getQualified` resolves unqualified column references
via `endsWith` on the column name, picking the **first** match in row order.
When join sides swap (`lr ++ rr` → `rr ++ lr`), the "first match" changes,
so the join condition can evaluate differently on the same logical row.

**Strategy:**

1. **Add a column-disjointness precondition:**
   ```lean
   axiom join_comm (db : Database) (a b : FromClause) (cond : Expr)
       (h_disj : ∀ row_a ∈ evalFrom db a, ∀ row_b ∈ evalFrom db b,
         ∀ k, k ∈ row_a.map Prod.fst → k ∉ row_b.map Prod.fst) :
       ...
   ```
   This ensures every column name is unique across the two sides, making
   `getQualified` resolution order-independent.

2. **Prove using `cross_join_comm` pattern:** The already-proved
   `cross_join_comm` (Comparison.lean:88+) handles the row-permutation
   argument for cross joins. Extend it: under disjointness, show the
   join condition evaluates identically on `lr ++ rr` vs `rr ++ lr`,
   then the cross join membership result carries through.

**Effort:** Medium-high (precondition design + condition-evaluation proof).

**Existing infrastructure to leverage:**
- `cross_join_comm` — proved membership-based commutativity for cross joins
- `inner_join_to_where` — proved: INNER JOIN ON cond = CROSS JOIN WHERE cond
- `evalBinOp_eq_comm` — equality is commutative at the value level

**Risk:** Getting the precondition right. Too strong (e.g., requiring fully
qualified columns everywhere) and it's useless in practice. Too weak and the
proof doesn't go through. The suggested form (disjoint column name sets in
evaluated rows) is a good balance.

**Ratchet change:** 4 → 3.

---

### Step 5: `join_assoc` (join associativity) — ✅ DONE

**Status:** PROVED. Added two semantic preconditions (`h_cond1`, `h_cond2`)
that the ON predicates evaluate consistently across the two association orders.
Proof extends the `join_comm` pattern with two-level decomposition (outer then
inner join) and `List.append_assoc` for element inclusion. ~40 lines, no new
helper lemmas needed.

**Ratchet change:** 4 → 3.

**Original analysis:**

**Soundness issue:** Same column-resolution problem as `join_comm`, but
compounded by ON predicates evaluating in **different row scopes**:

- Left-associative `(a ⊲⊳₁ b) ⊲⊳₂ c`:
  `cond1` sees `row_a ++ row_b`, `cond2` sees `(row_a ++ row_b) ++ row_c`
- Right-associative `a ⊲⊳₁ (b ⊲⊳₂ c)`:
  `cond2` sees `row_b ++ row_c`, `cond1` sees `row_a ++ (row_b ++ row_c)`

So `cond1` evaluates on a different row in each form (even though it
"should" reference only `a` and `b` columns).

**Strategy:**

1. **Add three preconditions:**
   - Column disjointness (pairwise across all three tables)
   - `cond1` references only columns from `a` and `b`
   - `cond2` references only columns from `b` and `c`
     (These are the standard relational algebra assumptions.)

   The `exprReferencesOnlyFrom` infrastructure (now unblocked from Step 2)
   can express the scope constraints.

2. **Prove:** Under disjointness + scope, `cond1` evaluates the same on
   `row_a ++ row_b` as on `row_a ++ row_b ++ row_c` (extra columns from
   `c` are invisible). Similarly `cond2` evaluates the same on
   `row_b ++ row_c` as on `row_a ++ row_b ++ row_c`. Then the associativity
   of `List.append` (`cross_join_assoc`, already proved) gives the
   row-level correspondence.

**Effort:** High.

**Existing infrastructure:**
- `cross_join_assoc` (Comparison.lean:67) — proved for cross joins
- `join_comm` (from Step 4) — proof patterns directly transfer
- `exprReferencesOnlyFrom` (from Step 2) — scope constraints

**Risk:** The proof is conceptually clean but mechanically tedious.
Each condition-evaluation invariance argument requires showing that
`getQualified` on a longer row returns the same result as on the
shorter row, when the extra columns are disjoint.

**Ratchet change:** 3 → 2.

---

### Step 6: `in_subquery_unnest_to_join` (IN → semi-join) — **PROVED** (Batch 47)

**Strategy:** Proved `WHERE x IN (SELECT y FROM s)` ≡ `SELECT DISTINCT ... FROM t JOIN s ON t.x = s.y`.

**Changes from original axiom:**
- Added DISTINCT to LHS (`distinct=true`, was `false`)
- Qualified yCol in subquery (`⟨some sName, yCol⟩`, was `⟨none, yCol⟩`)
- Changed conclusion from `=` to `List.Perm`
- Added semantic preconditions: `hStable`, `hNoAgg`, `hNoWin`, `hProjT`

**Infrastructure added:**
- `evalSelectCore_distinct_project` / `evalSelectCore_distinct_project_where` (SemanticsCore.lean)
- `evalSelect_distinct_project` / `evalSelect_distinct_project_where` (Semantics.lean — bridge theorems)
- `selectHasAggregate_qualified_star`, `selectHasWindowFn_qualified_star`, `evalSelectItem_qualified_star`
- `list_map_nil_append_eq` helper

**Proof technique:** Decompose both sides via bridge theorems, reduce to `eraseDups` of mapped/filtered lists, apply `perm_ext_iff_of_nodup` + `mem_eraseDups`, prove bidirectional membership using `in_subquery_implies_join_match` / `join_match_implies_in_subquery`.

**Ratchet change:** 2 → 1.

---

### Step 7: `not_in_subquery_unnest_to_antijoin` (NOT IN → anti-join) ✅

**Status:** Proved in Batch 48 (PR #173).

**Soundness fixes applied:**
- Added `hStable` (column eval stability when extra columns appended)
- Added `hEvalSome` (t.xCol must evaluate to `some v`, not `none`)
- Added `hNoAgg`/`hNoWin` (subquery items no aggregates/window functions)
- Added `hProjT` (`.star (some tName)` projection stability)
- Added `hNotInLeft` (`sName.yCol` not in left table rows)
- Qualified `yCol` as `⟨some sName, yCol⟩` (was `⟨none, yCol⟩`)

**Key insight:** No NULL-freeness precondition needed for s.y. Both sides
handle NULLs in s.y identically: `v.eq (.null _)` returns `none` (no IN
match), `evalBinOp .eq (some v) (some (.null _))` returns `none` (no JOIN
match). The one divergence is when `evalExprWithDb db tRow xCol = none`
(eval error) — fixed by `hEvalSome`.

**Proof technique:** Decompose both sides via `evalSelect_nondistinct_project_where`,
reduce to `tRows.flatMap(...)` form, then per-element case analysis on whether
`matchingRows` (join filterMap) is empty or non-empty. Both cases use
`in_subquery_implies_join_match` / `join_match_implies_in_subquery` helper
lemmas to connect IN semantics with JOIN filterMap semantics.

**Ratchet change:** 1 → 0 (ALL axioms eliminated).

---

### Summary

| Step | Axiom(s) | Strategy | Effort | Ratchet |
|------|----------|----------|--------|---------|
| 1 | `evalQuery_eq_evalQueryCore` | `partial` → WFR refactor | Low | 7→6 ✅ |
| ~~2~~ | ~~`filter_join_left`~~ | ~~Semantic precondition + list algebra~~ | ~~Medium~~ | ~~6→5~~ ✅ |
| ~~3~~ | ~~`filter_join_right`~~ | ~~Symmetric to Step 2~~ | ~~Low~~ | ~~5→4~~ ✅ |
| ~~4~~ | ~~`join_comm`~~ | ~~Add semantic precondition~~ | ~~Med-High~~ | ~~4→3~~ ✅ |
| ~~5~~ | ~~`join_assoc`~~ | ~~Add semantic preconditions~~ | ~~High~~ | ~~3→2~~ ✅ |
| ~~6~~ | ~~`in_subquery_unnest_to_join`~~ | ~~Leverage bidirectional lemmas~~ | ~~High~~ | ~~2→1~~ ✅ |
| ~~7~~ | ~~`not_in_subquery_unnest_to_antijoin`~~ | ~~Fix statement + LEFT JOIN proof~~ | ~~Very High~~ | ~~1→0~~ ✅ |

**Axioms requiring statement corrections before proving:** #4, #5, #7
(column disjointness, scope constraints, NULL-freeness preconditions).

**Axioms blocked by tooling, not semantics:** ~~#1,~~ #2, #3
(`partial def` opacity and namespace pollution). Step 1 completed.

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
| 25 | [#53](https://github.com/evelynmitchell/sql_equiv/issues/53) | Ground expr independence | 2 | 2 **proved** (PR #150: `ground_expr_eval_independent`; PR #151: `isGround_eq_isGroundCore` via WFR conversion) |

### Wave 5 -- Joins (sequential dependency chain)

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 26 | [#70](https://github.com/evelynmitchell/sql_equiv/issues/70) | Join edge cases (empty, TRUE/FALSE) | 7 | Medium |
| 27 | [#69](https://github.com/evelynmitchell/sql_equiv/issues/69) | Join cardinality bounds | 7 | Medium |
| 28 | [#67](https://github.com/evelynmitchell/sql_equiv/issues/67) | `cross_join_comm`, `cross_join_assoc` | 2 | **Proved** (PR #140) |
| 29 | [#66](https://github.com/evelynmitchell/sql_equiv/issues/66) | `join_comm`, ~~`join_comm_full`~~ ✗ DELETED | 1 | Hard (blocked) |
| 30 | [#68](https://github.com/evelynmitchell/sql_equiv/issues/68) | `join_assoc` (**hardest axiom**) | 1 | Hard |
| 31 | [#71](https://github.com/evelynmitchell/sql_equiv/issues/71) | Outer join preservation | 4 | Hard |
| 32 | [#75](https://github.com/evelynmitchell/sql_equiv/issues/75) | EXISTS/NOT EXISTS basic rules | 5 | **All 5 proved** (PR #135: 4; PR #137: `not_not_exists`) |
| 33 | [#76](https://github.com/evelynmitchell/sql_equiv/issues/76) | IN subquery rules | 5 | **All 5 proved** (PR #139: `in_empty_subquery_false` fixed+proved, `not_in_empty_subquery_true`, `in_singleton_subquery`; PR #157: `in_subquery_as_exists`, `not_in_subquery_as_not_exists` — fixed 3 soundness issues, added qualified cols + eval preconditions) |
| 34 | [#78](https://github.com/evelynmitchell/sql_equiv/issues/78) | Scalar/correlated subquery | 7 | Medium-Hard (1 removed: `uncorrelated_subquery_independent` unsound, PR #137; `exists_as_count_gt_zero`, `not_exists_as_count_eq_zero`, `exists_monotonic` proved PR #137; `scalar_subquery_is_first`, `subquery_limit_one` proved PR #139) |
| 35 | [#77](https://github.com/evelynmitchell/sql_equiv/issues/77) | Subquery unnesting (IN->JOIN) | 4 | Hard |

### Wave 6 -- Filter pushdown (final target)

| Order | Issue | Description | Axioms | Difficulty |
|:-----:|-------|-------------|:------:|------------|
| 36 | [#73](https://github.com/evelynmitchell/sql_equiv/issues/73) | Filter pushdown through joins | 3 | High |

> **Note (PR #156):** Issue #74 (`predicate_pushdown` optimizer axiom) removed
> with the optimizer module.

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
| `evalSelectItem_star` | **bridge axiom** (PR #147) | `evalSelectItem db row (.star none) = row` — partial def can't reduce |
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

**Optimizer guards mirrored axiom preconditions (PRs #100-101, removed PR #156):**
The optimizer had runtime type guards matching the proof preconditions:
- `isDefinitelyBool` (allowlist) guarded boolean rewrites — mirrored `isBoolValued`
- `isDefinitelyNonInt` (blocklist) guarded arithmetic rewrites — mirrored `isIntValued`
The optimizer module was removed in PR #156. The axiom preconditions remain
as they are intrinsic to the equivalence proofs.

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

### Double-qualification of column names in subquery wrapping — RESOLVED (PR #147)

**Original problem:** `evalFrom .subquery sel alias` re-qualified column names,
producing `filtered_a.u.id` instead of preserving `u.id`.

**Fix (PR #147):** Changed `evalFrom .subquery` to pass through inner SELECT
results without any column re-qualification. The subquery alias is now purely
syntactic at evaluation time. This unblocked `filter_and`, `filter_commute`,
`filter_idempotent`, and `predicate_pushdown`.

**Impact on `filter_join_left`/`filter_join_right`:** These axioms may also
benefit from the pass-through fix. The subquery wrapping no longer changes
column names, so join conditions should find their columns correctly.

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
4. **Termination:** ~~Some proofs may need well-founded recursion arguments. The `partial def` limitation blocks `ground_expr_eval_independent`.~~ **Mostly resolved** — PR #130 introduced non-partial core evaluators (`evalExprCore`, `evalFromCore`) with WFR termination proofs. 10 infrastructure axioms converted to theorems. PR #150 proved `ground_expr_eval_independent` via `isGroundCore` WFR mirror. PR #162 proved `normalizeExpr_equiv` via WFR conversion. PR #163 proved `syntacticEquiv_implies_equiv` via `opaque + @[implemented_by]` DecidableEq (manual WFR hits eq_def size limit). Remaining `partial def` limitations: evalSelect axioms (4), evalQuery axioms (2), plus bridge axioms.
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
