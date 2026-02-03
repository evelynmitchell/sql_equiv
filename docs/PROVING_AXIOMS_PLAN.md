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

### Phase 1: Foundation - Value and Boolean Properties ✅ COMPLETED

**Goal:** Prove properties about value comparison and boolean operations.

**Axioms proved (22 total):**
- `evalBinOp_and_assoc` - AND is associative ✅
- `evalBinOp_or_assoc` - OR is associative ✅
- `evalBinOp_and_or_distrib_left` - AND distributes over OR ✅
- `evalBinOp_or_and_distrib_left` - OR distributes over AND ✅
- `coalesce_int_left`, `coalesce_string_left`, `coalesce_bool_left` ✅
- `coalesce_single_int`, `coalesce_single_string`, `coalesce_single_bool` ✅
- `coalesce_single_null`, `coalesce_empty` ✅
- `nullif_same_int`, `nullif_diff_int` ✅
- `min_singleton`, `max_singleton` ✅
- `distinct_count_le`, `distinct_idempotent`, `count_distinct_le_count` ✅
- `filter_and_eq_filter_filter`, `filter_comm` ✅

**Removed (was unsound):**
- `coalesce_null_left` - deleted; was unsound for null second argument (see Known Soundness Issues). Replaced by `coalesce_null_left_nonnull`.

**Approach used:**
1. Exhaustive case analysis on all `Option Value` constructor triples (for associativity/distributivity)
2. `simp` with `evalFunc`/`isNullValue` unfolding (for COALESCE/NULLIF)
3. Standard library lemmas (for list properties)
4. Induction on list structure (for filter properties)

---

### Phase 2: Expression Evaluation Properties

**Goal:** Prove that expression evaluation is deterministic and respects structure.

**Key lemmas needed:**
```lean
-- Expression evaluation is deterministic
lemma evalExpr_deterministic (db : Database) (row : Row) (e : Expr) :
  ∀ v1 v2, evalExprWithDb db row e = some v1 →
           evalExprWithDb db row e = some v2 → v1 = v2

-- Column reference evaluation depends only on relevant row entries
lemma evalCol_depends_only_on_col (db : Database) (row1 row2 : Row) (c : ColumnRef) :
  row1.lookup (colRefToKey c) = row2.lookup (colRefToKey c) →
  evalExprWithDb db row1 (.col c) = evalExprWithDb db row2 (.col c)
```

**Approach:**
1. Structural induction on `Expr`
2. Case analysis on each constructor
3. Build library of evaluation lemmas

**Estimated complexity:** Medium - many cases but straightforward

---

### Phase 3: Single-Table Filter Properties

**Goal:** Prove filter operations preserve semantics for single tables.

**Target axiom:**
```lean
axiom filter_pushdown_table (db : Database) (t : TableRef) (filter : Expr) ... :
  evalSelect db (... WHERE filter ...) =
  evalSelect db (... FROM (SELECT * FROM t WHERE filter) ...)
```

**Key lemmas:**
```lean
-- Filtering is the same whether done in WHERE or subquery
lemma filter_subquery_equiv (db : Database) (t : TableRef) (pred : Expr) :
  (evalFrom db (.table t)).filter (rowSatisfies db pred) =
  evalFrom db (.subquery (selectWithWhere t pred) _)

-- Filter commutes with itself
lemma filter_filter (rows : Table) (p q : Row → Bool) :
  (rows.filter p).filter q = rows.filter (fun r => p r && q r)
```

**Approach:**
1. Unfold `evalFrom` and `evalSelect` definitions
2. Use list filter properties from Mathlib/Std
3. Show subquery wrapping is identity for simple cases

**Estimated complexity:** Medium

---

### Phase 4: Two-Table Join Properties

**Goal:** Prove commutativity and basic filter pushdown for two-table joins.

**Target axioms:**
```lean
axiom join_comm_full (db : Database) (a b : FromClause) (cond : Expr) :
  evalFrom db (.join a .inner b (some cond)) =
  evalFrom db (.join b .inner a (some cond))

axiom cross_join_comm (db : Database) (a b : FromClause) : ...
```

**Key challenge:** Row representation after join includes columns from both sides.

**Key lemmas needed:**
```lean
-- Join produces rows with columns from both sides
lemma join_row_structure (db : Database) (a b : FromClause) (row : Row) :
  row ∈ evalFrom db (.join a .inner b cond) →
  ∃ rowA rowB, rowA ∈ evalFrom db a ∧ rowB ∈ evalFrom db b ∧
               row = mergeRows rowA rowB ∧ ...

-- Merged rows are equivalent up to column ordering
lemma mergeRows_comm (rowA rowB : Row) :
  (mergeRows rowA rowB).toFinset = (mergeRows rowB rowA).toFinset
```

**Approach:**
1. Define precise semantics for row merging in joins
2. Prove merge is commutative (as sets of key-value pairs)
3. Show condition evaluation is symmetric

**Estimated complexity:** Medium-High

---

### Phase 5: Join Associativity

**Goal:** Prove `(A ⋈ B) ⋈ C ≡ A ⋈ (B ⋈ C)` for INNER/CROSS joins.

**Target axiom:**
```lean
axiom join_assoc (db : Database) (a b c : FromClause) (cond1 cond2 : Expr) :
  ∀ row ∈ evalFrom db (.join (.join a .inner b (some cond1)) .inner c (some cond2)),
  ∃ row' ∈ evalFrom db (.join a .inner (.join b .inner c (some cond2)) (some cond1)), ...
```

**Key challenge:** Predicates may reference columns from multiple tables.

**Approach:**
1. Build on Phase 4 row structure lemmas
2. Show three-way merge is associative
3. Prove condition evaluation respects associative regrouping

**Estimated complexity:** High

---

### Phase 6: Filter Pushdown Through Joins

**Goal:** Prove predicates can be pushed into join operands.

**Target axioms:**
```lean
axiom filter_join_left (db : Database) (a b : FromClause) (cond filter : Expr)
    (h_ref : exprReferencesOnlyFrom a filter = true) : ...

axiom filter_join_right (db : Database) (a b : FromClause) (cond filter : Expr)
    (h_ref : exprReferencesOnlyFrom b filter = true) : ...
```

**Key insight:** If filter only references left table columns, filtering before or after join is equivalent.

**Key lemmas:**
```lean
-- Filter on left-only columns can be pushed
lemma filter_join_push_left (db : Database) (a b : FromClause) (cond filter : Expr)
    (h : exprReferencesOnlyFrom a filter) :
  (evalFrom db (.join a .inner b cond)).filter (rowSatisfies db filter) =
  evalFrom db (.join (filtered a filter) .inner b cond)
```

**Approach:**
1. Use column reference tracking from `exprReferencesOnlyFrom`
2. Show filter evaluation only depends on left columns
3. Prove filtering before join produces same result

**Estimated complexity:** High

---

### Phase 7: Predicate Pushdown Optimization

**Goal:** Prove `pushdown_preserves_semantics`.

**Strategy:** Structural induction on `FromClause`, using Phase 3-6 lemmas.

**Cases:**
1. **Base table:** Use `filter_pushdown_table` (Phase 3)
2. **Subquery:** Induction + projection handling
3. **Join:** Use `filter_join_left/right` (Phase 6) based on `predReferencesOnlyTables`

**Key lemma:**
```lean
lemma pushSinglePredicate_correct (db : Database) (pred : Expr) (from_ : FromClause) :
  let result := pushSinglePredicate pred from_
  filterRows db (evalFrom db result.pushedFrom) result.remaining =
  filterRows db (evalFrom db from_) (some pred)
```

**Approach:**
1. Induction on `FromClause` structure
2. Case analysis matching `pushSinglePredicate` implementation
3. Apply appropriate Phase 3-6 lemmas for each case

**Estimated complexity:** High - ties everything together

---

### Phase 8: Join Reordering Optimization

**Goal:** Prove `join_reorder_preserves_*`.

**Strategy:** Use Phase 4-5 commutativity/associativity lemmas.

**Key insight:** `reorderJoins` only reorders, doesn't change the set of tables or predicates.

**Key lemmas:**
```lean
-- Greedy reordering produces equivalent join tree
lemma greedyReorder_equiv (nodes : List JoinNode) (edges : List JoinEdge) :
  ∀ steps ∈ greedyReorder nodes edges,
  buildFromSteps nodes steps produces equivalent result to any other ordering

-- Building from steps preserves table set
lemma buildFromSteps_tables (nodes : List JoinNode) (steps : List JoinStep) :
  getFromClauseTableNames (buildFromSteps nodes steps) =
  nodes.map (·.table.name)
```

**Approach:**
1. Show any reordering of INNER/CROSS joins is equivalent (using Phase 4-5)
2. Show predicates are preserved during reordering
3. Combine to prove full semantic preservation

**Estimated complexity:** High

---

## Summary: Proof Dependencies

```
pushdown_preserves_semantics
├── filter_join_left (Phase 6)
├── filter_join_right (Phase 6)
├── filter_pushdown_table (Phase 3)
└── filter composition lemmas (Phase 3)

join_reorder_preserves_*
├── join_comm_full (Phase 4)
├── join_assoc (Phase 5)
├── cross_join_comm (Phase 4)
└── cross_join_assoc (Phase 5)

All above depend on:
├── Expression evaluation lemmas (Phase 2)
└── Value/Boolean properties (Phase 1)
```

---

## Tooling Considerations

### Cleanroom Approach
- Define specifications precisely before proving
- Review proof strategies before committing to Lean
- Use stepwise refinement for complex proofs

### Lean 4 Tactics
- `simp` with custom simp lemmas for evaluation
- `induction` on Expr/FromClause structures
- `rcases` for existential elimination
- `ext` for list/set equality

### Mathlib/Std Dependencies
- List filter lemmas
- Decidable equality instances
- Option monad properties

---

## Recommended Starting Point

**Start with Phase 1 and Phase 3** in parallel:
- Phase 1 is self-contained and builds confidence
- Phase 3 (single-table filter) provides immediate value and tests the approach

**First concrete goal:**
```lean
theorem filter_pushdown_table_simple (db : Database) (tname : String) (pred : Expr) :
  (db tname).filter (fun row => evalExprWithDb db row pred == some (.bool true)) =
  (db tname).filter (fun row => evalExprWithDb db row pred == some (.bool true))
```

This is trivially true by reflexivity, but building toward a non-trivial version forces us to understand the semantic model properly.

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

## Open Questions

1. **Row representation:** Should we use `List (String × Value)` or a more structured type?
2. **NULL handling:** Three-valued logic adds complexity - start with two-valued subset?
3. **Column ordering:** Do we need to prove rows are equal as sets or as ordered lists?
4. **Termination:** Some proofs may need well-founded recursion arguments.
5. **Option Value soundness audit:** The unsound `coalesce_null_left` axiom has been removed, but other axioms quantifying over `Option Value` may have similar `none` vs `some (.null _)` confusion. A systematic audit is still recommended.

---

## Timeline Estimate

| Phase | Description | Effort |
|-------|-------------|--------|
| 1 | Value/Boolean properties | 1-2 days |
| 2 | Expression evaluation | 2-3 days |
| 3 | Single-table filter | 2-3 days |
| 4 | Two-table join comm | 3-5 days |
| 5 | Join associativity | 3-5 days |
| 6 | Filter pushdown joins | 5-7 days |
| 7 | Predicate pushdown opt | 5-7 days |
| 8 | Join reordering opt | 5-7 days |

**Total:** ~4-6 weeks of focused effort

This can be parallelized - Phases 1-3 are independent of Phases 4-5.
