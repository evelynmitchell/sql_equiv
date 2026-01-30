# Optimizer Formal Verification Plan

This document outlines the full formal verification strategy for the advanced query optimizer using Lean 4's proof system.

---

## Verification Goals

### Primary Goal
Prove that all optimizer transformations preserve query semantics:
```lean
∀ (db : Database) (stmt : SelectStmt),
  evalSelect db (optimizeSelectAdvanced stmt) = evalSelect db stmt
```

### Secondary Goals
1. **Termination** - All functions terminate on valid inputs
2. **Idempotency** - `normalize (normalize e) = normalize e`
3. **Completeness** - Safety checks don't reject valid transformations
4. **Determinism** - Same input always produces same output

---

## Verification by Component

### PR 0: Shared Utilities

These are structural utilities with no semantic claims. Verify structural properties only.

#### Theorems to Prove

```lean
-- Flatten/Unflatten roundtrip
theorem flattenAnd_unflattenAnd_equiv (e : Expr) :
  ∃ e', unflattenAnd (flattenAnd e) = some e' ∧ e' ≃ₑ e

theorem flattenOr_unflattenOr_equiv (e : Expr) :
  ∃ e', unflattenOr (flattenOr e) = some e' ∧ e' ≃ₑ e

-- Flatten produces non-empty list for valid expressions
theorem flattenAnd_nonempty (e : Expr) : (flattenAnd e).length ≥ 1

theorem flattenOr_nonempty (e : Expr) : (flattenOr e).length ≥ 1

-- Column extraction completeness
theorem getReferencedColumns_complete (e : Expr) (c : ColumnRef) :
  exprRefersToColumn c e = true → c ∈ getReferencedColumns e

-- Column extraction soundness
theorem getReferencedColumns_sound (e : Expr) (c : ColumnRef) :
  c ∈ getReferencedColumns e → exprRefersToColumn c e = true

-- getTableName matches existing pattern
theorem getTableName_spec (t : TableRef) :
  getTableName t = t.alias.getD t.name
```

#### Proof Strategy
- Structural induction on `Expr`
- Most proofs are straightforward case analysis
- No semantic reasoning required

#### Estimated Effort: 1-2 days

---

### PR A: Expression Normalization

#### Core Theorem
```lean
theorem normalizeExprCanonical_equiv (e : Expr) :
  normalizeExprCanonical e ≃ₑ e
```

#### Supporting Lemmas

```lean
-- Commutativity lemmas (foundation for reordering)
theorem and_comm_equiv (a b : Expr) :
  Expr.binOp .and a b ≃ₑ Expr.binOp .and b a

theorem or_comm_equiv (a b : Expr) :
  Expr.binOp .or a b ≃ₑ Expr.binOp .or b a

theorem add_comm_equiv (a b : Expr) :
  Expr.binOp .add a b ≃ₑ Expr.binOp .add b a

theorem mul_comm_equiv (a b : Expr) :
  Expr.binOp .mul a b ≃ₑ Expr.binOp .mul b a

theorem eq_comm_equiv (a b : Expr) :
  Expr.binOp .eq a b ≃ₑ Expr.binOp .eq b a

-- Associativity lemmas (foundation for flattening)
theorem and_assoc_equiv (a b c : Expr) :
  Expr.binOp .and (Expr.binOp .and a b) c ≃ₑ
  Expr.binOp .and a (Expr.binOp .and b c)

theorem or_assoc_equiv (a b c : Expr) :
  Expr.binOp .or (Expr.binOp .or a b) c ≃ₑ
  Expr.binOp .or a (Expr.binOp .or b c)

-- Permutation preserves equivalence (for sorting)
theorem and_perm_equiv (es1 es2 : List Expr) (h : es1 ~ es2) :
  unflattenAnd es1 ≃ₑ unflattenAnd es2

theorem or_perm_equiv (es1 es2 : List Expr) (h : es1 ~ es2) :
  unflattenOr es1 ≃ₑ unflattenOr es2

-- Congruence: normalization of subexpressions preserves equivalence
theorem binOp_congr (op : BinOp) (l1 l2 r1 r2 : Expr)
  (hl : l1 ≃ₑ l2) (hr : r1 ≃ₑ r2) :
  Expr.binOp op l1 r1 ≃ₑ Expr.binOp op l2 r2

theorem unaryOp_congr (op : UnaryOp) (e1 e2 : Expr) (h : e1 ≃ₑ e2) :
  Expr.unaryOp op e1 ≃ₑ Expr.unaryOp op e2

-- Idempotency
theorem normalizeExprCanonical_idempotent (e : Expr) :
  normalizeExprCanonical (normalizeExprCanonical e) = normalizeExprCanonical e

-- Determinism
theorem normalizeExprCanonical_deterministic (e : Expr) :
  ∀ e1 e2, normalizeExprCanonical e = e1 → normalizeExprCanonical e = e2 → e1 = e2
```

#### Proof Strategy

1. **Base cases** (lit, col, countStar): Trivial - function returns input unchanged
2. **Commutative ops** (and, or, add, mul, eq):
   - Use commutativity lemma to show any permutation is equivalent
   - Sorting produces a permutation, so sorted result ≃ₑ original
3. **Non-commutative ops**:
   - Induction on structure
   - Use congruence lemma with IH on subexpressions
4. **Idempotency**:
   - Show output is in canonical form (sorted, flattened)
   - Canonical form is a fixed point of normalization

#### Proof Sketch for Main Theorem
```lean
theorem normalizeExprCanonical_equiv (e : Expr) : normalizeExprCanonical e ≃ₑ e := by
  induction e with
  | lit v => rfl  -- unchanged
  | col c => rfl  -- unchanged
  | binOp op l r ih_l ih_r =>
    cases op with
    | and =>
      -- normalizeExprCanonical flattens, sorts, unflattens
      -- 1. flattenAnd l ++ flattenAnd r produces conjuncts
      -- 2. sorting produces a permutation
      -- 3. unflattenAnd rebuilds AND chain
      -- By and_perm_equiv and flatten_unflatten_equiv, result ≃ₑ original
      apply and_perm_equiv
      · exact flatten_produces_permutation l r
      · exact ih_l
      · exact ih_r
    | or => similar
    | add =>
      -- Either swapped or not; both ≃ₑ original by add_comm_equiv
      by_cases h : exprCompare (normalizeExprCanonical l) (normalizeExprCanonical r) == .gt
      · simp [normalizeExprCanonical, h]
        calc Expr.binOp .add nr nl
            ≃ₑ Expr.binOp .add nl nr := add_comm_equiv nr nl
          _ ≃ₑ Expr.binOp .add l r := binOp_congr .add ih_l ih_r
      · simp [normalizeExprCanonical, h]
        exact binOp_congr .add ih_l ih_r
    -- ... other cases
  | unaryOp op e ih => exact unaryOp_congr op ih
  | func name args ih => exact func_congr name ih
  -- ... remaining cases
```

#### Estimated Effort: 3-5 days

---

### PR B: Predicate Pushdown

#### Core Theorem
```lean
theorem pushPredicateDown_correct (pred : Expr) (from_ : FromClause) :
  let result := pushPredicateDown pred from_
  ∀ db,
    evalFrom db result.pushedFrom |>.filterByOpt result.remaining =
    evalFrom db from_ |>.filter (evalPred db pred)
```

Where `filterByOpt` is:
```lean
def Table.filterByOpt (t : Table) (pred : Option Expr) : Table :=
  match pred with
  | none => t
  | some p => t.filter (evalPred db p)
```

#### Supporting Lemmas

```lean
-- Filter distribution over INNER JOIN
theorem filter_inner_join_left (db : Database) (a b : FromClause)
  (cond pred : Expr) (h : exprReferencesOnlyFrom a pred) :
  (evalFrom db (.join a .inner b (some cond))).filter (evalPred db pred) =
  evalFrom db (.join (filterFrom a pred) .inner b (some cond))

theorem filter_inner_join_right (db : Database) (a b : FromClause)
  (cond pred : Expr) (h : exprReferencesOnlyFrom b pred) :
  (evalFrom db (.join a .inner b (some cond))).filter (evalPred db pred) =
  evalFrom db (.join a .inner (filterFrom b pred) (some cond))

-- Filter can move to ON clause for INNER JOIN
theorem filter_to_on_clause (db : Database) (a b : FromClause)
  (cond pred : Expr) :
  (evalFrom db (.join a .inner b (some cond))).filter (evalPred db pred) =
  evalFrom db (.join a .inner b (some (Expr.binOp .and cond pred)))

-- LEFT JOIN: can only push to left side
theorem filter_left_join_left (db : Database) (a b : FromClause)
  (cond pred : Expr) (h : exprReferencesOnlyFrom a pred) :
  (evalFrom db (.join a .left b (some cond))).filter (evalPred db pred) =
  evalFrom db (.join (filterFrom a pred) .left b (some cond))

-- LEFT JOIN: CANNOT push to right side (would change NULL behavior)
-- This is a negative result - we prove pushing is INCORRECT
theorem filter_left_join_right_incorrect (db : Database) :
  ∃ a b cond pred,
    exprReferencesOnlyFrom b pred ∧
    (evalFrom db (.join a .left b (some cond))).filter (evalPred db pred) ≠
    evalFrom db (.join a .left (filterFrom b pred) (some cond))

-- Safety check correctness
theorem canPushLeftThroughJoin_sound (jtype : JoinType) (pred : Expr)
  (a b : FromClause) (cond : Expr) (h : exprReferencesOnlyFrom a pred) :
  canPushLeftThroughJoin jtype = true →
  (evalFrom db (.join a jtype b (some cond))).filter (evalPred db pred) =
  evalFrom db (.join (filterFrom a pred) jtype b (some cond))

theorem canPushPastGroupBy_sound (pred : Expr) (groupBy : List Expr)
  (h : canPushPastGroupBy pred groupBy = true) :
  -- Predicate can be evaluated before grouping
  ∀ db rows,
    (groupAndAggregate db groupBy rows).filter (evalPred db pred) =
    groupAndAggregate db groupBy (rows.filter (evalPred db pred))

-- Conjunct splitting
theorem filter_and_split (db : Database) (t : Table) (p1 p2 : Expr) :
  t.filter (evalPred db (Expr.binOp .and p1 p2)) =
  (t.filter (evalPred db p1)).filter (evalPred db p2)
```

#### Proof Strategy

1. **Define filterFrom helper**:
   ```lean
   def filterFrom (from_ : FromClause) (pred : Expr) : FromClause :=
     .subquery (SelectStmt.mk false [.star none] (some from_) (some pred) [] none [] none none) "filtered"
   ```

2. **Base case (.table)**: Cannot push past base table; remaining = pred
3. **Subquery case**: Push into subquery's WHERE if columns available
4. **Join case**:
   - Split predicate into conjuncts
   - For each conjunct, determine which side it references
   - Apply appropriate filter_*_join_* lemma
   - Combine remaining conjuncts

#### Key Insight
The proof relies on the fact that `filter (p1 AND p2)` = `filter p1 ∘ filter p2`, which allows us to handle each conjunct independently and combine results.

#### Estimated Effort: 5-7 days

---

### PR C: Join Reordering

#### Core Theorem
```lean
theorem reorderJoins_correct (from_ : FromClause)
  (h : canReorderJoins from_ = true) :
  ∀ db, evalFrom db (reorderJoins from_) = evalFrom db from_
```

#### Supporting Lemmas

```lean
-- INNER JOIN commutativity
theorem inner_join_comm (db : Database) (a b : FromClause) (cond : Expr) :
  evalFrom db (.join a .inner b (some cond)) =
  evalFrom db (.join b .inner a (some cond))

-- INNER JOIN associativity
theorem inner_join_assoc (db : Database) (a b c : FromClause) (c1 c2 : Expr) :
  evalFrom db (.join (.join a .inner b (some c1)) .inner c (some c2)) =
  evalFrom db (.join a .inner (.join b .inner c (some c2)) (some c1))

-- CROSS JOIN commutativity
theorem cross_join_comm (db : Database) (a b : FromClause) :
  evalFrom db (.join a .cross b none) =
  evalFrom db (.join b .cross a none)

-- CROSS JOIN associativity
theorem cross_join_assoc (db : Database) (a b c : FromClause) :
  evalFrom db (.join (.join a .cross b none) .cross c none) =
  evalFrom db (.join a .cross (.join b .cross c none) none)

-- Safety check correctness: hasOnlyInnerJoins implies reordering is valid
theorem hasOnlyInnerJoins_enables_reorder (from_ : FromClause)
  (h : hasOnlyInnerJoins from_ = true) :
  ∀ perm : FromClause, isValidReordering from_ perm →
    ∀ db, evalFrom db perm = evalFrom db from_

-- Edge matching correctness
theorem edgeConnects_correct (edge : JoinEdge) (n1 n2 : JoinNode) :
  edgeConnects edge n1 n2 = true ↔
  (edge.leftTable ∈ n1.originalTables ∧ edge.rightTable ∈ n2.originalTables) ∨
  (edge.rightTable ∈ n1.originalTables ∧ edge.leftTable ∈ n2.originalTables)

-- originalTables preservation through combine
theorem combine_preserves_tables (n1 n2 : JoinNode) (cost : Nat) :
  (JoinNode.combine n1 n2 cost).originalTables =
  n1.originalTables ++ n2.originalTables

-- Greedy algorithm produces valid reordering
theorem greedy_produces_valid_reordering (nodes : List JoinNode) (edges : List JoinEdge) :
  isValidReordering (extractFrom nodes edges) (greedyReorder nodes edges)
```

#### Proof Strategy

1. **Extract join graph**: Convert FromClause to (nodes, edges)
2. **Prove graph operations preserve semantics**:
   - Combining two nodes = performing that join
   - Edge matching correctly identifies applicable predicates
3. **Prove greedy algorithm correctness**:
   - Each step combines two nodes with a valid edge
   - Result is a valid reordering (same tables, same predicates)
4. **Use commutativity/associativity**:
   - Any valid reordering is semantically equivalent
   - Greedy produces valid reordering → result ≃ original

#### Key Insight
The proof works because INNER/CROSS joins form a commutative monoid under join composition. Any permutation of the join order produces the same result (given the same predicates are applied).

#### Estimated Effort: 7-10 days

---

## Integration Verification

After PRs A, B, C are verified:

```lean
theorem optimizeSelectAdvanced_correct (sel : SelectStmt) :
  optimizeSelectAdvanced sel ≃ₛ sel := by
  unfold optimizeSelectAdvanced
  -- 1. optimizeSelectStmt preserves semantics (existing axiom)
  have h1 : optimizeSelectStmt sel ≃ₛ sel := optimizeSelectStmt_equiv sel
  -- 2. normalizeExprCanonical preserves semantics (PR A)
  have h2 : ... ≃ₛ ... := normalizeExprCanonical_preserves_select ...
  -- 3. reorderJoins preserves semantics (PR C)
  have h3 : ... ≃ₛ ... := reorderJoins_correct ...
  -- 4. pushPredicateDown preserves semantics (PR B)
  have h4 : ... ≃ₛ ... := pushPredicateDown_correct ...
  -- Chain equivalences
  exact trans h1 (trans h2 (trans h3 h4))
```

---

## Proof Dependencies Graph

```
                    ┌─────────────────────┐
                    │   Equivalence Defns │
                    │  (ExprEquiv, etc.)  │
                    └──────────┬──────────┘
                               │
              ┌────────────────┼────────────────┐
              │                │                │
              ▼                ▼                ▼
    ┌─────────────────┐ ┌─────────────┐ ┌─────────────────┐
    │  Commutativity  │ │Associativity│ │   Congruence    │
    │  (and_comm,etc) │ │ (and_assoc) │ │  (binOp_congr)  │
    └────────┬────────┘ └──────┬──────┘ └────────┬────────┘
             │                 │                 │
             └────────────┬────┴─────────────────┘
                          │
                          ▼
              ┌───────────────────────┐
              │   PR 0: Structural    │
              │  (flatten, unflatten) │
              └───────────┬───────────┘
                          │
         ┌────────────────┼────────────────┐
         │                │                │
         ▼                ▼                ▼
   ┌───────────┐   ┌─────────────┐   ┌───────────┐
   │   PR A    │   │    PR B     │   │   PR C    │
   │ normalize │   │  pushdown   │   │ reorder   │
   └─────┬─────┘   └──────┬──────┘   └─────┬─────┘
         │                │                │
         └────────────────┼────────────────┘
                          │
                          ▼
              ┌───────────────────────┐
              │     Integration       │
              │ optimizeSelectAdvanced│
              └───────────────────────┘
```

---

## What Must Remain Axiomatized

Some properties require axioms because they depend on:
1. **Database semantics** - How `evalFrom` actually works
2. **Three-valued logic** - NULL handling in SQL
3. **Aggregate semantics** - How GROUP BY interacts with filtering

```lean
-- These are axioms (not provable without full semantics implementation)
axiom evalBinOp_and_comm (v1 v2 : Value) :
  evalBinOp .and v1 v2 = evalBinOp .and v2 v1

axiom evalBinOp_and_assoc (v1 v2 v3 : Value) :
  evalBinOp .and (evalBinOp .and v1 v2) v3 =
  evalBinOp .and v1 (evalBinOp .and v2 v3)

axiom evalFrom_join_comm (db : Database) (a b : FromClause) (cond : Expr) :
  evalFrom db (.join a .inner b (some cond)) =
  evalFrom db (.join b .inner a (some cond))
```

---

## Verification Effort Summary

| Component | Theorems | Estimated Days | Difficulty |
|-----------|----------|----------------|------------|
| Equivalence foundations | 10 | 2 | Low |
| PR 0: Structural | 8 | 2 | Low |
| PR A: Normalization | 15 | 5 | Medium |
| PR B: Pushdown | 20 | 7 | High |
| PR C: Reordering | 15 | 10 | High |
| Integration | 5 | 2 | Medium |
| **Total** | **73** | **28 days** | |

---

## Verification Milestones

### Milestone 1: Foundations (Week 1)
- [ ] Define and prove commutativity lemmas
- [ ] Define and prove associativity lemmas
- [ ] Define and prove congruence lemmas
- [ ] Prove PR 0 structural properties

### Milestone 2: Normalization (Week 2)
- [ ] Prove `flattenAnd_unflattenAnd_equiv`
- [ ] Prove `and_perm_equiv`
- [ ] Prove `normalizeExprCanonical_equiv`
- [ ] Prove `normalizeExprCanonical_idempotent`

### Milestone 3: Pushdown (Weeks 3-4)
- [ ] Prove filter distribution lemmas
- [ ] Prove safety check soundness
- [ ] Prove `pushPredicateDown_correct`

### Milestone 4: Reordering (Weeks 4-5)
- [ ] Prove join commutativity/associativity at eval level
- [ ] Prove graph operations correct
- [ ] Prove `reorderJoins_correct`

### Milestone 5: Integration (Week 6)
- [ ] Prove `optimizeSelectAdvanced_correct`
- [ ] Clean up axioms
- [ ] Document any remaining gaps

---

## Testing Strategy (Parallel Track)

While proofs are developed, use property-based testing:

```lean
-- QuickCheck-style properties
def prop_normalize_equiv (e : Expr) (row : Row) : Bool :=
  evalExpr row (normalizeExprCanonical e) == evalExpr row e

def prop_normalize_idempotent (e : Expr) : Bool :=
  normalizeExprCanonical (normalizeExprCanonical e) == normalizeExprCanonical e

def prop_pushdown_equiv (pred : Expr) (from_ : FromClause) (db : Database) : Bool :=
  let result := pushPredicateDown pred from_
  evalAndFilter db result == evalAndFilter db (from_, pred)

-- Run with shrinking on failure
#eval Testable.check (config := { numTests := 1000 }) prop_normalize_equiv
```

This catches bugs before proof effort is invested.

---

## Related Documents

- [OPTIMIZER_REDESIGN_PLAN.md](./OPTIMIZER_REDESIGN_PLAN.md) - Implementation design
- [OPTIMIZER_STATE_VARIABLES.md](./OPTIMIZER_STATE_VARIABLES.md) - State variable specification
