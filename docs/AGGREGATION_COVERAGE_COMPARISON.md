# Aggregation Coverage: sql_equiv vs QED Prover

> **Note (Nov 2026):** the legacy `evalAggOverTable` / `groupRowsByKey` named below were removed in #278 step 3; the live functions are `evalAggOverTableParam` / `groupRowsByKeyParam` in `Semantics.lean`.
>
> **Historical snapshot.** Axiom/theorem counts in this document are as of when it was written. As of 2026-11 the codebase has **0 axioms** (all proved since PR #173) and **689 theorems**; run `python3 tools/count_axioms_theorems.py` for the live count.

**Date:** 2026-02-18

## Summary

QED (VLDB 2024) treats aggregation as **uninterpreted** — it compares aggregate
expressions structurally, without knowing what COUNT, SUM, AVG, MIN, or MAX
actually compute. sql_equiv has **interpreted aggregate semantics** with proven
theorems about their behavior. This document maps the exact boundary between what
each system can and cannot prove about aggregation, and recommends a hybrid
strategy.

---

## 1. What "Uninterpreted" Means in QED

QED's `Expr` type (in `shared.rs`) represents aggregates as opaque symbols:

```rust
enum Expr {
    Var(VL, DataType),
    Op(String, Vec<Expr>),      // operators — interpreted (arithmetic, comparison)
    HOp(String, Vec<Relation>), // higher-order ops — UNINTERPRETED
    Agg(String, Vec<Expr>),     // aggregates — UNINTERPRETED
}
```

During SPNF normalization, QED propagates aggregate expressions without
evaluating them. During unification, it checks **structural equality**: two
aggregate expressions are equal iff they have the same function name, the
same arguments, and operate over the same normalized relation.

### What QED can prove (structural equivalences)

QED can prove equivalences where the aggregate structure is preserved through
relational transformations:

```sql
-- Identical structure (trivial)
SELECT SUM(x) FROM t WHERE p
  ≡ SELECT SUM(x) FROM t WHERE p

-- Aggregate over equivalent subquery (relational restructuring)
SELECT SUM(x) FROM (SELECT x FROM t WHERE p)
  ≡ SELECT SUM(x) FROM t WHERE p

-- GROUP BY with equivalent filter pushdown
SELECT dept, COUNT(*) FROM emp WHERE sal > 50000 GROUP BY dept
  ≡ SELECT dept, COUNT(*) FROM (SELECT * FROM emp WHERE sal > 50000) GROUP BY dept

-- Aggregate preserved through join rewrite
SELECT COUNT(*) FROM t1 JOIN t2 ON t1.id = t2.id
  ≡ SELECT COUNT(*) FROM t2 JOIN t1 ON t2.id = t1.id
-- (only if QED can prove the joins equivalent; the COUNT(*) is carried along)
```

### What QED cannot prove (semantic equivalences)

Anything requiring knowledge of what an aggregate function *computes*:

```sql
-- Requires: SUM distributes over addition
SELECT SUM(x) + SUM(y) FROM t  ≢?  SELECT SUM(x + y) FROM t

-- Requires: AVG = SUM / COUNT
SELECT AVG(x) FROM t  ≢?  SELECT SUM(x) / COUNT(x) FROM t

-- Requires: COUNT semantics (counts non-NULL)
SELECT COUNT(x) FROM t  ≢?  SELECT COUNT(*) - COUNT_NULL(x) FROM t

-- Requires: COUNT(*) counts rows vs COUNT(col) counts non-NULLs
SELECT COUNT(*) FROM t  ≢?  SELECT COUNT(1) FROM t

-- Requires: SUM over empty set = NULL, not 0
SELECT COALESCE(SUM(x), 0) FROM t WHERE FALSE  ≢?  SELECT 0

-- Requires: MIN/MAX monotonicity
SELECT MIN(x) FROM t  ≢?  SELECT MIN(x) FROM t WHERE x IS NOT NULL

-- Requires: CASE-aggregate interchange
SELECT COUNT(*) FROM t WHERE p
  ≢?  SELECT SUM(CASE WHEN p THEN 1 ELSE 0 END) FROM t

-- Requires: GROUP BY / HAVING interaction
SELECT dept, SUM(sal) FROM emp GROUP BY dept HAVING SUM(sal) > 100000
  ≢?  SELECT dept, total FROM (SELECT dept, SUM(sal) as total FROM emp GROUP BY dept) WHERE total > 100000
```

The VLDB paper acknowledges this as a significant source of incompleteness,
contributing to many of the ~145 unprovable cases in the Calcite test suite.

---

## 2. What sql_equiv Has

### Interpreted aggregate semantics

`evalAggOverTable` (Semantics.lean:339-374) defines the actual computation:

```lean
def evalAggOverTable (db : Database) (fn : AggFunc) (argExpr : Option Expr)
    (distinct : Bool) (rows : Table) : Option Value :=
  let values := match argExpr with
    | none => []
    | some e => rows.filterMap fun row => evalExprWithDb db row e
  let distinctValues := if distinct then values.eraseDups else values
  match fn with
  | .count => some (.int distinctValues.length)
  | .sum   => if nums.isEmpty then some (.null none)
              else some (.int (nums.foldl (· + ·) 0))
  | .avg   => if nums.isEmpty then some (.null none)
              else some (.int (nums.foldl (· + ·) 0 / nums.length))
  | .min   => match nums with
              | []          => some (.null none)
              | n :: rest   => some (.int (rest.foldl min n))
  | .max   => match nums with
              | []          => some (.null none)
              | n :: rest   => some (.int (rest.foldl max n))
```

This is a **complete operational semantics** for aggregation. Every aggregate
function is defined in terms of `List.foldl`, `List.filterMap`, `List.length`,
and `List.eraseDups` — all of which have extensive Lean/Batteries lemma
libraries.

### Proven aggregate theorems (20 total)

#### COUNT properties

| Theorem | Location | Statement |
|---------|----------|-----------|
| `count_star_nonneg` | Comparison.lean:692 | `rows.length ≥ 0` |
| `count_star_empty` | Comparison.lean:697 | `[].length = 0` |
| `count_star_singleton` | Comparison.lean:700 | `[row].length = 1` |
| `count_after_filter_le` | Comparison.lean:703 | `(rows.filter p).length ≤ rows.length` |
| `distinct_count_le` | Comparison.lean:787 | `vs.eraseDups.length ≤ vs.length` |
| `count_distinct_le_count` | Comparison.lean:848 | `COUNT(DISTINCT) ≤ COUNT` |

#### SUM properties

| Theorem | Location | Statement |
|---------|----------|-----------|
| `sum_empty` | Comparison.lean:708 | `SUM([]) = 0` |
| `sum_singleton` | Comparison.lean:711 | `SUM([n]) = n` |
| `sum_add_zero` | Comparison.lean:715 | `SUM(xs ++ [0]) = SUM(xs)` |

#### MIN/MAX properties

| Theorem | Location | Statement |
|---------|----------|-----------|
| `min_singleton` | Comparison.lean:725 | `MIN([n]) = n` |
| `max_singleton` | Comparison.lean:729 | `MAX([n]) = n` |
| `min_le_elem` | Comparison.lean:773 | `n ∈ ns → MIN(ns) ≤ n` |
| `max_ge_elem` | Comparison.lean:780 | `n ∈ ns → MAX(ns) ≥ n` |

#### DISTINCT properties

| Theorem | Location | Statement |
|---------|----------|-----------|
| `distinct_idempotent` | Comparison.lean:843 | `DISTINCT(DISTINCT(xs)) = DISTINCT(xs)` |

#### EXISTS ↔ COUNT bridge

| Theorem | Location | Statement |
|---------|----------|-----------|
| `exists_as_count_gt_zero` | StatementAxioms.lean:742 | `EXISTS(q) ↔ COUNT(*) > 0` |
| `not_exists_as_count_eq_zero` | StatementAxioms.lean:753 | `NOT EXISTS(q) ↔ COUNT(*) = 0` |

#### Aggregate-aware evaluation guards

| Theorem / Function | Location | Purpose |
|---------|----------|-----------|
| `selectHasAggregate` | Semantics.lean:33 | Detects aggregate presence in SELECT items |
| `where_false_empty` | StatementAxioms.lean:941 | `WHERE FALSE → empty` **only when no aggregates** |
| `selectHasAggregate_star` | Semantics.lean:1084 | `SELECT *` has no aggregates |

The `selectHasAggregate` guard is particularly important: it correctly models
the SQL behavior where `SELECT COUNT(*) FROM t WHERE FALSE` returns **one row**
(with count = 0), not zero rows. QED has no mechanism for this distinction —
it would normalize the WHERE FALSE away without knowing that aggregation
changes empty-set behavior.

### Proof technique

All aggregate theorems reduce to **list induction**:

```lean
-- Example: min_le_elem
theorem min_le_elem (n : Int) (ns : List Int) (h : n ∈ ns) :
    ns.foldl min (ns.head (List.ne_nil_of_mem h)) ≤ n := by
  -- Induction on ns, using foldl_min_le_of_mem helper
  exact foldl_min_le_of_mem _ _ _ h
```

The pattern is: unfold `evalAggOverTable` → expose `List.foldl`/`List.filterMap`
→ apply standard list lemmas → close with `omega` or `simp`.

---

## 3. Coverage Comparison

### By equivalence category

| Category | QED | sql_equiv | Example |
|----------|-----|-----------|---------|
| Aggregate through filter pushdown | Yes | No | `SUM(x) FROM (SELECT x FROM t WHERE p)` ≡ `SUM(x) FROM t WHERE p` |
| Aggregate through join rewrite | Yes | No | Aggregate over rewritten join |
| Aggregate through subquery unnesting | Yes | No | Aggregate over flattened subquery |
| COUNT properties (bounds, empty, etc.) | No | **Yes** (6 theorems) | `COUNT(DISTINCT) ≤ COUNT` |
| SUM algebraic properties | No | **Partial** (3 theorems) | `SUM([]) = 0`, `SUM([n]) = n` |
| MIN/MAX bounds | No | **Yes** (4 theorems) | `MIN(xs) ≤ any element` |
| DISTINCT idempotence | Both | **Yes** (proven) | `DISTINCT(DISTINCT(x)) = DISTINCT(x)` |
| EXISTS ↔ COUNT bridge | No | **Yes** (2 theorems) | `EXISTS(q) ↔ COUNT(*) > 0` |
| Aggregate empty-set behavior | No | **Yes** (guard) | `SELECT COUNT(*) WHERE FALSE` → 1 row |
| SUM distributivity (`SUM(a+b)`) | No | No | Not yet proven in either |
| AVG decomposition (`AVG = SUM/COUNT`) | No | No | Not yet proven in either |
| COUNT(*) vs COUNT(col) | No | No | Not yet proven in either |
| Aggregate pushdown through GROUP BY | No | No | Hard in both systems |

### By proof difficulty

```
             Easy            Medium           Hard           Open research
             ─────────────── ──────────────── ────────────── ───────────────
sql_equiv:   count_empty     min_le_elem      SUM(a+b)       Aggregate pushdown
             count_singleton max_ge_elem      AVG=SUM/COUNT  through GROUP BY
             sum_empty       distinct_count   COUNT(*)≡
             sum_singleton   EXISTS↔COUNT     COUNT(1)       Window-aggregate
             min_singleton                                    interaction
             max_singleton

QED:         (structural     (structural      (nothing —     (nothing —
             matches are     matches through  uninterpreted) uninterpreted)
             trivial)        join rewrites)
```

---

## 4. The Hybrid Strategy

### Principle

Use each tool where it's strongest:

```
┌─────────────────────────────────────────────────────────────┐
│                   SQL Equivalence                            │
│                                                              │
│  ┌──────────────────────────┐ ┌───────────────────────────┐ │
│  │   QED Oracle              │ │   Lean Hand Proofs         │ │
│  │                           │ │                            │ │
│  │  • Join rewriting         │ │  • Aggregate semantics     │ │
│  │  • Filter pushdown        │ │  • COUNT/SUM/AVG/MIN/MAX  │ │
│  │  • Subquery unnesting     │ │  • DISTINCT counting       │ │
│  │  • Set operation algebra  │ │  • Empty-set edge cases    │ │
│  │  • Correlated→uncorrel.   │ │  • EXISTS ↔ COUNT bridge  │ │
│  │  • DISTINCT ↔ GROUP BY   │ │  • ORDER BY / LIMIT        │ │
│  │                           │ │  • NULL propagation        │ │
│  │  (relational structure)   │ │  (computational content)   │ │
│  └──────────────────────────┘ └───────────────────────────┘ │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐   │
│  │   OVERLAP (both can prove, cross-validates)            │   │
│  │   • WHERE algebra  • Basic DISTINCT  • EXISTS ↔ IN    │   │
│  └──────────────────────────────────────────────────────┘   │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐   │
│  │   NEITHER (future work)                                │   │
│  │   • Aggregate pushdown through GROUP BY                │   │
│  │   • Window function equivalences                       │   │
│  │   • Recursive CTE equivalences                         │   │
│  └──────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
```

### Aggregate theorems to prove next (hand proofs, not oracle)

These are high-value targets achievable with the current `evalAggOverTable`
definition and standard list lemmas:

| Theorem | Approach | Difficulty | Value |
|---------|----------|-----------|-------|
| `sum_append` : `SUM(xs ++ ys) = SUM(xs) + SUM(ys)` | `List.foldl_append` | Easy | Enables SUM splitting |
| `sum_map_add` : `SUM(map (·+k) xs) = SUM(xs) + k * COUNT(xs)` | Induction + `foldl` | Medium | Constant shift |
| `sum_distrib` : `SUM(xs.map f) + SUM(xs.map g) = SUM(xs.map (f+g))` | Induction + `foldl` | Medium | `SUM(a)+SUM(b)=SUM(a+b)` |
| `avg_as_sum_div_count` : `AVG(xs) = SUM(xs) / COUNT(xs)` | Unfold + `rfl` | Easy | AVG decomposition |
| `count_filter` : `COUNT(filter p xs) + COUNT(filter (¬p) xs) = COUNT(xs)` | `List.filter_partition` | Easy | Partition counting |
| `count_star_eq_count_one` : `rows.length = COUNT(1) over rows` | Unfold + `rfl` | Easy | `COUNT(*)≡COUNT(1)` |
| `min_le_max` : `MIN(xs) ≤ MAX(xs)` when `xs ≠ []` | `foldl_min/max` lemmas | Medium | Ordering bound |
| `sum_nonneg` : all elements ≥ 0 → `SUM(xs) ≥ 0` | Induction + `omega` | Easy | Monotonicity |

### Where the oracle helps with aggregation (indirectly)

Even though QED can't reason about aggregate semantics, the oracle still helps
with aggregate queries by proving the **relational scaffolding** around them:

```sql
-- The oracle proves the relational part:
SELECT dept, agg(sal) FROM emp JOIN dept ON emp.dept_id = dept.id GROUP BY dept
  ≡ SELECT dept, agg(sal) FROM dept JOIN emp ON dept.id = emp.dept_id GROUP BY dept
-- (join commutativity — QED normalizes this; aggregate is carried along)

-- Then hand proofs handle the aggregate part:
-- "agg(sal) over the same set of rows computes the same value"
-- (follows from the oracle proving the input rows are identical)
```

This is a **composition** pattern: oracle proves row-set equivalence,
hand proofs prove aggregate equivalence over equivalent row sets.

### Composition theorem (the bridge)

The key lemma connecting the two worlds:

```lean
-- If two queries produce the same rows (proven by oracle),
-- then any aggregate over those rows produces the same result (by definition)
theorem agg_over_equiv_rows (db : Database) (fn : AggFunc) (argExpr : Option Expr)
    (distinct : Bool) (rows1 rows2 : Table) (h : rows1 = rows2) :
    evalAggOverTable db fn argExpr distinct rows1 =
    evalAggOverTable db fn argExpr distinct rows2 := by
  rw [h]
```

For bag equivalence (permutation, not exact equality):

```lean
-- Harder but provable: aggregates are permutation-invariant
-- (because foldl of commutative+associative op is permutation-invariant)
theorem agg_perm_invariant (fn : AggFunc) (argExpr : Option Expr)
    (distinct : Bool) (rows1 rows2 : Table)
    (h : rows1.Perm rows2) :
    evalAggOverTable db fn argExpr distinct rows1 =
    evalAggOverTable db fn argExpr distinct rows2 := by
  -- SUM: foldl (·+·) is Perm-invariant (Int.add_comm + Int.add_assoc)
  -- COUNT: List.length is Perm-invariant (Perm.length_eq)
  -- MIN/MAX: foldl min/max is Perm-invariant (min_comm + min_assoc)
  -- DISTINCT: eraseDups is Perm-invariant up to Perm (Perm.eraseDups)
  sorry -- provable via case split on fn + Perm lemmas
```

This `agg_perm_invariant` theorem is the formal bridge between QED's
bag-semantic proofs and sql_equiv's aggregate reasoning. Once proven,
it means: "if QED proves two subqueries produce permutation-equivalent
rows, then any aggregate over them is equal." This covers the indirect
aggregate cases above.

---

## 5. Gap Analysis: What Neither System Proves

### Aggregate pushdown through GROUP BY

```sql
SELECT dept, SUM(sal) FROM emp WHERE sal > 50000 GROUP BY dept
  ≡ SELECT dept, SUM(sal) FROM (SELECT * FROM emp WHERE sal > 50000) GROUP BY dept
```

QED can prove the relational restructuring but can't verify that
`SUM` computes the same value. sql_equiv can reason about `SUM` but
has no proven infrastructure for `groupRowsByKey` equivalence.

**Path forward:** Prove `groupRowsByKey` is invariant under filter
pushdown (the grouped rows are the same), then apply `agg_over_equiv_rows`.

### Window function–aggregate interaction

```sql
SELECT SUM(x) OVER (PARTITION BY y) FROM t
  ≡ SELECT (SELECT SUM(x) FROM t t2 WHERE t2.y = t.y) FROM t
```

Neither system handles this. Window functions would need their own
semantic definition and equivalence theory.

### Recursive CTE with aggregation

```sql
WITH RECURSIVE cte AS (
  SELECT 1 as n
  UNION ALL
  SELECT n + 1 FROM cte WHERE n < 10
)
SELECT SUM(n) FROM cte
```

Neither system handles recursive CTEs formally.

---

## 6. Recommendations

1. **Keep all 20 proven aggregate theorems.** They are complementary to the
   oracle, not redundant.

2. **Prove `agg_perm_invariant` next.** This is the composition bridge
   between oracle (bag-equivalence proofs) and hand proofs (aggregate
   semantics). It's medium difficulty — case split on `AggFunc`, then
   use `List.Perm` lemmas from Batteries.

3. **Prove `sum_append` and `avg_as_sum_div_count`.** These are easy wins
   that unlock the most commonly-needed aggregate equivalences.

4. **Don't try to make QED aggregate-aware.** Extending QED's U-semiring
   with aggregate laws is a research contribution in itself (and the QED
   authors acknowledge it as future work). It's more practical to compose
   the two systems than to merge them.

5. **The `selectHasAggregate` guard is critical.** Any integration with QED
   must preserve this: QED might normalize `WHERE FALSE` away, but the
   Lean checker must know that aggregate queries behave differently with
   empty inputs. The certificate checker should flag this case.

---

## References

- QED: Wang, Pan, Cheung. "QED: A Powerful Query Equivalence Decider for SQL."
  VLDB 2024. §5.3 discusses aggregation limitations.
- U-semiring foundations: Chu, Weitz, Cheung, Suciu. "Axiomatic Foundations and
  Algorithms for Deciding Semantic Equivalences of SQL Queries." VLDB 2018.
- sql_equiv aggregate proofs: `SqlEquiv/Equiv/Comparison.lean:692-848`,
  `SqlEquiv/Equiv/StatementAxioms.lean:742-753`
- sql_equiv aggregate semantics: `SqlEquiv/Semantics.lean:339-398`
