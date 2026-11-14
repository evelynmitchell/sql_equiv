# Future Directions

## Current Roadmap

1. ~~**Prove the 152 axioms**~~ ✅ **COMPLETE** (2026-02) — every axiom has been
   converted to a proven theorem (561 theorems, 0 axioms; the CI ratchet in
   `tools/axiom_count_minimum.txt` is at 0).
   See `PROVING_AXIOMS_PLAN.md` for the batch-by-batch record.

2. **Expand SQL types** from 4 to 11 — the current main track
   - See `SQL_TYPES_CONCRETE_PLAN.md` for batch ordering
   - Cross-type elimination lemma (`mismatched_types_null`) mitigates proof explosion

3. **Remaining proof debt** (small, tracked)
   - (done, #212) The evaluator's termination is kernel-checked and no
     theorem depends on `sorryAx`; `Test/TrustBaseTest.lean` enforces it
   - (done, #213 / #278) Statement-level certified checkers exist:
     `checkSelectEquiv` / `checkQueryEquiv` in
     `SqlEquiv/Equiv/StatementChecker.lean` (syntactic equality, WHERE
     congruence via `checkEquivFull`, set-operation congruence). Extending
     them (projection, GROUP BY, join reordering) is open.

## Next Project: Datalog Equivalence

With the SQL axioms fully proven, a natural companion project is
**formally verified Datalog equivalence** in Lean 4.

### Why Datalog

- **Completable** — Datalog has ~20 core equivalence rules vs SQL's unbounded list.
  A "finished" verified project is achievable.
- **Cleaner semantics** — fixpoint evaluation gives a natural induction principle
  that SQL's bag semantics lack.
- **Publishable** — verified Datalog is an active research area (Datalog engines
  like Soufflé and Rel use these transformations; no one has machine-checked them).
- **Directly transfers** — Datalog is a SQL fragment (SELECT-FROM-WHERE with
  recursion, no ORDER BY/aggregates/subqueries). Skills, tactics, and even
  some infrastructure from sql_equiv carry over.

### Scope

A minimal Datalog equivalence prover would cover:

| Category | Rules | Example |
|----------|-------|---------|
| Rule rewriting | ~5 | Body literal reordering, redundant atom elimination |
| Query containment | ~4 | Homomorphism-based containment, equivalence via mutual containment |
| Magic sets | ~3 | Sideways information passing transforms |
| Seminaive evaluation | ~3 | Delta rule correctness, fixpoint equivalence |
| Stratification | ~3 | Negation stratification preserves model |
| Optimization | ~3 | Predicate pushdown (shared with sql_equiv), join ordering |

Total: ~20 theorems for a complete core, vs the 561 sql_equiv ultimately needed.

### What Carries Over from sql_equiv

- **Lean 4 fluency** — tactic writing, mutual inductive types, decidability
- **Custom tactics** — `sql_equiv`-style decision procedures adapt to Datalog
- **AST design patterns** — mutual recursion for rules/atoms/terms
- **Equivalence proof patterns** — unfold semantics, case split, rewrite
- **Lake project structure** — tests, CI, documentation patterns

### AST Sketch

```lean
-- Datalog is much simpler than SQL
inductive Term where
  | var : String → Term
  | const : Value → Term

structure Atom where
  predicate : String
  args : List Term

structure Rule where
  head : Atom
  body : List Atom

structure Program where
  rules : List Rule
  edb : Database      -- extensional (base) facts
```

### Key Theorems to Target

1. **Fixpoint existence** — `Program.eval` terminates and produces a unique minimal model
2. **Rule body reordering** — evaluation order of body atoms doesn't affect results
3. **Query containment** — if a homomorphism exists from Q1 to Q2, then Q1 ⊆ Q2
4. **Seminaive correctness** — delta iteration computes the same fixpoint as naive
5. **Magic sets correctness** — transformed program produces same answers for query

### Open Questions

Two of these are answered in `DATALOG_FORMALIZATION_PLAN.md` (separate repo
with sql_equiv as a Lake dependency; reuse `Value`). Still open:

- Target Soufflé-style Datalog (with aggregates, ADTs) or pure Datalog?
- Include negation (stratified Datalog) from the start?
- Re-verify the novelty claim ("first triple semantic equivalence in a proof
  assistant") against current literature before committing — the prior-art
  survey in `DATALOG_FORMALIZATION_PLAN.md` dates from early 2026.

### Resources

- *Foundations of Databases* (Abiteboul, Hull, Vianu) — chapters 12-15
- *Alice Book* — Datalog semantics and optimization
- Soufflé documentation — practical Datalog transformations
- Lean 4 Mathlib `Order.FixedPoints` — for Knaster-Tarski fixpoint theorems
