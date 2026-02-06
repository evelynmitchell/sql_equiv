# Future Directions

## Current Roadmap

1. **Prove the 152 axioms** (axioms-first, on current 4 types)
   - ~120 type-independent axioms carry forward with zero rework
   - ~30 type-sensitive axioms need revisiting after type expansion
   - See `scripts/create_axiom_issues.sh` for grouped issues
   - See `PROVING_AXIOMS_PLAN.md` for phased strategy

2. **Expand SQL types** from 4 to 11
   - See `SQL_TYPES_CONCRETE_PLAN.md` for batch ordering
   - Cross-type elimination lemma (`mismatched_types_null`) mitigates proof explosion

## Next Project: Datalog Equivalence

After the SQL axioms reach a solid state, a natural companion project is
**formally verified Datalog equivalence** in Lean 4.

### Why Datalog

- **Completable** — Datalog has ~20 core equivalence rules vs SQL's unbounded list.
  A "finished" verified project is achievable.
- **Cleaner semantics** — fixpoint evaluation gives a natural induction principle
  that SQL's bag semantics lack.
- **Publishable** — verified Datalog is an active research area (Datalog engines
  like Souffl and Rel use these transformations; no one has machine-checked them).
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

Total: ~20 theorems for a complete core, vs 152+ for SQL.

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

- Share a Lake workspace with sql_equiv, or separate repo?
- Reuse `Value` type from sql_equiv, or start fresh?
- Target Souffl-style Datalog (with aggregates, ADTs) or pure Datalog?
- Include negation (stratified Datalog) from the start?

### Resources

- *Foundations of Databases* (Abiteboul, Hull, Vianu) — chapters 12-15
- *Alice Book* — Datalog semantics and optimization
- Soufflé documentation — practical Datalog transformations
- Lean 4 Mathlib `Order.FixedPoints` — for Knaster-Tarski fixpoint theorems
