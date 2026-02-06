# Plan: Datalog Formalization in Lean 4

## Prior Art

### What Already Exists

| Prover | Authors | Year | What's Formalized |
|--------|---------|------|-------------------|
| **Lean 4** | Tantow, Gerlach, Mennicke, Krotzsch | ITP 2025 | Syntax, model-theoretic + proof-theoretic semantics, their equivalence, certified checker |
| **Coq** | Benzaken, Contejean, Dumbrava | ITP 2017 | Model-theoretic + fixed-point semantics, stratified negation, bottom-up evaluation |
| **Coq** | CPP 2021 (Orange) | CPP 2021 | Trace semantics, program transformations, static analysis |
| **Isabelle** | Schlichtkrull, Hansen, Nielson | SAC 2024 | Stratified Datalog, least solutions, program analysis |

**Key gap:** Nobody has formalized all three classical semantics (model-theoretic,
fixed-point, proof-theoretic) in one framework. Tantow proved model=proof in Lean 4.
Benzaken proved model=fixpoint in Coq. The triple equivalence is open.

### What Tantow et al. Did NOT Do

- Fixed-point semantics (T_P operator, Knaster-Tarski, Kleene iteration)
- Connection to Mathlib's `Order.FixedPoints` lattice infrastructure
- Stratified negation
- Magic sets or other optimizations
- Connection to SQL / relational algebra
- Seminaive evaluation correctness

These are all fair game for us.

---

## Novel Contribution

**Primary thesis:** Formalize Datalog's fixed-point semantics in Lean 4 using
Mathlib's lattice theory, prove the triple semantic equivalence, and connect
Datalog to our existing SQL formalization via the Datalog-to-SQL correspondence.

This gives us three publishable results:
1. First complete triple equivalence in any proof assistant
2. First Datalog formalization using Mathlib's `OrderHom.lfp` / Knaster-Tarski
3. First mechanically verified bridge between Datalog and SQL semantics

---

## Architecture Decision: Separate Repo with Shared Dependency

```
datalog_equiv/           -- new repo
  lakefile.toml          -- depends on sql_equiv for Value, Row, Table types
  DatalogEquiv/
    Ast.lean             -- Term, Atom, Rule, Program
    Substitution.lean    -- variable binding, unification
    Semantics.lean       -- naive evaluation, T_P operator
    Seminaive.lean       -- delta rules
    Fixpoint.lean        -- lfp via Mathlib, Kleene iteration
    ModelTheoretic.lean  -- minimal Herbrand model
    ProofTheoretic.lean  -- proof trees (adapt from Tantow)
    Equivalence.lean     -- triple equivalence proofs
    Stratification.lean  -- dependency graph, stratified negation
    Optimizations/
      MagicSets.lean     -- transformation + correctness
      BodyReordering.lean
    Bridge/
      DatalogToSQL.lean  -- non-recursive Datalog ≃ conjunctive queries
    Tactics.lean         -- datalog_equiv decision procedure
  Test/
    ...
```

**Why separate repo:** Datalog is a different project with different theorems.
Sharing a Lake workspace bloats both builds. Import the shared types via:

```toml
[[require]]
name = "sql_equiv"
path = "../sql_equiv"  -- or a git URL
```

---

## AST Design

### Core Types

```lean
-- A ground value is just sql_equiv's Value
-- import SqlEquiv.Ast (Value, SqlType)

/-- A Datalog term is either a variable or a constant. -/
inductive Term where
  | var : String → Term
  | const : Value → Term
  deriving BEq, Repr, Inhabited

/-- A Datalog atom: predicate name applied to a list of terms. -/
structure Atom where
  predicate : String
  args : List Term
  deriving BEq, Repr, Inhabited

/-- A ground atom: predicate applied to constants only. -/
structure GroundAtom where
  predicate : String
  args : List Value
  deriving BEq, Repr, Inhabited

/-- A Datalog rule: head :- body. -/
structure Rule where
  head : Atom
  body : List Atom
  deriving BEq, Repr, Inhabited

/-- A Datalog program: rules + extensional database (base facts). -/
structure Program where
  rules : List Rule
  edb : List GroundAtom
  deriving Repr, Inhabited
```

### Key Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Typed vs untyped | Untyped (any Value in any position) | Matches sql_equiv's current model; add types later |
| Negation | Not in Phase 1; add stratified in Phase 3 | Pure Datalog is cleaner to formalize first |
| Aggregates | Not in Phase 1-3 | Future work (Zaniolo's aggregate fixpoint semantics) |
| Ground atoms vs Herbrand base | Explicit `GroundAtom` type | Cleaner than `Atom` with a well-groundedness proof |
| Substitution representation | `String → Option Value` | Matches Lean's function type; partial = unbound vars |
| Equality built-in? | Yes, `=(X,Y)` as a special predicate | Needed for Datalog-to-SQL bridge |

---

## Semantics

### Substitution

```lean
abbrev Substitution := String → Option Value

def applySubst (σ : Substitution) : Term → Option Value
  | .var x => σ x
  | .const v => some v

def groundAtom (σ : Substitution) (a : Atom) : Option GroundAtom :=
  -- Apply σ to all args; succeed only if all are ground
  ...
```

### Naive Evaluation (T_P Operator)

```lean
/-- The immediate consequence operator. -/
def T_P (prog : Program) (I : Set GroundAtom) : Set GroundAtom :=
  prog.edb.toFinset ∪
  { ga | ∃ rule ∈ prog.rules, ∃ σ : Substitution,
    (∀ bodyAtom ∈ rule.body, ∃ ga' ∈ I, groundAtom σ bodyAtom = some ga') ∧
    groundAtom σ rule.head = some ga }
```

### Fixed-Point via Mathlib

```lean
import Mathlib.Order.FixedPoints

/-- T_P is monotone: if I ⊆ J then T_P(I) ⊆ T_P(J). -/
theorem T_P_monotone (prog : Program) : Monotone (T_P prog) := by
  intro I J hIJ
  -- If a body atom is satisfied in I, it's satisfied in J
  ...

/-- Bundle T_P as an OrderHom to use Mathlib's lfp. -/
def T_P_hom (prog : Program) : Set GroundAtom →o Set GroundAtom :=
  ⟨T_P prog, T_P_monotone prog⟩

/-- The least fixed point of T_P is the meaning of the program. -/
def evalProgram (prog : Program) : Set GroundAtom :=
  OrderHom.lfp (T_P_hom prog)
```

Mathlib gives us for free:
- `OrderHom.map_lfp` — `T_P (lfp T_P) = lfp T_P` (fixed point property)
- `OrderHom.lfp_le` — `lfp T_P` is below any pre-fixed point
- `fixedPoints.completeLattice` — Knaster-Tarski
- `fixedPoints.lfp_eq_sSup_iterate` — Kleene's theorem (lfp = ⊔ᵢ T_Pⁱ(∅))

### Computable Evaluation

The `Set GroundAtom` formulation is for proofs. For computation, use finite sets:

```lean
/-- Computable T_P over Finset. -/
def T_P_fin (prog : Program) (I : Finset GroundAtom) : Finset GroundAtom :=
  -- iterate over rules, enumerate substitutions from I
  ...

/-- Naive iteration until fixpoint. -/
def naiveEval (prog : Program) (fuel : Nat) : Finset GroundAtom :=
  match fuel with
  | 0 => prog.edb.toFinset
  | n + 1 =>
    let next := T_P_fin prog (naiveEval prog n)
    if next == naiveEval prog n then next
    else naiveEval prog n  -- should recur, but use fuel for termination
```

---

## Phased Implementation

### Phase 1: Core Semantics (weeks 1-3)

**Goal:** AST + naive evaluation + T_P monotonicity + lfp existence.

| # | Task | Theorems | Effort |
|---|------|----------|--------|
| 1.1 | Define `Term`, `Atom`, `GroundAtom`, `Rule`, `Program` | — | Small |
| 1.2 | Define `Substitution`, `applySubst`, `groundAtom` | — | Small |
| 1.3 | Define `T_P` as `Set GroundAtom → Set GroundAtom` | — | Medium |
| 1.4 | Prove `T_P_monotone` | 1 theorem | Medium |
| 1.5 | Define `evalProgram` via `OrderHom.lfp` | — | Small (Mathlib does the work) |
| 1.6 | Prove `evalProgram` is a fixed point | 1 theorem (from Mathlib) | Small |
| 1.7 | Define computable `T_P_fin` + `naiveEval` | — | Medium |
| 1.8 | Prove `naiveEval` terminates (finite Herbrand base) | 1 theorem | Hard |
| 1.9 | Prove `naiveEval` agrees with `evalProgram` | 1 theorem | Hard |

**Milestone:** `lake build` succeeds, can `#eval` small Datalog programs.

### Phase 2: Model-Theoretic + Proof-Theoretic Semantics (weeks 4-6)

**Goal:** Define two alternative semantics and prove equivalences.

| # | Task | Theorems | Effort |
|---|------|----------|--------|
| 2.1 | Define Herbrand interpretation, Herbrand model | — | Small |
| 2.2 | Define minimal model | — | Small |
| 2.3 | Prove `evalProgram = minimalModel` (fixpoint = model) | 1 theorem | Hard |
| 2.4 | Define proof trees | — | Medium |
| 2.5 | Prove soundness: proof tree → fact in lfp | 1 theorem | Medium |
| 2.6 | Prove completeness: fact in lfp → proof tree exists | 1 theorem | Hard |
| 2.7 | Triple equivalence corollary | 1 theorem | Small (combines 2.3 + 2.5 + 2.6) |

**Milestone:** Triple semantic equivalence proven. This is the main publishable result.

### Phase 3: Stratified Negation (weeks 7-9)

**Goal:** Extend to Datalog with stratified negation.

| # | Task | Theorems | Effort |
|---|------|----------|--------|
| 3.1 | Add `NegAtom` (negated body literals) to AST | — | Small |
| 3.2 | Define predicate dependency graph | — | Medium |
| 3.3 | Define stratification (topological sort, no neg cycles) | — | Medium |
| 3.4 | Define stratum-by-stratum evaluation | — | Medium |
| 3.5 | Prove stratified evaluation produces unique perfect model | 2 theorems | Hard |
| 3.6 | Prove stratification is decidable | 1 theorem | Medium |

### Phase 4: Optimizations (weeks 10-13)

**Goal:** Verify key Datalog optimizations.

| # | Task | Theorems | Effort |
|---|------|----------|--------|
| 4.1 | Body literal reordering preserves semantics | 1 theorem | Easy |
| 4.2 | Redundant atom elimination | 1 theorem | Easy |
| 4.3 | Seminaive evaluation correctness | 2 theorems | Hard |
| 4.4 | Magic sets transformation | 1 transform + 1 correctness proof | Very hard |
| 4.5 | `datalog_equiv` tactic (adapt from `sql_equiv`) | — | Medium |

### Phase 5: Bridge to SQL (weeks 14-16)

**Goal:** Prove the classical correspondence between Datalog and SQL.

| # | Task | Theorems | Effort |
|---|------|----------|--------|
| 5.1 | Define conjunctive queries (CQ) as non-recursive single-rule Datalog | — | Small |
| 5.2 | Define translation: CQ → SQL SELECT-FROM-WHERE | — | Medium |
| 5.3 | Prove translation preserves semantics | 1 theorem | Hard |
| 5.4 | Define homomorphism between CQs | — | Medium |
| 5.5 | Prove Chandra-Merlin: containment ↔ homomorphism | 2 theorems | Very hard |
| 5.6 | Show recursive Datalog = SQL + recursion (WITH RECURSIVE) | 1 theorem | Hard |

---

## Key Theorems (Target List)

### Phase 1 (~5 theorems)
1. `T_P_monotone` — immediate consequence operator is monotone
2. `evalProgram_fixpoint` — `T_P (evalProgram P) = evalProgram P`
3. `evalProgram_least` — `evalProgram P` is the least fixed point
4. `naiveEval_terminates` — iteration reaches fixpoint in ≤ |Herbrand base| steps
5. `naiveEval_correct` — computable evaluation agrees with denotational semantics

### Phase 2 (~4 theorems)
6. `fixpoint_eq_minimal_model` — lfp(T_P) is the minimal Herbrand model
7. `proof_tree_sound` — derivable ⊂ lfp(T_P)
8. `proof_tree_complete` — lfp(T_P) ⊂ derivable
9. `triple_equivalence` — all three semantics coincide

### Phase 3 (~3 theorems)
10. `stratification_decidable` — stratifiability is decidable
11. `stratified_eval_unique` — result independent of stratification choice
12. `perfect_model_exists` — stratified Datalog has a unique perfect model

### Phase 4 (~5 theorems)
13. `body_reorder_equiv` — body literal order doesn't matter
14. `redundant_atom_elim` — removing redundant body atoms preserves semantics
15. `seminaive_correct` — seminaive computes same fixpoint as naive
16. `seminaive_efficient` — seminaive derives each fact at most once
17. `magic_sets_correct` — magic transformation preserves query answers

### Phase 5 (~4 theorems)
18. `cq_to_sql_correct` — conjunctive query = SELECT-FROM-WHERE
19. `chandra_merlin_forward` — homomorphism → containment
20. `chandra_merlin_backward` — containment → homomorphism
21. `recursive_datalog_eq_with_recursive` — recursive Datalog = SQL WITH RECURSIVE

**Total: ~21 theorems.** Compare to sql_equiv's 152+ axioms — this is completable.

---

## What We Reuse from sql_equiv

| Component | Action | Effort |
|-----------|--------|--------|
| `Value`, `SqlType`, `Trilean` | Import via Lake dep | Zero |
| `Row`, `Table`, `Database` aliases | Import | Zero |
| `evalBinOp`, `Value.eq`, `Value.compare` | Import (for built-in predicates) | Zero |
| batteries, LSpec dependencies | Same `lakefile.toml` pattern | Trivial |
| Equivalence scaffolding (refl/symm/trans) | Copy pattern | Minimal |
| Tactic architecture (`sql_equiv` → `datalog_equiv`) | Adapt | Medium |
| Proof patterns (case analysis, congruence) | Transfer skill | Zero (it's in our heads) |

---

## Comparison: Tantow et al. vs Our Plan

| Feature | Tantow (ITP 2025) | Our Plan |
|---------|-------------------|----------|
| Syntax | Custom (no shared types) | Reuses sql_equiv's `Value` |
| Model-theoretic semantics | Yes | Yes |
| Proof-theoretic semantics | Yes | Yes |
| Fixed-point semantics | **No** | **Yes (via Mathlib)** |
| Triple equivalence | **No** (only model=proof) | **Yes** |
| Mathlib integration | **No** | **Yes (Order.FixedPoints)** |
| Stratified negation | No | Phase 3 |
| Optimizations | No | Phase 4 (magic sets, seminaive) |
| SQL bridge | No | Phase 5 |
| Certified checker | Yes | Not planned (different goal) |
| Executable engine | Yes (JSON-based) | Yes (via `#eval`) |

Our work is complementary, not competing. They built a certified checker for
external Datalog engines. We're building verified semantics and optimizations
with a SQL bridge.

---

## Open Questions

1. **Mathlib dependency weight** — Importing Mathlib's `Order.FixedPoints` pulls
   in a lot of the lattice hierarchy. Is the build time acceptable? Test early.

2. **Finite vs infinite Herbrand base** — Pure Datalog over a finite EDB has a
   finite Herbrand base (termination is easy). If we allow function symbols
   (full logic programming), the Herbrand base is infinite and termination is
   undecidable. Stick to function-free Datalog.

3. **Relation to CertifyingDatalog** — Should we build on Tantow's Lean 4 code
   or start fresh? Their code doesn't use Mathlib, so integrating would mean
   refactoring their proofs. Starting fresh with Mathlib is probably cleaner.

4. **Name** — `datalog_equiv`? `verified_datalog`? `datalog_lean`?

---

## References

- Tantow et al., "Verifying Datalog Reasoning with Lean" (ITP 2025)
  [LIPIcs.ITP.2025.36](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.36)
- Benzaken, Contejean, Dumbrava, "Certifying Standard and Stratified Datalog" (ITP 2017)
- Green et al., "Datalog and Recursive Query Processing" (Foundations and Trends, 2013)
- Ceri, Gottlob, Tanca, "What You Always Wanted to Know About Datalog" (1989)
- Abiteboul, Hull, Vianu, *Foundations of Databases* (chapters 12-15)
- Mathlib `Order.FixedPoints` [docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/FixedPoints.html)
- knowsys/CertifyingDatalog [GitHub](https://github.com/knowsys/CertifyingDatalog)
