# Refactoring sql_equiv with QED Prover as Oracle

> **Historical snapshot.** Axiom/theorem counts in this document are as of when it was written. As of 2026-11 the codebase has **0 axioms** (all proved since PR #173) and **697 theorems**; run `python3 tools/count_axioms_theorems.py` for the live count. The optimizer specs it mentions under `docs/specs/` were removed (#179).

**Date:** 2026-02-18
**Status:** Proposal

## Executive Summary

This document proposes a fundamental architectural shift: instead of proving each
SQL equivalence individually in Lean 4 (the current approach), we use the
[QED prover](https://github.com/qed-solver/prover) (VLDB 2024) as an external
**decision oracle** and Lean 4 as a **certificate checker**. This separates the
*finder* (QED — fast, automated, wide coverage) from the *checker* (Lean — small,
trustworthy, formally verified).

Three options for bridging SMT solver results into the Lean trust kernel are
analyzed in detail.

---

## Table of Contents

1. [Motivation: Why Change](#1-motivation-why-change)
2. [Architecture Overview](#2-architecture-overview)
3. [Phase 1: U-Semiring Kernel in Lean](#3-phase-1-u-semiring-kernel-in-lean)
4. [Phase 2: SQL-to-UExpr Translation](#4-phase-2-sql-to-uexpr-translation)
5. [Phase 3: QED Certificate Output](#5-phase-3-qed-certificate-output)
6. [Phase 4: Certificate Checker in Lean](#6-phase-4-certificate-checker-in-lean)
7. [Phase 5: SMT Certificate Bridging](#7-phase-5-smt-certificate-bridging)
   - [Option A: Trust SMT as Axiom](#option-a-trust-smt-as-axiom)
   - [Option B: Verify SMT Proof Certificates](#option-b-verify-smt-proof-certificates-alethelfsc)
   - [Option C: Lean-Native Decision Procedures](#option-c-lean-native-decision-procedures)
   - [Recommendation: Phased Option C→B→A](#recommendation-phased-option-cba)
8. [Phase 6: Integration and Migration](#8-phase-6-integration-and-migration)
9. [What Stays, What Goes](#9-what-stays-what-goes)
10. [Risk Analysis](#10-risk-analysis)
11. [Comparison: Current vs Oracle Approach](#11-comparison-current-vs-oracle-approach)
12. [Open Questions](#12-open-questions)
13. [References](#13-references)

---

## 1. Motivation: Why Change

### Current pain points

| Problem | Root cause | Impact |
|---------|-----------|--------|
| 12 axioms stuck, some structurally blocked | `partial def` opacity, column ordering in joins | Can't reach 100% proven |
| Each new equivalence = bespoke proof | No automation layer | Linear effort per theorem |
| Join commutativity requires row-set reasoning | `Row = List (String × Value)` is ordered | `join_comm` blocked for months |
| `filter_join_left/right` blocked | `exprReferencesOnlyFrom` is `partial def` | Phase 9 inaccessible |
| 486 theorems for ~150 equivalence rules | High LOC-per-theorem ratio | Maintenance burden |

### What QED offers

QED (Wang, Pan, Cheung — UC Berkeley, VLDB 2024) is a Rust-based SQL equivalence
decider that:

- Proves **299/444** Apache Calcite test cases and **979/1,287** CockroachDB cases
- Averages **0.88 seconds** per query pair
- Is **sound** — no false positives (if it says equivalent, they are)
- Has an **Agda formalization** of its normalization algorithm
- Handles: SELECT-FROM-WHERE, all join types (inner/outer/semi/anti/correlated),
  set operations, DISTINCT, VALUES, aggregation (structurally), GROUP BY,
  IN/EXISTS subqueries
- Uses dual SMT solvers (Z3 + CVC5) in parallel

### The key insight

The classic verified-systems pattern applies here:

> **Separate the finder from the checker.**
>
> CompCert doesn't verify the optimizer — it verifies a *translation validator*
> that checks the optimizer's output. CakeML doesn't verify the compiler passes —
> it verifies a *proof-producing* backend. seL4 doesn't verify the C compiler —
> it verifies against a *formal spec*.

QED is the finder. Lean should be the checker.

---

## 2. Architecture Overview

```
                    ┌─────────────────────────────┐
                    │     SQL Query Pair           │
                    │   (q₁, q₂)                  │
                    └──────────┬──────────────────┘
                               │
                    ┌──────────▼──────────────────┐
                    │   QED Prover (Rust)          │
                    │                              │
                    │  1. Parse → Relation AST     │
                    │  2. Translate → UExpr         │
                    │  3. Normalize → SPNF          │
                    │  4. Stabilize (Z3/CVC5)       │
                    │  5. Unify                      │
                    │                              │
                    │  Output: Certificate trace    │
                    └──────────┬──────────────────┘
                               │
                    ┌──────────▼──────────────────┐
                    │   Certificate (JSON/S-expr)   │
                    │                              │
                    │  - Sequence of rewrite steps  │
                    │  - Each step: algebraic law   │
                    │    or SMT-verified equality   │
                    │  - SMT sub-certificates       │
                    └──────────┬──────────────────┘
                               │
                    ┌──────────▼──────────────────┐
                    │   Lean 4 Certificate Checker │
                    │                              │
                    │  1. Parse certificate         │
                    │  2. Replay each rewrite step  │
                    │     against proven semiring   │
                    │     laws                      │
                    │  3. Verify SMT sub-certs      │
                    │     (Option A/B/C)            │
                    │  4. Produce Lean proof term   │
                    └──────────┬──────────────────┘
                               │
                    ┌──────────▼──────────────────┐
                    │   Lean Proof: q₁ ≃ q₂       │
                    │   (kernel-checked)            │
                    └─────────────────────────────┘
```

### Trust boundaries

| Component | Trusted? | Justification |
|-----------|----------|---------------|
| QED prover | **No** | Its output is verified by the checker |
| Certificate format | **No** | Just data; checker validates it |
| Lean certificate checker | **Yes** | Small, auditable, kernel-checked |
| U-semiring laws in Lean | **Yes** | Proven once, machine-checked |
| SMT solver | **Depends on option** | See Phase 5 |
| SQL→UExpr translation | **Yes** | Must be proven correct or axiomatized |
| Lean kernel | **Yes** | Foundation (same trust as current approach) |

---

## 3. Phase 1: U-Semiring Kernel in Lean

### Goal

Define the U-semiring algebra and prove its laws. This is the mathematical
foundation that makes certificate checking possible.

### U-semiring definition

```lean
-- The semantic domain for bag-relational queries
-- Following Chu et al. (VLDB 2018) and QED (VLDB 2024)

inductive DataType where
  | integer | real | boolean | string
  deriving DecidableEq, Repr

-- Variables (de Bruijn-style or named)
structure VL where
  name : String
  ty : DataType
  deriving DecidableEq, Repr

-- Expressions over tuple variables
inductive Expr where
  | var : VL → Expr
  | lit : Value → Expr
  | op : String → List Expr → Expr       -- uninterpreted functions/operators
  | agg : String → Expr → Expr           -- aggregate (uninterpreted)
  deriving Repr

-- First-order logic formulas
inductive Logic where
  | tt : Logic                             -- true
  | ff : Logic                             -- false
  | eq : Expr → Expr → Logic              -- expression equality
  | and : Logic → Logic → Logic
  | or : Logic → Logic → Logic
  | not : Logic → Logic
  | isNull : Expr → Logic                 -- NULL test
  deriving Repr

-- U-semiring expressions (the core algebraic type)
inductive UExpr where
  | zero : UExpr                           -- ∅ (empty bag)
  | one : UExpr                            -- singleton unit
  | add : UExpr → UExpr → UExpr           -- ⊕ (UNION ALL)
  | mul : UExpr → UExpr → UExpr           -- ⊗ (JOIN, WHERE)
  | squash : UExpr → UExpr                -- ‖·‖ (DISTINCT)
  | not : UExpr → UExpr                   -- ¬ (NOT EXISTS)
  | sum : List DataType → UExpr → UExpr   -- Σ (iterate over tuples)
  | pred : Logic → UExpr                  -- [φ] (boolean → 0/1)
  | app : String → List Expr → UExpr      -- R(t₁,...,tₙ) (table access)
  deriving Repr
```

### Semiring laws to prove

These are the algebraic identities that make SPNF normalization sound. Each
one becomes a Lean theorem:

```
-- Additive monoid
add_comm      : add a b = add b a
add_assoc     : add (add a b) c = add a (add b c)
add_zero_left : add zero a = a
add_zero_right: add a zero = a

-- Multiplicative monoid
mul_assoc     : mul (mul a b) c = mul a (mul b c)
mul_one_left  : mul one a = a
mul_one_right : mul a one = a

-- Zero annihilates
mul_zero_left : mul zero a = zero
mul_zero_right: mul a zero = zero

-- Distributivity
mul_add_left  : mul a (add b c) = add (mul a b) (mul a c)
mul_add_right : mul (add a b) c = add (mul a c) (mul b c)

-- Squash properties
squash_idem   : squash (squash a) = squash a
squash_zero   : squash zero = zero
squash_one    : squash one = one
squash_mul    : squash (mul (squash a) (squash b)) = mul (squash a) (squash b)

-- Not properties (not is defined as: not(e) = if e = 0 then 1 else 0)
not_zero             : not zero = one
not_one              : not one = zero
-- Derived: the conditional form useful for normalization proofs
not_squash_nonzero   : (a ≠ zero) → not (squash a) = zero

-- Pred properties
pred_tt       : pred tt = one
pred_ff       : pred ff = zero
pred_and      : pred (and φ ψ) = mul (pred φ) (pred ψ)
pred_or       : pred (or φ ψ) = squash (add (pred φ) (pred ψ))
pred_not      : pred (not φ) = not (pred φ)

-- Sum properties
sum_zero      : sum τ zero = zero
sum_add       : sum τ (add a b) = add (sum τ a) (sum τ b)
sum_comm      : sum τ₁ (sum τ₂ a) = sum τ₂ (sum τ₁ a)  -- when τ₁ ≠ τ₂
sum_squash    : squash (sum τ a) = squash (sum τ (squash a))
```

**Estimated scope:** ~30-40 lemmas. These are the **only** things that need to be
proven in Lean about the algebra itself. All SQL equivalences then reduce to
sequences of these laws.

### Semantic model

The laws above are stated *syntactically* over `UExpr`. To prove them sound,
we need a *denotational semantics* mapping `UExpr` to actual bag multiplicities:

```lean
-- A bag is a function from tuples to natural numbers (multiplicities)
def Bag (τ : Type) := τ → Nat

-- Interpretation of UExpr as a bag operation
def denote (env : Env) : UExpr → Bag Tuple
```

The semiring laws then become theorems about `denote`:

```lean
theorem add_comm_sound (a b : UExpr) (env : Env) :
    denote env (add a b) = denote env (add b a) := by
  funext t; simp [denote]; omega
```

### What to port from QED's Agda formalization

QED's `agda/` directory contains:
- `Syntax.agda` — AST definitions (maps directly to our `UExpr`)
- `Partial.agda` — Partial evaluation proofs
- `Normal.agda` — Normal form proofs
- `Stable.agda` — Stabilization proofs

The Agda→Lean4 port is mechanical: both are dependently-typed, both use
pattern matching and structural recursion. The main differences are syntactic
(`Set` → `Type`, `rewrite` → `rw`, record syntax).

**Estimated effort:** 2-3 weeks for one person familiar with both systems.

---

## 4. Phase 2: SQL-to-UExpr Translation

### Goal

Define a function `translate : SelectStmt → UExpr` that maps our existing
SQL AST to the U-semiring representation.

### Translation rules

These follow Section 3 of Chu et al. (VLDB 2018):

```lean
def translate : SelectStmt → UExpr
  -- SELECT * FROM t WHERE p
  --   ↦ Σ_τ (R(vars) ⊗ [p])
  | { items := [.star _], fromClause := some (.table name alias),
      whereClause := some p, .. } =>
    let τ := schemaOf name
    UExpr.sum τ (UExpr.mul (UExpr.app name (varsOf τ)) (UExpr.pred (translateExpr p)))

  -- SELECT cols FROM t WHERE p
  --   ↦ Σ_τ (R(vars) ⊗ [p] ⊗ [out = f(vars)])
  | { items, fromClause := some (.table name alias),
      whereClause := some p, .. } =>
    let τ := schemaOf name
    UExpr.sum τ (UExpr.mul
      (UExpr.mul (UExpr.app name (varsOf τ)) (UExpr.pred (translateExpr p)))
      (UExpr.pred (projectConstraint items (varsOf τ))))

  -- SELECT DISTINCT ...
  --   ↦ ‖translate(SELECT ...)‖
  | { distinct := true, .. } => UExpr.squash (translate { s with distinct := false })

  -- FROM t1 JOIN t2 ON p
  --   ↦ Σ_τ₁ Σ_τ₂ (R₁(vars₁) ⊗ R₂(vars₂) ⊗ [p])
  | { fromClause := some (.join .inner left right (some cond) _), .. } =>
    translateJoin left right cond

  -- UNION ALL
  --   ↦ translate(q₁) ⊕ translate(q₂)

  -- EXCEPT
  --   ↦ translate(q₁) ⊗ ¬(translate(q₂))

  -- EXISTS (subquery)
  --   ↦ ‖Σ_τ translate(subquery)‖
```

### Schema handling

QED tracks schemas (types, primary keys, nullability, CHECK constraints)
as metadata on tables. We'd extend our existing `Database` type:

```lean
structure TableSchema where
  columns : List (String × DataType)
  primaryKey : List String           -- functional dependencies
  nullable : List String             -- columns that allow NULL
  checks : List Logic                -- CHECK constraints (guaranteed predicates)

-- Extended database with schema info
structure DatabaseWithSchema where
  tables : String → Table
  schemas : String → TableSchema
```

Primary key information is critical for QED's stabilization phase — it enables
eliminating redundant summation variables.

### Proving translation correctness

The translation must be shown to preserve semantics:

```lean
theorem translate_correct (s : SelectStmt) (db : DatabaseWithSchema) :
    denoteBag (translate s) (envOf db) = evalSelect db.tables s
```

This is the single hardest theorem in the entire plan. It connects the
operational semantics (`evalSelect` — our current evaluator) to the
denotational semantics (`denoteBag` — the U-semiring interpretation).

**Strategy:** Prove it incrementally:
1. Start with SELECT-FROM-WHERE (single table, no joins) — straightforward
2. Add joins — requires the row-merge / cross-product correspondence
3. Add DISTINCT — requires squash ↔ `List.eraseDups` correspondence
4. Add set operations — requires add/mul ↔ append/filter correspondence
5. Leave aggregation and correlated subqueries as axioms initially

Alternatively, take the entire translation as a **trusted axiom** initially
and refine later. This is pragmatic — the translation is a small, auditable
function, and QED's own correctness argument rests on the same translation
being correct.

---

## 5. Phase 3: QED Certificate Output

### Goal

Fork QED and modify it to emit a machine-checkable **proof certificate** rather
than just a boolean result.

### Current QED pipeline (what to instrument)

```rust
// pipeline.rs — current signature
pub fn unify(ctx: &Ctx, r1: &Relation, r2: &Relation) -> bool

// Proposed change: return a certificate
pub fn unify(ctx: &Ctx, r1: &Relation, r2: &Relation) -> Option<Certificate>
```

### Certificate format

```rust
/// A proof certificate for query equivalence
#[derive(Serialize)]
struct Certificate {
    /// The two queries being compared
    query1: Relation,
    query2: Relation,
    /// Schema information used
    schemas: Vec<TableSchema>,
    /// The normalized form of query1
    normal1: NormalForm,
    /// The normalized form of query2
    normal2: NormalForm,
    /// Trace of normalization steps for query1
    trace1: Vec<RewriteStep>,
    /// Trace of normalization steps for query2
    trace2: Vec<RewriteStep>,
    /// How the normal forms were unified
    unification: UnificationProof,
}

#[derive(Serialize)]
enum RewriteStep {
    /// Apply a semiring law (e.g., distribute mul over add)
    SemiringLaw { law: SemiringLaw, position: Path },
    /// Evaluate/simplify a sub-expression
    Eval { from: UExpr, to: UExpr },
    /// Push a predicate into a sum
    PredPush { pred: Logic, into: UExpr },
    /// Eliminate a redundant summation variable (requires SMT justification)
    StabilizeElim { var: VL, witness: SmtCertificate },
    /// Merge congruent variables
    StabilizeMerge { var1: VL, var2: VL, witness: SmtCertificate },
}

#[derive(Serialize)]
enum SemiringLaw {
    AddComm, AddAssoc, AddZeroLeft, AddZeroRight,
    MulAssoc, MulOneLeft, MulOneRight,
    MulZeroLeft, MulZeroRight,
    MulAddLeft, MulAddRight,
    SquashIdem, SquashZero, SquashOne, SquashMul,
    NotZero, NotOne, NotSquashNonzero,
    PredTt, PredFf, PredAnd, PredOr, PredNot,
    SumZero, SumAdd, SumComm, SumSquash,
}

#[derive(Serialize)]
struct UnificationProof {
    /// Permutation mapping terms of normal1 to normal2
    permutation: Vec<usize>,
    /// For each pair of matched terms, proof of equality
    term_proofs: Vec<TermProof>,
}

#[derive(Serialize)]
struct TermProof {
    /// Variable renaming / substitution
    substitution: Vec<(VL, VL)>,
    /// SMT certificate for expression equality under substitution
    expr_equality: SmtCertificate,
    /// SMT certificate for logic equality under substitution
    logic_equality: SmtCertificate,
}

/// Opaque SMT proof — format depends on Phase 5 option
#[derive(Serialize)]
enum SmtCertificate {
    /// Option A: just the query and result (trusted)
    Trusted { query: String, result: bool },
    /// Option B: Alethe/LFSC proof
    Proof { format: String, proof: Vec<u8> },
    /// Option C: simplified claim for Lean to re-decide
    Claim { formula: Logic },
}
```

### Where to instrument QED

| QED file | What to capture |
|----------|----------------|
| `syntax.rs` | Record the Relation→UExpr translation |
| `partial.rs` | Record partial evaluation steps |
| `normal.rs` | Record SPNF normalization steps (the bulk of the trace) |
| `stable.rs` | Record variable eliminations with SMT witnesses |
| `unify.rs` | Record the permutation and term-matching proofs |

### Estimated effort

QED's core is 2,520 lines of Rust. Adding certificate output is an
instrumentation task — adding `trace.push(...)` calls at each rewrite
step — not a rewrite. Estimated: 1-2 weeks.

---

## 6. Phase 4: Certificate Checker in Lean

### Goal

A small Lean 4 program that takes a `Certificate` (parsed from JSON),
replays each step against the proven semiring laws, and produces a Lean
proof term.

### Checker architecture

```lean
-- Parse certificate from JSON
def parseCertificate (json : String) : Except String Certificate := ...

-- Check a single rewrite step
def checkStep (laws : SemiringLaws) (step : RewriteStep) (current : UExpr)
    : Except String UExpr :=
  match step with
  | .semiringLaw law pos =>
    -- Look up the proven law, apply it at the given position
    applyLawAt laws law pos current
  | .stabilizeElim var witness =>
    -- Verify the SMT certificate (Option A/B/C), then apply elimination
    checkSmtCert witness >>= fun _ => eliminateVar var current
  | ...

-- Check the full certificate
def checkCertificate (cert : Certificate) : Except String (UExpr × UExpr) := do
  -- Replay trace1 to get normal form of query1
  let nf1 ← cert.trace1.foldlM (checkStep semiringLaws) cert.uexpr1
  -- Replay trace2 to get normal form of query2
  let nf2 ← cert.trace2.foldlM (checkStep semiringLaws) cert.uexpr2
  -- Verify the unification
  checkUnification cert.unification nf1 nf2
  -- If all checks pass, we've verified: uexpr1 =[trace1]=> nf1 =[unify]=> nf2 <=[trace2]= uexpr2
  return (cert.uexpr1, cert.uexpr2)
```

### From checked certificate to proof term

The checker's output must be a Lean proof, not just a boolean. Two approaches:

**Approach A: Proof by reflection.** Define a *decidable* checker and use
`Decidable.decide`:

```lean
def checkCertificateDecidable (cert : Certificate) : Bool := ...

theorem checkCertificateDecidable_sound (cert : Certificate) :
    checkCertificateDecidable cert = true →
    denote (translate cert.query1) = denote (translate cert.query2) := by
  intro h
  -- ... proof that the checker is sound ...
```

Then for any specific certificate:
```lean
theorem specific_equiv : query1 ≃ query2 := by
  native_decide  -- or decide, if the checker is in the Decidable instance
```

**Approach B: Tactic-based replay.** Write a Lean tactic that reads the
certificate and emits a sequence of `rw` calls:

```lean
-- A tactic that reads a certificate file and produces a proof
syntax "qed_cert" str : tactic

macro_rules
  | `(tactic| qed_cert $file) => ...
  -- Generates: rw [add_comm]; rw [mul_assoc]; ...
```

Usage:
```lean
theorem filter_pushdown_through_join :
    translate q1 = translate q2 := by
  qed_cert "certs/filter_pushdown_001.json"
```

**Approach A is preferred** — it's simpler, and `native_decide` leverages
compiled Lean code for performance.

### Estimated scope

The checker is small because the semiring laws are already proven:
- Certificate parser: ~200 LOC (JSON → Lean structures)
- Step validator: ~300 LOC (pattern match on step type, apply proven law)
- Unification validator: ~200 LOC (check permutation + SMT sub-certs)
- Proof-producing wrapper: ~100 LOC

**Total: ~800-1,000 LOC** for the trusted checker kernel.

---

## 7. Phase 5: SMT Certificate Bridging

QED relies on Z3/CVC5 at two critical points:
1. **Stabilization:** Determining that summation variables are redundant
   (quantified first-order formulas over integers, reals, strings, booleans)
2. **Unification:** Checking expression equality under substitutions

The certificate checker must handle these SMT-dependent steps. Three options:

---

### Option A: Trust SMT as Axiom

#### Approach

Add a single axiom to the Lean kernel:

```lean
-- The SMT oracle axiom
axiom smt_oracle_sound (φ : Logic) :
    smtCheck φ = true → logicValid φ

-- Where smtCheck calls Z3/CVC5 via FFI or external process
@[implemented_by smtCheckImpl]
opaque smtCheck : Logic → Bool
```

When the certificate checker encounters an SMT-backed step, it calls
`smtCheck` on the claimed formula and uses `smt_oracle_sound` to discharge
the proof obligation.

#### Trust model

```
┌──────────────────────────────────────────────┐
│  Trusted Computing Base                       │
│                                               │
│  ┌───────────┐  ┌────────────┐  ┌──────────┐│
│  │ Lean 4    │  │ U-semiring │  │ SMT      ││
│  │ kernel    │  │ laws       │  │ oracle   ││
│  │           │  │ (proven)   │  │ (axiom)  ││
│  └───────────┘  └────────────┘  └──────────┘│
└──────────────────────────────────────────────┘
```

#### Pros

- **Fastest to implement** — no SMT proof parsing needed
- **Pragmatic** — this is what most verified systems do initially
  (e.g., Verasco, VeriML, early CompCert)
- **High coverage** — any formula Z3/CVC5 can decide, we can use
- **Compatible with current axiom budget** — we already have 12 axioms;
  one more (well-scoped) axiom is a modest increase in trust
- **Z3/CVC5 are battle-tested** — billions of queries, extensive fuzzing

#### Cons

- **Z3 bugs exist** — Z3 has had soundness bugs (though rare)
- **Not independently checkable** — you must trust the SMT solver binary
- **Audit difficulty** — "does this axiom cover what we think?" requires
  understanding the SMT formula encoding
- **Not publishable as "fully verified"** — reviewers will note the SMT trust

#### Mitigations

- Run **both** Z3 and CVC5 (if both agree, bugs are far less likely)
- Log all SMT queries for **offline auditing**
- Limit the SMT axiom scope: only for quantifier-free LIA/LRA/strings,
  not arbitrary first-order logic
- Maintain a **regression test suite** of formulas with known answers

#### Implementation sketch

```lean
-- In a new file: SqlEquiv/SmtOracle.lean

/-- External SMT solver interface -/
@[implemented_by smtCheckFFI]
opaque smtCheck : Logic → Bool

/-- Trust axiom: if the SMT solver says valid, it's valid.
    This is the ONLY axiom added by the oracle approach. -/
axiom smt_oracle_sound (φ : Logic) :
    smtCheck φ = true → ∀ env : Env, evalLogic env φ = true

/-- Convenience: use SMT to close a goal -/
macro "smt" : tactic => `(tactic| exact smt_oracle_sound _ (by native_decide))
```

#### Estimated effort

- Lean FFI to Z3: 1 week (or shell out to z3 binary)
- Axiom + wrapper: 1 day
- Testing: 1 week
- **Total: 2-3 weeks**

---

### Option B: Verify SMT Proof Certificates (Alethe/LFSC)

#### Approach

Instead of trusting the SMT solver, require it to produce a **proof
certificate** in a standard format, then verify that certificate in Lean.

Modern SMT solvers support proof output:
- **Z3**: LFSC proofs (via `set-option :produce-proofs true`)
- **CVC5**: Alethe proofs (the emerging standard, SMTLIB-compatible)

```
┌────────┐         ┌─────────────┐        ┌───────────────┐
│ QED    │ ──φ──→ │ CVC5        │ ──π──→ │ Lean checker  │
│ prover │         │ SMT solver  │         │ (Alethe→Lean) │
└────────┘         └─────────────┘        └───────────────┘
                   Returns proof π         Verifies π
                   of validity of φ        against Lean
                                           proof rules
```

#### Alethe proof format

Alethe (Barbosa et al., 2023) is a proof format for SMT solvers:

```smt2
(assume a1 (not (= (+ x 0) x)))
(step t1 (cl (= (+ x 0) x)) :rule la_generic :args (1))
(step t2 (cl) :rule resolution :premises (a1 t1))
```

Each step references a **rule** (from a fixed set of ~100 rules covering
propositional logic, arithmetic, equality, quantifiers) and **premises**
(earlier steps or assumptions).

#### Lean proof rule implementation

For each Alethe rule, we need a proven Lean lemma:

```lean
-- Example: the la_generic rule (linear arithmetic)
-- In practice this would be more granular
theorem alethe_la_generic (coeffs : List Int) (lits : List Logic)
    (h : linearCombCheck coeffs lits = true) :
    disjunction lits := by ...

-- Example: resolution rule
theorem alethe_resolution (c1 c2 : Clause) (pivot : Logic)
    (h1 : pivot ∈ c1) (h2 : Logic.not pivot ∈ c2) :
    resolvent c1 c2 pivot ⊆ clauseUnion (c1.erase pivot) (c2.erase (Logic.not pivot)) := by ...
```

#### The Alethe rule set

| Category | Rules | Lean difficulty |
|----------|-------|-----------------|
| Propositional | ~20 (resolution, factoring, etc.) | Easy — boolean algebra |
| Equality | ~10 (congruence, transitivity, etc.) | Easy — `Eq` lemmas |
| Linear arithmetic | ~15 (Farkas, cuts, etc.) | Medium — need `omega` or custom |
| Quantifiers | ~10 (instantiation, skolemization) | Hard — first-order logic |
| Arrays/datatypes | ~15 | Medium — algebraic reasoning |
| Strings | ~10 | Hard — string theory |

#### Trust model

```
┌──────────────────────────────────────────────┐
│  Trusted Computing Base                       │
│                                               │
│  ┌───────────┐  ┌────────────┐               │
│  │ Lean 4    │  │ U-semiring │               │
│  │ kernel    │  │ laws       │               │
│  │           │  │ (proven)   │               │
│  └───────────┘  └────────────┘               │
│                                               │
│  ┌────────────────────────────┐              │
│  │ Alethe checker (proven)    │              │
│  │ ~100 rules, each a lemma   │              │
│  └────────────────────────────┘              │
└──────────────────────────────────────────────┘

NOT in TCB: Z3, CVC5, QED — all produce checkable artifacts
```

#### Pros

- **No SMT trust** — the solver is completely untrusted
- **Publishable** — "fully verified SQL equivalence" is a strong claim
- **Catches solver bugs** — any Z3/CVC5 bug manifests as a failed check
- **Standard format** — Alethe is gaining traction; investment pays off
  for other projects too
- **Precedent** — SMTCoq (Coq) and Hammers (Isabelle) do this successfully

#### Cons

- **Large implementation effort** — the Alethe checker is ~100 rules,
  each requiring a Lean proof. SMTCoq took years.
- **Proof output is fragile** — SMT solver proof generation is less
  stable than solving; proofs can be huge (megabytes)
- **Performance** — checking large proofs can be slow; proof certificates
  for quantified formulas are especially large
- **Incomplete rule coverage** — we may not need all 100 rules; QED
  uses a specific fragment (QF_LIA, QF_LRA, QF_S, QF_BV isn't needed)
- **Maintenance burden** — solver proof formats evolve; we'd need to
  track Alethe spec updates

#### Reducing scope

We don't need the full Alethe checker. QED's SMT usage falls into a
narrow fragment:

1. **Quantifier-free linear integer arithmetic** (QF_LIA) — for column
   equality, key constraints
2. **Quantifier-free equality with uninterpreted functions** (QF_UF) —
   for expression equivalence
3. **Quantifier-free strings** (QF_S) — for LIKE patterns, CONCAT
4. **Quantified LIA** — for stabilization (∀x. φ(x) → ψ(x))

A **focused checker** covering ~30 rules (propositional + equality +
linear arithmetic) would handle the vast majority of QED's SMT calls.

#### Existing work to build on

- **SMTCoq** (Coq): Full Alethe checker in Coq. Could study its
  architecture for Lean port.
- **Lean 4 `omega` tactic**: Already handles LIA in Lean's kernel.
  We could delegate arithmetic steps to `omega`.
- **Lean 4 `simp` with `Decidable`**: Propositional steps could use
  `decide`.

#### Implementation plan

1. Define `AletheProof` AST in Lean (~200 LOC)
2. Implement propositional rules (~500 LOC, easy)
3. Implement equality rules (~300 LOC, easy)
4. Implement linear arithmetic rules (~800 LOC, medium — delegate to `omega`)
5. Implement quantifier instantiation (~400 LOC, medium)
6. Skip string theory rules initially (use Option A for those)

**Total: ~2,200 LOC, estimated 2-3 months**

#### Hybrid approach

A practical compromise: use Option B for the decidable fragments
(propositional + equality + LIA) and Option A for the rest (strings,
quantified formulas). This gives high assurance for the common case
while keeping the implementation tractable:

```lean
def checkSmtCert : SmtCertificate → Except String Unit
  | .aletheProof pf => verifyAlethe pf         -- Option B: fully verified
  | .trusted query result => do                  -- Option A: trust fallback
    guard (smtCheck query = result)
    pure ()
```

---

### Option C: Lean-Native Decision Procedures

#### Approach

Instead of checking SMT proof certificates, re-decide the claimed formulas
entirely within Lean using its own decision procedures.

```
┌────────┐                    ┌───────────────────────┐
│ QED    │ ──claim──────────→│ Lean decision          │
│ prover │   "∀x. f(x)=g(x)" │ procedures             │
└────────┘                    │                        │
                              │ omega (LIA)            │
                              │ decide (propositional) │
                              │ simp (rewriting)       │
                              │ native_decide (bool)   │
                              └───────────────────────┘
```

The certificate includes only the **claim** (the formula), not a proof.
Lean must independently verify it.

#### Available Lean 4 decision procedures

| Procedure | Fragment | Source | Performance |
|-----------|----------|--------|-------------|
| `decide` | Finite/decidable propositions | Lean core | Slow for large instances |
| `native_decide` | Same, compiled to native code | Lean core | Fast |
| `omega` | Linear integer arithmetic (LIA) | Lean core (since v4.3) | Good for small formulas |
| `simp` | Equational rewriting | Lean core + local simp lemmas | Depends on lemma set |
| `norm_num` | Numeric normalization | Mathlib | Requires Mathlib dependency |
| `polyrith` | Polynomial arithmetic | Mathlib | Requires Mathlib dependency |
| `aesop` | Automated reasoning | Mathlib | General-purpose, requires Mathlib |

**Dependency note:** `decide`, `native_decide`, `omega`, and `simp` are available
from Lean core with no extra dependencies. `norm_num`, `polyrith`, and `aesop`
require a Mathlib dependency. This project currently uses only Batteries (via Std).
If Option C needs Mathlib tactics, adding Mathlib as a dependency would need to be
evaluated for build-time and maintenance impact.

#### Trust model

```
┌──────────────────────────────────────────────┐
│  Trusted Computing Base                       │
│                                               │
│  ┌───────────┐  ┌────────────┐               │
│  │ Lean 4    │  │ U-semiring │               │
│  │ kernel    │  │ laws       │               │
│  │           │  │ (proven)   │               │
│  └───────────┘  └────────────┘               │
│                                               │
│  (Nothing else — all decisions are            │
│   kernel-checked via Lean's type theory)      │
└──────────────────────────────────────────────┘

NOT in TCB: Z3, CVC5, QED, SMT proofs
```

This is the **smallest possible trusted computing base.**

#### Pros

- **Zero external trust** — everything is Lean kernel-checked
- **Simplest certificate format** — just claims, no proof artifacts
- **No SMT proof parsing** — avoids the fragility of proof output
- **Leverages Lean ecosystem** — `omega`, `decide`, `simp` are maintained
  by the Lean community
- **Best for publication** — strongest formal verification claim possible

#### Cons

- **Limited fragment coverage** — Lean's built-in procedures handle LIA
  but not strings, reals (QF_LRA), or quantified formulas well
- **Performance** — `omega` is slower than Z3 for large formulas; `decide`
  is exponential for propositional logic
- **Quantifier handling** — QED's stabilization requires ∀-quantified
  formulas; Lean has no built-in ∀-decider for arithmetic
- **String theory** — no native Lean decision procedure for string
  constraints (LIKE patterns, CONCAT properties)
- **May not cover all QED cases** — some QED proofs require reasoning
  that Lean's tactics can't automate

#### What this covers and what it doesn't

| QED's SMT usage | Lean tactic | Coverage |
|-----------------|-------------|----------|
| Variable equality (x = y under constraints) | `decide`/`simp` | Full |
| Linear arithmetic (3x + 2y ≤ 5z) | `omega` | Full (integers) |
| Propositional combinations | `decide` | Full |
| Quantified LIA (∀x. P(x) → Q(x)) | None built-in | **Gap** |
| String equality/LIKE | None built-in | **Gap** |
| Real arithmetic | `norm_num` (limited) | Partial |
| NULL propagation logic | Custom tactic | Needed |

#### Filling the gaps

**For quantified LIA:** We could implement a **bounded quantifier
elimination** procedure. QED's quantified formulas arise from schemas
with finite domains (table rows). If we can bound the quantification:

```lean
-- If the domain is finite, ∀ becomes a conjunction
theorem forall_fin_iff (P : Fin n → Prop) [DecidablePred P] :
    (∀ i, P i) ↔ (List.range n).Forall (fun i => P ⟨i, by omega⟩) := by ...
```

**For strings:** Implement a small decision procedure for the string
fragment QED actually uses:
- String equality: `decide`
- CONCAT associativity: proven lemma + `simp`
- LIKE pattern matching: decision procedure over regex

**For NULL logic:** Write a `null_decide` tactic that handles three-valued
logic by case-splitting on NULL/non-NULL:

```lean
-- Custom tactic for three-valued logic
macro "null_decide" : tactic => `(tactic|
  simp only [evalLogic, evalNullLogic];
  cases ‹Option Value› with
  | none => simp
  | some v => cases v with
    | null _ => simp
    | _ => decide)
```

#### Implementation plan

1. Define the claim format (subset of `Logic`) — ~100 LOC
2. Write a claim dispatcher that routes to the right tactic — ~200 LOC
3. Implement `null_decide` for three-valued logic — ~300 LOC
4. Test against QED's actual SMT queries to find coverage gaps — 1 week
5. Implement string fragment decision procedure — ~500 LOC
6. For uncovered cases, fall back to Option A (trust axiom) — ~50 LOC

**Total: ~1,200 LOC, estimated 1-2 months**

#### Performance considerations

The main risk is performance. QED makes ~10 SMT calls per query pair,
each typically resolved in <100ms by Z3. If Lean's `omega` takes 10x
longer per call, the total overhead is ~10 seconds per query pair —
acceptable for batch verification but slow for interactive use.

Mitigation: use `native_decide` where possible (compiles to native code),
and cache verified claims.

---

### Recommendation: Phased Option C→B→A

Start with the highest-assurance option and fall back as needed:

```
┌─────────────────────────────────────────────────────┐
│  Phase 5a: Option C for what Lean can decide         │
│  (propositional, LIA, simple equality)               │
│  Coverage: ~60-70% of QED's SMT calls                │
│                                                       │
│  Phase 5b: Option B for arithmetic certificates       │
│  (Alethe proofs for QF_LIA, QF_UF)                   │
│  Coverage: +20-25%, total ~85-90%                     │
│                                                       │
│  Phase 5c: Option A for the long tail                 │
│  (trust axiom for strings, complex quantifiers)       │
│  Coverage: remaining ~10-15%                          │
│                                                       │
│  TOTAL: 100% of QED's provable cases                 │
│  Trust: 1 scoped axiom for ~10-15% of SMT calls      │
└─────────────────────────────────────────────────────┘
```

This gives a clear **trust budget**: "100% of algebraic rewrites are
kernel-checked; 85-90% of SMT steps are kernel-checked; the remaining
10-15% use a scoped trust axiom for string/quantifier reasoning."

---

## 8. Phase 6: Integration and Migration

### Step 1: Parallel existence

The new oracle-based system runs alongside the current `Equiv/` module.
No existing theorems are deleted. The oracle provides an **additional**
path to proving equivalences.

```
SqlEquiv/
├── Ast.lean                    -- KEEP (shared)
├── Semantics*.lean             -- KEEP (shared, reference implementation)
├── Equiv/                      -- KEEP (current hand proofs)
│   ├── ExprAxioms.lean
│   ├── StatementAxioms.lean
│   └── ...
├── USemiring/                  -- NEW (Phase 1)
│   ├── Defs.lean               -- UExpr, Logic, etc.
│   ├── Laws.lean               -- Semiring law proofs
│   └── Denote.lean             -- Denotational semantics
├── Translate/                  -- NEW (Phase 2)
│   ├── SqlToUExpr.lean         -- translate function
│   └── Correctness.lean        -- translation correctness
├── Oracle/                     -- NEW (Phases 4-5)
│   ├── Certificate.lean        -- Certificate AST
│   ├── Checker.lean            -- Certificate checker
│   ├── SmtBridge.lean          -- SMT certificate handling
│   └── Tactic.lean             -- qed_cert tactic
└── Parser.lean, Pretty.lean    -- KEEP (shared)
```

### Step 2: Prove current axioms via oracle

The 12 remaining axioms become test cases for the oracle:

| Current axiom | Oracle path |
|---------------|-------------|
| `join_comm` | QED normalizes both sides to same SPNF; permutation unifies |
| `join_assoc` | QED normalizes nested joins to flat SPNF |
| `filter_join_left` | QED pushes predicate into join's left operand |
| `filter_join_right` | QED pushes predicate into join's right operand |
| `order_by_idempotent` | Outside QED's scope (ORDER BY is uninterpreted) |
| `order_by_reverse` | Outside QED's scope |
| Decidable axioms (3) | Not applicable (infrastructure, not equivalences) |

**8 of 12 axioms** are candidates for oracle-based proof. The remaining 4
(2 ORDER BY + 2 infrastructure) stay as-is or get hand proofs.

### Step 3: Scale up

With the oracle pipeline working, generate proofs for the Calcite and
CockroachDB test suites:

```lean
-- Auto-generated from QED certificates
theorem calcite_001 : translate q1_001 = translate q2_001 := by qed_cert "certs/calcite/001.json"
theorem calcite_002 : translate q1_002 = translate q2_002 := by qed_cert "certs/calcite/002.json"
-- ... 299 more ...
```

### Step 4: Deprecate hand proofs where oracle covers

Once the oracle path is stable, hand proofs for the same equivalences
become redundant (but not harmful). They serve as:
- **Cross-validation** — if the oracle and hand proof agree, both gain confidence
- **Fallback** — if the oracle pipeline has a bug, hand proofs still hold
- **Education** — the tutorials reference hand proofs for pedagogy

---

## 9. What Stays, What Goes

### Keep (valuable as-is)

| Component | Reason |
|-----------|--------|
| `Ast.lean` | Shared SQL AST; QED input maps to this |
| `Parser.lean` | SQL string → AST; no change needed |
| `Pretty.lean` | AST → SQL string; useful for debugging |
| `SemanticsBase.lean` | Operator semantics (evalBinOp etc.) |
| `SemanticsCore.lean` | Reference implementation for translation proof |
| `Semantics.lean` | Practical evaluator; test oracle |
| `Equiv/ValueLemmas.lean` | 38 proven lemmas about values |
| `Equiv/ExprAxioms.lean` | 42 proven expression lemmas |
| `Equiv/SetBagLemmas.lean` | 6 proven set/bag lemmas |
| All 486 proven theorems | Cross-validation with oracle |
| Test infrastructure | Regression testing |
| Tutorials and docs | Educational value |

### New (to build)

| Component | Estimated LOC | Phase |
|-----------|--------------|-------|
| `USemiring/Defs.lean` | ~200 | 1 |
| `USemiring/Laws.lean` | ~600 | 1 |
| `USemiring/Denote.lean` | ~400 | 1 |
| `Translate/SqlToUExpr.lean` | ~500 | 2 |
| `Translate/Correctness.lean` | ~800 | 2 |
| `Oracle/Certificate.lean` | ~200 | 4 |
| `Oracle/Checker.lean` | ~500 | 4 |
| `Oracle/SmtBridge.lean` | ~300-2000 | 5 (depends on option) |
| `Oracle/Tactic.lean` | ~200 | 4 |
| QED fork (Rust changes) | ~500 | 3 |
| **Total** | **~4,200-5,900** | |

### Could eventually remove

| Component | When |
|-----------|------|
| Bridge axioms in `Semantics.lean` | If translation correctness is proven |
| Remaining 12 axioms | When oracle covers them or hand proofs complete |
| Optimizer specs in `docs/specs/` | If optimizer is not rebuilt |

---

## 10. Risk Analysis

### Technical risks

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Agda→Lean port harder than expected | Medium | Delays Phase 1 by weeks | Start with subset; `add/mul/squash` only |
| Translation correctness proof intractable | High | Blocks full verification | Accept as axiom initially |
| QED certificate format too coarse | Medium | Checker can't replay steps | Work with QED authors; they're responsive |
| Lean `omega` too slow for large formulas | Low | Performance degradation | Fall back to Option A for those |
| SMT proof certificates too large | Medium | Memory issues in checker | Stream/lazy evaluation; use Option C first |
| QED doesn't cover our remaining axioms | Low | Limited immediate ROI | 8 of 12 are covered; remaining 4 are hand-provable |

### Strategic risks

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| QED becomes unmaintained | Low | Fork maintenance burden | QED is active research (UC Berkeley) |
| New QED version breaks our fork | Medium | Certificate format changes | Pin to a specific commit; adapt incrementally |
| Lean 4 breaks our tactics | Low | Rebuild needed | Pin toolchain; Lean 4 is stabilizing |
| Effort exceeds one-person bandwidth | High | Stalls | Prioritize Phase 1+3+4; defer Phase 2 proof |

---

## 11. Comparison: Current vs Oracle Approach

| Dimension | Current (hand proofs) | Oracle (QED + checker) |
|-----------|----------------------|----------------------|
| **Theorems proved** | 486 | 486 + 299 Calcite + 979 CockroachDB |
| **Axioms remaining** | 12 | 3-4 (ORDER BY + Decidable) + SMT trust |
| **Effort per new equiv** | Hours to weeks | Seconds (QED) + minutes (checker) |
| **Trust base** | Lean kernel + 12 axioms | Lean kernel + ~1 SMT axiom (Option A) or 0 (Option C) |
| **SQL coverage** | Custom (whatever we prove) | QED's fragment (wide) |
| **Aggregation** | Custom semantics (ahead of QED) | Uninterpreted (QED's weakness) |
| **ORDER BY / LIMIT** | 16 proven theorems | Uninterpreted (QED's weakness) |
| **NULL handling** | Option 3 (proven) | Three-valued via Z3 optionals |
| **Join commutativity** | Blocked | Automatic (SPNF normalization) |
| **Publishability** | "486 machine-checked SQL theorems" | "Verified SQL equiv checker with 1,278+ test cases" |
| **Ongoing maintenance** | Linear in theorem count | Constant (just maintain checker) |

### Hybrid strength

The ideal is **both**: hand proofs for what's already proven (aggregation,
ORDER BY, expression-level), oracle for what's blocked or new (joins,
subquery unnesting, filter pushdown). The two approaches cover each
other's blind spots:

- **Hand proofs cover QED's gaps:** aggregation semantics, ORDER BY, LIMIT
- **Oracle covers hand-proof gaps:** join commutativity, filter pushdown, complex subquery rewrites

---

## 12. Open Questions

1. **Collaboration with QED authors?** Shuxian Wang (UC Berkeley) is the
   lead author. Reaching out could accelerate the certificate output work.

2. **Schema information flow:** QED requires schema annotations (primary
   keys, types). How do we feed these from sql_equiv's `Database` type?

3. **Bag vs set semantics:** Our `≃ᵇ` (bag) and `≃ˢ` (set) equivalence
   levels map naturally to U-semiring (bag) and squashed U-semiring (set).
   Does the certificate need to distinguish these?

4. **Aggregation strategy:** QED treats aggregation as uninterpreted.
   Our current `evalAggOverTable` gives actual semantics. Do we:
   - Keep hand proofs for aggregation?
   - Extend QED with aggregate reasoning?
   - Define aggregate laws in the U-semiring?

5. **Window functions:** Neither QED nor the current approach handles
   window function equivalences well. Defer entirely?

6. **Lean toolchain version:** The Agda→Lean port should target a stable
   Lean 4 toolchain. Which version?

7. **Monorepo or separate repo?** Should the U-semiring kernel and
   oracle checker live in sql_equiv or a separate package?

---

## 13. References

1. **QED: A Powerful Query Equivalence Decider for SQL.** Wang, Pan, Cheung.
   VLDB 2024. https://www.vldb.org/pvldb/vol17/p3602-wang.pdf

2. **Cosette: An Automated Prover for SQL.** Chu, Wang, Weitz, Cheung.
   CIDR 2017.

3. **Axiomatic Foundations and Algorithms for Deciding Semantic Equivalences
   of SQL Queries.** Chu, Weitz, Cheung, Suciu. VLDB 2018.
   https://www.vldb.org/pvldb/vol11/p1482-chu.pdf

4. **SMTCoq: A Plug-In for Integrating SMT Solvers into Coq.** Ekici et al.
   CAV 2017.

5. **Alethe: Towards a Generic SMT Proof Format.** Barbosa et al. FMCAD 2023.

6. **CompCert: Formal Verification of a Realistic Compiler.** Leroy.
   CACM 2009.

7. **Lean 4 Metaprogramming.** https://leanprover-community.github.io/lean4-metaprogramming-book/

---

## Appendix A: QED's Agda Formalization Structure

For reference, the files to port from `qed-solver/prover/agda/`:

| File | LOC (est.) | Contents | Port difficulty |
|------|-----------|----------|-----------------|
| `Syntax.agda` | ~100 | UExpr, Logic, Expr types | Easy (direct translation) |
| `Shared.agda` | ~80 | DataType, Schema, VL | Easy |
| `Partial.agda` | ~200 | Partial evaluation proofs | Medium |
| `Normal.agda` | ~300 | SPNF normalization proofs | Medium |
| `Stable.agda` | ~200 | Stabilization proofs | Medium-Hard (uses SMT) |
| `Main.agda` | ~50 | Entry point | Easy |
| **Total** | **~930** | | ~2-3 weeks |

## Appendix B: Timeline Estimate

| Phase | Description | Effort | Dependencies |
|-------|-------------|--------|--------------|
| 1 | U-semiring kernel in Lean | 3-4 weeks | None |
| 2 | SQL→UExpr translation | 2-3 weeks | Phase 1 |
| 3 | QED certificate output (Rust) | 1-2 weeks | None (parallel with 1-2) |
| 4 | Certificate checker in Lean | 2-3 weeks | Phases 1, 3 |
| 5a | Option C (Lean-native) | 3-4 weeks | Phase 4 |
| 5b | Option B (Alethe subset) | 6-8 weeks | Phase 4 |
| 5c | Option A (SMT trust) | 1-2 weeks | Phase 4 |
| 6 | Integration + migration | 2-3 weeks | Phases 4, 5 |
| **Total (C→A path)** | | **~14-19 weeks** | |
| **Total (full B path)** | | **~20-27 weeks** | |

**Recommended path:** Phases 1+3 in parallel (4 weeks) → Phase 4 (3 weeks)
→ Phase 5c/Option A (2 weeks) → working system in ~9 weeks. Then
incrementally upgrade to Option C/B.
