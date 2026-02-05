# Float Proof Strategies in Lean 4

References and strategies for handling IEEE 754 floats in formal proofs,
relevant to the SQL type system expansion (see `PLAN_expand_types.md`).

## Background: Lean's `Float` is opaque

Lean's built-in `Float` compiles to C `double` (IEEE 754 binary64) but is
opaque to the kernel — it cannot reduce float expressions or do structural
induction. `decide` and `native_decide` don't work on float propositions.

Reference: https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/

## Strategies

### 1. Axiomatize needed properties (recommended for us)

Declare the float properties we rely on as axioms without proving them from
IEEE 754 first principles. For SQL equivalence we only need:

- Commutativity: `a + b = b + a`, `a * b = b * a`
- Identity: `a + 0.0 = a`, `a * 1.0 = a`
- Type-mismatch operations return null

We are proving SQL-level equivalences, not IEEE 754 compliance, so this is
sufficient and avoids a massive formalization effort.

### 2. FloatSpec — verified IEEE 754 in Lean 4

Port of Coq's Flocq library. Provides executable reference operations
(alignment, plus, minus, multiply, sqrt) with Hoare-triple specifications.
Actively developed, many theorems still `sorry`. Uses Mathlib v4.25.0-rc1.

- Repository: https://github.com/Beneficial-AI-Foundation/FloatSpec
- Reservoir: https://reservoir.lean-lang.org/@Beneficial-AI-Foundation/FloatSpec

### 3. Flean — floats via rational rounding

Defines floats as rounded rationals (`Rat`). Arithmetic operations are
"correctly rounded exact values." Avoids opaqueness by working in `Rat`
and only converting at boundaries.

- Blog post: https://josephmckinsey.com/flean2.html

### 4. Avoid `Float` in proofs entirely

Use `Rat` or Mathlib's `Real` for proof-level reasoning. Only use `Float`
at execution boundaries (parsing, pretty-printing, runtime evaluation).
Cleanest approach if proofs don't need rounding behavior.

## Historical context

FloatSpec's lineage traces to **Flocq** in Coq, used by the CompCert
verified C compiler for its floating-point semantics. CompCert extended
Flocq to handle signed zeros and special values (NaN, infinity).

- CompCert float verification: https://xavierleroy.org/publi/floating-point-compcert.pdf
- General FP verification survey: https://www.cl.cam.ac.uk/~jrh13/papers/sfm.pdf

## Decision for sql_equiv

We use **strategy 1 (axiomatize)** for now. If FloatSpec matures, we could
swap axioms for verified lemmas later without changing the proof structure.
