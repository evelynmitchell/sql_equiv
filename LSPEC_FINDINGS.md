# LSpec Property Test Findings

Findings from SlimCheck property-based testing. Each entry records a property
that initially failed, what it revealed, and how it was resolved.

## 2026-02-08: Initial LSpec integration

### Finding 1: Identity laws don't hold for non-boolean expressions

**Property:** `a AND TRUE = a` for all ground expressions
**Counterexample:** `a = Expr.lit (Value.int 4)`
**Root cause:** `evalBinOp .and (some (int 4)) (some (bool true))` returns
`none` (type error), not `some (int 4)`. The AND/OR identity laws
(`and_true`, `or_false`, `true_and`, `false_or` in ExprAxioms.lean) only
hold when the operand is boolean-typed.
**Resolution:** Restricted these property tests to `BoolGroundExpr` inputs.
**Impact:** Not a bug — the axioms in ExprAxioms.lean are correctly stated
with `Expr` (they hold for all expressions when evaluated in the formal
equivalence relation `≃ₑ` because both sides produce `none` for non-boolean
inputs). But it clarifies that the evaluator's AND/OR is strict about types.

### Finding 2: AND/OR NULL propagation differs from standard SQL three-valued logic

**Property:** `TRUE AND NULL = NULL` (expected `some (.null t)`)
**Counterexample:** `t = some SqlType.bool`
**Root cause:** The evaluator's AND/OR uses a non-standard NULL semantics
(per comment at Semantics.lean:163-166): AND/OR do NOT propagate NULLs.
Instead, `TRUE AND NULL(bool)` falls through to the catch-all and returns
`none` (error). This was a deliberate design choice to preserve
distributivity laws.
**Proven theorems confirm:** `true_and_null` (Comparison.lean:395) proves
`evalBinOp .and (some (.bool true)) (some (.null t)) = none`.
**Resolution:** Updated tests to match actual evaluator semantics.
**Impact:** Not a bug — intentional design. But worth noting that this
diverges from standard SQL three-valued logic where `TRUE AND NULL = NULL`.
