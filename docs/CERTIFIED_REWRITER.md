# Certified Expression Rewriter

## Overview

The certified rewriter (`SqlEquiv/Rewriter.lean`) is a bottom-up expression simplifier where **every simplification step is justified by an existing proven theorem**. The core function `certifiedRewrite` takes an `Expr` and returns both the simplified expression and a proof of equivalence:

```lean
def certifiedRewrite : (e : Expr) → { e' : Expr // e ≃ₑ e' }
```

The return type `{ e' : Expr // e ≃ₑ e' }` is a subtype: a pair of a simplified expression `e'` and a proof that `e` is semantically equivalent to `e'`. This means the rewriter **cannot produce incorrect simplifications** — any bug would be a compile-time error, not a runtime one.

**Zero axioms. Zero sorry. Fully proven.**

## Simplification Rules

The rewriter implements **34 rules**: 24 unconditional + 10 conditional (guarded by static type checks).

### Boolean Short-Circuit (4 rules, unconditional)

| Input | Output | Theorem |
|-------|--------|---------|
| `e AND FALSE` | `FALSE` | `and_false` |
| `FALSE AND e` | `FALSE` | `false_and` |
| `e OR TRUE` | `TRUE` | `or_true` |
| `TRUE OR e` | `TRUE` | `true_or` |

### NOT Comparison Flips (6 rules, unconditional)

| Input | Output | Theorem |
|-------|--------|---------|
| `NOT (a = b)` | `a <> b` | `not_eq_is_ne` |
| `NOT (a <> b)` | `a = b` | `not_ne_is_eq` |
| `NOT (a < b)` | `a >= b` | `not_lt_is_ge` |
| `NOT (a <= b)` | `a > b` | `not_le_is_gt` |
| `NOT (a > b)` | `a <= b` | `not_gt_is_le` |
| `NOT (a >= b)` | `a < b` | `not_ge_is_lt` |

### NOT EXISTS Flip (2 rules, unconditional)

| Input | Output | Theorem |
|-------|--------|---------|
| `NOT (EXISTS sel)` | `NOT EXISTS sel` (flip negation flag) | `not_not_exists` |
| `NOT (NOT EXISTS sel)` | `EXISTS sel` (flip negation flag) | `not_exists_true_flip` |

### BETWEEN Expansion (1 rule, unconditional)

| Input | Output | Theorem |
|-------|--------|---------|
| `e BETWEEN lo AND hi` | `e >= lo AND e <= hi` | `between_expansion` |

### NOT BETWEEN (1 rule, unconditional)

| Input | Output | Theorem |
|-------|--------|---------|
| `NOT (e BETWEEN lo AND hi)` | `e < lo OR e > hi` | `not_between_expansion` |

### IN List (4 rules, unconditional)

| Input | Output | Theorem |
|-------|--------|---------|
| `e IN ()` | `FALSE` | `in_empty_false` |
| `e NOT IN ()` | `TRUE` | `not_in_empty_true` |
| `e IN (a)` | `e = a` | `in_singleton` |
| `e NOT IN (a)` | `e <> a` | `not_in_singleton` |

### CASE (5 rules, unconditional)

| Input | Output | Theorem |
|-------|--------|---------|
| `CASE WHEN TRUE THEN x ELSE y` | `x` | `case_when_true` |
| `CASE WHEN FALSE THEN x ELSE y` | `y` | `case_when_false` |
| `CASE WHEN FALSE THEN x` | `NULL` | `case_when_false_no_else` |
| `CASE ELSE y` (empty branches) | `y` | `case_empty_else` |
| `CASE` (empty, no else) | `NULL` | `case_empty_no_else` |

### LIKE (1 rule, unconditional)

| Input | Output | Theorem |
|-------|--------|---------|
| `e LIKE ''` | `e = ''` | `like_empty_pattern` |

### Boolean Identity (4 rules, conditional)

| Input | Output | Guard | Theorem |
|-------|--------|-------|---------|
| `e AND TRUE` | `e` | `e.isDefinitelyBool` | `and_true` |
| `TRUE AND e` | `e` | `e.isDefinitelyBool` | `true_and` |
| `e OR FALSE` | `e` | `e.isDefinitelyBool` | `or_false` |
| `FALSE OR e` | `e` | `e.isDefinitelyBool` | `false_or` |

### Double Negation (1 rule, conditional)

| Input | Output | Guard | Theorem |
|-------|--------|-------|---------|
| `NOT (NOT e)` | `e` | `e.isDefinitelyBool` | `not_not` |

### Arithmetic Identity (5 rules, conditional)

| Input | Output | Guard | Theorem |
|-------|--------|-------|---------|
| `e + 0` | `e` | `e.isDefinitelyInt` | `expr_add_zero` |
| `0 + e` | `e` | `e.isDefinitelyInt` | `expr_zero_add` |
| `e * 1` | `e` | `e.isDefinitelyInt` | `expr_mul_one` |
| `1 * e` | `e` | `e.isDefinitelyInt` | `expr_one_mul` |
| `e - 0` | `e` | `e.isDefinitelyInt` | `expr_sub_zero` |

## Static Type Guards

Conditional rules require knowing that an expression always evaluates to a specific type. The rewriter uses conservative **static type guards** — pure syntactic checks that return `true` only when the expression is guaranteed to produce the expected type for any row/database context.

### `Expr.isDefinitelyBool`

Returns `true` for expressions guaranteed to evaluate to `some (.bool _)`:

- Boolean literals (`TRUE`, `FALSE`)
- `IS NULL` / `IS NOT NULL` (always return a bool)
- `NOT e` where `e` is definitely bool
- `e AND f` / `e OR f` where both are definitely bool
- `EXISTS sel` / `NOT EXISTS sel`

**Excluded** (can return `none` or `null`):
- Comparisons (`=`, `<>`, `<`, etc.) — `Value.eq`/`Value.compare` return `none` on type mismatch
- `BETWEEN` — defined via comparisons that propagate null
- `IN (list)` — folds with `evalBinOp .or/.eq` which propagate null

### `Expr.isDefinitelyInt`

Returns `true` for expressions guaranteed to evaluate to `some (.int _)`:

- Integer literals
- `e + f`, `e - f`, `e * f` where both operands are definitely int
- `-e` where `e` is definitely int

**Excluded**:
- `DIV`, `MOD` — division by zero returns `none`

### Bridge Lemmas

Two proven theorems connect static guards to semantic predicates:

```lean
theorem isDefinitelyBool_implies_isBoolValued (e : Expr) (h : e.isDefinitelyBool = true) :
    e.isBoolValued

theorem isDefinitelyInt_implies_isIntValued (e : Expr) (h : e.isDefinitelyInt = true) :
    e.isIntValued
```

These allow conditional rules to use the `if h : guard then ... else ...` pattern: when the guard succeeds, the bridge lemma converts it to the semantic predicate needed by the equivalence theorem.

## Architecture

### Bottom-Up Traversal

`certifiedRewrite` recursively simplifies subexpressions first, then applies top-level simplifications. This ensures inner rewrites compose correctly with outer ones.

The rewriter recurses into **all Expr subexpressions**: `binOp`, `unaryOp`, `between`, `inList` (both expression and values), `func` arguments, `case` (branch conditions, results, and else clause), `agg` arguments, `windowFn` arguments, and `inSubquery` expressions.

**Remaining limitation**: `SelectStmt` payloads inside `.exists`, `.subquery`, and `.inSubquery` are NOT recursed into (they contain `SelectStmt`, not just `Expr`).

For example, `NOT(NOT(IS_NULL(x))) AND TRUE`:
1. Inner: `NOT(NOT(IS_NULL(x)))` rewrites to `IS_NULL(x)` (conditional NOT-NOT, guard passes)
2. Outer: `IS_NULL(x) AND TRUE` rewrites to `IS_NULL(x)` (conditional AND TRUE, guard passes)

### Proof Chaining

The rewriter uses a split architecture: `certifiedRewriteAux` (computation, WFR) + `certifiedRewriteAux_equiv` (proof, strong induction) + `certifiedRewrite` (wrapper returning subtype). This avoids eq_def derivation failures in Lean's WFR compiler.

Each case proves equivalence by:
1. Recursive IH: each subexpression is equivalent to its rewrite
2. Congruence: the parent node with rewritten subexpressions is equivalent
3. Simplification: the simplified form is equivalent to the congruent form
4. Transport: chain via `expr_equiv_trans` and bridge across the WFR unfolding

### Special NOT(BETWEEN) Handling

BETWEEN is normally expanded to `AND(GE, LE)` bottom-up. But `NOT(BETWEEN)` needs special treatment: if BETWEEN expands first, the NOT(BETWEEN) pattern is lost. The rewriter handles `NOT(BETWEEN e lo hi)` as a dedicated match arm, expanding directly to `e < lo OR e > hi` using `not_between_expansion`.

### Congruence Lemmas

The rewriter uses internal (private) congruence lemmas that propagate equivalence through each node type:
- `between_congr`, `inList_congr_expr`, `inList_congr_vals` — BETWEEN and IN list
- `func_congr` — function arguments
- `case_congr` — CASE branches and else clause (uses `evalCaseHelper_map_congr`)
- `agg_congr`, `windowFn_congr` — trivially true (eval returns `none` for these)
- `inSubquery_congr_expr` — IN subquery expression

These are implementation details of the rewriter proof, not part of the public API.

## Usage

```lean
open SqlEquiv

-- Simplify an expression
let input := Expr.binOp .and (Expr.col ⟨none, "x"⟩) (Expr.lit (.bool false))
let ⟨result, proof⟩ := certifiedRewrite input
-- result = Expr.lit (.bool false)
-- proof : Expr.binOp .and (Expr.col ⟨none, "x"⟩) (Expr.lit (.bool false)) ≃ₑ Expr.lit (.bool false)
```

The proof witness can be used with `expr_equiv_subst` to substitute equivalent expressions in any evaluation context.

## Phases

- **Phase 1** (PR #187): 24 unconditional rules. No type preconditions.
- **Phase 2a** (PR #188): 10 conditional rules guarded by `isDefinitelyBool`/`isDefinitelyInt` static type checks.
- **Phase 2b** (this PR): Complete recursion into all Expr subexpressions (func args, CASE branches/else, IN list values, agg/windowFn args, inSubquery expr). Uses well-founded recursion with `termination_by sizeOf`.

## Testing

- **79 unit tests** (`Test/RewriterTest.lean`): structural tests for each rule, guard-pass and guard-fail cases, bottom-up composition, conditional composition, idempotency, leaf node preservation, and subexpression recursion (func, case, inList vals, agg, windowFn, inSubquery).
- **LSpec property tests** (`LSpecTests/RewriterProperties.lean`): SlimCheck-powered tests for semantic equivalence across random expressions (bool/int/bounded generators), structural idempotency, BETWEEN elimination, short-circuit properties, boolean/arithmetic identity, and NOT-NOT.
- **Compile-time verification**: the type signature `{ e' : Expr // e ≃ₑ e' }` means Lean's type checker verifies correctness at compile time. Tests confirm the evaluator agrees with the proofs.

## File Layout

| File | Lines | Purpose |
|------|-------|---------|
| `SqlEquiv/Rewriter.lean` | ~750 | Rewriter implementation, type guards, bridge lemmas, congruence lemmas, WFR proof |
| `Test/RewriterTest.lean` | ~470 | Unit tests (79 tests) |
| `LSpecTests/RewriterProperties.lean` | ~300 | LSpec property tests |
