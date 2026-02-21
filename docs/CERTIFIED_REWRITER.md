# Certified Expression Rewriter

## Overview

The certified rewriter (`SqlEquiv/Rewriter.lean`) is a bottom-up expression simplifier where **every simplification step is justified by an existing proven theorem**. The core function `certifiedRewrite` takes an `Expr` and returns both the simplified expression and a proof of equivalence:

```lean
def certifiedRewrite : (e : Expr) → { e' : Expr // e ≃ₑ e' }
```

The return type `{ e' : Expr // e ≃ₑ e' }` is a subtype: a pair of a simplified expression `e'` and a proof that `e` is semantically equivalent to `e'`. This means the rewriter **cannot produce incorrect simplifications** — any bug would be a compile-time error, not a runtime one.

**Zero axioms. Zero sorry. Fully proven.**

## Simplification Rules

Phase 1 implements 24 unconditional rules (no type preconditions needed):

### Boolean Short-Circuit (4 rules)

| Input | Output | Theorem |
|-------|--------|---------|
| `e AND FALSE` | `FALSE` | `and_false` |
| `FALSE AND e` | `FALSE` | `false_and` |
| `e OR TRUE` | `TRUE` | `or_true` |
| `TRUE OR e` | `TRUE` | `true_or` |

### NOT Comparison Flips (6 rules)

| Input | Output | Theorem |
|-------|--------|---------|
| `NOT (a = b)` | `a <> b` | `not_eq_is_ne` |
| `NOT (a <> b)` | `a = b` | `not_ne_is_eq` |
| `NOT (a < b)` | `a >= b` | `not_lt_is_ge` |
| `NOT (a <= b)` | `a > b` | `not_le_is_gt` |
| `NOT (a > b)` | `a <= b` | `not_gt_is_le` |
| `NOT (a >= b)` | `a < b` | `not_ge_is_lt` |

### NOT EXISTS Flip (2 rules)

| Input | Output | Theorem |
|-------|--------|---------|
| `NOT (EXISTS sel)` | `NOT EXISTS sel` (flip negation flag) | `not_not_exists` |
| `NOT (NOT EXISTS sel)` | `EXISTS sel` (flip negation flag) | `not_exists_true_flip` |

### BETWEEN Expansion (1 rule)

| Input | Output | Theorem |
|-------|--------|---------|
| `e BETWEEN lo AND hi` | `e >= lo AND e <= hi` | `between_expansion` |

### NOT BETWEEN (1 rule)

| Input | Output | Theorem |
|-------|--------|---------|
| `NOT (e BETWEEN lo AND hi)` | `e < lo OR e > hi` | `not_between_expansion` |

### IN List (4 rules)

| Input | Output | Theorem |
|-------|--------|---------|
| `e IN ()` | `FALSE` | `in_empty_false` |
| `e NOT IN ()` | `TRUE` | `not_in_empty_true` |
| `e IN (a)` | `e = a` | `in_singleton` |
| `e NOT IN (a)` | `e <> a` | `not_in_singleton` |

### CASE (5 rules)

| Input | Output | Theorem |
|-------|--------|---------|
| `CASE WHEN TRUE THEN x ELSE y` | `x` | `case_when_true` |
| `CASE WHEN FALSE THEN x ELSE y` | `y` | `case_when_false` |
| `CASE WHEN FALSE THEN x` | `NULL` | `case_when_false_no_else` |
| `CASE ELSE y` (empty branches) | `y` | `case_empty_else` |
| `CASE` (empty, no else) | `NULL` | `case_empty_no_else` |

### LIKE (1 rule)

| Input | Output | Theorem |
|-------|--------|---------|
| `e LIKE ''` | `e = ''` | `like_empty_pattern` |

## Architecture

### Bottom-Up Traversal

`certifiedRewrite` recursively simplifies subexpressions first, then applies top-level simplifications for `binOp`, `unaryOp`, `between`, and `inList` nodes. This ensures inner rewrites compose correctly with outer ones.

**Phase 1 exceptions**: CASE branch/else subexpressions, IN list values, function arguments, and aggregate arguments are NOT recursively rewritten. Only top-level CASE pattern matching (true/false/empty) is applied. This means the rewriter is not structurally idempotent for expressions containing these nodes — a known limitation addressed in Phase 2.

For example, `NOT(NOT(a = b)) AND FALSE`:
1. Inner: `NOT(a = b)` rewrites to `a <> b`
2. Middle: `NOT(a <> b)` rewrites to `a = b`
3. Outer: `(a = b) AND FALSE` rewrites to `FALSE`

### Proof Chaining

Each step produces a proof of equivalence. These are composed using `expr_equiv_trans` (transitivity):

```lean
| .binOp op l r =>
    let ⟨l', hl⟩ := certifiedRewrite l        -- recursively rewrite left
    let ⟨r', hr⟩ := certifiedRewrite r        -- recursively rewrite right
    let step1 := binOp_congr hl hr             -- congruence: op(l,r) ≃ op(l',r')
    let ⟨result, step2⟩ := simplifyBinOp op l' r'  -- simplify the top node
    ⟨result, expr_equiv_trans step1 step2⟩     -- chain the proofs
```

### Special NOT(BETWEEN) Handling

BETWEEN is normally expanded to `AND(GE, LE)` bottom-up. But `NOT(BETWEEN)` needs special treatment: if BETWEEN expands first, the NOT(BETWEEN) pattern is lost. The rewriter handles `NOT(BETWEEN e lo hi)` as a dedicated match arm, expanding directly to `e < lo OR e > hi` using `not_between_expansion`.

### Congruence Lemmas

The rewriter includes two congruence lemmas (`between_congr`, `inList_congr_expr`) that propagate equivalence through node types not covered by the existing `binOp_congr` and `unaryOp_congr`.

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

## Phase 1 Scope

Phase 1 includes only **unconditional** rules — simplifications that are valid regardless of the types of subexpressions. Rules requiring type preconditions (like `isBoolValued` or `isIntValued`) are planned for Phase 2.

## Testing

- **77 unit tests** (`Test/RewriterTest.lean`): structural tests for each rule, bottom-up composition, idempotency, and leaf node preservation.
- **LSpec property tests** (`LSpecTests/RewriterProperties.lean`): SlimCheck-powered tests for semantic equivalence across random expressions, idempotency, BETWEEN elimination, short-circuit properties, and more.
- **Compile-time verification**: the type signature `{ e' : Expr // e ≃ₑ e' }` means Lean's type checker verifies correctness at compile time. Tests confirm the evaluator agrees with the proofs.

## File Layout

| File | Lines | Purpose |
|------|-------|---------|
| `SqlEquiv/Rewriter.lean` | 179 | Rewriter implementation + congruence lemmas |
| `Test/RewriterTest.lean` | 293 | Unit tests (77 tests) |
| `LSpecTests/RewriterProperties.lean` | ~170 | LSpec property tests |
