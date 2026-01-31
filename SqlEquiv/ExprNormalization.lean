/-
  ExprNormalization - Canonical expression normalization for optimization

  This module provides comprehensive expression normalization that produces
  canonical forms for better pattern matching during optimization.

  Key features:
  - Weight-based ordering: literals < columns < complex expressions
  - Flattens AND/OR chains and sorts conjuncts/disjuncts
  - Normalizes commutative operators (AND, OR, ADD, MUL, EQ)
  - Idempotent: normalize (normalize e) = normalize e

  Depends on PR 0 utilities: flattenAnd, flattenOr, unflattenAnd, unflattenOr, exprStructuralCmp

  See docs/OPTIMIZER_REDESIGN_PLAN.md for full specification.
-/

import SqlEquiv.OptimizerUtils
import SqlEquiv.Semantics

namespace SqlEquiv

-- ============================================================================
-- Weight-Based Expression Ordering
-- ============================================================================

/-- Weight-based ordering: literals < columns < simple ops < functions < aggregates < complex.
    Used as primary sort key for canonical ordering. -/
def exprWeight : Expr → Nat
  | .lit _ => 0
  | .col _ => 1
  | .binOp _ _ _ => 2
  | .unaryOp _ _ => 2
  | .func _ _ => 3
  | .agg _ _ _ => 4
  | .countStar => 4
  | .«case» _ _ => 5
  | .inList _ _ _ => 5
  | .between _ _ _ => 5
  | .windowFn _ _ _ => 6
  | .inSubquery _ _ _ => 7
  | .exists _ _ => 7
  | .subquery _ => 7

/-- Total ordering on expressions for canonical form.
    Primary: compare by weight (simpler expressions first)
    Secondary: use exprStructuralCmp for deterministic ordering within same weight -/
def exprCompare (e1 e2 : Expr) : Ordering :=
  match compare (exprWeight e1) (exprWeight e2) with
  | .eq => exprStructuralCmp e1 e2
  | ord => ord

/-- Comparison function suitable for Array.qsort (returns true if e1 < e2) -/
def exprLt (e1 e2 : Expr) : Bool :=
  exprCompare e1 e2 == .lt

-- ============================================================================
-- Canonical Expression Normalization
-- ============================================================================

/-- Normalize an expression to canonical form.
    - Flattens AND/OR chains and sorts conjuncts/disjuncts
    - Reorders commutative binary operators (AND, OR, ADD, MUL, EQ)
    - Recursively normalizes subexpressions
    - Idempotent: normalizeExprCanonical (normalizeExprCanonical e) = normalizeExprCanonical e -/
partial def normalizeExprCanonical : Expr → Expr
  -- AND: flatten, normalize each conjunct, sort, rebuild
  | .binOp .and l r =>
    let conjuncts := (flattenAnd l ++ flattenAnd r).map normalizeExprCanonical
    let sorted := conjuncts.toArray.qsort exprLt |>.toList
    unflattenAnd sorted |>.getD (.lit (.bool true))

  -- OR: flatten, normalize each disjunct, sort, rebuild
  | .binOp .or l r =>
    let disjuncts := (flattenOr l ++ flattenOr r).map normalizeExprCanonical
    let sorted := disjuncts.toArray.qsort exprLt |>.toList
    unflattenOr sorted |>.getD (.lit (.bool false))

  -- Commutative binary ops: normalize children, then order them
  | .binOp .add l r =>
    let nl := normalizeExprCanonical l
    let nr := normalizeExprCanonical r
    if exprCompare nl nr == .gt then .binOp .add nr nl else .binOp .add nl nr

  | .binOp .mul l r =>
    let nl := normalizeExprCanonical l
    let nr := normalizeExprCanonical r
    if exprCompare nl nr == .gt then .binOp .mul nr nl else .binOp .mul nl nr

  | .binOp .eq l r =>
    let nl := normalizeExprCanonical l
    let nr := normalizeExprCanonical r
    if exprCompare nl nr == .gt then .binOp .eq nr nl else .binOp .eq nl nr

  -- Non-commutative binary ops: just recurse into children
  | .binOp op l r => .binOp op (normalizeExprCanonical l) (normalizeExprCanonical r)

  -- Unary ops: recurse
  | .unaryOp op e => .unaryOp op (normalizeExprCanonical e)

  -- Functions: recurse into args
  | .func name args => .func name (args.map normalizeExprCanonical)

  -- Aggregates: recurse into arg if present
  | .agg fn arg distinct => .agg fn (arg.map normalizeExprCanonical) distinct

  -- Case expressions: recurse into branches and else
  | .«case» branches else_ =>
    .«case» (branches.map fun (c, r) => (normalizeExprCanonical c, normalizeExprCanonical r))
            (else_.map normalizeExprCanonical)

  -- IN list: recurse into expression and values
  | .inList e neg vals =>
    .inList (normalizeExprCanonical e) neg (vals.map normalizeExprCanonical)

  -- BETWEEN: recurse into all three expressions
  | .between e lo hi =>
    .between (normalizeExprCanonical e) (normalizeExprCanonical lo) (normalizeExprCanonical hi)

  -- Window functions: recurse into arg and spec expressions
  | .windowFn fn arg (.mk partBy orderBy) =>
    let normArg := arg.map normalizeExprCanonical
    let normPartBy := partBy.map normalizeExprCanonical
    let normOrderBy := orderBy.map fun item => OrderByItem.mk (normalizeExprCanonical item.expr) item.dir
    .windowFn fn normArg (.mk normPartBy normOrderBy)

  -- Leaves (lit, col, countStar) and subqueries (own scope): unchanged
  | e => e

-- ============================================================================
-- Semantic Equivalence Axiom
-- ============================================================================

/-- Normalization preserves semantic equivalence.
    The normalized expression evaluates to the same result as the original. -/
axiom normalizeExprCanonical_equiv (e : Expr) :
  ∀ db row, evalExprWithDb db row (normalizeExprCanonical e) = evalExprWithDb db row e

-- ============================================================================
-- Idempotency Theorem
-- ============================================================================

/-- Normalization is idempotent: applying it twice gives the same result as once.
    Axiom for now; can be proven by showing normalized form is already canonical. -/
axiom normalizeExprCanonical_idempotent (e : Expr) :
  normalizeExprCanonical (normalizeExprCanonical e) = normalizeExprCanonical e

end SqlEquiv
