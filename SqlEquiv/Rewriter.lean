/-
  Certified Expression Rewriter

  Each simplification step is justified by an existing proven theorem —
  producing both the simplified expression AND a proof of equivalence,
  with zero new axioms or sorry.

  Phase 1: Unconditional rules only (no isBoolValued/isIntValued preconditions).
-/
import SqlEquiv.Equiv

namespace SqlEquiv

-- ============================================================================
-- Congruence Lemmas
-- ============================================================================

/-- BETWEEN congruence: if subexpressions are equivalent, BETWEEN is equivalent -/
theorem between_congr {e1 e2 lo1 lo2 hi1 hi2 : Expr}
    (he : e1 ≃ₑ e2) (hlo : lo1 ≃ₑ lo2) (hhi : hi1 ≃ₑ hi2) :
    Expr.between e1 lo1 hi1 ≃ₑ Expr.between e2 lo2 hi2 := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_between, evalExprWithDb_between]
  dsimp only []
  have he' := he row; simp only [evalExpr] at he'
  have hlo' := hlo row; simp only [evalExpr] at hlo'
  have hhi' := hhi row; simp only [evalExpr] at hhi'
  rw [he', hlo', hhi']

/-- IN list congruence for the expression argument -/
theorem inList_congr_expr {e1 e2 : Expr} (neg : Bool) (vals : List Expr)
    (h : e1 ≃ₑ e2) :
    Expr.inList e1 neg vals ≃ₑ Expr.inList e2 neg vals := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_inList, evalExprWithDb_inList]
  dsimp only []
  have h' := h row; simp only [evalExpr] at h'
  rw [h']

-- ============================================================================
-- Helper Theorems
-- ============================================================================

/-- NOT(EXISTS true sel) ≃ₑ EXISTS false sel (flip negation flag) -/
private theorem not_exists_true_flip (sel : SelectStmt) :
    Expr.unaryOp .not (Expr.«exists» true sel) ≃ₑ Expr.«exists» false sel := by
  intro row
  simp only [evalExpr, evalExprWithDb_unaryOp, evalExprWithDb_exists, evalUnaryOp]
  cases evalSelectWithContext (fun _ => []) row sel with
  | nil => rfl
  | cons _ _ => rfl

-- ============================================================================
-- Simplification Helpers
-- ============================================================================

/-- Simplify a binary operation node (already rewritten children) -/
def simplifyBinOp (op : BinOp) (l r : Expr) :
    { e' : Expr // Expr.binOp op l r ≃ₑ e' } :=
  match op, l, r with
  -- AND short-circuits
  | .and, l, .lit (.bool false) => ⟨.lit (.bool false), and_false l⟩
  | .and, .lit (.bool false), r => ⟨.lit (.bool false), false_and r⟩
  -- OR short-circuits
  | .or, l, .lit (.bool true) => ⟨.lit (.bool true), or_true l⟩
  | .or, .lit (.bool true), r => ⟨.lit (.bool true), true_or r⟩
  -- LIKE empty pattern
  | .like, l, .lit (.string "") => ⟨.binOp .eq l (.lit (.string "")), like_empty_pattern l⟩
  -- Default: no simplification
  | op, l, r => ⟨.binOp op l r, expr_equiv_refl _⟩

/-- Simplify a unary operation node (already rewritten child) -/
def simplifyUnaryOp (op : UnaryOp) (e : Expr) :
    { e' : Expr // Expr.unaryOp op e ≃ₑ e' } :=
  match op, e with
  -- NOT(BETWEEN e lo hi) → e < lo OR e > hi
  | .not, .between e' lo hi =>
    ⟨.binOp .or (.binOp .lt e' lo) (.binOp .gt e' hi),
     not_between_expansion e' lo hi⟩
  -- NOT(comparison) → flipped comparison
  | .not, .binOp .eq a b => ⟨.binOp .ne a b, not_eq_is_ne a b⟩
  | .not, .binOp .ne a b => ⟨.binOp .eq a b, not_ne_is_eq a b⟩
  | .not, .binOp .lt a b => ⟨.binOp .ge a b, not_lt_is_ge a b⟩
  | .not, .binOp .le a b => ⟨.binOp .gt a b, not_le_is_gt a b⟩
  | .not, .binOp .gt a b => ⟨.binOp .le a b, not_gt_is_le a b⟩
  | .not, .binOp .ge a b => ⟨.binOp .lt a b, not_ge_is_lt a b⟩
  -- NOT(EXISTS neg sel) → EXISTS (!neg) sel
  | .not, .«exists» false sel =>
    ⟨.«exists» true sel, expr_equiv_symm (not_not_exists sel)⟩
  | .not, .«exists» true sel =>
    ⟨.«exists» false sel, not_exists_true_flip sel⟩
  -- Default: no simplification
  | op, e => ⟨.unaryOp op e, expr_equiv_refl _⟩

/-- Simplify an IN list node (already rewritten expression) -/
def simplifyInList (e : Expr) (neg : Bool) (vals : List Expr) :
    { e' : Expr // Expr.inList e neg vals ≃ₑ e' } :=
  match neg, vals with
  | false, [] => ⟨.lit (.bool false), in_empty_false e⟩
  | true, [] => ⟨.lit (.bool true), not_in_empty_true e⟩
  | false, [a] => ⟨.binOp .eq e a, in_singleton e a⟩
  | true, [a] => ⟨.binOp .ne e a, not_in_singleton e a⟩
  | neg, vals => ⟨.inList e neg vals, expr_equiv_refl _⟩

/-- Simplify a CASE expression (top-level patterns only, no recursion into branches) -/
def simplifyCaseExpr (branches : List (Expr × Expr)) (else_ : Option Expr) :
    { e' : Expr // Expr.«case» branches else_ ≃ₑ e' } :=
  match branches, else_ with
  | [], some y => ⟨y, case_empty_else y⟩
  | [], none => ⟨.lit (.null none), case_empty_no_else⟩
  | [(.lit (.bool true), x)], some y => ⟨x, case_when_true x y⟩
  | [(.lit (.bool false), x)], some y => ⟨y, case_when_false x y⟩
  | [(.lit (.bool false), x)], none => ⟨.lit (.null none), case_when_false_no_else x⟩
  | branches, else_ => ⟨.«case» branches else_, expr_equiv_refl _⟩

/-- Simplify a BETWEEN node — always expands to AND(GE, LE) -/
def simplifyBetween (e lo hi : Expr) :
    { e' : Expr // Expr.between e lo hi ≃ₑ e' } :=
  ⟨.binOp .and (.binOp .ge e lo) (.binOp .le e hi),
   between_expansion e lo hi⟩

-- ============================================================================
-- Main Recursive Function
-- ============================================================================

/-- Certified expression rewriter: simplifies bottom-up, returning both
    the result and a proof of equivalence. Zero axioms, zero sorry. -/
def certifiedRewrite : (e : Expr) → { e' : Expr // e ≃ₑ e' }
  | .lit v => ⟨.lit v, expr_equiv_refl _⟩
  | .col c => ⟨.col c, expr_equiv_refl _⟩
  | .countStar => ⟨.countStar, expr_equiv_refl _⟩
  | .agg f arg d => ⟨.agg f arg d, expr_equiv_refl _⟩
  | .windowFn f arg spec => ⟨.windowFn f arg spec, expr_equiv_refl _⟩
  | .«exists» neg sel => ⟨.«exists» neg sel, expr_equiv_refl _⟩
  | .subquery sel => ⟨.subquery sel, expr_equiv_refl _⟩
  | .inSubquery e neg sel => ⟨.inSubquery e neg sel, expr_equiv_refl _⟩
  | .func name args => ⟨.func name args, expr_equiv_refl _⟩
  | .binOp op l r =>
    let ⟨l', hl⟩ := certifiedRewrite l
    let ⟨r', hr⟩ := certifiedRewrite r
    let step1 := binOp_congr hl hr
    let ⟨result, step2⟩ := simplifyBinOp op l' r'
    ⟨result, expr_equiv_trans step1 step2⟩
  | .unaryOp .not (.between e lo hi) =>
    -- Special case: expand NOT(BETWEEN) before recursing, since bottom-up
    -- would expand BETWEEN first, losing the NOT(BETWEEN) pattern.
    let ⟨e', he⟩ := certifiedRewrite e
    let ⟨lo', hlo⟩ := certifiedRewrite lo
    let ⟨hi', hhi⟩ := certifiedRewrite hi
    let step1 := not_between_expansion e lo hi
    let lCongr : Expr.binOp .lt e lo ≃ₑ Expr.binOp .lt e' lo' := binOp_congr he hlo
    let rCongr : Expr.binOp .gt e hi ≃ₑ Expr.binOp .gt e' hi' := binOp_congr he hhi
    let step2 : Expr.binOp .or _ _ ≃ₑ _ := binOp_congr lCongr rCongr
    ⟨.binOp .or (.binOp .lt e' lo') (.binOp .gt e' hi'),
     expr_equiv_trans step1 step2⟩
  | .unaryOp op e =>
    let ⟨e', he⟩ := certifiedRewrite e
    let step1 := unaryOp_congr he
    let ⟨result, step2⟩ := simplifyUnaryOp op e'
    ⟨result, expr_equiv_trans step1 step2⟩
  | .between e lo hi =>
    let ⟨e', he⟩ := certifiedRewrite e
    let ⟨lo', hlo⟩ := certifiedRewrite lo
    let ⟨hi', hhi⟩ := certifiedRewrite hi
    let step1 := between_congr he hlo hhi
    let ⟨result, step2⟩ := simplifyBetween e' lo' hi'
    ⟨result, expr_equiv_trans step1 step2⟩
  | .inList e neg vals =>
    let ⟨e', he⟩ := certifiedRewrite e
    let step1 := inList_congr_expr neg vals he
    let ⟨result, step2⟩ := simplifyInList e' neg vals
    ⟨result, expr_equiv_trans step1 step2⟩
  | .«case» branches else_ =>
    let ⟨result, step⟩ := simplifyCaseExpr branches else_
    ⟨result, step⟩

end SqlEquiv
