/-
  Certified Expression Rewriter

  Each simplification step is justified by an existing proven theorem —
  producing both the simplified expression AND a proof of equivalence,
  with zero new axioms or sorry.

  Phase 1: Unconditional rules (no type preconditions).
  Phase 2a: Conditional rules guarded by static type checks.
-/
import SqlEquiv.Equiv

namespace SqlEquiv

-- ============================================================================
-- Static Type Guards
-- ============================================================================

/-- Conservative static check: returns true only for expressions that are
    guaranteed to evaluate to `some (.bool _)` regardless of row/db context.
    Excludes comparisons (can return none on type mismatch), BETWEEN, IN list. -/
def Expr.isDefinitelyBool : Expr → Bool
  | .lit (.bool _) => true
  | .unaryOp .isNull _ => true
  | .unaryOp .isNotNull _ => true
  | .unaryOp .not e => e.isDefinitelyBool
  | .binOp .and l r => l.isDefinitelyBool && r.isDefinitelyBool
  | .binOp .or l r => l.isDefinitelyBool && r.isDefinitelyBool
  | .«exists» _ _ => true
  | _ => false

/-- Conservative static check: returns true only for expressions that are
    guaranteed to evaluate to `some (.int _)` regardless of row/db context.
    Excludes div/mod (division by zero returns none). -/
def Expr.isDefinitelyInt : Expr → Bool
  | .lit (.int _) => true
  | .binOp .add l r => l.isDefinitelyInt && r.isDefinitelyInt
  | .binOp .sub l r => l.isDefinitelyInt && r.isDefinitelyInt
  | .binOp .mul l r => l.isDefinitelyInt && r.isDefinitelyInt
  | .unaryOp .neg e => e.isDefinitelyInt
  | _ => false

-- ============================================================================
-- Bridge Lemmas: static guards → semantic predicates
-- ============================================================================

/-- If `isDefinitelyBool` returns true, then `e` is semantically bool-valued:
    for every row, `evalExpr row e = some (.bool b)` for some `b`. -/
theorem isDefinitelyBool_implies_isBoolValued (e : Expr) (h : e.isDefinitelyBool = true) :
    e.isBoolValued := by
  intro row
  simp only [evalExpr]
  cases e with
  | lit v =>
    cases v with
    | bool b => exact ⟨b, evalExprWithDb_lit ..⟩
    | _ => simp [Expr.isDefinitelyBool] at h
  | unaryOp op inner =>
    cases op with
    | isNull =>
      rw [evalExprWithDb_unaryOp]
      cases evalExprWithDb _ row inner with
      | none => exact ⟨true, rfl⟩
      | some v => cases v <;> exact ⟨_, rfl⟩
    | isNotNull =>
      rw [evalExprWithDb_unaryOp]
      cases evalExprWithDb _ row inner with
      | none => exact ⟨false, rfl⟩
      | some v => cases v <;> exact ⟨_, rfl⟩
    | not =>
      simp [Expr.isDefinitelyBool] at h
      have ⟨b, hb⟩ := isDefinitelyBool_implies_isBoolValued inner h row
      simp only [evalExpr] at hb
      rw [evalExprWithDb_unaryOp, hb]
      exact ⟨!b, rfl⟩
    | neg => simp [Expr.isDefinitelyBool] at h
  | binOp op l r =>
    cases op with
    | «and» =>
      simp [Expr.isDefinitelyBool] at h
      have ⟨bl, hbl⟩ := isDefinitelyBool_implies_isBoolValued l h.1 row
      have ⟨br, hbr⟩ := isDefinitelyBool_implies_isBoolValued r h.2 row
      simp only [evalExpr] at hbl hbr
      rw [evalExprWithDb_binOp, hbl, hbr]
      exact ⟨bl && br, rfl⟩
    | «or» =>
      simp [Expr.isDefinitelyBool] at h
      have ⟨bl, hbl⟩ := isDefinitelyBool_implies_isBoolValued l h.1 row
      have ⟨br, hbr⟩ := isDefinitelyBool_implies_isBoolValued r h.2 row
      simp only [evalExpr] at hbl hbr
      rw [evalExprWithDb_binOp, hbl, hbr]
      exact ⟨bl || br, rfl⟩
    | _ => simp [Expr.isDefinitelyBool] at h
  | «exists» neg sel =>
    rw [evalExprWithDb_exists]
    simp only
    cases neg with
    | false =>
      exact ⟨!(evalSubQueryWithContext _ row sel).isEmpty, rfl⟩
    | true =>
      exact ⟨!!(evalSubQueryWithContext _ row sel).isEmpty, rfl⟩
  | _ => simp [Expr.isDefinitelyBool] at h

/-- If `isDefinitelyInt` returns true, then `e` is semantically int-valued:
    for every row, `evalExpr row e = some (.int n)` for some `n`. -/
theorem isDefinitelyInt_implies_isIntValued (e : Expr) (h : e.isDefinitelyInt = true) :
    e.isIntValued := by
  intro row
  simp only [evalExpr]
  cases e with
  | lit v =>
    cases v with
    | int n => exact ⟨n, evalExprWithDb_lit ..⟩
    | _ => simp [Expr.isDefinitelyInt] at h
  | binOp op l r =>
    cases op with
    | add =>
      simp [Expr.isDefinitelyInt] at h
      have ⟨nl, hnl⟩ := isDefinitelyInt_implies_isIntValued l h.1 row
      have ⟨nr, hnr⟩ := isDefinitelyInt_implies_isIntValued r h.2 row
      simp only [evalExpr] at hnl hnr
      rw [evalExprWithDb_binOp, hnl, hnr]
      exact ⟨nl + nr, rfl⟩
    | sub =>
      simp [Expr.isDefinitelyInt] at h
      have ⟨nl, hnl⟩ := isDefinitelyInt_implies_isIntValued l h.1 row
      have ⟨nr, hnr⟩ := isDefinitelyInt_implies_isIntValued r h.2 row
      simp only [evalExpr] at hnl hnr
      rw [evalExprWithDb_binOp, hnl, hnr]
      exact ⟨nl - nr, rfl⟩
    | mul =>
      simp [Expr.isDefinitelyInt] at h
      have ⟨nl, hnl⟩ := isDefinitelyInt_implies_isIntValued l h.1 row
      have ⟨nr, hnr⟩ := isDefinitelyInt_implies_isIntValued r h.2 row
      simp only [evalExpr] at hnl hnr
      rw [evalExprWithDb_binOp, hnl, hnr]
      exact ⟨nl * nr, rfl⟩
    | _ => simp [Expr.isDefinitelyInt] at h
  | unaryOp op inner =>
    cases op with
    | neg =>
      simp [Expr.isDefinitelyInt] at h
      have ⟨n, hn⟩ := isDefinitelyInt_implies_isIntValued inner h row
      simp only [evalExpr] at hn
      rw [evalExprWithDb_unaryOp, hn]
      exact ⟨-n, rfl⟩
    | _ => simp [Expr.isDefinitelyInt] at h
  | _ => simp [Expr.isDefinitelyInt] at h

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

/-- CASE congruence: if branch conditions, results, and else are pairwise equivalent, CASE is equivalent -/
private theorem case_congr (branches : List (Expr × Expr)) (else_ : Option Expr)
    (f : Expr → Expr)
    (hc : ∀ p ∈ branches, p.1 ≃ₑ f p.1)
    (hr : ∀ p ∈ branches, p.2 ≃ₑ f p.2)
    (helse : ∀ e, else_ = some e → e ≃ₑ f e) :
    Expr.case branches else_ ≃ₑ
    Expr.case (branches.map fun p => (f p.1, f p.2)) (else_.map f) := by
  cases else_ with
  | none =>
    intro row; simp only [evalExpr]
    rw [evalExprWithDb_case, evalExprWithDb_case]
    simp only [evalCase, Option.map]
    exact (evalCaseHelper_map_congr (evalExprWithDb (fun _ => []) row)
      f f branches _
      (fun p hp => by have := hc p hp row; simp only [evalExpr] at this; exact this.symm)
      (fun p hp => by have := hr p hp row; simp only [evalExpr] at this; exact this.symm)).symm
  | some elseExpr =>
    intro row; simp only [evalExpr]
    rw [evalExprWithDb_case, evalExprWithDb_case]
    simp only [evalCase, Option.map]
    have helse_eq : evalExprWithDb (fun _ => []) row (f elseExpr) =
        evalExprWithDb (fun _ => []) row elseExpr := by
      have := helse elseExpr rfl row; simp only [evalExpr] at this; exact this.symm
    rw [helse_eq]
    exact (evalCaseHelper_map_congr (evalExprWithDb (fun _ => []) row)
      f f branches _
      (fun p hp => by have := hc p hp row; simp only [evalExpr] at this; exact this.symm)
      (fun p hp => by have := hr p hp row; simp only [evalExpr] at this; exact this.symm)).symm

/-- IN list congruence for the value list -/
private theorem inList_congr_vals (e : Expr) (neg : Bool) (vals : List Expr) (f : Expr → Expr)
    (h : ∀ v ∈ vals, v ≃ₑ f v) :
    Expr.inList e neg vals ≃ₑ Expr.inList e neg (vals.map f) := by
  intro row; simp only [evalExpr]
  rw [evalExprWithDb_inList, evalExprWithDb_inList]
  dsimp only []
  suffices hfoldl : ∀ init,
      vals.foldl (fun acc vi =>
        evalBinOp .or acc (evalBinOp .eq (evalExprWithDb (fun _ => []) row e)
          (evalExprWithDb (fun _ => []) row vi))) init =
      (vals.map f).foldl (fun acc vi =>
        evalBinOp .or acc (evalBinOp .eq (evalExprWithDb (fun _ => []) row e)
          (evalExprWithDb (fun _ => []) row vi))) init by
    rw [hfoldl]
  intro init
  induction vals generalizing init with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.foldl, List.map]
    have hv := h v List.mem_cons_self
    have hv' := hv row; simp only [evalExpr] at hv'
    rw [hv']
    exact ih (fun vi hvi => h vi (List.mem_cons_of_mem v hvi)) _

/-- Function congruence: if args evaluate the same, func is equivalent -/
private theorem func_congr (name : String) (args1 args2 : List Expr)
    (h : ∀ row, args1.map (evalExprWithDb (fun _ => []) row) =
                args2.map (evalExprWithDb (fun _ => []) row)) :
    Expr.func name args1 ≃ₑ Expr.func name args2 := by
  intro row; simp only [evalExpr]
  rw [evalExprWithDb_func, evalExprWithDb_func]
  exact congrArg (evalFunc name) (h row)

/-- Aggregate congruence: trivially true since evalExprCore returns none for .agg -/
private theorem agg_congr (fn : AggFunc) (arg1 arg2 : Option Expr) (d : Bool) :
    Expr.agg fn arg1 d ≃ₑ Expr.agg fn arg2 d := by
  intro row; simp only [evalExpr]
  rw [evalExprWithDb_eq_evalExprCore, evalExprWithDb_eq_evalExprCore]
  simp [evalExprCore]

/-- Window function congruence: trivially true since evalExprCore returns none for .windowFn -/
private theorem windowFn_congr (fn : WindowFunc) (arg1 arg2 : Option Expr) (spec : WindowSpec) :
    Expr.windowFn fn arg1 spec ≃ₑ Expr.windowFn fn arg2 spec := by
  intro row; simp only [evalExpr]
  rw [evalExprWithDb_eq_evalExprCore, evalExprWithDb_eq_evalExprCore]
  simp [evalExprCore]

/-- IN subquery congruence for the expression argument -/
private theorem inSubquery_congr_expr {e1 e2 : Expr} (neg : Bool) (sel : SubQuery)
    (h : e1 ≃ₑ e2) :
    Expr.inSubquery e1 neg sel ≃ₑ Expr.inSubquery e2 neg sel := by
  intro row; simp only [evalExpr]
  rw [evalExprWithDb_inSubquery, evalExprWithDb_inSubquery]
  have h' := h row; simp only [evalExpr] at h'
  rw [h']

-- ============================================================================
-- Helper Theorems
-- ============================================================================

/-- NOT(EXISTS true sel) ≃ₑ EXISTS false sel (flip negation flag) -/
private theorem not_exists_true_flip (sel : SubQuery) :
    Expr.unaryOp .not (Expr.«exists» true sel) ≃ₑ Expr.«exists» false sel := by
  intro row
  simp only [evalExpr, evalExprWithDb_unaryOp, evalExprWithDb_exists, evalUnaryOp]
  cases evalSubQueryWithContext (fun _ => []) row sel with
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
  -- Boolean identity (conditional on type guard)
  | .and, l, .lit (.bool true) =>
    if h : l.isDefinitelyBool = true
    then ⟨l, and_true l (isDefinitelyBool_implies_isBoolValued l h)⟩
    else ⟨.binOp .and l (.lit (.bool true)), expr_equiv_refl _⟩
  | .and, .lit (.bool true), r =>
    if h : r.isDefinitelyBool = true
    then ⟨r, true_and r (isDefinitelyBool_implies_isBoolValued r h)⟩
    else ⟨.binOp .and (.lit (.bool true)) r, expr_equiv_refl _⟩
  | .or, l, .lit (.bool false) =>
    if h : l.isDefinitelyBool = true
    then ⟨l, or_false l (isDefinitelyBool_implies_isBoolValued l h)⟩
    else ⟨.binOp .or l (.lit (.bool false)), expr_equiv_refl _⟩
  | .or, .lit (.bool false), r =>
    if h : r.isDefinitelyBool = true
    then ⟨r, false_or r (isDefinitelyBool_implies_isBoolValued r h)⟩
    else ⟨.binOp .or (.lit (.bool false)) r, expr_equiv_refl _⟩
  -- Arithmetic identity (conditional on type guard)
  | .add, l, .lit (.int 0) =>
    if h : l.isDefinitelyInt = true
    then ⟨l, expr_add_zero l (isDefinitelyInt_implies_isIntValued l h)⟩
    else ⟨.binOp .add l (.lit (.int 0)), expr_equiv_refl _⟩
  | .add, .lit (.int 0), r =>
    if h : r.isDefinitelyInt = true
    then ⟨r, expr_zero_add r (isDefinitelyInt_implies_isIntValued r h)⟩
    else ⟨.binOp .add (.lit (.int 0)) r, expr_equiv_refl _⟩
  | .mul, l, .lit (.int 1) =>
    if h : l.isDefinitelyInt = true
    then ⟨l, expr_mul_one l (isDefinitelyInt_implies_isIntValued l h)⟩
    else ⟨.binOp .mul l (.lit (.int 1)), expr_equiv_refl _⟩
  | .mul, .lit (.int 1), r =>
    if h : r.isDefinitelyInt = true
    then ⟨r, expr_one_mul r (isDefinitelyInt_implies_isIntValued r h)⟩
    else ⟨.binOp .mul (.lit (.int 1)) r, expr_equiv_refl _⟩
  | .sub, l, .lit (.int 0) =>
    if h : l.isDefinitelyInt = true
    then ⟨l, expr_sub_zero l (isDefinitelyInt_implies_isIntValued l h)⟩
    else ⟨.binOp .sub l (.lit (.int 0)), expr_equiv_refl _⟩
  -- Default: no simplification
  | op, l, r => ⟨.binOp op l r, expr_equiv_refl _⟩

/-- Simplify a unary operation node (already rewritten child) -/
def simplifyUnaryOp (op : UnaryOp) (e : Expr) :
    { e' : Expr // Expr.unaryOp op e ≃ₑ e' } :=
  match op, e with
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
  -- NOT(NOT(e)) → e (conditional on type guard)
  | .not, .unaryOp .not e =>
    if h : e.isDefinitelyBool = true
    then ⟨e, not_not e (isDefinitelyBool_implies_isBoolValued e h)⟩
    else ⟨.unaryOp .not (.unaryOp .not e), expr_equiv_refl _⟩
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
-- Opaque Wrappers (prevent inlining into certifiedRewriteAux compiled body)
-- ============================================================================

/-- Extract simplified expression from simplifyBinOp -/
@[noinline] private def simplifyBinOpVal (op : BinOp) (l r : Expr) : Expr :=
  (simplifyBinOp op l r).val

/-- Extract simplified expression from simplifyUnaryOp -/
@[noinline] private def simplifyUnaryOpVal (op : UnaryOp) (e : Expr) : Expr :=
  (simplifyUnaryOp op e).val

/-- Extract simplified expression from simplifyInList -/
@[noinline] private def simplifyInListVal (e : Expr) (neg : Bool) (vals : List Expr) : Expr :=
  (simplifyInList e neg vals).val

/-- Extract simplified expression from simplifyCaseExpr -/
@[noinline] private def simplifyCaseExprVal
    (branches : List (Expr × Expr)) (else_ : Option Expr) : Expr :=
  (simplifyCaseExpr branches else_).val

/-- Extract simplified expression from simplifyBetween -/
@[noinline] private def simplifyBetweenVal (e lo hi : Expr) : Expr :=
  (simplifyBetween e lo hi).val

-- Bridge lemmas for the wrappers
private theorem simplifyBinOpVal_spec (op : BinOp) (l r : Expr) :
    Expr.binOp op l r ≃ₑ simplifyBinOpVal op l r :=
  (simplifyBinOp op l r).property

private theorem simplifyUnaryOpVal_spec (op : UnaryOp) (e : Expr) :
    Expr.unaryOp op e ≃ₑ simplifyUnaryOpVal op e :=
  (simplifyUnaryOp op e).property

private theorem simplifyInListVal_spec (e : Expr) (neg : Bool) (vals : List Expr) :
    Expr.inList e neg vals ≃ₑ simplifyInListVal e neg vals :=
  (simplifyInList e neg vals).property

private theorem simplifyCaseExprVal_spec (branches : List (Expr × Expr)) (else_ : Option Expr) :
    Expr.«case» branches else_ ≃ₑ simplifyCaseExprVal branches else_ :=
  (simplifyCaseExpr branches else_).property

private theorem simplifyBetweenVal_spec (e lo hi : Expr) :
    Expr.between e lo hi ≃ₑ simplifyBetweenVal e lo hi :=
  (simplifyBetween e lo hi).property

-- ============================================================================
-- Main Recursive Function
-- ============================================================================

/-- Computation part of the certified rewriter: bottom-up simplification.
    Returns just the simplified expression. The proof is in `certifiedRewriteAux_equiv`. -/
def certifiedRewriteAux : Expr → Expr
  | .lit v => .lit v
  | .col c => .col c
  | .countStar => .countStar
  | .«exists» neg sel => .«exists» neg sel
  | .subquery sel => .subquery sel
  | .agg fn arg d =>
    .agg fn (match arg with | none => none | some e => some (certifiedRewriteAux e)) d
  | .windowFn fn arg spec =>
    .windowFn fn (match arg with | none => none | some e => some (certifiedRewriteAux e)) spec
  | .inSubquery e neg sel => .inSubquery (certifiedRewriteAux e) neg sel
  | .func name args =>
    .func name (args.map certifiedRewriteAux)
  | .binOp op l r =>
    simplifyBinOpVal op (certifiedRewriteAux l) (certifiedRewriteAux r)
  | .unaryOp .not (.between e lo hi) =>
    .binOp .or (.binOp .lt (certifiedRewriteAux e) (certifiedRewriteAux lo))
      (.binOp .gt (certifiedRewriteAux e) (certifiedRewriteAux hi))
  | .unaryOp op e =>
    simplifyUnaryOpVal op (certifiedRewriteAux e)
  | .between e lo hi =>
    simplifyBetweenVal (certifiedRewriteAux e) (certifiedRewriteAux lo)
      (certifiedRewriteAux hi)
  | .inList e neg vals =>
    simplifyInListVal (certifiedRewriteAux e) neg
      (vals.map certifiedRewriteAux)
  | .«case» branches else_ =>
    simplifyCaseExprVal
      (branches.map (fun pair =>
          (certifiedRewriteAux pair.1, certifiedRewriteAux pair.2)))
      (match else_ with | none => none | some e => some (certifiedRewriteAux e))
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_›; omega)
    | (have h := List.sizeOf_lt_of_mem ‹_›
       have : sizeOf pair = 1 + sizeOf pair.fst + sizeOf pair.snd := by
         obtain ⟨a, b⟩ := pair; simp [Prod.mk.sizeOf_spec]
       omega)

/-- The certified rewriter preserves equivalence: for all expressions,
    the rewritten form is semantically equivalent to the original. -/
theorem certifiedRewriteAux_equiv (e : Expr) : e ≃ₑ certifiedRewriteAux e := by
  suffices key : ∀ (n : Nat) (e : Expr), sizeOf e < n → e ≃ₑ certifiedRewriteAux e by
    exact key (sizeOf e + 1) e (by omega)
  intro n; induction n with
  | zero => intro _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro e hlt
    -- Helper: transport an equivalence proof across certifiedRewriteAux unfolding
    -- Given step : e ≃ₑ expanded and h_unfold : certifiedRewriteAux e = expanded,
    -- produces e ≃ₑ certifiedRewriteAux e
    have transport {e expanded : Expr}
        (step : e ≃ₑ expanded) (h_unfold : certifiedRewriteAux e = expanded) :
        e ≃ₑ certifiedRewriteAux e :=
      fun row => (step row).trans (congrArg (evalExpr row) h_unfold).symm
    cases e with
    | lit v =>
      exact transport (expr_equiv_refl _) (by simp [certifiedRewriteAux])
    | col c =>
      exact transport (expr_equiv_refl _) (by simp [certifiedRewriteAux])
    | countStar =>
      exact transport (expr_equiv_refl _) (by simp [certifiedRewriteAux])
    | «exists» neg sel =>
      exact transport (expr_equiv_refl _) (by simp [certifiedRewriteAux])
    | subquery sel =>
      exact transport (expr_equiv_refl _) (by simp [certifiedRewriteAux])
    | agg fn arg d =>
      have h_unfold : certifiedRewriteAux (.agg fn arg d) =
          .agg fn (match arg with | none => none | some e => some (certifiedRewriteAux e)) d := by
        cases arg <;> simp [certifiedRewriteAux]
      exact transport (agg_congr fn arg _ d) h_unfold
    | windowFn fn arg spec =>
      have h_unfold : certifiedRewriteAux (.windowFn fn arg spec) =
          .windowFn fn (match arg with | none => none | some e => some (certifiedRewriteAux e)) spec := by
        cases arg <;> simp [certifiedRewriteAux]
      exact transport (windowFn_congr fn arg _ spec) h_unfold
    | inSubquery e neg sel =>
      have he : e ≃ₑ certifiedRewriteAux e := ih e (by
        have : sizeOf (Expr.inSubquery e neg sel) = 1 + sizeOf e + sizeOf neg + sizeOf sel := by
          simp [Expr.inSubquery.sizeOf_spec]
        omega)
      exact transport (inSubquery_congr_expr neg sel he)
        (by simp [certifiedRewriteAux])
    | func name args =>
      have hargs : ∀ a ∈ args, a ≃ₑ certifiedRewriteAux a := by
        intro a ha
        have h_mem_sz := List.sizeOf_lt_of_mem ha
        have : sizeOf (Expr.func name args) = 1 + sizeOf name + sizeOf args := by
          simp [Expr.func.sizeOf_spec]
        exact ih a (by omega)
      have h_unfold : certifiedRewriteAux (.func name args) =
          .func name (args.map certifiedRewriteAux) := by
        simp [certifiedRewriteAux]
      exact transport
        (func_congr name args (args.map certifiedRewriteAux) (by
          intro row; rw [List.map_map]
          exact List.map_congr_left fun e he => by
            have := hargs e he row; simp only [evalExpr] at this; exact this))
        h_unfold
    | binOp op l r =>
      have hl : l ≃ₑ certifiedRewriteAux l := ih l (by
        have : sizeOf (Expr.binOp op l r) = 1 + sizeOf op + sizeOf l + sizeOf r := by
          simp [Expr.binOp.sizeOf_spec]
        omega)
      have hr : r ≃ₑ certifiedRewriteAux r := ih r (by
        have : sizeOf (Expr.binOp op l r) = 1 + sizeOf op + sizeOf l + sizeOf r := by
          simp [Expr.binOp.sizeOf_spec]
        omega)
      have h_unfold : certifiedRewriteAux (.binOp op l r) =
          simplifyBinOpVal op (certifiedRewriteAux l) (certifiedRewriteAux r) := by
        simp [certifiedRewriteAux]
      exact transport
        (expr_equiv_trans (binOp_congr hl hr) (simplifyBinOpVal_spec op _ _))
        h_unfold
    | unaryOp op inner =>
      have sz_inner : sizeOf inner < n := by
        have : sizeOf (Expr.unaryOp op inner) = 1 + sizeOf op + sizeOf inner := by
          simp [Expr.unaryOp.sizeOf_spec]
        omega
      have hi : inner ≃ₑ certifiedRewriteAux inner := ih inner sz_inner
      cases op with
      | not =>
        cases inner with
        | between e lo hi_expr =>
          -- NOT(BETWEEN) special case: expands to OR(LT, GT)
          have he : e ≃ₑ certifiedRewriteAux e := ih e (by
            have : sizeOf (Expr.between e lo hi_expr) = 1 + sizeOf e + sizeOf lo + sizeOf hi_expr := by
              simp [Expr.between.sizeOf_spec]
            omega)
          have hlo : lo ≃ₑ certifiedRewriteAux lo := ih lo (by
            have : sizeOf (Expr.between e lo hi_expr) = 1 + sizeOf e + sizeOf lo + sizeOf hi_expr := by
              simp [Expr.between.sizeOf_spec]
            omega)
          have hhi : hi_expr ≃ₑ certifiedRewriteAux hi_expr := ih hi_expr (by
            have : sizeOf (Expr.between e lo hi_expr) = 1 + sizeOf e + sizeOf lo + sizeOf hi_expr := by
              simp [Expr.between.sizeOf_spec]
            omega)
          have h_unfold : certifiedRewriteAux (.unaryOp .not (.between e lo hi_expr)) =
              .binOp .or (.binOp .lt (certifiedRewriteAux e) (certifiedRewriteAux lo))
                (.binOp .gt (certifiedRewriteAux e) (certifiedRewriteAux hi_expr)) := by
            simp [certifiedRewriteAux]
          exact transport
            (expr_equiv_trans (not_between_expansion e lo hi_expr)
              (binOp_congr (binOp_congr he hlo) (binOp_congr he hhi)))
            h_unfold
        | _ =>
          -- NOT(other): use simplifyUnaryOp (inner is destructured, don't name it)
          exact transport
            (expr_equiv_trans (unaryOp_congr hi) (simplifyUnaryOpVal_spec .not _))
            (by simp [certifiedRewriteAux])
      | _ =>
        -- isNull, isNotNull, neg: use simplifyUnaryOp
        exact transport
          (expr_equiv_trans (unaryOp_congr hi) (simplifyUnaryOpVal_spec _ _))
          (by simp [certifiedRewriteAux])
    | between e lo hi =>
      have he : e ≃ₑ certifiedRewriteAux e := ih e (by
        have : sizeOf (Expr.between e lo hi) = 1 + sizeOf e + sizeOf lo + sizeOf hi := by
          simp [Expr.between.sizeOf_spec]
        omega)
      have hlo : lo ≃ₑ certifiedRewriteAux lo := ih lo (by
        have : sizeOf (Expr.between e lo hi) = 1 + sizeOf e + sizeOf lo + sizeOf hi := by
          simp [Expr.between.sizeOf_spec]
        omega)
      have hhi : hi ≃ₑ certifiedRewriteAux hi := ih hi (by
        have : sizeOf (Expr.between e lo hi) = 1 + sizeOf e + sizeOf lo + sizeOf hi := by
          simp [Expr.between.sizeOf_spec]
        omega)
      have h_unfold : certifiedRewriteAux (.between e lo hi) =
          simplifyBetweenVal (certifiedRewriteAux e) (certifiedRewriteAux lo)
            (certifiedRewriteAux hi) := by
        simp [certifiedRewriteAux]
      exact transport
        (expr_equiv_trans (between_congr he hlo hhi) (simplifyBetweenVal_spec _ _ _))
        h_unfold
    | inList e neg vals =>
      have he : e ≃ₑ certifiedRewriteAux e := ih e (by
        have : sizeOf (Expr.inList e neg vals) = 1 + sizeOf e + sizeOf neg + sizeOf vals := by
          simp [Expr.inList.sizeOf_spec]
        omega)
      have hvals : ∀ v ∈ vals, v ≃ₑ certifiedRewriteAux v := by
        intro v hv
        have h_mem_sz := List.sizeOf_lt_of_mem hv
        have : sizeOf (Expr.inList e neg vals) = 1 + sizeOf e + sizeOf neg + sizeOf vals := by
          simp [Expr.inList.sizeOf_spec]
        exact ih v (by omega)
      have h_unfold : certifiedRewriteAux (.inList e neg vals) =
          simplifyInListVal (certifiedRewriteAux e) neg
            (vals.map certifiedRewriteAux) := by
        simp [certifiedRewriteAux]
      -- Compose: inList e neg vals ≃ₑ inList e' neg vals' ≃ₑ simplified
      have step1 := inList_congr_expr neg vals he
      have step2 := inList_congr_vals (certifiedRewriteAux e) neg vals certifiedRewriteAux
        (fun v hv => hvals v hv)
      exact transport
        (expr_equiv_trans step1
          (expr_equiv_trans step2 (simplifyInListVal_spec _ neg _)))
        h_unfold
    | «case» branches else_ =>
      -- Case-split else_ first to avoid WFR compiled match contamination
      cases else_ with
      | none =>
        -- IH for branch conditions and results
        have hbr_c : ∀ p ∈ branches, p.1 ≃ₑ certifiedRewriteAux p.1 := by
          intro p hp
          have h_mem_sz := List.sizeOf_lt_of_mem hp
          have h_pair_sz : sizeOf p = 1 + sizeOf p.fst + sizeOf p.snd := by
            obtain ⟨a, b⟩ := p; simp [Prod.mk.sizeOf_spec]
          have : sizeOf (Expr.case branches none) = 1 + sizeOf branches + sizeOf (none : Option Expr) := by
            simp [Expr.case.sizeOf_spec]
          exact ih p.1 (by omega)
        have hbr_r : ∀ p ∈ branches, p.2 ≃ₑ certifiedRewriteAux p.2 := by
          intro p hp
          have h_mem_sz := List.sizeOf_lt_of_mem hp
          have h_pair_sz : sizeOf p = 1 + sizeOf p.fst + sizeOf p.snd := by
            obtain ⟨a, b⟩ := p; simp [Prod.mk.sizeOf_spec]
          have : sizeOf (Expr.case branches none) = 1 + sizeOf branches + sizeOf (none : Option Expr) := by
            simp [Expr.case.sizeOf_spec]
          exact ih p.2 (by omega)
        have step1 := case_congr branches none certifiedRewriteAux hbr_c hbr_r
          (fun _ h => by cases h)
        have h_unfold : certifiedRewriteAux (.case branches none) =
            simplifyCaseExprVal
              (branches.map (fun p => (certifiedRewriteAux p.1, certifiedRewriteAux p.2)))
              none := by
          simp [certifiedRewriteAux]
        exact transport
          (expr_equiv_trans step1 (simplifyCaseExprVal_spec _ _))
          (by simp [Option.map] at step1; exact h_unfold)
      | some elseExpr =>
        -- IH for branch conditions and results
        have hbr_c : ∀ p ∈ branches, p.1 ≃ₑ certifiedRewriteAux p.1 := by
          intro p hp
          have h_mem_sz := List.sizeOf_lt_of_mem hp
          have h_pair_sz : sizeOf p = 1 + sizeOf p.fst + sizeOf p.snd := by
            obtain ⟨a, b⟩ := p; simp [Prod.mk.sizeOf_spec]
          have : sizeOf (Expr.case branches (some elseExpr)) = 1 + sizeOf branches + sizeOf (some elseExpr) := by
            simp [Expr.case.sizeOf_spec]
          exact ih p.1 (by omega)
        have hbr_r : ∀ p ∈ branches, p.2 ≃ₑ certifiedRewriteAux p.2 := by
          intro p hp
          have h_mem_sz := List.sizeOf_lt_of_mem hp
          have h_pair_sz : sizeOf p = 1 + sizeOf p.fst + sizeOf p.snd := by
            obtain ⟨a, b⟩ := p; simp [Prod.mk.sizeOf_spec]
          have : sizeOf (Expr.case branches (some elseExpr)) = 1 + sizeOf branches + sizeOf (some elseExpr) := by
            simp [Expr.case.sizeOf_spec]
          exact ih p.2 (by omega)
        -- IH for else
        have helse : elseExpr ≃ₑ certifiedRewriteAux elseExpr := ih elseExpr (by
          have h1 : sizeOf (Expr.case branches (some elseExpr)) = 1 + sizeOf branches + sizeOf (some elseExpr) := by
            simp [Expr.case.sizeOf_spec]
          have h2 : sizeOf (some elseExpr) = 1 + sizeOf elseExpr := by simp [Option.some.sizeOf_spec]
          omega)
        have step1 := case_congr branches (some elseExpr) certifiedRewriteAux hbr_c hbr_r
          (fun e he => by cases he; exact helse)
        have h_unfold : certifiedRewriteAux (.case branches (some elseExpr)) =
            simplifyCaseExprVal
              (branches.map (fun p => (certifiedRewriteAux p.1, certifiedRewriteAux p.2)))
              (some (certifiedRewriteAux elseExpr)) := by
          simp [certifiedRewriteAux]
        exact transport
          (expr_equiv_trans step1 (simplifyCaseExprVal_spec _ _))
          (by simp [Option.map] at step1; exact h_unfold)

/-- Certified expression rewriter: simplifies bottom-up, returning both
    the result and a proof of equivalence. Zero axioms, zero sorry. -/
def certifiedRewrite (e : Expr) : { e' : Expr // e ≃ₑ e' } :=
  ⟨certifiedRewriteAux e, certifiedRewriteAux_equiv e⟩

end SqlEquiv
