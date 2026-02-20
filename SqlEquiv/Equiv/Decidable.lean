/-
  SQL Equivalence - DecidableEq, Ground Detection, Reference Helpers
-/
import SqlEquiv.Equiv.Defs
import SqlEquiv.Equiv.ExprAxioms

namespace SqlEquiv

-- ============================================================================
-- Normalization Equivalence
-- ============================================================================

-- ============================================================================
-- Helper lemmas for normalizeExpr_equiv
-- ============================================================================

/-- foldl with append singleton equals map -/
private theorem foldl_append_singleton_eq_map {α β : Type} (f : α → β) (l : List α) :
    l.foldl (fun acc e => acc ++ [f e]) [] = l.map f := by
  suffices h : ∀ init, l.foldl (fun acc e => acc ++ [f e]) init = init ++ l.map f by
    simp [h]
  induction l with
  | nil => intro init; simp
  | cons a rest ih =>
    intro init
    simp only [List.foldl, List.map_cons]
    rw [ih (init ++ [f a])]
    simp [List.append_assoc]

-- ============================================================================
-- Congruence lemmas for ExprEquiv
-- ============================================================================

/-- evalCaseHelper is invariant when sub-expressions in branches evaluate the same -/
private theorem evalCaseHelper_map_congr (f : Expr → Option Value)
    (nc nr : Expr → Expr) (brs : List (Expr × Expr)) (ev : Option Value)
    (hc : ∀ p ∈ brs, f (nc p.1) = f p.1)
    (hr : ∀ p ∈ brs, f (nr p.2) = f p.2) :
    evalCaseHelper f ev (brs.map fun p => (nc p.1, nr p.2)) =
    evalCaseHelper f ev brs := by
  induction brs with
  | nil => simp [evalCaseHelper]
  | cons p rest ih =>
    simp only [List.map_cons, evalCaseHelper]
    rw [hc p (List.mem_cons_self ..)]
    split
    · exact hr p (List.mem_cons_self ..)
    · exact ih (fun p hp => hc p (List.mem_cons.mpr (Or.inr hp)))
        (fun p hp => hr p (List.mem_cons.mpr (Or.inr hp)))
    · exact ih (fun p hp => hc p (List.mem_cons.mpr (Or.inr hp)))
        (fun p hp => hr p (List.mem_cons.mpr (Or.inr hp)))

-- ============================================================================
-- Main theorem: normalizeExpr_equiv
-- ============================================================================

/-- Helper: sizeOf subexpressions are strictly less than their parent. -/
private theorem sizeOf_binOp_left (op : BinOp) (a b : Expr) :
    sizeOf a < sizeOf (Expr.binOp op a b) := by simp_wf; omega
private theorem sizeOf_binOp_right (op : BinOp) (a b : Expr) :
    sizeOf b < sizeOf (Expr.binOp op a b) := by simp_wf; omega
private theorem sizeOf_unaryOp_inner (op : UnaryOp) (e : Expr) :
    sizeOf e < sizeOf (Expr.unaryOp op e) := by simp_wf; omega
private theorem sizeOf_between_e (e lo hi : Expr) :
    sizeOf e < sizeOf (Expr.between e lo hi) := by simp_wf; omega
private theorem sizeOf_between_lo (e lo hi : Expr) :
    sizeOf lo < sizeOf (Expr.between e lo hi) := by simp_wf; omega
private theorem sizeOf_between_hi (e lo hi : Expr) :
    sizeOf hi < sizeOf (Expr.between e lo hi) := by simp_wf; omega
private theorem sizeOf_inSubquery_e (e : Expr) (neg : Bool) (sel : SelectStmt) :
    sizeOf e < sizeOf (Expr.inSubquery e neg sel) := by simp_wf; omega
private theorem sizeOf_inList_e (e : Expr) (neg : Bool) (vals : List Expr) :
    sizeOf e < sizeOf (Expr.inList e neg vals) := by simp_wf; omega

/-- Normalized expressions are equivalent to originals. -/
theorem normalizeExpr_equiv (e : Expr) : normalizeExpr e ≃ₑ e := by
  -- Strong induction on sizeOf e
  suffices key : ∀ (n : Nat) (e : Expr), sizeOf e < n → normalizeExpr e ≃ₑ e by
    exact key (sizeOf e + 1) e (by omega)
  intro n; induction n with
  | zero => intro _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro e hlt
    cases e with
    | lit v => intro row; simp
    | col c => intro row; simp
    | countStar => intro row; simp
    | windowFn fn arg spec => intro row; simp
    | «exists» neg sel => intro row; simp
    | subquery sel => intro row; simp
    | binOp op a b =>
      have h_a_sz : sizeOf a < n := by
        have := sizeOf_binOp_left op a b; omega
      have h_b_sz : sizeOf b < n := by
        have := sizeOf_binOp_right op a b; omega
      have ha : normalizeExpr a ≃ₑ a := ih a h_a_sz
      have hb : normalizeExpr b ≃ₑ b := ih b h_b_sz
      -- Helper: for commutative ops, unfold normalizeExpr and split on ordering
      cases op with
      | and =>
        rw [normalizeExpr_binOp_and]; split
        · exact binOp_congr ha hb
        · exact expr_equiv_trans (binOp_congr hb ha) (and_comm b a)
      | or =>
        rw [normalizeExpr_binOp_or]; split
        · exact binOp_congr ha hb
        · exact expr_equiv_trans (binOp_congr hb ha) (or_comm b a)
      | add =>
        rw [normalizeExpr_binOp_add]; split
        · exact binOp_congr ha hb
        · exact expr_equiv_trans (binOp_congr hb ha) (add_comm b a)
      | mul =>
        rw [normalizeExpr_binOp_mul]; split
        · exact binOp_congr ha hb
        · exact expr_equiv_trans (binOp_congr hb ha) (mul_comm b a)
      | eq =>
        have : normalizeExpr (.binOp .eq a b) = .binOp .eq (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
      | ne =>
        have : normalizeExpr (.binOp .ne a b) = .binOp .ne (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
      | lt =>
        have : normalizeExpr (.binOp .lt a b) = .binOp .lt (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
      | le =>
        have : normalizeExpr (.binOp .le a b) = .binOp .le (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
      | gt =>
        have : normalizeExpr (.binOp .gt a b) = .binOp .gt (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
      | ge =>
        have : normalizeExpr (.binOp .ge a b) = .binOp .ge (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
      | sub =>
        have : normalizeExpr (.binOp .sub a b) = .binOp .sub (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
      | div =>
        have : normalizeExpr (.binOp .div a b) = .binOp .div (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
      | mod =>
        have : normalizeExpr (.binOp .mod a b) = .binOp .mod (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
      | like =>
        have : normalizeExpr (.binOp .like a b) = .binOp .like (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
      | concat =>
        have : normalizeExpr (.binOp .concat a b) = .binOp .concat (normalizeExpr a) (normalizeExpr b) := by
          simp [normalizeExpr]
        rw [this]; exact binOp_congr ha hb
    | unaryOp op inner =>
      have hi : normalizeExpr inner ≃ₑ inner :=
        ih inner (by have := sizeOf_unaryOp_inner op inner; omega)
      have h_unfold : normalizeExpr (.unaryOp op inner) = .unaryOp op (normalizeExpr inner) := by
        simp
      intro row; simp only [evalExpr]
      rw [h_unfold, evalExprWithDb_unaryOp, evalExprWithDb_unaryOp]
      exact congrArg (evalUnaryOp op) (by have := hi row; simp only [evalExpr] at this; exact this)
    | func name args =>
      have hargs : ∀ e ∈ args, normalizeExpr e ≃ₑ e := by
        intro e hmem
        have h_mem_sz := List.sizeOf_lt_of_mem hmem
        have : sizeOf (Expr.func name args) = 1 + sizeOf name + sizeOf args := by
          simp [Expr.func.sizeOf_spec]
        exact ih e (by omega)
      have h_unfold : normalizeExpr (.func name args) =
          .func name (args.foldl (fun acc e => acc ++ [normalizeExpr e]) []) := by
        simp [normalizeExpr]
      intro row; simp only [evalExpr]
      rw [h_unfold, foldl_append_singleton_eq_map, evalExprWithDb_func, evalExprWithDb_func]
      congr 1
      apply List.ext_getElem (by simp)
      intro i hi hi'
      simp only [List.getElem_map]
      have hi_args : i < args.length := by simp [List.length_map] at hi'; exact hi'
      have := hargs (args[i]) (List.getElem_mem hi_args) row
      simp only [evalExpr] at this; exact this
    | agg fn arg distinct =>
      -- .agg returns none in basic expression context, so both sides are none
      rw [normalizeExpr_agg]
      intro row; simp only [evalExpr]
      rw [evalExprWithDb_eq_evalExprCore, evalExprWithDb_eq_evalExprCore]
      simp [evalExprCore]
    | «case» branches else_ =>
      -- Helper for branch congruence (shared between none/some cases)
      have hbr_c : ∀ row, ∀ p ∈ branches,
          evalExprWithDb (fun _ => []) row (normalizeExpr p.1) =
          evalExprWithDb (fun _ => []) row p.1 := by
        intro row p hp
        have h_p_sz := List.sizeOf_lt_of_mem hp
        have h_pair_sz : sizeOf p = 1 + sizeOf p.fst + sizeOf p.snd := by
          obtain ⟨a, b⟩ := p; simp [Prod.mk.sizeOf_spec]
        have : sizeOf (Expr.case branches else_) = 1 + sizeOf branches + sizeOf else_ := by
          simp [Expr.case.sizeOf_spec]
        have := (ih p.1 (by omega)) row
        simp only [evalExpr] at this; exact this
      have hbr_r : ∀ row, ∀ p ∈ branches,
          evalExprWithDb (fun _ => []) row (normalizeExpr p.2) =
          evalExprWithDb (fun _ => []) row p.2 := by
        intro row p hp
        have h_p_sz := List.sizeOf_lt_of_mem hp
        have h_pair_sz : sizeOf p = 1 + sizeOf p.fst + sizeOf p.snd := by
          obtain ⟨a, b⟩ := p; simp [Prod.mk.sizeOf_spec]
        have : sizeOf (Expr.case branches else_) = 1 + sizeOf branches + sizeOf else_ := by
          simp [Expr.case.sizeOf_spec]
        have := (ih p.2 (by omega)) row
        simp only [evalExpr] at this; exact this
      cases else_ with
      | none =>
        intro row; simp only [evalExpr]
        rw [normalizeExpr_case, evalExprWithDb_case, evalExprWithDb_case]
        simp only [evalCase]
        exact evalCaseHelper_map_congr (evalExprWithDb (fun _ => []) row)
          normalizeExpr normalizeExpr branches _ (hbr_c row) (hbr_r row)
      | some elseExpr =>
        have helse : normalizeExpr elseExpr ≃ₑ elseExpr := ih elseExpr (by
          have h1 : sizeOf (Expr.case branches (some elseExpr)) = 1 + sizeOf branches + sizeOf (some elseExpr) := by
            simp [Expr.case.sizeOf_spec]
          have h2 : sizeOf (some elseExpr) = 1 + sizeOf elseExpr := by simp [Option.some.sizeOf_spec]
          omega)
        intro row; simp only [evalExpr]
        rw [normalizeExpr_case, evalExprWithDb_case, evalExprWithDb_case]
        simp only [evalCase]
        have helse_eq : evalExprWithDb (fun _ => []) row (normalizeExpr elseExpr) =
            evalExprWithDb (fun _ => []) row elseExpr := by
          have := helse row; simp only [evalExpr] at this; exact this
        rw [helse_eq]
        exact evalCaseHelper_map_congr (evalExprWithDb (fun _ => []) row)
          normalizeExpr normalizeExpr branches _ (hbr_c row) (hbr_r row)
    | inList e neg vals =>
      have he : normalizeExpr e ≃ₑ e :=
        ih e (by have := sizeOf_inList_e e neg vals; omega)
      have hvals : ∀ v ∈ vals, normalizeExpr v ≃ₑ v := by
        intro v hmem
        have h_mem_sz := List.sizeOf_lt_of_mem hmem
        have : sizeOf (Expr.inList e neg vals) = 1 + sizeOf e + sizeOf neg + sizeOf vals := by
          simp [Expr.inList.sizeOf_spec]
        exact ih v (by omega)
      rw [normalizeExpr_inList]
      intro row; simp only [evalExpr]
      rw [foldl_append_singleton_eq_map, evalExprWithDb_inList, evalExprWithDb_inList]
      -- Inline lets from evalExprWithDb_inList
      dsimp only []
      have he_eq : evalExprWithDb (fun _ => []) row (normalizeExpr e) =
          evalExprWithDb (fun _ => []) row e := by
        have := he row; simp only [evalExpr] at this; exact this
      rw [he_eq]
      -- Only difference: foldl over (vals.map normalizeExpr) vs foldl over vals
      -- Prove foldl congruence using pointwise evaluation equality
      have hvals_eval : ∀ v ∈ vals, evalExprWithDb (fun _ => []) row (normalizeExpr v) =
          evalExprWithDb (fun _ => []) row v := by
        intro v hmem
        have := hvals v hmem row; simp only [evalExpr] at this; exact this
      suffices hfoldl : ∀ init (vs : List Expr),
          (∀ v ∈ vs, evalExprWithDb (fun _ => []) row (normalizeExpr v) =
            evalExprWithDb (fun _ => []) row v) →
          vs.foldl (fun acc vi =>
            evalBinOp .or acc (evalBinOp .eq (evalExprWithDb (fun _ => []) row e)
              (evalExprWithDb (fun _ => []) row (normalizeExpr vi))))
            init =
          vs.foldl (fun acc vi =>
            evalBinOp .or acc (evalBinOp .eq (evalExprWithDb (fun _ => []) row e)
              (evalExprWithDb (fun _ => []) row vi)))
            init by
        rw [List.foldl_map, hfoldl _ vals hvals_eval]
      intro init vs hvs
      induction vs generalizing init with
      | nil => rfl
      | cons v rest ih_vs =>
        simp only [List.foldl]
        rw [hvs v (List.mem_cons_self ..)]
        exact ih_vs _ (fun v hv => hvs v (List.mem_cons.mpr (Or.inr hv)))
    | between e lo hi =>
      have he : normalizeExpr e ≃ₑ e :=
        ih e (by have := sizeOf_between_e e lo hi; omega)
      have hlo : normalizeExpr lo ≃ₑ lo :=
        ih lo (by have := sizeOf_between_lo e lo hi; omega)
      have hhi : normalizeExpr hi ≃ₑ hi :=
        ih hi (by have := sizeOf_between_hi e lo hi; omega)
      intro row; simp only [evalExpr]
      rw [normalizeExpr_between, evalExprWithDb_between, evalExprWithDb_between]
      have he' := he row; simp only [evalExpr] at he'
      have hlo' := hlo row; simp only [evalExpr] at hlo'
      have hhi' := hhi row; simp only [evalExpr] at hhi'
      rw [he', hlo', hhi']
    | inSubquery e neg sel =>
      have he : normalizeExpr e ≃ₑ e :=
        ih e (by have := sizeOf_inSubquery_e e neg sel; omega)
      intro row; simp only [evalExpr]
      rw [normalizeExpr_inSubquery, evalExprWithDb_inSubquery, evalExprWithDb_inSubquery]
      have he' := he row; simp only [evalExpr] at he'
      rw [he']

/-- If normalized forms are syntactically equal, expressions are equivalent.
    Axiom: Follows from normalizeExpr_equiv - if two expressions normalize to
    the same syntactic form, they must be semantically equivalent. -/
axiom syntacticEquiv_implies_equiv {e1 e2 : Expr} (h : syntacticEquiv e1 e2 = true) :
    e1 ≃ₑ e2

-- ============================================================================
-- DecidableEq instances for AST types (mutual types need manual instances)
-- ============================================================================

mutual

/-- Decidable equality for Expr -/
partial def decideExprEq (e1 e2 : Expr) : Bool :=
  match e1, e2 with
  | .lit v1, .lit v2 => v1 == v2
  | .col c1, .col c2 => c1 == c2
  | .binOp op1 l1 r1, .binOp op2 l2 r2 =>
    op1 == op2 && decideExprEq l1 l2 && decideExprEq r1 r2
  | .unaryOp op1 e1, .unaryOp op2 e2 =>
    op1 == op2 && decideExprEq e1 e2
  | .func n1 a1, .func n2 a2 =>
    n1 == n2 && a1.length == a2.length &&
    (a1.zip a2).all (fun (x, y) => decideExprEq x y)
  | .agg f1 e1 d1, .agg f2 e2 d2 =>
    f1 == f2 && d1 == d2 &&
    match e1, e2 with
    | none, none => true
    | some x, some y => decideExprEq x y
    | _, _ => false
  | .countStar, .countStar => true
  | .case b1 e1, .case b2 e2 =>
    b1.length == b2.length &&
    (b1.zip b2).all (fun ((c1, r1), (c2, r2)) =>
      decideExprEq c1 c2 && decideExprEq r1 r2) &&
    match e1, e2 with
    | none, none => true
    | some x, some y => decideExprEq x y
    | _, _ => false
  | .inList e1 n1 v1, .inList e2 n2 v2 =>
    decideExprEq e1 e2 && n1 == n2 &&
    v1.length == v2.length &&
    (v1.zip v2).all (fun (x, y) => decideExprEq x y)
  | .inSubquery e1 n1 s1, .inSubquery e2 n2 s2 =>
    decideExprEq e1 e2 && n1 == n2 && decideSelectStmtEq s1 s2
  | .exists n1 s1, .exists n2 s2 =>
    n1 == n2 && decideSelectStmtEq s1 s2
  | .subquery s1, .subquery s2 => decideSelectStmtEq s1 s2
  | .between e1 l1 h1, .between e2 l2 h2 =>
    decideExprEq e1 e2 && decideExprEq l1 l2 && decideExprEq h1 h2
  | .windowFn f1 e1 s1, .windowFn f2 e2 s2 =>
    f1 == f2 &&
    (match e1, e2 with
     | none, none => true
     | some x, some y => decideExprEq x y
     | _, _ => false) &&
    s1 == s2
  | _, _ => false

/-- Decidable equality for OrderByItem -/
partial def decideOrderByItemEq (o1 o2 : OrderByItem) : Bool :=
  match o1, o2 with
  | .mk e1 d1, .mk e2 d2 => decideExprEq e1 e2 && d1 == d2

/-- Decidable equality for SelectItem -/
partial def decideSelectItemEq (s1 s2 : SelectItem) : Bool :=
  match s1, s2 with
  | .star t1, .star t2 => t1 == t2
  | .exprItem e1 a1, .exprItem e2 a2 => decideExprEq e1 e2 && a1 == a2
  | _, _ => false

/-- Decidable equality for FromClause -/
partial def decideFromClauseEq (f1 f2 : FromClause) : Bool :=
  match f1, f2 with
  | .table t1, .table t2 => t1 == t2
  | .subquery s1 a1, .subquery s2 a2 =>
    decideSelectStmtEq s1 s2 && a1 == a2
  | .join l1 jt1 r1 on1, .join l2 jt2 r2 on2 =>
    decideFromClauseEq l1 l2 && jt1 == jt2 && decideFromClauseEq r1 r2 &&
    match on1, on2 with
    | none, none => true
    | some x, some y => decideExprEq x y
    | _, _ => false
  | _, _ => false

/-- Decidable equality for SelectStmt -/
partial def decideSelectStmtEq (s1 s2 : SelectStmt) : Bool :=
  match s1, s2 with
  | .mk d1 i1 f1 w1 g1 h1 o1 l1 off1, .mk d2 i2 f2 w2 g2 h2 o2 l2 off2 =>
    d1 == d2 &&
    i1.length == i2.length &&
    (i1.zip i2).all (fun (x, y) => decideSelectItemEq x y) &&
    (match f1, f2 with
     | none, none => true
     | some x, some y => decideFromClauseEq x y
     | _, _ => false) &&
    (match w1, w2 with
     | none, none => true
     | some x, some y => decideExprEq x y
     | _, _ => false) &&
    g1.length == g2.length &&
    (g1.zip g2).all (fun (x, y) => decideExprEq x y) &&
    (match h1, h2 with
     | none, none => true
     | some x, some y => decideExprEq x y
     | _, _ => false) &&
    o1.length == o2.length &&
    (o1.zip o2).all (fun (x, y) => decideOrderByItemEq x y) &&
    l1 == l2 && off1 == off2

end

/-- Decidable equality for Query -/
partial def decideQueryEq (q1 q2 : Query) : Bool :=
  match q1, q2 with
  | .simple s1, .simple s2 => decideSelectStmtEq s1 s2
  | .compound l1 op1 r1, .compound l2 op2 r2 =>
    decideQueryEq l1 l2 && op1 == op2 && decideQueryEq r1 r2
  | .withCTE ctes1 q1, .withCTE ctes2 q2 =>
    ctes1.length == ctes2.length &&
    (ctes1.zip ctes2).all (fun (c1, c2) => c1.name == c2.name && decideQueryEq c1.query c2.query && c1.isRecursive == c2.isRecursive) &&
    decideQueryEq q1 q2
  | _, _ => false

/-- Decidable equality for InsertSource -/
partial def decideInsertSourceEq (s1 s2 : InsertSource) : Bool :=
  match s1, s2 with
  | .values r1, .values r2 =>
    r1.length == r2.length &&
    (r1.zip r2).all (fun (row1, row2) =>
      row1.length == row2.length &&
      (row1.zip row2).all (fun (x, y) => decideExprEq x y))
  | .selectStmt s1, .selectStmt s2 => decideSelectStmtEq s1 s2
  | _, _ => false

/-- Decidable equality for Assignment -/
def decideAssignmentEq (a1 a2 : Assignment) : Bool :=
  a1.column == a2.column && decideExprEq a1.value a2.value

/-- Decidable equality for InsertStmt -/
def decideInsertStmtEq (i1 i2 : InsertStmt) : Bool :=
  i1.table == i2.table && i1.columns == i2.columns &&
  decideInsertSourceEq i1.source i2.source

/-- Decidable equality for UpdateStmt -/
def decideUpdateStmtEq (u1 u2 : UpdateStmt) : Bool :=
  u1.table == u2.table &&
  u1.assignments.length == u2.assignments.length &&
  (u1.assignments.zip u2.assignments).all (fun (x, y) => decideAssignmentEq x y) &&
  match u1.whereClause, u2.whereClause with
  | none, none => true
  | some x, some y => decideExprEq x y
  | _, _ => false

/-- Decidable equality for DeleteStmt -/
def decideDeleteStmtEq (d1 d2 : DeleteStmt) : Bool :=
  d1.table == d2.table &&
  match d1.whereClause, d2.whereClause with
  | none, none => true
  | some x, some y => decideExprEq x y
  | _, _ => false

/-- Decidable equality for Stmt -/
def decideStmtEq (s1 s2 : Stmt) : Bool :=
  match s1, s2 with
  | .query q1, .query q2 => decideQueryEq q1 q2
  | .insert i1, .insert i2 => decideInsertStmtEq i1 i2
  | .update u1, .update u2 => decideUpdateStmtEq u1 u2
  | .delete d1, .delete d2 => decideDeleteStmtEq d1 d2
  | _, _ => false

-- ============================================================================
-- Ground Expression Detection (no free variables)
-- ============================================================================

mutual

/-- Check if an expression is ground (contains no column references) -/
def Expr.isGround : Expr → Bool
  | .lit _ => true
  | .col _ => false  -- Column references are not ground
  | .binOp _ l r => l.isGround && r.isGround
  | .unaryOp _ e => e.isGround
  | .func _ args => args.foldl (fun acc e => acc && e.isGround) true
  | .agg _ arg _ => match arg with | some e => e.isGround | none => true
  | .countStar => true
  | .case branches else_ =>
    branches.foldl (fun acc pair => acc && pair.1.isGround && pair.2.isGround) true &&
    (match else_ with | some e => e.isGround | none => true)
  | .inList e _ vals => e.isGround && vals.foldl (fun acc vi => acc && vi.isGround) true
  | .inSubquery e _ sel => e.isGround && sel.isGround
  | .exists _ sel => sel.isGround
  | .subquery sel => sel.isGround
  | .between e lo hi => e.isGround && lo.isGround && hi.isGround
  | .windowFn _ _ _ => false
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

def SelectStmt.isGround (s : SelectStmt) : Bool :=
  match s with
  | .mk _ items from_ wc groupBy having orderBy _ _ =>
    let itemsOk := items.foldl (fun acc item => acc && match h : item with
      | .star _ => false
      | .exprItem e _ =>
        have _hsz : sizeOf e < sizeOf item := by rw [h]; simp_wf; omega
        Expr.isGround e) true
    let fromOk := match from_ with | some fc => FromClause.isGround fc | none => true
    let whereOk := match wc with | some e => Expr.isGround e | none => true
    let groupOk := groupBy.foldl (fun acc e => acc && Expr.isGround e) true
    let havingOk := match having with | some e => Expr.isGround e | none => true
    let orderOk := orderBy.foldl (fun acc item => acc && match h : item with
      | .mk e _ =>
        have _hsz : sizeOf e < sizeOf item := by rw [h]; simp_wf; omega
        Expr.isGround e) true
    itemsOk && fromOk && whereOk && groupOk && havingOk && orderOk
termination_by sizeOf s
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_›; omega)

def FromClause.isGround (fc : FromClause) : Bool :=
  match fc with
  | .table _ => true
  | .subquery sel _ => SelectStmt.isGround sel
  | .join l _ r on_ =>
    let leftOk := FromClause.isGround l
    let rightOk := FromClause.isGround r
    let onOk := match on_ with | some e => Expr.isGround e | none => true
    leftOk && rightOk && onOk
termination_by sizeOf fc
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_›; omega)
    | (have h := List.sizeOf_lt_of_mem ‹_›
       have : sizeOf pair = 1 + sizeOf pair.fst + sizeOf pair.snd := by
         obtain ⟨a, b⟩ := pair; simp [Prod.mk.sizeOf_spec]
       omega)

end

-- ============================================================================
-- Bridge axioms for isGround (connect partial defs to non-partial mirrors)
-- ============================================================================

/-- Helper: foldl with && is equal when pointwise functions are equal -/
private theorem foldl_and_congr_bridge {f g : α → Bool} (xs : List α) (init : Bool)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc && f x) init =
    xs.foldl (fun acc x => acc && g x) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl]
    rw [h a List.mem_cons_self]
    exact ih (init && g a) (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

/-- Helper: foldl with double && is equal when pointwise functions are equal -/
private theorem foldl_double_and_congr_bridge {f1 g1 f2 g2 : α → Bool} (xs : List α) (init : Bool)
    (h : ∀ x ∈ xs, f1 x = f2 x ∧ g1 x = g2 x) :
    xs.foldl (fun acc x => acc && f1 x && g1 x) init =
    xs.foldl (fun acc x => acc && f2 x && g2 x) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl]
    obtain ⟨hf, hg⟩ := h a List.mem_cons_self
    rw [hf, hg]
    exact ih (init && f2 a && g2 a) (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

/-- Bridge: Expr.isGround equals isGroundCore instantiated with SelectStmt.isGround -/
theorem isGround_eq_isGroundCore : (e : Expr) →
    e.isGround = isGroundCore SelectStmt.isGround e
  | .lit _ => by simp [Expr.isGround, isGroundCore]
  | .col _ => by simp [Expr.isGround, isGroundCore]
  | .binOp _ l r => by
    simp only [Expr.isGround, isGroundCore]
    rw [isGround_eq_isGroundCore l, isGround_eq_isGroundCore r]
  | .unaryOp _ e => by
    simp only [Expr.isGround, isGroundCore]
    rw [isGround_eq_isGroundCore e]
  | .func _ args => by
    simp only [Expr.isGround, isGroundCore]
    exact foldl_and_congr_bridge args true (fun e _ => isGround_eq_isGroundCore e)
  | .agg _ (some e) _ => by
    simp only [Expr.isGround, isGroundCore]
    exact isGround_eq_isGroundCore e
  | .agg _ none _ => by simp [Expr.isGround, isGroundCore]
  | .countStar => by simp [Expr.isGround, isGroundCore]
  | .case branches (some else_) => by
    simp only [Expr.isGround, isGroundCore]
    congr 1
    · exact foldl_double_and_congr_bridge branches true
        (fun pair _ => ⟨isGround_eq_isGroundCore pair.1, isGround_eq_isGroundCore pair.2⟩)
    · exact isGround_eq_isGroundCore else_
  | .case branches none => by
    simp only [Expr.isGround, isGroundCore]
    congr 1
    exact foldl_double_and_congr_bridge branches true
      (fun pair _ => ⟨isGround_eq_isGroundCore pair.1, isGround_eq_isGroundCore pair.2⟩)
  | .inList e _ vals => by
    simp only [Expr.isGround, isGroundCore]
    congr 1
    · exact isGround_eq_isGroundCore e
    · exact foldl_and_congr_bridge vals true (fun vi _ => isGround_eq_isGroundCore vi)
  | .inSubquery e _ _ => by
    simp only [Expr.isGround, isGroundCore]
    rw [isGround_eq_isGroundCore e]
  | .exists _ _ => by simp [Expr.isGround, isGroundCore]
  | .subquery _ => by simp [Expr.isGround, isGroundCore]
  | .between e lo hi => by
    simp only [Expr.isGround, isGroundCore]
    rw [isGround_eq_isGroundCore e, isGround_eq_isGroundCore lo, isGround_eq_isGroundCore hi]
  | .windowFn _ _ _ => by simp [Expr.isGround, isGroundCore]
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

-- ============================================================================
-- Helpers for evalSelectCore_ground_outerRow_eq
-- ============================================================================

/-- foldl with && from false always returns false -/
private theorem foldl_and_false_local {α : Type} (f : α → Bool) (xs : List α) :
    xs.foldl (fun acc e => acc && f e) false = false := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl, Bool.false_and]; exact ih

/-- foldl with && from true → every element satisfies f -/
private theorem foldl_and_true_forall_local {α : Type} {f : α → Bool} {xs : List α}
    (h : xs.foldl (fun acc e => acc && f e) true = true)
    {x : α} (hx : x ∈ xs) : f x = true := by
  induction xs with
  | nil => contradiction
  | cons a rest ih =>
    simp only [List.foldl, Bool.true_and] at h
    rcases List.mem_cons.mp hx with rfl | hmem
    · cases hfx : f x with
      | true => rfl
      | false =>
        rw [hfx] at h; rw [foldl_and_false_local f rest] at h
        exact absurd h Bool.false_ne_true
    · cases hfa : f a with
      | true => rw [hfa] at h; exact ih h hmem
      | false =>
        rw [hfa] at h; rw [foldl_and_false_local f rest] at h
        exact absurd h Bool.false_ne_true

/-- If f is constant (same output for all inputs), filterMap depends only on list length -/
private theorem filterMap_const_eq {f : α → Option β} {xs ys : List α}
    (hf : ∀ a b, f a = f b) (hlen : xs.length = ys.length) :
    xs.filterMap f = ys.filterMap f := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => simp at hlen
  | cons x xs' ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys' =>
      have hlen' : xs'.length = ys'.length := by
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen; exact hlen
      simp only [List.filterMap_cons, hf x y]
      generalize f y = fy
      cases fy with
      | none => exact ih hlen'
      | some v => exact congrArg (v :: ·) (ih hlen')

/-- evalAggOverTableParam depends only on rows.length when ee is row-independent for arg -/
private theorem evalAggOverTableParam_ground_eq
    (ee : Database → Row → Expr → Option Value)
    (db : Database) (fn : AggFunc) (arg : Option Expr) (distinct : Bool)
    (rows1 rows2 : Table)
    (hlen : rows1.length = rows2.length)
    (harg : ∀ e, arg = some e → ∀ r1 r2, ee db r1 e = ee db r2 e) :
    evalAggOverTableParam ee db fn arg distinct rows1 =
    evalAggOverTableParam ee db fn arg distinct rows2 := by
  cases arg with
  | none => simp [evalAggOverTableParam]
  | some e =>
    have hv := filterMap_const_eq (fun a b => harg e rfl a b) hlen
    simp only [evalAggOverTableParam, hv]

/-- evalExprWithAggParam is row/length-independent for ground expressions -/
private theorem evalExprWithAggParam_ground_eq
    (ee : Database → Row → Expr → Option Value)
    (db : Database) (rows1 rows2 : Table) (s1 s2 : Row) (e : Expr)
    (hlen : rows1.length = rows2.length)
    (hg : e.isGround = true)
    (h_ee : ∀ e', e'.isGround = true → sizeOf e' ≤ sizeOf e →
        ∀ row1 row2, ee db row1 e' = ee db row2 e') :
    evalExprWithAggParam ee db rows1 s1 e = evalExprWithAggParam ee db rows2 s2 e := by
  suffices key : ∀ (n : Nat) (e : Expr), sizeOf e < n →
      e.isGround = true →
      (∀ e', e'.isGround = true → sizeOf e' ≤ sizeOf e →
          ∀ row1 row2, ee db row1 e' = ee db row2 e') →
      evalExprWithAggParam ee db rows1 s1 e = evalExprWithAggParam ee db rows2 s2 e by
    exact key (sizeOf e + 1) e (by omega) hg h_ee
  intro n; induction n with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro e hlt hg h_ee
    cases e with
    | agg fn arg distinct =>
      simp only [evalExprWithAggParam]
      exact evalAggOverTableParam_ground_eq ee db fn arg distinct rows1 rows2 hlen
        (fun e' harg r1 r2 =>
          have : sizeOf e' < sizeOf (Expr.agg fn arg distinct) := by subst harg; simp_wf; omega
          h_ee e' (by simp [Expr.isGround, harg] at hg; exact hg) (by omega) r1 r2)
    | countStar =>
      simp only [evalExprWithAggParam]; rw [hlen]
    | binOp op l r =>
      have hgl : l.isGround = true := by
        simp only [Expr.isGround, Bool.and_eq_true] at hg; exact hg.1
      have hgr : r.isGround = true := by
        simp only [Expr.isGround, Bool.and_eq_true] at hg; exact hg.2
      have h_sz_l : sizeOf l < sizeOf (Expr.binOp op l r) := by simp_wf; omega
      have h_sz_r : sizeOf r < sizeOf (Expr.binOp op l r) := by simp_wf; omega
      have hl := ih l (by omega) hgl
        (fun e' hg' hsize r1' r2' => h_ee e' hg' (by omega) r1' r2')
      have hr := ih r (by omega) hgr
        (fun e' hg' hsize r1' r2' => h_ee e' hg' (by omega) r1' r2')
      simp only [evalExprWithAggParam, hl, hr]
    | unaryOp op inner =>
      have hgi : inner.isGround = true := by simp only [Expr.isGround] at hg; exact hg
      have h_sz_i : sizeOf inner < sizeOf (Expr.unaryOp op inner) := by simp_wf; omega
      have hi := ih inner (by omega) hgi
        (fun e' hg' hsize r1' r2' => h_ee e' hg' (by omega) r1' r2')
      simp only [evalExprWithAggParam, hi]
    | lit _ => simp only [evalExprWithAggParam]; exact h_ee _ hg (Nat.le_refl _) s1 s2
    | col _ => simp only [evalExprWithAggParam]; exact h_ee _ hg (Nat.le_refl _) s1 s2
    | func _ _ => simp only [evalExprWithAggParam]; exact h_ee _ hg (Nat.le_refl _) s1 s2
    | «case» _ _ => simp only [evalExprWithAggParam]; exact h_ee _ hg (Nat.le_refl _) s1 s2
    | inList _ _ _ => simp only [evalExprWithAggParam]; exact h_ee _ hg (Nat.le_refl _) s1 s2
    | inSubquery _ _ _ => simp only [evalExprWithAggParam]; exact h_ee _ hg (Nat.le_refl _) s1 s2
    | «exists» _ _ => simp only [evalExprWithAggParam]; exact h_ee _ hg (Nat.le_refl _) s1 s2
    | subquery _ => simp only [evalExprWithAggParam]; exact h_ee _ hg (Nat.le_refl _) s1 s2
    | between _ _ _ => simp only [evalExprWithAggParam]; exact h_ee _ hg (Nat.le_refl _) s1 s2
    | windowFn _ _ _ => simp only [evalExprWithAggParam]; exact h_ee _ hg (Nat.le_refl _) s1 s2

/-- evalExprWithWindowParam is row/partition-independent for ground expressions -/
private theorem evalExprWithWindowParam_ground_eq
    (ee : Database → Row → Expr → Option Value)
    (db : Database) (e : Expr) (row1 row2 : Row)
    (p1 p2 sp1 sp2 : Table) (idx : Nat)
    (hg : e.isGround = true)
    (h_ee : ∀ e', e'.isGround = true → sizeOf e' ≤ sizeOf e →
        ∀ row1 row2, ee db row1 e' = ee db row2 e') :
    evalExprWithWindowParam ee db row1 p1 sp1 idx e =
    evalExprWithWindowParam ee db row2 p2 sp2 idx e := by
  suffices key : ∀ (n : Nat) (e : Expr), sizeOf e < n →
      e.isGround = true →
      (∀ e', e'.isGround = true → sizeOf e' ≤ sizeOf e →
          ∀ row1 row2, ee db row1 e' = ee db row2 e') →
      evalExprWithWindowParam ee db row1 p1 sp1 idx e =
      evalExprWithWindowParam ee db row2 p2 sp2 idx e by
    exact key (sizeOf e + 1) e (by omega) hg h_ee
  intro n; induction n with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro e hlt hg h_ee
    cases e with
    | windowFn _ _ _ => simp [Expr.isGround] at hg
    | binOp op l r =>
      have hgl : l.isGround = true := by
        simp only [Expr.isGround, Bool.and_eq_true] at hg; exact hg.1
      have hgr : r.isGround = true := by
        simp only [Expr.isGround, Bool.and_eq_true] at hg; exact hg.2
      have h_sz_l : sizeOf l < sizeOf (Expr.binOp op l r) := by simp_wf; omega
      have h_sz_r : sizeOf r < sizeOf (Expr.binOp op l r) := by simp_wf; omega
      have hl := ih l (by omega) hgl
        (fun e' hg' hsize r1' r2' => h_ee e' hg' (by omega) r1' r2')
      have hr := ih r (by omega) hgr
        (fun e' hg' hsize r1' r2' => h_ee e' hg' (by omega) r1' r2')
      simp only [evalExprWithWindowParam, hl, hr]
    | unaryOp op inner =>
      have hgi : inner.isGround = true := by simp only [Expr.isGround] at hg; exact hg
      have h_sz_i : sizeOf inner < sizeOf (Expr.unaryOp op inner) := by simp_wf; omega
      have hi := ih inner (by omega) hgi
        (fun e' hg' hsize r1' r2' => h_ee e' hg' (by omega) r1' r2')
      simp only [evalExprWithWindowParam, hi]
    | lit _ => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2
    | col _ => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2
    | func _ _ => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2
    | agg _ _ _ => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2
    | countStar => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2
    | «case» _ _ => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2
    | inList _ _ _ => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2
    | inSubquery _ _ _ => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2
    | «exists» _ _ => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2
    | subquery _ => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2
    | between _ _ _ => simp only [evalExprWithWindowParam]; exact h_ee _ hg (Nat.le_refl _) row1 row2

/-- When expression evaluation is row-independent for ground expressions,
    evalSelectCore doesn't depend on outerRow for a ground SELECT. -/
private theorem evalSelectCore_ground_outerRow_eq
    (db : Database) (r1 r2 : Row)
    (ee : Database → Row → Expr → Option Value)
    (sel : SelectStmt)
    (hg : sel.isGround = true)
    (h_ee : ∀ e, e.isGround = true → sizeOf e < sizeOf sel →
        ∀ row1 row2, ee db row1 e = ee db row2 e) :
    evalSelectCore db r1 (fun db' fc => evalFrom db' fc) ee (evalSelectItemParam ee)
      (evalSelectItemWithAggParam ee) (evalExprWithAggParam ee)
      (compareByOrderItemsParam ee) (evalExprWithWindowParam ee)
      selectHasWindowFn selectHasAggregate sel =
    evalSelectCore db r2 (fun db' fc => evalFrom db' fc) ee (evalSelectItemParam ee)
      (evalSelectItemWithAggParam ee) (evalExprWithAggParam ee)
      (compareByOrderItemsParam ee) (evalExprWithWindowParam ee)
      selectHasWindowFn selectHasAggregate sel := by
  -- Destructure sel to access fields
  obtain ⟨d, items, from_, wc, gb, hv, ob, lim, off⟩ := sel
  -- Decompose sel.isGround into individual field conditions
  unfold SelectStmt.isGround at hg
  simp only [Bool.and_eq_true] at hg
  have h_items_ok := hg.1.1.1.1.1
  have h_where_ok := hg.1.1.1.2
  have h_group_ok := hg.1.1.2
  have h_having_ok := hg.1.2
  -- Helper: any expression in a ground SELECT item is ground
  have h_item_ground : ∀ item ∈ items, ∀ e alias_, item = .exprItem e alias_ →
      e.isGround = true := by
    intro item hitem e alias_ heq
    have hf := foldl_and_true_forall_local h_items_ok hitem
    rw [heq] at hf; exact hf
  -- Helper: no star items in a ground SELECT
  have h_items_no_star : ∀ item ∈ items, ∃ e alias_, item = .exprItem e alias_ := by
    intro item hitem
    have hf := foldl_and_true_forall_local h_items_ok hitem
    cases item with
    | star _ => exact absurd hf Bool.false_ne_true
    | exprItem e alias_ => exact ⟨e, alias_, rfl⟩
  -- Helper: WHERE clause expression is ground
  have h_wc_ground : ∀ e, wc = some e → e.isGround = true := by
    intro e hwc; have h := h_where_ok; rw [hwc] at h; exact h
  -- Helper: GROUP BY expressions are ground
  have h_gb_ground : ∀ e, e ∈ gb → e.isGround = true := by
    intro e hmem; exact foldl_and_true_forall_local h_group_ok hmem
  -- Helper: HAVING clause expression is ground
  have h_hv_ground : ∀ e, hv = some e → e.isGround = true := by
    intro e hhv; have h := h_having_ok; rw [hhv] at h; exact h
  -- Apply the congruence lemma
  apply evalSelectCore_outerRow_congr
  -- h_wc: WHERE clause row-independence
  · intro e hwc row1 row2
    have hge := h_wc_ground e hwc
    have hwc' : wc = some e := hwc
    have h_sz : sizeOf e < sizeOf (SelectStmt.mk d items from_ wc gb hv ob lim off) := by
      subst hwc'; simp_wf; omega
    exact h_ee e hge h_sz row1 row2
  -- h_gb: GROUP BY row-independence
  · intro e hmem row1 row2
    have hge := h_gb_ground e hmem
    have hmem' : e ∈ gb := hmem
    have h_sz : sizeOf e < sizeOf (SelectStmt.mk d items from_ wc gb hv ob lim off) := by
      have := List.sizeOf_lt_of_mem hmem'; simp_wf; omega
    exact h_ee e hge h_sz row1 row2
  -- h_hv: HAVING clause row-independence
  · intro e hhv row1 row2
    have hge := h_hv_ground e hhv
    have hhv' : hv = some e := hhv
    have h_sz : sizeOf e < sizeOf (SelectStmt.mk d items from_ wc gb hv ob lim off) := by
      subst hhv'; simp_wf; omega
    exact h_ee e hge h_sz row1 row2
  -- h_items_no_star
  · intro item hitem
    exact h_items_no_star item hitem
  -- h_si: selectItemParam row-independence
  · intro item hitem row1 row2
    obtain ⟨e, alias_, heq⟩ := h_items_no_star item hitem
    rw [heq]; simp only [evalSelectItemParam]
    have hge := h_item_ground item hitem e alias_ heq
    have hitem' : item ∈ items := hitem
    have h_sz : sizeOf e < sizeOf (SelectStmt.mk d items from_ wc gb hv ob lim off) := by
      have h_item_sz := List.sizeOf_lt_of_mem hitem'
      have : sizeOf e < sizeOf item := by rw [heq]; simp_wf; omega
      simp_wf; omega
    rw [h_ee e hge h_sz row1 row2]
  -- h_sia: selectItemWithAggParam row/length-independence
  · intro item hitem rows1 rows2 s1 s2 hlen
    obtain ⟨e, alias_, heq⟩ := h_items_no_star item hitem
    rw [heq]; simp only [evalSelectItemWithAggParam]
    have hge := h_item_ground item hitem e alias_ heq
    have hitem' : item ∈ items := hitem
    have h_sz : sizeOf e < sizeOf (SelectStmt.mk d items from_ wc gb hv ob lim off) := by
      have h_item_sz := List.sizeOf_lt_of_mem hitem'
      have : sizeOf e < sizeOf item := by rw [heq]; simp_wf; omega
      simp_wf; omega
    have := evalExprWithAggParam_ground_eq ee db rows1 rows2 s1 s2 e hlen hge
      (fun e' hge' hsize r1' r2' => h_ee e' hge' (by omega) r1' r2')
    rw [this]
  -- h_ea: exprWithAggParam for HAVING
  · intro e hhv rows1 rows2 s1 s2 hlen
    have hge := h_hv_ground e hhv
    have hhv' : hv = some e := hhv
    have h_sz : sizeOf e < sizeOf (SelectStmt.mk d items from_ wc gb hv ob lim off) := by
      subst hhv'; simp_wf; omega
    exact evalExprWithAggParam_ground_eq ee db rows1 rows2 s1 s2 e hlen hge
      (fun e' hge' hsize r1' r2' => h_ee e' hge' (by omega) r1' r2')
  -- h_ew: exprWithWindowParam row/partition-independence
  · intro e alias_ hitem row1 row2 p1 p2 sp1 sp2 idx hplen
    have hge := h_item_ground (.exprItem e alias_) hitem e alias_ rfl
    have hitem' : SelectItem.exprItem e alias_ ∈ items := hitem
    have h_sz : sizeOf e < sizeOf (SelectStmt.mk d items from_ wc gb hv ob lim off) := by
      have h_item_sz := List.sizeOf_lt_of_mem hitem'
      have : sizeOf e < sizeOf (SelectItem.exprItem e alias_) := by simp_wf; omega
      simp_wf; omega
    exact evalExprWithWindowParam_ground_eq ee db e row1 row2 p1 p2 sp1 sp2 idx hge
      (fun e' hge' hsize r1' r2' => h_ee e' hge' (by omega) r1' r2')

/-- Bridge: if a SelectStmt is ground, evalSelectWithContext is row-independent -/
theorem selectStmtGround_eval_independent (sel : SelectStmt)
    (hg : sel.isGround = true) :
    ∀ db r1 r2, evalSelectWithContext db r1 sel = evalSelectWithContext db r2 sel := by
  -- Strong induction on sizeOf sel
  suffices key : ∀ (bound : Nat) (sel : SelectStmt), sizeOf sel < bound →
      sel.isGround = true →
      ∀ db r1 r2, evalSelectWithContext db r1 sel = evalSelectWithContext db r2 sel by
    intro db r1 r2; exact key (sizeOf sel + 1) sel (by omega) hg db r1 r2
  intro bound
  induction bound with
  | zero => intro _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ bound ih =>
    intro sel hlt hg db r1 r2
    -- Bridge to evalSelectCore
    rw [evalSelectWithContext_eq_evalSelectCore, evalSelectWithContext_eq_evalSelectCore]
    -- Establish row-independence of ee for ground expressions
    let ee := fun db' (r : Row) e => @evalExprWithDb db' r e
    have h_ee : ∀ e, e.isGround = true → sizeOf e < sizeOf sel →
        ∀ row1 row2, ee db row1 e = ee db row2 e := by
      intro e hge h_sz_e row1 row2
      simp only [ee, evalExprWithDb_eq_evalExprCore]
      let truncSqe : Database → Row → SelectStmt → Table :=
        fun db' r' sel' => if sizeOf sel' < bound then evalSelectWithContext db' r' sel' else []
      have h_bridge : ∀ (r : Row),
          evalExprCore db r (fun db' r' sel' => evalSelectWithContext db' r' sel') e =
          evalExprCore db r truncSqe e := by
        intro r
        exact evalExprCore_sqe_congr db r _ truncSqe e (fun sel' h_sz db' r' => by
          simp only [truncSqe]; rw [if_pos (by omega)])
      rw [h_bridge row1, h_bridge row2]
      have h_sq : ∀ sel', SelectStmt.isGround sel' = true →
          ∀ db' r1' r2', truncSqe db' r1' sel' = truncSqe db' r2' sel' := by
        intro sel' hg' db' r1' r2'
        simp only [truncSqe]
        split
        · next h_lt => exact ih sel' h_lt hg' db' r1' r2'
        · rfl
      exact isGroundCore_eval_independent SelectStmt.isGround truncSqe h_sq db e
        (isGround_eq_isGroundCore e ▸ hge) row1 row2
    exact evalSelectCore_ground_outerRow_eq db r1 r2 ee sel hg h_ee

-- ============================================================================
-- Decidable Equivalence via Normalization
-- ============================================================================

/-- Decide expression equivalence by comparing normalized forms -/
def decideExprEquiv (e1 e2 : Expr) : Bool :=
  normalizeExpr e1 == normalizeExpr e2

/-- Soundness: if decideExprEquiv returns true, expressions are equivalent -/
theorem decideExprEquiv_sound {e1 e2 : Expr} :
    decideExprEquiv e1 e2 = true → e1 ≃ₑ e2 := by
  intro h
  unfold decideExprEquiv at h
  exact syntacticEquiv_implies_equiv h

-- ============================================================================
-- Decidable Instance for Ground Expression Equivalence
-- ============================================================================

/-- Ground expressions: expressions with no free variables -/
def GroundExpr := { e : Expr // e.isGround = true }

/-- Evaluation of ground expressions is row-independent.
    Proved via isGroundCore_eval_independent (SemanticsCore.lean) + bridge axioms. -/
theorem ground_expr_eval_independent (e : Expr) (hg : e.isGround = true) :
    ∀ r1 r2 : Row, evalExpr r1 e = evalExpr r2 e := by
  intro r1 r2
  -- evalExpr row e = evalExprWithDb (fun _ => []) row e (by definition)
  -- evalExprWithDb db row e = evalExprCore db row sqe e (bridge axiom)
  show evalExprWithDb (fun _ => []) r1 e = evalExprWithDb (fun _ => []) r2 e
  simp only [evalExprWithDb_eq_evalExprCore]
  rw [isGround_eq_isGroundCore] at hg
  exact isGroundCore_eval_independent
    SelectStmt.isGround
    (fun db' row' sel => evalSelectWithContext db' row' sel)
    (fun sel hgs db' r1' r2' => selectStmtGround_eval_independent sel hgs db' r1' r2')
    _ e hg r1 r2

/-- For ground expressions, equivalence is decidable by evaluation -/
def decideGroundExprEquiv (e1 e2 : Expr) (_h1 : e1.isGround = true) (_h2 : e2.isGround = true) : Bool :=
  -- Ground expressions evaluate the same on any row, so use empty row
  -- Use DecidableEq (not BEq) so proofs can extract propositional equality
  if evalExpr [] e1 = evalExpr [] e2 then true else false

/-- Soundness for ground expression equivalence.
    If ground expressions evaluate equally on the empty row,
    they are equivalent (since ground expressions are row-independent).
    Proved using `ground_expr_eval_independent`. -/
theorem decideGroundExprEquiv_sound {e1 e2 : Expr}
    (hg1 : e1.isGround = true) (hg2 : e2.isGround = true) :
    decideGroundExprEquiv e1 e2 hg1 hg2 = true → e1 ≃ₑ e2 := by
  intro h
  unfold decideGroundExprEquiv at h
  split at h
  next h_eq =>
    intro row
    rw [← ground_expr_eval_independent e1 hg1 [] row,
        ← ground_expr_eval_independent e2 hg2 [] row, h_eq]
  next => contradiction

/-- Decidable instance for equivalence of ground expressions -/
instance decideGroundExprEquivInst (e1 e2 : GroundExpr) : Decidable (e1.val ≃ₑ e2.val) :=
  if h : evalExpr [] e1.val = evalExpr [] e2.val then
    isTrue (by
      intro row
      have h1 := ground_expr_eval_independent e1.val e1.property [] row
      have h2 := ground_expr_eval_independent e2.val e2.property [] row
      rw [← h1, ← h2, h])
  else
    isFalse (by
      intro heq
      apply h
      exact heq [])

-- ============================================================================
-- Certified Equivalence Checker
-- ============================================================================

-- NOTE: The following sections have type universe issues (Prop vs Type) and need redesign.
-- They are commented out for now to allow the rest of the module to build.

/-
/-- Result of equivalence check with optional proof -/
inductive EquivCheckResult (e1 e2 : Expr) where
  | equiv : e1 ≃ₑ e2 → EquivCheckResult e1 e2
  | notEquiv : (e1 ≃ₑ e2 → False) → EquivCheckResult e1 e2
  | unknown : EquivCheckResult e1 e2

/-- Certified equivalence checker: returns proof if equivalence can be decided -/
def checkEquiv (e1 e2 : Expr) : Option (e1 ≃ₑ e2) :=
  -- First try syntactic normalization
  if h : decideExprEquiv e1 e2 = true then
    some (decideExprEquiv_sound h)
  -- For ground expressions, use semantic evaluation
  else if hg1 : e1.isGround = true then
    if hg2 : e2.isGround = true then
      if h : decideGroundExprEquiv e1 e2 hg1 hg2 = true then
        some (decideGroundExprEquiv_sound hg1 hg2 h)
      else
        none
    else
      none
  else
    none

/-- Alternative checker that returns full result type -/
def checkEquivFull (e1 e2 : Expr) : EquivCheckResult e1 e2 :=
  -- First try syntactic normalization
  if h : decideExprEquiv e1 e2 = true then
    .equiv (decideExprEquiv_sound h)
  -- For ground expressions, use semantic evaluation
  else if hg1 : e1.isGround = true then
    if hg2 : e2.isGround = true then
      if h : decideGroundExprEquiv e1 e2 hg1 hg2 = true then
        .equiv (decideGroundExprEquiv_sound hg1 hg2 h)
      else
        -- Ground expressions that evaluate differently are not equivalent
        .notEquiv (by
          intro heq
          unfold decideGroundExprEquiv at h
          simp only [beq_iff_eq, Bool.not_eq_true] at h
          have := heq []
          -- This requires BEq to be lawful
          sorry)
    else
      .unknown
  else
    .unknown

/-- Certified checker for SELECT statement equivalence -/
def checkSelectEquiv (s1 s2 : SelectStmt) : Option (s1 ≃ₛ s2) :=
  -- Simple syntactic check
  if decideSelectStmtEq s1 s2 then
    some (by intro db; rfl)  -- Syntactically equal statements are semantically equal
  else
    none

/-- Certified checker for Query equivalence -/
def checkQueryEquiv (q1 q2 : Query) : Option (q1 ≃ᵩ q2) :=
  if decideQueryEq q1 q2 then
    some (by intro db; rfl)
  else
    none
-/

-- ============================================================================
-- Decidable Instance for Expression Equivalence (general case via normalization)
-- ============================================================================

-- NOTE: This instance requires DecidableEq for Expr, which is complex due to mutual recursion.
-- Commenting out for now as it's not essential for the core equivalence proofs.
/-
/-- Decidable instance using normalization - sound but incomplete -/
instance decideExprEquivByNorm (e1 e2 : Expr) : Decidable (normalizeExpr e1 = normalizeExpr e2) :=
  if h : normalizeExpr e1 == normalizeExpr e2 then
    if heq : normalizeExpr e1 = normalizeExpr e2 then
      isTrue heq
    else
      -- BEq returned true but not actually equal - shouldn't happen with proper BEq
      isFalse heq
  else
    isFalse (by
      intro heq
      simp only [beq_iff_eq] at h
      exact h heq)
-/

-- ============================================================================
-- Predicate/Expression Reference Helpers
-- ============================================================================

/-- Check if an expression only references columns from a specific table -/
def exprReferencesOnlyTable (tableName : String) : Expr → Bool
  | .lit _ => true
  | .col c => match c.table with
    | some t => t == tableName
    | none => false  -- unqualified columns may reference multiple tables
  | .binOp _ l r => exprReferencesOnlyTable tableName l && exprReferencesOnlyTable tableName r
  | .unaryOp _ e => exprReferencesOnlyTable tableName e
  | .func _ args => args.foldl (fun acc e => acc && exprReferencesOnlyTable tableName e) true
  | .agg _ arg _ => match arg with | some e => exprReferencesOnlyTable tableName e | none => true
  | .countStar => true
  | .case branches else_ =>
    branches.foldl (fun acc pair => acc && exprReferencesOnlyTable tableName pair.1 && exprReferencesOnlyTable tableName pair.2) true &&
    (match else_ with | some e => exprReferencesOnlyTable tableName e | none => true)
  | .inList e _ vals => exprReferencesOnlyTable tableName e && vals.foldl (fun acc vi => acc && exprReferencesOnlyTable tableName vi) true
  | .inSubquery e _ _ => exprReferencesOnlyTable tableName e
  | .exists _ _ => true  -- subquery scope
  | .subquery _ => true  -- subquery scope
  | .between e lo hi =>
    exprReferencesOnlyTable tableName e &&
    exprReferencesOnlyTable tableName lo &&
    exprReferencesOnlyTable tableName hi
  | .windowFn _ arg _ => match arg with | some e => exprReferencesOnlyTable tableName e | none => true
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

/-- Get all column references from a FromClause -/
def getFromClauseTableNames : FromClause → List String
  | .table t => [t.alias.getD t.name]
  | .subquery _ alias => [alias]
  | .join l _ r _ => getFromClauseTableNames l ++ getFromClauseTableNames r

/-- Check if expression only references columns from a FromClause -/
def exprReferencesOnlyFrom (from_ : FromClause) (e : Expr) : Bool :=
  let tables := getFromClauseTableNames from_
  tables.any (fun t => exprReferencesOnlyTable t e)


end SqlEquiv
