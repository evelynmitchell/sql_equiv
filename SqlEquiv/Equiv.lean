/-
  SQL Equivalence Definitions and Proofs

  This module defines what it means for two SQL expressions/statements
  to be equivalent, and proves basic equivalence theorems.
-/
import SqlEquiv.Ast
import SqlEquiv.Semantics

namespace SqlEquiv

-- ============================================================================
-- Equivalence Definitions
-- ============================================================================

/-- Two expressions are equivalent if they evaluate to the same value for all rows -/
def ExprEquiv (e1 e2 : Expr) : Prop :=
  ∀ row : Row, evalExpr row e1 = evalExpr row e2

/-- Notation for expression equivalence -/
scoped infix:50 " ≃ₑ " => ExprEquiv

/-- Two SELECT statements are equivalent if they produce the same result for all databases -/
def SelectEquiv (s1 s2 : SelectStmt) : Prop :=
  ∀ db : Database, evalSelect db s1 = evalSelect db s2

/-- Notation for select equivalence -/
scoped infix:50 " ≃ₛ " => SelectEquiv

/-- Two queries are equivalent if they produce the same result for all databases -/
def QueryEquiv (q1 q2 : Query) : Prop :=
  ∀ db : Database, evalQuery db q1 = evalQuery db q2

/-- Notation for query equivalence -/
scoped infix:50 " ≃ᵩ " => QueryEquiv

/-- Two statements are equivalent if they have the same effect on all databases -/
def StmtEquiv (s1 s2 : Stmt) : Prop :=
  ∀ db : Database, evalStmt db s1 = evalStmt db s2

/-- Notation for statement equivalence -/
scoped infix:50 " ≃ " => StmtEquiv

-- ============================================================================
-- Basic Expression Equivalence Theorems
-- ============================================================================

/-- Expression equivalence is reflexive -/
theorem expr_equiv_refl (e : Expr) : e ≃ₑ e := by
  intro row
  rfl

/-- Expression equivalence is symmetric -/
theorem expr_equiv_symm {e1 e2 : Expr} (h : e1 ≃ₑ e2) : e2 ≃ₑ e1 := by
  intro row
  exact (h row).symm

/-- Expression equivalence is transitive -/
theorem expr_equiv_trans {e1 e2 e3 : Expr} (h12 : e1 ≃ₑ e2) (h23 : e2 ≃ₑ e3) : e1 ≃ₑ e3 := by
  intro row
  rw [h12 row, h23 row]

-- ============================================================================
-- SELECT Equivalence Theorems
-- ============================================================================

/-- Select equivalence is reflexive -/
theorem select_equiv_refl (s : SelectStmt) : s ≃ₛ s := by
  intro db
  rfl

/-- Select equivalence is symmetric -/
theorem select_equiv_symm {s1 s2 : SelectStmt} (h : s1 ≃ₛ s2) : s2 ≃ₛ s1 := by
  intro db
  exact (h db).symm

/-- Select equivalence is transitive -/
theorem select_equiv_trans {s1 s2 s3 : SelectStmt}
    (h12 : s1 ≃ₛ s2) (h23 : s2 ≃ₛ s3) : s1 ≃ₛ s3 := by
  intro db
  rw [h12 db, h23 db]

-- ============================================================================
-- Query Equivalence Theorems
-- ============================================================================

/-- Query equivalence is reflexive -/
theorem query_equiv_refl (q : Query) : q ≃ᵩ q := by
  intro db
  rfl

/-- Query equivalence is symmetric -/
theorem query_equiv_symm {q1 q2 : Query} (h : q1 ≃ᵩ q2) : q2 ≃ᵩ q1 := by
  intro db
  exact (h db).symm

/-- Query equivalence is transitive -/
theorem query_equiv_trans {q1 q2 q3 : Query}
    (h12 : q1 ≃ᵩ q2) (h23 : q2 ≃ᵩ q3) : q1 ≃ᵩ q3 := by
  intro db
  rw [h12 db, h23 db]

-- ============================================================================
-- Statement Equivalence Theorems
-- ============================================================================

/-- Statement equivalence is reflexive -/
theorem stmt_equiv_refl (s : Stmt) : s ≃ s := by
  intro db
  rfl

/-- Statement equivalence is symmetric -/
theorem stmt_equiv_symm {s1 s2 : Stmt} (h : s1 ≃ s2) : s2 ≃ s1 := by
  intro db
  exact (h db).symm

/-- Statement equivalence is transitive -/
theorem stmt_equiv_trans {s1 s2 s3 : Stmt} (h12 : s1 ≃ s2) (h23 : s2 ≃ s3) : s1 ≃ s3 := by
  intro db
  rw [h12 db, h23 db]

-- ============================================================================
-- Normalization (for decidable equivalence checking)
-- ============================================================================

/-- Normalize expression to canonical form -/
partial def normalizeExpr : Expr → Expr
  | .binOp .and a b =>
    let na := normalizeExpr a
    let nb := normalizeExpr b
    -- Sort AND operands lexicographically for canonical form
    if toString (repr na) ≤ toString (repr nb) then
      .binOp .and na nb
    else
      .binOp .and nb na
  | .binOp .or a b =>
    let na := normalizeExpr a
    let nb := normalizeExpr b
    if toString (repr na) ≤ toString (repr nb) then
      .binOp .or na nb
    else
      .binOp .or nb na
  | .binOp .add a b =>
    let na := normalizeExpr a
    let nb := normalizeExpr b
    if toString (repr na) ≤ toString (repr nb) then
      .binOp .add na nb
    else
      .binOp .add nb na
  | .binOp .mul a b =>
    let na := normalizeExpr a
    let nb := normalizeExpr b
    if toString (repr na) ≤ toString (repr nb) then
      .binOp .mul na nb
    else
      .binOp .mul nb na
  | .binOp op a b => .binOp op (normalizeExpr a) (normalizeExpr b)
  | .unaryOp .not (.unaryOp .not e) => normalizeExpr e  -- Double negation
  | .unaryOp op e => .unaryOp op (normalizeExpr e)
  | .func name args => .func name (args.map normalizeExpr)
  | .agg fn arg distinct => .agg fn (arg.map normalizeExpr) distinct
  | .case branches else_ =>
    .case (branches.map fun (c, r) => (normalizeExpr c, normalizeExpr r))
          (else_.map normalizeExpr)
  | .inList e neg vals => .inList (normalizeExpr e) neg (vals.map normalizeExpr)
  | .inSubquery e neg sel => .inSubquery (normalizeExpr e) neg sel
  | .exists neg sel => .exists neg sel
  | .subquery sel => .subquery sel
  | .between e lo hi => .between (normalizeExpr e) (normalizeExpr lo) (normalizeExpr hi)
  | e => e

/-- Check syntactic equivalence after normalization -/
def syntacticEquiv (e1 e2 : Expr) : Bool :=
  normalizeExpr e1 == normalizeExpr e2

-- ============================================================================
-- Tactic Support
-- ============================================================================

/-- Rewrite using expression equivalence -/
theorem expr_equiv_subst {e1 e2 : Expr} (h : e1 ≃ₑ e2) (row : Row) :
    evalExpr row e1 = evalExpr row e2 := h row

end SqlEquiv
