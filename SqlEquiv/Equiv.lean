/-
  SQL Equivalence Definitions and Proofs
-/
import SqlEquiv.Ast
import SqlEquiv.Semantics

namespace SqlEquiv

def ExprEquiv (e1 e2 : Expr) : Prop :=
  ∀ row : Row, evalExpr row e1 = evalExpr row e2
scoped infix:50 " ≃ₑ " => ExprEquiv

def SelectEquiv (s1 s2 : SelectStmt) : Prop :=
  ∀ db : Database, evalSelect db s1 = evalSelect db s2
scoped infix:50 " ≃ₛ " => SelectEquiv

def QueryEquiv (q1 q2 : Query) : Prop :=
  ∀ db : Database, evalQuery db q1 = evalQuery db q2
scoped infix:50 " ≃ᵩ " => QueryEquiv

def StmtEquiv (s1 s2 : Stmt) : Prop :=
  ∀ db : Database, evalStmt db s1 = evalStmt db s2
scoped infix:50 " ≃ " => StmtEquiv

theorem expr_equiv_refl (e : Expr) : e ≃ₑ e := by intro row; rfl
theorem expr_equiv_symm {e1 e2 : Expr} (h : e1 ≃ₑ e2) : e2 ≃ₑ e1 := by intro row; exact (h row).symm
theorem expr_equiv_trans {e1 e2 e3 : Expr} (h12 : e1 ≃ₑ e2) (h23 : e2 ≃ₑ e3) : e1 ≃ₑ e3 := by intro row; rw [h12 row, h23 row]

theorem select_equiv_refl (s : SelectStmt) : s ≃ₛ s := by intro db; rfl
theorem select_equiv_symm {s1 s2 : SelectStmt} (h : s1 ≃ₛ s2) : s2 ≃ₛ s1 := by intro db; exact (h db).symm
theorem select_equiv_trans {s1 s2 s3 : SelectStmt} (h12 : s1 ≃ₛ s2) (h23 : s2 ≃ₛ s3) : s1 ≃ₛ s3 := by intro db; rw [h12 db, h23 db]

theorem query_equiv_refl (q : Query) : q ≃ᵩ q := by intro db; rfl
theorem query_equiv_symm {q1 q2 : Query} (h : q1 ≃ᵩ q2) : q2 ≃ᵩ q1 := by intro db; exact (h db).symm
theorem query_equiv_trans {q1 q2 q3 : Query} (h12 : q1 ≃ᵩ q2) (h23 : q2 ≃ᵩ q3) : q1 ≃ᵩ q3 := by intro db; rw [h12 db, h23 db]

theorem stmt_equiv_refl (s : Stmt) : s ≃ s := by intro db; rfl
theorem stmt_equiv_symm {s1 s2 : Stmt} (h : s1 ≃ s2) : s2 ≃ s1 := by intro db; exact (h db).symm
theorem stmt_equiv_trans {s1 s2 s3 : Stmt} (h12 : s1 ≃ s2) (h23 : s2 ≃ s3) : s1 ≃ s3 := by intro db; rw [h12 db, h23 db]

theorem and_comm (a b : Expr) : Expr.binOp .and a b ≃ₑ Expr.binOp .and b a := by intro row; sorry
theorem or_comm (a b : Expr) : Expr.binOp .or a b ≃ₑ Expr.binOp .or b a := by intro row; sorry
theorem add_comm (a b : Expr) : Expr.binOp .add a b ≃ₑ Expr.binOp .add b a := by intro row; sorry
theorem mul_comm (a b : Expr) : Expr.binOp .mul a b ≃ₑ Expr.binOp .mul b a := by intro row; sorry
theorem not_not (e : Expr) : Expr.unaryOp .not (Expr.unaryOp .not e) ≃ₑ e := by intro row; sorry
theorem eq_comm (a b : Expr) : Expr.binOp .eq a b ≃ₑ Expr.binOp .eq b a := by intro row; sorry

theorem and_assoc (a b c : Expr) :
    Expr.binOp .and (Expr.binOp .and a b) c ≃ₑ Expr.binOp .and a (Expr.binOp .and b c) := by intro row; sorry

theorem or_assoc (a b c : Expr) :
    Expr.binOp .or (Expr.binOp .or a b) c ≃ₑ Expr.binOp .or a (Expr.binOp .or b c) := by intro row; sorry

theorem where_true_elim (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderByItem)
    (limit offset : Option Nat) :
    evalSelect db (.mk false items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ none groupBy having orderBy limit offset) := by sorry

theorem where_false_empty (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderByItem)
    (limit offset : Option Nat) :
    (evalSelect db (.mk false items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset)).length = 0 ∨
    from_.isNone := by cases from_ with | none => right; rfl | some f => left; sorry

theorem join_comm (db : Database) (a b : FromClause) (cond : Expr) :
    ∀ row ∈ evalFrom db (.join a .inner b (some cond)),
    ∃ row2 ∈ evalFrom db (.join b .inner a (some cond)),
    (∀ p, p ∈ row ↔ p ∈ row2) := by sorry

partial def normalizeExpr : Expr → Expr
  | .binOp .and a b => let na := normalizeExpr a; let nb := normalizeExpr b; if toString (repr na) ≤ toString (repr nb) then .binOp .and na nb else .binOp .and nb na
  | .binOp .or a b => let na := normalizeExpr a; let nb := normalizeExpr b; if toString (repr na) ≤ toString (repr nb) then .binOp .or na nb else .binOp .or nb na
  | .binOp .add a b => let na := normalizeExpr a; let nb := normalizeExpr b; if toString (repr na) ≤ toString (repr nb) then .binOp .add na nb else .binOp .add nb na
  | .binOp .mul a b => let na := normalizeExpr a; let nb := normalizeExpr b; if toString (repr na) ≤ toString (repr nb) then .binOp .mul na nb else .binOp .mul nb na
  | .binOp op a b => .binOp op (normalizeExpr a) (normalizeExpr b)
  | .unaryOp .not (.unaryOp .not e) => normalizeExpr e
  | .unaryOp op e => .unaryOp op (normalizeExpr e)
  | .func name args => .func name (args.map normalizeExpr)
  | .agg fn arg distinct => .agg fn (arg.map normalizeExpr) distinct
  | .case branches else_ => .case (branches.map fun (c, r) => (normalizeExpr c, normalizeExpr r)) (else_.map normalizeExpr)
  | .inList e neg vals => .inList (normalizeExpr e) neg (vals.map normalizeExpr)
  | .inSubquery e neg sel => .inSubquery (normalizeExpr e) neg sel
  | .exists neg sel => .exists neg sel
  | .subquery sel => .subquery sel
  | .between e lo hi => .between (normalizeExpr e) (normalizeExpr lo) (normalizeExpr hi)
  | e => e

def syntacticEquiv (e1 e2 : Expr) : Bool := normalizeExpr e1 == normalizeExpr e2

theorem expr_equiv_subst {e1 e2 : Expr} (h : e1 ≃ₑ e2) (row : Row) : evalExpr row e1 = evalExpr row e2 := h row

end SqlEquiv
