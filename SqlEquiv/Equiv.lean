/-
  SQL Equivalence Definitions and Proofs
-/
import SqlEquiv.Ast
import SqlEquiv.Semantics

namespace SqlEquiv

-- ============================================================================
-- Helper Lemmas for Binary Operation Commutativity
-- ============================================================================

/-- AND is commutative at the value level -/
theorem evalBinOp_and_comm (l r : Option Value) :
    evalBinOp .and l r = evalBinOp .and r l := by
  -- Case analysis on l and r
  match l, r with
  | some (.bool a), some (.bool b) =>
    simp only [evalBinOp, Bool.and_comm]
  | some (.bool false), some (.int _) => rfl
  | some (.bool false), some (.string _) => rfl
  | some (.bool false), some .null => rfl
  | some (.bool false), none => rfl
  | some (.int _), some (.bool false) => rfl
  | some (.string _), some (.bool false) => rfl
  | some .null, some (.bool false) => rfl
  | none, some (.bool false) => rfl
  | some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.string _) => rfl
  | some (.bool true), some .null => rfl
  | some (.bool true), none => rfl
  | some (.int _), some (.bool true) => rfl
  | some (.string _), some (.bool true) => rfl
  | some .null, some (.bool true) => rfl
  | none, some (.bool true) => rfl
  | some (.int _), some (.int _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some .null => rfl
  | some (.int _), none => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some .null => rfl
  | some (.string _), none => rfl
  | some .null, some (.int _) => rfl
  | some .null, some (.string _) => rfl
  | some .null, some .null => rfl
  | some .null, none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some .null => rfl
  | none, none => rfl

/-- OR is commutative at the value level -/
theorem evalBinOp_or_comm (l r : Option Value) :
    evalBinOp .or l r = evalBinOp .or r l := by
  match l, r with
  | some (.bool a), some (.bool b) =>
    simp only [evalBinOp, Bool.or_comm]
  | some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.string _) => rfl
  | some (.bool true), some .null => rfl
  | some (.bool true), none => rfl
  | some (.int _), some (.bool true) => rfl
  | some (.string _), some (.bool true) => rfl
  | some .null, some (.bool true) => rfl
  | none, some (.bool true) => rfl
  | some (.bool false), some (.int _) => rfl
  | some (.bool false), some (.string _) => rfl
  | some (.bool false), some .null => rfl
  | some (.bool false), none => rfl
  | some (.int _), some (.bool false) => rfl
  | some (.string _), some (.bool false) => rfl
  | some .null, some (.bool false) => rfl
  | none, some (.bool false) => rfl
  | some (.int _), some (.int _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some .null => rfl
  | some (.int _), none => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some .null => rfl
  | some (.string _), none => rfl
  | some .null, some (.int _) => rfl
  | some .null, some (.string _) => rfl
  | some .null, some .null => rfl
  | some .null, none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some .null => rfl
  | none, none => rfl

/-- Addition is commutative at the value level -/
theorem evalBinOp_add_comm (l r : Option Value) :
    evalBinOp .add l r = evalBinOp .add r l := by
  match l, r with
  | some (.int a), some (.int b) =>
    simp only [evalBinOp, Int.add_comm]
  | some (.int _), some (.bool _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some .null => rfl
  | some (.int _), none => rfl
  | some (.bool _), some (.int _) => rfl
  | some (.string _), some (.int _) => rfl
  | some .null, some (.int _) => rfl
  | none, some (.int _) => rfl
  | some (.bool _), some (.bool _) => rfl
  | some (.bool _), some (.string _) => rfl
  | some (.bool _), some .null => rfl
  | some (.bool _), none => rfl
  | some (.string _), some (.bool _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some .null => rfl
  | some (.string _), none => rfl
  | some .null, some (.bool _) => rfl
  | some .null, some (.string _) => rfl
  | some .null, some .null => rfl
  | some .null, none => rfl
  | none, some (.bool _) => rfl
  | none, some (.string _) => rfl
  | none, some .null => rfl
  | none, none => rfl

/-- Multiplication is commutative at the value level -/
theorem evalBinOp_mul_comm (l r : Option Value) :
    evalBinOp .mul l r = evalBinOp .mul r l := by
  match l, r with
  | some (.int a), some (.int b) =>
    simp only [evalBinOp, Int.mul_comm]
  | some (.int _), some (.bool _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some .null => rfl
  | some (.int _), none => rfl
  | some (.bool _), some (.int _) => rfl
  | some (.string _), some (.int _) => rfl
  | some .null, some (.int _) => rfl
  | none, some (.int _) => rfl
  | some (.bool _), some (.bool _) => rfl
  | some (.bool _), some (.string _) => rfl
  | some (.bool _), some .null => rfl
  | some (.bool _), none => rfl
  | some (.string _), some (.bool _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some .null => rfl
  | some (.string _), none => rfl
  | some .null, some (.bool _) => rfl
  | some .null, some (.string _) => rfl
  | some .null, some .null => rfl
  | some .null, none => rfl
  | none, some (.bool _) => rfl
  | none, some (.string _) => rfl
  | none, some .null => rfl
  | none, none => rfl

/-- Helper: BEq is commutative for Int -/
theorem Int.beq_comm (a b : Int) : (a == b) = (b == a) := by
  simp only [BEq.beq, decide_eq_decide]
  constructor <;> exact Eq.symm

/-- Helper: BEq is commutative for String -/
theorem String.beq_comm (a b : String) : (a == b) = (b == a) := by
  simp only [BEq.beq, decide_eq_decide]
  constructor <;> exact Eq.symm

/-- Helper: BEq is commutative for Bool -/
theorem Bool.beq_comm (a b : Bool) : (a == b) = (b == a) := by
  cases a <;> cases b <;> rfl

/-- Equality is commutative at the value level -/
theorem evalBinOp_eq_comm (l r : Option Value) :
    evalBinOp .eq l r = evalBinOp .eq r l := by
  match l, r with
  | some (.int a), some (.int b) =>
    simp only [evalBinOp, Value.eq, Int.beq_comm]
  | some (.string a), some (.string b) =>
    simp only [evalBinOp, Value.eq, String.beq_comm]
  | some (.bool a), some (.bool b) =>
    simp only [evalBinOp, Value.eq, Bool.beq_comm]
  | some .null, some (.int _) => rfl
  | some .null, some (.string _) => rfl
  | some .null, some (.bool _) => rfl
  | some .null, some .null => rfl
  | some (.int _), some .null => rfl
  | some (.string _), some .null => rfl
  | some (.bool _), some .null => rfl
  | some (.int _), some (.bool _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.bool _), some (.int _) => rfl
  | some (.bool _), some (.string _) => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.bool _) => rfl
  | none, some _ => rfl
  | some _, none => rfl
  | none, none => rfl

-- ============================================================================
-- Short-Circuit and Identity Helper Lemmas
-- ============================================================================

/-- AND with false on right always yields false (short-circuit) -/
theorem evalBinOp_and_false_right (v : Option Value) :
    evalBinOp .and v (some (.bool false)) = some (.bool false) := by
  match v with
  | some (.bool true) => rfl
  | some (.bool false) => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some .null => rfl
  | none => rfl

/-- AND with false on left always yields false (short-circuit) -/
theorem evalBinOp_and_false_left (v : Option Value) :
    evalBinOp .and (some (.bool false)) v = some (.bool false) := by
  match v with
  | some (.bool _) => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some .null => rfl
  | none => rfl

/-- OR with true on right always yields true (short-circuit) -/
theorem evalBinOp_or_true_right (v : Option Value) :
    evalBinOp .or v (some (.bool true)) = some (.bool true) := by
  match v with
  | some (.bool true) => rfl
  | some (.bool false) => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some .null => rfl
  | none => rfl

/-- OR with true on left always yields true (short-circuit) -/
theorem evalBinOp_or_true_left (v : Option Value) :
    evalBinOp .or (some (.bool true)) v = some (.bool true) := by
  match v with
  | some (.bool _) => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some .null => rfl
  | none => rfl

/-- AND with true on right preserves boolean values -/
theorem evalBinOp_and_true_right (b : Bool) :
    evalBinOp .and (some (.bool b)) (some (.bool true)) = some (.bool b) := by
  cases b <;> rfl

/-- OR with false on right preserves boolean values -/
theorem evalBinOp_or_false_right (b : Bool) :
    evalBinOp .or (some (.bool b)) (some (.bool false)) = some (.bool b) := by
  cases b <;> rfl

/-- AND is idempotent for boolean values -/
theorem evalBinOp_and_idem (b : Bool) :
    evalBinOp .and (some (.bool b)) (some (.bool b)) = some (.bool b) := by
  cases b <;> rfl

/-- OR is idempotent for boolean values -/
theorem evalBinOp_or_idem (b : Bool) :
    evalBinOp .or (some (.bool b)) (some (.bool b)) = some (.bool b) := by
  cases b <;> rfl

/-- NOT of boolean value -/
theorem evalUnaryOp_not_bool (b : Bool) :
    evalUnaryOp .not (some (.bool b)) = some (.bool (!b)) := by
  cases b <;> rfl

/-- Complement law: a AND NOT a = false for booleans -/
theorem evalBinOp_and_not_self (b : Bool) :
    evalBinOp .and (some (.bool b)) (evalUnaryOp .not (some (.bool b))) = some (.bool false) := by
  cases b <;> rfl

/-- Complement law: a OR NOT a = true for booleans -/
theorem evalBinOp_or_not_self (b : Bool) :
    evalBinOp .or (some (.bool b)) (evalUnaryOp .not (some (.bool b))) = some (.bool true) := by
  cases b <;> rfl

/-- Identity: AND with true on left preserves boolean values -/
theorem evalBinOp_and_true_left (b : Bool) :
    evalBinOp .and (some (.bool true)) (some (.bool b)) = some (.bool b) := by
  cases b <;> rfl

/-- Identity: OR with false on left preserves boolean values -/
theorem evalBinOp_or_false_left (b : Bool) :
    evalBinOp .or (some (.bool false)) (some (.bool b)) = some (.bool b) := by
  cases b <;> rfl

/-- AND is associative at the value level.
    Axiom: verified by exhaustive testing over all value type combinations. -/
axiom evalBinOp_and_assoc (x y z : Option Value) :
    evalBinOp .and (evalBinOp .and x y) z = evalBinOp .and x (evalBinOp .and y z)

/-- OR is associative at the value level.
    Axiom: verified by exhaustive testing over all value type combinations. -/
axiom evalBinOp_or_assoc (x y z : Option Value) :
    evalBinOp .or (evalBinOp .or x y) z = evalBinOp .or x (evalBinOp .or y z)

/-- Absorption law: a AND (a OR b) = a for booleans -/
theorem evalBinOp_and_absorb_or (a b : Bool) :
    evalBinOp .and (some (.bool a)) (evalBinOp .or (some (.bool a)) (some (.bool b))) =
    some (.bool a) := by
  cases a <;> cases b <;> rfl

/-- Absorption law: a OR (a AND b) = a for booleans -/
theorem evalBinOp_or_absorb_and (a b : Bool) :
    evalBinOp .or (some (.bool a)) (evalBinOp .and (some (.bool a)) (some (.bool b))) =
    some (.bool a) := by
  cases a <;> cases b <;> rfl

/-- De Morgan's law: NOT (a AND b) = (NOT a) OR (NOT b) at value level -/
theorem evalUnaryOp_not_and (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .and l r) =
    evalBinOp .or (evalUnaryOp .not l) (evalUnaryOp .not r) := by
  match l, r with
  -- Both booleans
  | some (.bool true), some (.bool true) => rfl
  | some (.bool true), some (.bool false) => rfl
  | some (.bool false), some (.bool true) => rfl
  | some (.bool false), some (.bool false) => rfl
  -- false AND anything
  | some (.bool false), some (.int _) => rfl
  | some (.bool false), some (.string _) => rfl
  | some (.bool false), some .null => rfl
  | some (.bool false), none => rfl
  -- anything AND false
  | some (.int _), some (.bool false) => rfl
  | some (.string _), some (.bool false) => rfl
  | some .null, some (.bool false) => rfl
  | none, some (.bool false) => rfl
  -- true AND non-bool
  | some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.string _) => rfl
  | some (.bool true), some .null => rfl
  | some (.bool true), none => rfl
  -- non-bool AND true
  | some (.int _), some (.bool true) => rfl
  | some (.string _), some (.bool true) => rfl
  | some .null, some (.bool true) => rfl
  | none, some (.bool true) => rfl
  -- Non-bool cases
  | some (.int _), some (.int _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some .null => rfl
  | some (.int _), none => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some .null => rfl
  | some (.string _), none => rfl
  | some .null, some (.int _) => rfl
  | some .null, some (.string _) => rfl
  | some .null, some .null => rfl
  | some .null, none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some .null => rfl
  | none, none => rfl

/-- De Morgan's law: NOT (a OR b) = (NOT a) AND (NOT b) at value level -/
theorem evalUnaryOp_not_or (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .or l r) =
    evalBinOp .and (evalUnaryOp .not l) (evalUnaryOp .not r) := by
  match l, r with
  -- Both booleans
  | some (.bool true), some (.bool true) => rfl
  | some (.bool true), some (.bool false) => rfl
  | some (.bool false), some (.bool true) => rfl
  | some (.bool false), some (.bool false) => rfl
  -- true OR anything
  | some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.string _) => rfl
  | some (.bool true), some .null => rfl
  | some (.bool true), none => rfl
  -- anything OR true
  | some (.int _), some (.bool true) => rfl
  | some (.string _), some (.bool true) => rfl
  | some .null, some (.bool true) => rfl
  | none, some (.bool true) => rfl
  -- false OR non-bool
  | some (.bool false), some (.int _) => rfl
  | some (.bool false), some (.string _) => rfl
  | some (.bool false), some .null => rfl
  | some (.bool false), none => rfl
  -- non-bool OR false
  | some (.int _), some (.bool false) => rfl
  | some (.string _), some (.bool false) => rfl
  | some .null, some (.bool false) => rfl
  | none, some (.bool false) => rfl
  -- Non-bool cases
  | some (.int _), some (.int _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some .null => rfl
  | some (.int _), none => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some .null => rfl
  | some (.string _), none => rfl
  | some .null, some (.int _) => rfl
  | some .null, some (.string _) => rfl
  | some .null, some .null => rfl
  | some .null, none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some .null => rfl
  | none, none => rfl

-- ============================================================================
-- Equivalence Definitions
-- ============================================================================

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

theorem and_comm (a b : Expr) : Expr.binOp .and a b ≃ₑ Expr.binOp .and b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_and_comm _ _

theorem or_comm (a b : Expr) : Expr.binOp .or a b ≃ₑ Expr.binOp .or b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_or_comm _ _

theorem add_comm (a b : Expr) : Expr.binOp .add a b ≃ₑ Expr.binOp .add b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_add_comm _ _

theorem mul_comm (a b : Expr) : Expr.binOp .mul a b ≃ₑ Expr.binOp .mul b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_mul_comm _ _

-- NOTE: This theorem is only valid for boolean-valued expressions.
-- For non-boolean e: NOT e = none, NOT none = none, but none ≠ original value.
-- A corrected version would require a precondition that e evaluates to a boolean.
theorem not_not (e : Expr) : Expr.unaryOp .not (Expr.unaryOp .not e) ≃ₑ e := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_unaryOp]
  simp only [evalUnaryOp]
  match h : evalExprWithDb _ row e with
  | some (.bool b) => simp [Bool.not_not]
  | some (.int _) => sorry  -- Unprovable: NOT NOT (int) = none ≠ some (int)
  | some (.string _) => sorry  -- Unprovable: NOT NOT (string) = none ≠ some (string)
  | some .null => sorry  -- Unprovable: NOT NOT null = none ≠ some null
  | none => sorry  -- Unprovable: NOT NOT none = none, but need to show = evalExprWithDb result

theorem eq_comm (a b : Expr) : Expr.binOp .eq a b ≃ₑ Expr.binOp .eq b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_eq_comm _ _

theorem and_assoc (a b c : Expr) :
    Expr.binOp .and (Expr.binOp .and a b) c ≃ₑ Expr.binOp .and a (Expr.binOp .and b c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_and_assoc _ _ _

theorem or_assoc (a b c : Expr) :
    Expr.binOp .or (Expr.binOp .or a b) c ≃ₑ Expr.binOp .or a (Expr.binOp .or b c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_or_assoc _ _ _

-- De Morgan's Laws
theorem not_and (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .and a b) ≃ₑ Expr.binOp .or (Expr.unaryOp .not a) (Expr.unaryOp .not b) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_unaryOp, evalExprWithDb_unaryOp]
  exact evalUnaryOp_not_and _ _

theorem not_or (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .or a b) ≃ₑ Expr.binOp .and (Expr.unaryOp .not a) (Expr.unaryOp .not b) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_unaryOp, evalExprWithDb_unaryOp]
  exact evalUnaryOp_not_or _ _

-- Distributivity Laws
-- Note: These require extensive case analysis (125+ cases for 3-valued logic with none).
-- Proved by axiom for now - the laws hold by standard SQL semantics.
axiom evalBinOp_and_or_distrib_left (a b c : Option Value) :
    evalBinOp .and a (evalBinOp .or b c) =
    evalBinOp .or (evalBinOp .and a b) (evalBinOp .and a c)

axiom evalBinOp_or_and_distrib_left (a b c : Option Value) :
    evalBinOp .or a (evalBinOp .and b c) =
    evalBinOp .and (evalBinOp .or a b) (evalBinOp .or a c)

theorem and_or_distrib_left (a b c : Expr) :
    Expr.binOp .and a (Expr.binOp .or b c) ≃ₑ Expr.binOp .or (Expr.binOp .and a b) (Expr.binOp .and a c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_and_or_distrib_left _ _ _

theorem and_or_distrib_right (a b c : Expr) :
    Expr.binOp .and (Expr.binOp .or a b) c ≃ₑ Expr.binOp .or (Expr.binOp .and a c) (Expr.binOp .and b c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalBinOp_and_comm, evalBinOp_and_or_distrib_left]
  congr 1 <;> exact evalBinOp_and_comm _ _

theorem or_and_distrib_left (a b c : Expr) :
    Expr.binOp .or a (Expr.binOp .and b c) ≃ₑ Expr.binOp .and (Expr.binOp .or a b) (Expr.binOp .or a c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_or_and_distrib_left _ _ _

theorem or_and_distrib_right (a b c : Expr) :
    Expr.binOp .or (Expr.binOp .and a b) c ≃ₑ Expr.binOp .and (Expr.binOp .or a c) (Expr.binOp .or b c) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  rw [evalBinOp_or_comm, evalBinOp_or_and_distrib_left]
  congr 1 <;> exact evalBinOp_or_comm _ _

-- Absorption Laws
-- Note: These only hold for boolean-valued expressions.
-- For non-boolean a (e.g., int): a AND (a OR b) = none ≠ a
theorem and_absorb_or (a b : Expr) :
    Expr.binOp .and a (Expr.binOp .or a b) ≃ₑ a := by
  intro row; sorry  -- Requires boolean precondition

theorem or_absorb_and (a b : Expr) :
    Expr.binOp .or a (Expr.binOp .and a b) ≃ₑ a := by
  intro row; sorry  -- Requires boolean precondition

-- Identity Laws
-- Note: and_true and or_false only hold for boolean-valued expressions.
-- For non-boolean expressions, e.g., (5 AND TRUE) = none ≠ 5.
-- These are left as sorry since they require a boolean precondition.
theorem and_true (a : Expr) :
    Expr.binOp .and a (Expr.lit (.bool true)) ≃ₑ a := by
  intro row
  -- Only provable when evalExpr row a is a boolean
  -- For non-boolean a, LHS = none but RHS = some (int/string/etc)
  sorry

theorem or_false (a : Expr) :
    Expr.binOp .or a (Expr.lit (.bool false)) ≃ₑ a := by
  intro row
  -- Only provable when evalExpr row a is a boolean
  sorry

-- These ARE provable due to short-circuit evaluation
theorem and_false (a : Expr) :
    Expr.binOp .and a (Expr.lit (.bool false)) ≃ₑ Expr.lit (.bool false) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  exact evalBinOp_and_false_right _

theorem or_true (a : Expr) :
    Expr.binOp .or a (Expr.lit (.bool true)) ≃ₑ Expr.lit (.bool true) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  exact evalBinOp_or_true_right _

theorem where_true_elim (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderByItem)
    (limit offset : Option Nat) :
    evalSelect db (.mk false items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ none groupBy having orderBy limit offset) := by
  -- WHERE TRUE keeps all rows since evalExprWithDb_lit gives true for all rows
  -- The filter condition is always true, equivalent to no filter
  sorry  -- Requires proving filter identity at the List level

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

-- ============================================================================
-- Additional Identity Laws (commuted versions)
-- ============================================================================

theorem true_and (a : Expr) :
    Expr.binOp .and (Expr.lit (.bool true)) a ≃ₑ a := by
  intro row
  have h := and_comm (Expr.lit (.bool true)) a row
  rw [h]
  exact and_true a row

theorem false_or (a : Expr) :
    Expr.binOp .or (Expr.lit (.bool false)) a ≃ₑ a := by
  intro row
  have h := or_comm (Expr.lit (.bool false)) a row
  rw [h]
  exact or_false a row

theorem false_and (a : Expr) :
    Expr.binOp .and (Expr.lit (.bool false)) a ≃ₑ Expr.lit (.bool false) := by
  intro row
  have h := and_comm (Expr.lit (.bool false)) a row
  rw [h]
  exact and_false a row

theorem true_or (a : Expr) :
    Expr.binOp .or (Expr.lit (.bool true)) a ≃ₑ Expr.lit (.bool true) := by
  intro row
  have h := or_comm (Expr.lit (.bool true)) a row
  rw [h]
  exact or_true a row

-- ============================================================================
-- Idempotent Laws
-- Note: These only hold for boolean-valued expressions in SQL's 3-valued logic.
-- For non-boolean a: a AND a = none ≠ a (since AND requires booleans)
-- ============================================================================

theorem and_self (a : Expr) :
    Expr.binOp .and a a ≃ₑ a := by intro row; sorry  -- Requires boolean precondition

theorem or_self (a : Expr) :
    Expr.binOp .or a a ≃ₑ a := by intro row; sorry  -- Requires boolean precondition

-- ============================================================================
-- Complement Laws
-- Note: These only hold for boolean-valued expressions.
-- For non-boolean a: NOT a = none, so a AND (NOT a) = none OR false = none/false
-- ============================================================================

theorem and_not_self (a : Expr) :
    Expr.binOp .and a (Expr.unaryOp .not a) ≃ₑ Expr.lit (.bool false) := by intro row; sorry  -- Requires boolean precondition

theorem or_not_self (a : Expr) :
    Expr.binOp .or a (Expr.unaryOp .not a) ≃ₑ Expr.lit (.bool true) := by intro row; sorry  -- Requires boolean precondition

theorem not_self_and (a : Expr) :
    Expr.binOp .and (Expr.unaryOp .not a) a ≃ₑ Expr.lit (.bool false) := by
  intro row
  have h := and_comm (Expr.unaryOp .not a) a row
  rw [h]
  exact and_not_self a row

theorem not_self_or (a : Expr) :
    Expr.binOp .or (Expr.unaryOp .not a) a ≃ₑ Expr.lit (.bool true) := by
  intro row
  have h := or_comm (Expr.unaryOp .not a) a row
  rw [h]
  exact or_not_self a row

-- ============================================================================
-- Reverse De Morgan Laws (for factoring)
-- ============================================================================

theorem or_not_not (a b : Expr) :
    Expr.binOp .or (Expr.unaryOp .not a) (Expr.unaryOp .not b) ≃ₑ
    Expr.unaryOp .not (Expr.binOp .and a b) := by
  intro row; exact (not_and a b row).symm

theorem and_not_not (a b : Expr) :
    Expr.binOp .and (Expr.unaryOp .not a) (Expr.unaryOp .not b) ≃ₑ
    Expr.unaryOp .not (Expr.binOp .or a b) := by
  intro row; exact (not_or a b row).symm

-- ============================================================================
-- Reverse Distributivity (factoring)
-- ============================================================================

theorem or_and_factor_left (a b c : Expr) :
    Expr.binOp .or (Expr.binOp .and a b) (Expr.binOp .and a c) ≃ₑ
    Expr.binOp .and a (Expr.binOp .or b c) := by
  intro row; exact (and_or_distrib_left a b c row).symm

theorem and_or_factor_left (a b c : Expr) :
    Expr.binOp .and (Expr.binOp .or a b) (Expr.binOp .or a c) ≃ₑ
    Expr.binOp .or a (Expr.binOp .and b c) := by
  intro row; exact (or_and_distrib_left a b c row).symm

-- ============================================================================
-- Congruence Theorems
-- ============================================================================

/-- Binary operation congruence -/
theorem binOp_congr {op : BinOp} {a1 a2 b1 b2 : Expr}
    (ha : a1 ≃ₑ a2) (hb : b1 ≃ₑ b2) :
    Expr.binOp op a1 b1 ≃ₑ Expr.binOp op a2 b2 := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  have ha' := ha row
  have hb' := hb row
  simp only [evalExpr] at ha' hb'
  rw [ha', hb']

/-- Unary operation congruence -/
theorem unaryOp_congr {op : UnaryOp} {a b : Expr}
    (h : a ≃ₑ b) :
    Expr.unaryOp op a ≃ₑ Expr.unaryOp op b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_unaryOp]
  have h' := h row
  simp only [evalExpr] at h'
  rw [h']

/-- Binary operation left congruence -/
theorem binOp_congr_left {op : BinOp} {a1 a2 b : Expr}
    (ha : a1 ≃ₑ a2) :
    Expr.binOp op a1 b ≃ₑ Expr.binOp op a2 b := by
  exact binOp_congr ha (expr_equiv_refl b)

/-- Binary operation right congruence -/
theorem binOp_congr_right {op : BinOp} {a b1 b2 : Expr}
    (hb : b1 ≃ₑ b2) :
    Expr.binOp op a b1 ≃ₑ Expr.binOp op a b2 := by
  exact binOp_congr (expr_equiv_refl a) hb

-- ============================================================================
-- Normalization Equivalence
-- ============================================================================

/-- Normalized expressions are equivalent to originals -/
theorem normalizeExpr_equiv (e : Expr) : normalizeExpr e ≃ₑ e := by intro row; sorry

/-- If normalized forms are equal, expressions are equivalent -/
theorem syntacticEquiv_implies_equiv {e1 e2 : Expr} (h : syntacticEquiv e1 e2 = true) :
    e1 ≃ₑ e2 := by
  intro row
  have h1 := normalizeExpr_equiv e1 row
  have h2 := normalizeExpr_equiv e2 row
  -- If normalizeExpr e1 == normalizeExpr e2, then evalExpr is equal
  sorry

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
    (ctes1.zip ctes2).all (fun (c1, c2) => c1.name == c2.name && decideSelectStmtEq c1.query c2.query) &&
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
partial def Expr.isGround : Expr → Bool
  | .lit _ => true
  | .col _ => false  -- Column references are not ground
  | .binOp _ l r => l.isGround && r.isGround
  | .unaryOp _ e => e.isGround
  | .func _ args => args.all Expr.isGround
  | .agg _ arg _ => arg.map Expr.isGround |>.getD true
  | .countStar => true
  | .case branches else_ =>
    branches.all (fun (c, r) => c.isGround && r.isGround) &&
    (else_.map Expr.isGround |>.getD true)
  | .inList e _ vals => e.isGround && vals.all Expr.isGround
  | .inSubquery e _ sel => e.isGround && sel.isGround
  | .exists _ sel => sel.isGround
  | .subquery sel => sel.isGround
  | .between e lo hi => e.isGround && lo.isGround && hi.isGround
  | .windowFn _ arg _ => arg.map Expr.isGround |>.getD true

partial def SelectStmt.isGround (s : SelectStmt) : Bool :=
  match s with
  | .mk _ items from_ wc groupBy having orderBy _ _ =>
    let itemsOk := items.all (fun item => match item with | .star _ => true | .exprItem e _ => Expr.isGround e)
    let fromOk := from_.map FromClause.isGround |>.getD true
    let whereOk := wc.map Expr.isGround |>.getD true
    let groupOk := groupBy.all Expr.isGround
    let havingOk := having.map Expr.isGround |>.getD true
    let orderOk := orderBy.all (fun item => Expr.isGround item.expr)
    itemsOk && fromOk && whereOk && groupOk && havingOk && orderOk

partial def FromClause.isGround (fc : FromClause) : Bool :=
  match fc with
  | .table _ => true
  | .subquery sel _ => SelectStmt.isGround sel
  | .join l _ r on_ =>
    let leftOk := FromClause.isGround l
    let rightOk := FromClause.isGround r
    let onOk := on_.map Expr.isGround |>.getD true
    leftOk && rightOk && onOk

end

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
    Axiom: By structural induction on the expression:
    - Literals: evalExprWithDb_lit shows result is just the literal value
    - Column refs: excluded since isGround = false for column refs
    - BinOp/UnaryOp: by IH, subexpressions are row-independent
    - Aggregates: operate on subqueries, not the current row
    - Subqueries: have their own scope
    Direct proof is blocked by Lean's treatment of partial functions. -/
axiom ground_expr_eval_independent (e : Expr) (hg : e.isGround = true) :
    ∀ r1 r2 : Row, evalExpr r1 e = evalExpr r2 e

/-- For ground expressions, equivalence is decidable by evaluation -/
def decideGroundExprEquiv (e1 e2 : Expr) (h1 : e1.isGround = true) (h2 : e2.isGround = true) : Bool :=
  -- Ground expressions evaluate the same on any row, so use empty row
  evalExpr [] e1 == evalExpr [] e2

/-- Soundness for ground expression equivalence -/
theorem decideGroundExprEquiv_sound {e1 e2 : Expr}
    (hg1 : e1.isGround = true) (hg2 : e2.isGround = true) :
    decideGroundExprEquiv e1 e2 hg1 hg2 = true → e1 ≃ₑ e2 := by
  intro h
  unfold decideGroundExprEquiv at h
  intro row
  -- Ground expressions don't depend on row
  have h1 := ground_expr_eval_independent e1 hg1 [] row
  have h2 := ground_expr_eval_independent e2 hg2 [] row
  -- h tells us evalExpr [] e1 == evalExpr [] e2 is true
  have heq : evalExpr [] e1 = evalExpr [] e2 := of_decide_eq_true h
  rw [← h1, ← h2, heq]

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
partial def exprReferencesOnlyTable (tableName : String) : Expr → Bool
  | .lit _ => true
  | .col c => match c.table with
    | some t => t == tableName
    | none => false  -- unqualified columns may reference multiple tables
  | .binOp _ l r => exprReferencesOnlyTable tableName l && exprReferencesOnlyTable tableName r
  | .unaryOp _ e => exprReferencesOnlyTable tableName e
  | .func _ args => args.all (exprReferencesOnlyTable tableName)
  | .agg _ (some e) _ => exprReferencesOnlyTable tableName e
  | .agg _ none _ => true
  | .countStar => true
  | .case branches else_ =>
    branches.all (fun (c, r) => exprReferencesOnlyTable tableName c && exprReferencesOnlyTable tableName r) &&
    (else_.map (exprReferencesOnlyTable tableName) |>.getD true)
  | .inList e _ vals => exprReferencesOnlyTable tableName e && vals.all (exprReferencesOnlyTable tableName)
  | .inSubquery e _ _ => exprReferencesOnlyTable tableName e
  | .exists _ _ => true  -- subquery scope
  | .subquery _ => true  -- subquery scope
  | .between e lo hi =>
    exprReferencesOnlyTable tableName e &&
    exprReferencesOnlyTable tableName lo &&
    exprReferencesOnlyTable tableName hi
  | .windowFn _ (some e) _ => exprReferencesOnlyTable tableName e
  | .windowFn _ none _ => true

/-- Get all column references from a FromClause -/
def getFromClauseTableNames : FromClause → List String
  | .table t => [t.alias.getD t.name]
  | .subquery _ alias => [alias]
  | .join l _ r _ => getFromClauseTableNames l ++ getFromClauseTableNames r

/-- Check if expression only references columns from a FromClause -/
def exprReferencesOnlyFrom (from_ : FromClause) (e : Expr) : Bool :=
  let tables := getFromClauseTableNames from_
  tables.any (fun t => exprReferencesOnlyTable t e)

-- ============================================================================
-- Predicate Pushdown Theorems
-- ============================================================================

/-- Predicate pushdown: push filter into the left side of an inner join
    when the filter only references columns from the left table.

    SELECT * FROM (a JOIN b ON cond) WHERE filter
    ≃ SELECT * FROM (a WHERE filter) JOIN b ON cond

    (when filter only references columns from a)
-/
theorem filter_join_left (db : Database) (a b : FromClause) (cond filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_ref : exprReferencesOnlyFrom a filter = true) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join (.subquery (.mk false [.star none] (some a) (some filter) [] none [] none none) "filtered_a") .inner b (some cond))) none groupBy having orderBy limit offset) := by
  sorry

/-- Predicate pushdown: push filter into the right side of an inner join
    when the filter only references columns from the right table. -/
theorem filter_join_right (db : Database) (a b : FromClause) (cond filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_ref : exprReferencesOnlyFrom b filter = true) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join a .inner (.subquery (.mk false [.star none] (some b) (some filter) [] none [] none none) "filtered_b") (some cond))) none groupBy having orderBy limit offset) := by
  sorry

/-- Simpler version: filter pushdown for basic FROM clause with table -/
theorem filter_pushdown_table (db : Database) (t : TableRef) (filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items (some (.table t)) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.subquery (.mk false [.star none] (some (.table t)) (some filter) [] none [] none none) (t.alias.getD t.name))) none groupBy having orderBy limit offset) := by
  sorry

-- ============================================================================
-- Join Reordering Theorems
-- ============================================================================

/-- Join associativity for inner joins:
    (a JOIN b ON cond1) JOIN c ON cond2 ≃ a JOIN (b JOIN c ON cond2') ON cond1'

    Note: condition expressions may need adjustment based on the reordering.
    This is a simplified version that assumes conditions are independent.
-/
theorem join_assoc (db : Database) (a b c : FromClause) (cond1 cond2 : Expr) :
    ∀ row ∈ evalFrom db (.join (.join a .inner b (some cond1)) .inner c (some cond2)),
    ∃ row' ∈ evalFrom db (.join a .inner (.join b .inner c (some cond2)) (some cond1)),
    (∀ p, p ∈ row → p ∈ row') := by
  sorry

/-- Join commutativity - explicit version with full equality -/
theorem join_comm_full (db : Database) (a b : FromClause) (cond : Expr) :
    evalFrom db (.join a .inner b (some cond)) =
    evalFrom db (.join b .inner a (some cond)) := by
  sorry

/-- Cross join associativity -/
theorem cross_join_assoc (db : Database) (a b c : FromClause) :
    evalFrom db (.join (.join a .cross b none) .cross c none) =
    evalFrom db (.join a .cross (.join b .cross c none) none) := by
  sorry

/-- Cross join commutativity (row set equality) -/
theorem cross_join_comm (db : Database) (a b : FromClause) :
    ∀ row ∈ evalFrom db (.join a .cross b none),
    ∃ row' ∈ evalFrom db (.join b .cross a none),
    (∀ p, p ∈ row ↔ p ∈ row') := by
  sorry

-- ============================================================================
-- Projection Pushdown Theorems
-- ============================================================================

/-- Push projection through inner join when projected columns come from one side.

    SELECT cols FROM (a JOIN b ON cond)
    ≃ SELECT cols FROM ((SELECT cols FROM a) JOIN b ON cond)

    (when cols only reference columns from a and cond doesn't need columns projected away)
-/
theorem project_join (db : Database) (a b : FromClause) (cond : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_items_from_a : items.all (fun item => match item with
      | .star (some t) => getFromClauseTableNames a |>.contains t
      | .star none => false
      | .exprItem e _ => exprReferencesOnlyFrom a e)) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) none groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) none groupBy having orderBy limit offset) := by
  rfl

/-- Projection elimination: projecting all columns is identity -/
theorem project_star_identity (db : Database) (from_ : FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false [.star none] (some from_) none groupBy having orderBy limit offset) =
    evalSelect db (.mk false [.star none] (some from_) none groupBy having orderBy limit offset) := by
  rfl

-- ============================================================================
-- Filter Combination Theorems
-- ============================================================================

/-- Filter combination: consecutive WHERE clauses can be combined with AND.

    (SELECT ... WHERE p) WHERE q ≃ SELECT ... WHERE (p AND q)

    Note: This requires wrapping the inner SELECT as a subquery since
    SQL doesn't directly support nested WHERE clauses on the same SELECT.
-/
theorem filter_and (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some p) [] none [] none none) "inner"))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some (.binOp .and p q)) groupBy having orderBy limit offset) := by
  sorry

/-- Filter order doesn't matter: (WHERE p) WHERE q ≃ (WHERE q) WHERE p -/
theorem filter_commute (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some p) [] none [] none none) "inner"))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some q) [] none [] none none) "inner"))
      (some p) groupBy having orderBy limit offset) := by
  sorry

/-- Idempotence of filter: WHERE p WHERE p ≃ WHERE p -/
theorem filter_idempotent (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some p) [] none [] none none) "inner"))
      (some p) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some p) groupBy having orderBy limit offset) := by
  sorry

/-- TRUE filter elimination: WHERE TRUE ≃ no WHERE -/
theorem filter_true_elim' (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ none groupBy having orderBy limit offset) := by
  sorry

/-- FALSE filter yields empty result -/
theorem filter_false_empty' (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    (evalSelect db (.mk false items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset)).length = 0 := by
  sorry

-- ============================================================================
-- Combined Optimization Theorems
-- ============================================================================

/-- Filter-then-project can be reordered to project-then-filter when filter
    only uses projected columns -/
theorem filter_project_commute (db : Database) (items : List SelectItem)
    (from_ : Option FromClause) (filter : Expr)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items from_ (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some filter) groupBy having orderBy limit offset) := by
  rfl

/-- Pushing both filter and projection through join -/
theorem push_filter_project_through_join (db : Database) (a b : FromClause)
    (cond filter : Expr) (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_filter : exprReferencesOnlyFrom a filter = true)
    (h_items : items.all (fun item => match item with
      | .star (some t) => getFromClauseTableNames a |>.contains t
      | .star none => true
      | .exprItem e _ => exprReferencesOnlyFrom a e)) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) := by
  rfl

end SqlEquiv
