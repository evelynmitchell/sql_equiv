/-
  SQL Equivalence - Value-Level Helper Lemmas
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
  | some (.bool false), some (.null _) => rfl
  | some (.bool false), none => rfl
  | some (.int _), some (.bool false) => rfl
  | some (.string _), some (.bool false) => rfl
  | some (.null _), some (.bool false) => rfl
  | none, some (.bool false) => rfl
  | some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.string _) => rfl
  | some (.bool true), some (.null _) => rfl
  | some (.bool true), none => rfl
  | some (.int _), some (.bool true) => rfl
  | some (.string _), some (.bool true) => rfl
  | some (.null _), some (.bool true) => rfl
  | none, some (.bool true) => rfl
  | some (.int _), some (.int _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.string _), none => rfl
  | some (.null _), some (.int _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.null _), none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.null _) => rfl
  | none, none => rfl

/-- OR is commutative at the value level -/
theorem evalBinOp_or_comm (l r : Option Value) :
    evalBinOp .or l r = evalBinOp .or r l := by
  match l, r with
  | some (.bool a), some (.bool b) =>
    simp only [evalBinOp, Bool.or_comm]
  | some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.string _) => rfl
  | some (.bool true), some (.null _) => rfl
  | some (.bool true), none => rfl
  | some (.int _), some (.bool true) => rfl
  | some (.string _), some (.bool true) => rfl
  | some (.null _), some (.bool true) => rfl
  | none, some (.bool true) => rfl
  | some (.bool false), some (.int _) => rfl
  | some (.bool false), some (.string _) => rfl
  | some (.bool false), some (.null _) => rfl
  | some (.bool false), none => rfl
  | some (.int _), some (.bool false) => rfl
  | some (.string _), some (.bool false) => rfl
  | some (.null _), some (.bool false) => rfl
  | none, some (.bool false) => rfl
  | some (.int _), some (.int _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.string _), none => rfl
  | some (.null _), some (.int _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.null _), none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.null _) => rfl
  | none, none => rfl

/-- Addition is commutative at the value level -/
theorem evalBinOp_add_comm (l r : Option Value) :
    evalBinOp .add l r = evalBinOp .add r l := by
  match l, r with
  | some (.int a), some (.int b) =>
    simp only [evalBinOp, Int.add_comm]
  | some (.int _), some (.bool _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.bool _), some (.int _) => rfl
  | some (.string _), some (.int _) => rfl
  | some (.null _), some (.int _) => rfl
  | none, some (.int _) => rfl
  | some (.bool _), some (.bool _) => rfl
  | some (.bool _), some (.string _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.bool _), none => rfl
  | some (.string _), some (.bool _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.string _), none => rfl
  | some (.null _), some (.bool _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.null _), none => rfl
  | none, some (.bool _) => rfl
  | none, some (.string _) => rfl
  | none, some (.null _) => rfl
  | none, none => rfl

/-- Multiplication is commutative at the value level -/
theorem evalBinOp_mul_comm (l r : Option Value) :
    evalBinOp .mul l r = evalBinOp .mul r l := by
  match l, r with
  | some (.int a), some (.int b) =>
    simp only [evalBinOp, Int.mul_comm]
  | some (.int _), some (.bool _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.bool _), some (.int _) => rfl
  | some (.string _), some (.int _) => rfl
  | some (.null _), some (.int _) => rfl
  | none, some (.int _) => rfl
  | some (.bool _), some (.bool _) => rfl
  | some (.bool _), some (.string _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.bool _), none => rfl
  | some (.string _), some (.bool _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.string _), none => rfl
  | some (.null _), some (.bool _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.null _), none => rfl
  | none, some (.bool _) => rfl
  | none, some (.string _) => rfl
  | none, some (.null _) => rfl
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
  | some (.null _), some (.int _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.bool _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int _), some (.bool _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.bool _), some (.int _) => rfl
  | some (.bool _), some (.string _) => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.bool _) => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
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
  | some (.null _) => rfl
  | none => rfl

/-- AND with false on left always yields false (short-circuit) -/
theorem evalBinOp_and_false_left (v : Option Value) :
    evalBinOp .and (some (.bool false)) v = some (.bool false) := by
  match v with
  | some (.bool _) => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.null _) => rfl
  | none => rfl

/-- OR with true on right always yields true (short-circuit) -/
theorem evalBinOp_or_true_right (v : Option Value) :
    evalBinOp .or v (some (.bool true)) = some (.bool true) := by
  match v with
  | some (.bool true) => rfl
  | some (.bool false) => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.null _) => rfl
  | none => rfl

/-- OR with true on left always yields true (short-circuit) -/
theorem evalBinOp_or_true_left (v : Option Value) :
    evalBinOp .or (some (.bool true)) v = some (.bool true) := by
  match v with
  | some (.bool _) => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.null _) => rfl
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

/-- AND is associative at the value level -/
theorem evalBinOp_and_assoc (x y z : Option Value) :
    evalBinOp .and (evalBinOp .and x y) z = evalBinOp .and x (evalBinOp .and y z) := by
  match x, y, z with
  | some (.bool true), some (.bool true), some (.bool true) => rfl
  | some (.bool true), some (.bool true), some (.bool false) => rfl
  | some (.bool true), some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.bool true), some (.string _) => rfl
  | some (.bool true), some (.bool true), some (.null _) => rfl
  | some (.bool true), some (.bool true), none => rfl
  | some (.bool true), some (.bool false), some (.bool true) => rfl
  | some (.bool true), some (.bool false), some (.bool false) => rfl
  | some (.bool true), some (.bool false), some (.int _) => rfl
  | some (.bool true), some (.bool false), some (.string _) => rfl
  | some (.bool true), some (.bool false), some (.null _) => rfl
  | some (.bool true), some (.bool false), none => rfl
  | some (.bool true), some (.int _), some (.bool true) => rfl
  | some (.bool true), some (.int _), some (.bool false) => rfl
  | some (.bool true), some (.int _), some (.int _) => rfl
  | some (.bool true), some (.int _), some (.string _) => rfl
  | some (.bool true), some (.int _), some (.null _) => rfl
  | some (.bool true), some (.int _), none => rfl
  | some (.bool true), some (.string _), some (.bool true) => rfl
  | some (.bool true), some (.string _), some (.bool false) => rfl
  | some (.bool true), some (.string _), some (.int _) => rfl
  | some (.bool true), some (.string _), some (.string _) => rfl
  | some (.bool true), some (.string _), some (.null _) => rfl
  | some (.bool true), some (.string _), none => rfl
  | some (.bool true), some (.null _), some (.bool true) => rfl
  | some (.bool true), some (.null _), some (.bool false) => rfl
  | some (.bool true), some (.null _), some (.int _) => rfl
  | some (.bool true), some (.null _), some (.string _) => rfl
  | some (.bool true), some (.null _), some (.null _) => rfl
  | some (.bool true), some (.null _), none => rfl
  | some (.bool true), none, some (.bool true) => rfl
  | some (.bool true), none, some (.bool false) => rfl
  | some (.bool true), none, some (.int _) => rfl
  | some (.bool true), none, some (.string _) => rfl
  | some (.bool true), none, some (.null _) => rfl
  | some (.bool true), none, none => rfl
  | some (.bool false), some (.bool true), some (.bool true) => rfl
  | some (.bool false), some (.bool true), some (.bool false) => rfl
  | some (.bool false), some (.bool true), some (.int _) => rfl
  | some (.bool false), some (.bool true), some (.string _) => rfl
  | some (.bool false), some (.bool true), some (.null _) => rfl
  | some (.bool false), some (.bool true), none => rfl
  | some (.bool false), some (.bool false), some (.bool true) => rfl
  | some (.bool false), some (.bool false), some (.bool false) => rfl
  | some (.bool false), some (.bool false), some (.int _) => rfl
  | some (.bool false), some (.bool false), some (.string _) => rfl
  | some (.bool false), some (.bool false), some (.null _) => rfl
  | some (.bool false), some (.bool false), none => rfl
  | some (.bool false), some (.int _), some (.bool true) => rfl
  | some (.bool false), some (.int _), some (.bool false) => rfl
  | some (.bool false), some (.int _), some (.int _) => rfl
  | some (.bool false), some (.int _), some (.string _) => rfl
  | some (.bool false), some (.int _), some (.null _) => rfl
  | some (.bool false), some (.int _), none => rfl
  | some (.bool false), some (.string _), some (.bool true) => rfl
  | some (.bool false), some (.string _), some (.bool false) => rfl
  | some (.bool false), some (.string _), some (.int _) => rfl
  | some (.bool false), some (.string _), some (.string _) => rfl
  | some (.bool false), some (.string _), some (.null _) => rfl
  | some (.bool false), some (.string _), none => rfl
  | some (.bool false), some (.null _), some (.bool true) => rfl
  | some (.bool false), some (.null _), some (.bool false) => rfl
  | some (.bool false), some (.null _), some (.int _) => rfl
  | some (.bool false), some (.null _), some (.string _) => rfl
  | some (.bool false), some (.null _), some (.null _) => rfl
  | some (.bool false), some (.null _), none => rfl
  | some (.bool false), none, some (.bool true) => rfl
  | some (.bool false), none, some (.bool false) => rfl
  | some (.bool false), none, some (.int _) => rfl
  | some (.bool false), none, some (.string _) => rfl
  | some (.bool false), none, some (.null _) => rfl
  | some (.bool false), none, none => rfl
  | some (.int _), some (.bool true), some (.bool true) => rfl
  | some (.int _), some (.bool true), some (.bool false) => rfl
  | some (.int _), some (.bool true), some (.int _) => rfl
  | some (.int _), some (.bool true), some (.string _) => rfl
  | some (.int _), some (.bool true), some (.null _) => rfl
  | some (.int _), some (.bool true), none => rfl
  | some (.int _), some (.bool false), some (.bool true) => rfl
  | some (.int _), some (.bool false), some (.bool false) => rfl
  | some (.int _), some (.bool false), some (.int _) => rfl
  | some (.int _), some (.bool false), some (.string _) => rfl
  | some (.int _), some (.bool false), some (.null _) => rfl
  | some (.int _), some (.bool false), none => rfl
  | some (.int _), some (.int _), some (.bool true) => rfl
  | some (.int _), some (.int _), some (.bool false) => rfl
  | some (.int _), some (.int _), some (.int _) => rfl
  | some (.int _), some (.int _), some (.string _) => rfl
  | some (.int _), some (.int _), some (.null _) => rfl
  | some (.int _), some (.int _), none => rfl
  | some (.int _), some (.string _), some (.bool true) => rfl
  | some (.int _), some (.string _), some (.bool false) => rfl
  | some (.int _), some (.string _), some (.int _) => rfl
  | some (.int _), some (.string _), some (.string _) => rfl
  | some (.int _), some (.string _), some (.null _) => rfl
  | some (.int _), some (.string _), none => rfl
  | some (.int _), some (.null _), some (.bool true) => rfl
  | some (.int _), some (.null _), some (.bool false) => rfl
  | some (.int _), some (.null _), some (.int _) => rfl
  | some (.int _), some (.null _), some (.string _) => rfl
  | some (.int _), some (.null _), some (.null _) => rfl
  | some (.int _), some (.null _), none => rfl
  | some (.int _), none, some (.bool true) => rfl
  | some (.int _), none, some (.bool false) => rfl
  | some (.int _), none, some (.int _) => rfl
  | some (.int _), none, some (.string _) => rfl
  | some (.int _), none, some (.null _) => rfl
  | some (.int _), none, none => rfl
  | some (.string _), some (.bool true), some (.bool true) => rfl
  | some (.string _), some (.bool true), some (.bool false) => rfl
  | some (.string _), some (.bool true), some (.int _) => rfl
  | some (.string _), some (.bool true), some (.string _) => rfl
  | some (.string _), some (.bool true), some (.null _) => rfl
  | some (.string _), some (.bool true), none => rfl
  | some (.string _), some (.bool false), some (.bool true) => rfl
  | some (.string _), some (.bool false), some (.bool false) => rfl
  | some (.string _), some (.bool false), some (.int _) => rfl
  | some (.string _), some (.bool false), some (.string _) => rfl
  | some (.string _), some (.bool false), some (.null _) => rfl
  | some (.string _), some (.bool false), none => rfl
  | some (.string _), some (.int _), some (.bool true) => rfl
  | some (.string _), some (.int _), some (.bool false) => rfl
  | some (.string _), some (.int _), some (.int _) => rfl
  | some (.string _), some (.int _), some (.string _) => rfl
  | some (.string _), some (.int _), some (.null _) => rfl
  | some (.string _), some (.int _), none => rfl
  | some (.string _), some (.string _), some (.bool true) => rfl
  | some (.string _), some (.string _), some (.bool false) => rfl
  | some (.string _), some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _), some (.string _) => rfl
  | some (.string _), some (.string _), some (.null _) => rfl
  | some (.string _), some (.string _), none => rfl
  | some (.string _), some (.null _), some (.bool true) => rfl
  | some (.string _), some (.null _), some (.bool false) => rfl
  | some (.string _), some (.null _), some (.int _) => rfl
  | some (.string _), some (.null _), some (.string _) => rfl
  | some (.string _), some (.null _), some (.null _) => rfl
  | some (.string _), some (.null _), none => rfl
  | some (.string _), none, some (.bool true) => rfl
  | some (.string _), none, some (.bool false) => rfl
  | some (.string _), none, some (.int _) => rfl
  | some (.string _), none, some (.string _) => rfl
  | some (.string _), none, some (.null _) => rfl
  | some (.string _), none, none => rfl
  | some (.null _), some (.bool true), some (.bool true) => rfl
  | some (.null _), some (.bool true), some (.bool false) => rfl
  | some (.null _), some (.bool true), some (.int _) => rfl
  | some (.null _), some (.bool true), some (.string _) => rfl
  | some (.null _), some (.bool true), some (.null _) => rfl
  | some (.null _), some (.bool true), none => rfl
  | some (.null _), some (.bool false), some (.bool true) => rfl
  | some (.null _), some (.bool false), some (.bool false) => rfl
  | some (.null _), some (.bool false), some (.int _) => rfl
  | some (.null _), some (.bool false), some (.string _) => rfl
  | some (.null _), some (.bool false), some (.null _) => rfl
  | some (.null _), some (.bool false), none => rfl
  | some (.null _), some (.int _), some (.bool true) => rfl
  | some (.null _), some (.int _), some (.bool false) => rfl
  | some (.null _), some (.int _), some (.int _) => rfl
  | some (.null _), some (.int _), some (.string _) => rfl
  | some (.null _), some (.int _), some (.null _) => rfl
  | some (.null _), some (.int _), none => rfl
  | some (.null _), some (.string _), some (.bool true) => rfl
  | some (.null _), some (.string _), some (.bool false) => rfl
  | some (.null _), some (.string _), some (.int _) => rfl
  | some (.null _), some (.string _), some (.string _) => rfl
  | some (.null _), some (.string _), some (.null _) => rfl
  | some (.null _), some (.string _), none => rfl
  | some (.null _), some (.null _), some (.bool true) => rfl
  | some (.null _), some (.null _), some (.bool false) => rfl
  | some (.null _), some (.null _), some (.int _) => rfl
  | some (.null _), some (.null _), some (.string _) => rfl
  | some (.null _), some (.null _), some (.null _) => rfl
  | some (.null _), some (.null _), none => rfl
  | some (.null _), none, some (.bool true) => rfl
  | some (.null _), none, some (.bool false) => rfl
  | some (.null _), none, some (.int _) => rfl
  | some (.null _), none, some (.string _) => rfl
  | some (.null _), none, some (.null _) => rfl
  | some (.null _), none, none => rfl
  | none, some (.bool true), some (.bool true) => rfl
  | none, some (.bool true), some (.bool false) => rfl
  | none, some (.bool true), some (.int _) => rfl
  | none, some (.bool true), some (.string _) => rfl
  | none, some (.bool true), some (.null _) => rfl
  | none, some (.bool true), none => rfl
  | none, some (.bool false), some (.bool true) => rfl
  | none, some (.bool false), some (.bool false) => rfl
  | none, some (.bool false), some (.int _) => rfl
  | none, some (.bool false), some (.string _) => rfl
  | none, some (.bool false), some (.null _) => rfl
  | none, some (.bool false), none => rfl
  | none, some (.int _), some (.bool true) => rfl
  | none, some (.int _), some (.bool false) => rfl
  | none, some (.int _), some (.int _) => rfl
  | none, some (.int _), some (.string _) => rfl
  | none, some (.int _), some (.null _) => rfl
  | none, some (.int _), none => rfl
  | none, some (.string _), some (.bool true) => rfl
  | none, some (.string _), some (.bool false) => rfl
  | none, some (.string _), some (.int _) => rfl
  | none, some (.string _), some (.string _) => rfl
  | none, some (.string _), some (.null _) => rfl
  | none, some (.string _), none => rfl
  | none, some (.null _), some (.bool true) => rfl
  | none, some (.null _), some (.bool false) => rfl
  | none, some (.null _), some (.int _) => rfl
  | none, some (.null _), some (.string _) => rfl
  | none, some (.null _), some (.null _) => rfl
  | none, some (.null _), none => rfl
  | none, none, some (.bool true) => rfl
  | none, none, some (.bool false) => rfl
  | none, none, some (.int _) => rfl
  | none, none, some (.string _) => rfl
  | none, none, some (.null _) => rfl
  | none, none, none => rfl

/-- OR is associative at the value level -/
theorem evalBinOp_or_assoc (x y z : Option Value) :
    evalBinOp .or (evalBinOp .or x y) z = evalBinOp .or x (evalBinOp .or y z) := by
  match x, y, z with
  | some (.bool true), some (.bool true), some (.bool true) => rfl
  | some (.bool true), some (.bool true), some (.bool false) => rfl
  | some (.bool true), some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.bool true), some (.string _) => rfl
  | some (.bool true), some (.bool true), some (.null _) => rfl
  | some (.bool true), some (.bool true), none => rfl
  | some (.bool true), some (.bool false), some (.bool true) => rfl
  | some (.bool true), some (.bool false), some (.bool false) => rfl
  | some (.bool true), some (.bool false), some (.int _) => rfl
  | some (.bool true), some (.bool false), some (.string _) => rfl
  | some (.bool true), some (.bool false), some (.null _) => rfl
  | some (.bool true), some (.bool false), none => rfl
  | some (.bool true), some (.int _), some (.bool true) => rfl
  | some (.bool true), some (.int _), some (.bool false) => rfl
  | some (.bool true), some (.int _), some (.int _) => rfl
  | some (.bool true), some (.int _), some (.string _) => rfl
  | some (.bool true), some (.int _), some (.null _) => rfl
  | some (.bool true), some (.int _), none => rfl
  | some (.bool true), some (.string _), some (.bool true) => rfl
  | some (.bool true), some (.string _), some (.bool false) => rfl
  | some (.bool true), some (.string _), some (.int _) => rfl
  | some (.bool true), some (.string _), some (.string _) => rfl
  | some (.bool true), some (.string _), some (.null _) => rfl
  | some (.bool true), some (.string _), none => rfl
  | some (.bool true), some (.null _), some (.bool true) => rfl
  | some (.bool true), some (.null _), some (.bool false) => rfl
  | some (.bool true), some (.null _), some (.int _) => rfl
  | some (.bool true), some (.null _), some (.string _) => rfl
  | some (.bool true), some (.null _), some (.null _) => rfl
  | some (.bool true), some (.null _), none => rfl
  | some (.bool true), none, some (.bool true) => rfl
  | some (.bool true), none, some (.bool false) => rfl
  | some (.bool true), none, some (.int _) => rfl
  | some (.bool true), none, some (.string _) => rfl
  | some (.bool true), none, some (.null _) => rfl
  | some (.bool true), none, none => rfl
  | some (.bool false), some (.bool true), some (.bool true) => rfl
  | some (.bool false), some (.bool true), some (.bool false) => rfl
  | some (.bool false), some (.bool true), some (.int _) => rfl
  | some (.bool false), some (.bool true), some (.string _) => rfl
  | some (.bool false), some (.bool true), some (.null _) => rfl
  | some (.bool false), some (.bool true), none => rfl
  | some (.bool false), some (.bool false), some (.bool true) => rfl
  | some (.bool false), some (.bool false), some (.bool false) => rfl
  | some (.bool false), some (.bool false), some (.int _) => rfl
  | some (.bool false), some (.bool false), some (.string _) => rfl
  | some (.bool false), some (.bool false), some (.null _) => rfl
  | some (.bool false), some (.bool false), none => rfl
  | some (.bool false), some (.int _), some (.bool true) => rfl
  | some (.bool false), some (.int _), some (.bool false) => rfl
  | some (.bool false), some (.int _), some (.int _) => rfl
  | some (.bool false), some (.int _), some (.string _) => rfl
  | some (.bool false), some (.int _), some (.null _) => rfl
  | some (.bool false), some (.int _), none => rfl
  | some (.bool false), some (.string _), some (.bool true) => rfl
  | some (.bool false), some (.string _), some (.bool false) => rfl
  | some (.bool false), some (.string _), some (.int _) => rfl
  | some (.bool false), some (.string _), some (.string _) => rfl
  | some (.bool false), some (.string _), some (.null _) => rfl
  | some (.bool false), some (.string _), none => rfl
  | some (.bool false), some (.null _), some (.bool true) => rfl
  | some (.bool false), some (.null _), some (.bool false) => rfl
  | some (.bool false), some (.null _), some (.int _) => rfl
  | some (.bool false), some (.null _), some (.string _) => rfl
  | some (.bool false), some (.null _), some (.null _) => rfl
  | some (.bool false), some (.null _), none => rfl
  | some (.bool false), none, some (.bool true) => rfl
  | some (.bool false), none, some (.bool false) => rfl
  | some (.bool false), none, some (.int _) => rfl
  | some (.bool false), none, some (.string _) => rfl
  | some (.bool false), none, some (.null _) => rfl
  | some (.bool false), none, none => rfl
  | some (.int _), some (.bool true), some (.bool true) => rfl
  | some (.int _), some (.bool true), some (.bool false) => rfl
  | some (.int _), some (.bool true), some (.int _) => rfl
  | some (.int _), some (.bool true), some (.string _) => rfl
  | some (.int _), some (.bool true), some (.null _) => rfl
  | some (.int _), some (.bool true), none => rfl
  | some (.int _), some (.bool false), some (.bool true) => rfl
  | some (.int _), some (.bool false), some (.bool false) => rfl
  | some (.int _), some (.bool false), some (.int _) => rfl
  | some (.int _), some (.bool false), some (.string _) => rfl
  | some (.int _), some (.bool false), some (.null _) => rfl
  | some (.int _), some (.bool false), none => rfl
  | some (.int _), some (.int _), some (.bool true) => rfl
  | some (.int _), some (.int _), some (.bool false) => rfl
  | some (.int _), some (.int _), some (.int _) => rfl
  | some (.int _), some (.int _), some (.string _) => rfl
  | some (.int _), some (.int _), some (.null _) => rfl
  | some (.int _), some (.int _), none => rfl
  | some (.int _), some (.string _), some (.bool true) => rfl
  | some (.int _), some (.string _), some (.bool false) => rfl
  | some (.int _), some (.string _), some (.int _) => rfl
  | some (.int _), some (.string _), some (.string _) => rfl
  | some (.int _), some (.string _), some (.null _) => rfl
  | some (.int _), some (.string _), none => rfl
  | some (.int _), some (.null _), some (.bool true) => rfl
  | some (.int _), some (.null _), some (.bool false) => rfl
  | some (.int _), some (.null _), some (.int _) => rfl
  | some (.int _), some (.null _), some (.string _) => rfl
  | some (.int _), some (.null _), some (.null _) => rfl
  | some (.int _), some (.null _), none => rfl
  | some (.int _), none, some (.bool true) => rfl
  | some (.int _), none, some (.bool false) => rfl
  | some (.int _), none, some (.int _) => rfl
  | some (.int _), none, some (.string _) => rfl
  | some (.int _), none, some (.null _) => rfl
  | some (.int _), none, none => rfl
  | some (.string _), some (.bool true), some (.bool true) => rfl
  | some (.string _), some (.bool true), some (.bool false) => rfl
  | some (.string _), some (.bool true), some (.int _) => rfl
  | some (.string _), some (.bool true), some (.string _) => rfl
  | some (.string _), some (.bool true), some (.null _) => rfl
  | some (.string _), some (.bool true), none => rfl
  | some (.string _), some (.bool false), some (.bool true) => rfl
  | some (.string _), some (.bool false), some (.bool false) => rfl
  | some (.string _), some (.bool false), some (.int _) => rfl
  | some (.string _), some (.bool false), some (.string _) => rfl
  | some (.string _), some (.bool false), some (.null _) => rfl
  | some (.string _), some (.bool false), none => rfl
  | some (.string _), some (.int _), some (.bool true) => rfl
  | some (.string _), some (.int _), some (.bool false) => rfl
  | some (.string _), some (.int _), some (.int _) => rfl
  | some (.string _), some (.int _), some (.string _) => rfl
  | some (.string _), some (.int _), some (.null _) => rfl
  | some (.string _), some (.int _), none => rfl
  | some (.string _), some (.string _), some (.bool true) => rfl
  | some (.string _), some (.string _), some (.bool false) => rfl
  | some (.string _), some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _), some (.string _) => rfl
  | some (.string _), some (.string _), some (.null _) => rfl
  | some (.string _), some (.string _), none => rfl
  | some (.string _), some (.null _), some (.bool true) => rfl
  | some (.string _), some (.null _), some (.bool false) => rfl
  | some (.string _), some (.null _), some (.int _) => rfl
  | some (.string _), some (.null _), some (.string _) => rfl
  | some (.string _), some (.null _), some (.null _) => rfl
  | some (.string _), some (.null _), none => rfl
  | some (.string _), none, some (.bool true) => rfl
  | some (.string _), none, some (.bool false) => rfl
  | some (.string _), none, some (.int _) => rfl
  | some (.string _), none, some (.string _) => rfl
  | some (.string _), none, some (.null _) => rfl
  | some (.string _), none, none => rfl
  | some (.null _), some (.bool true), some (.bool true) => rfl
  | some (.null _), some (.bool true), some (.bool false) => rfl
  | some (.null _), some (.bool true), some (.int _) => rfl
  | some (.null _), some (.bool true), some (.string _) => rfl
  | some (.null _), some (.bool true), some (.null _) => rfl
  | some (.null _), some (.bool true), none => rfl
  | some (.null _), some (.bool false), some (.bool true) => rfl
  | some (.null _), some (.bool false), some (.bool false) => rfl
  | some (.null _), some (.bool false), some (.int _) => rfl
  | some (.null _), some (.bool false), some (.string _) => rfl
  | some (.null _), some (.bool false), some (.null _) => rfl
  | some (.null _), some (.bool false), none => rfl
  | some (.null _), some (.int _), some (.bool true) => rfl
  | some (.null _), some (.int _), some (.bool false) => rfl
  | some (.null _), some (.int _), some (.int _) => rfl
  | some (.null _), some (.int _), some (.string _) => rfl
  | some (.null _), some (.int _), some (.null _) => rfl
  | some (.null _), some (.int _), none => rfl
  | some (.null _), some (.string _), some (.bool true) => rfl
  | some (.null _), some (.string _), some (.bool false) => rfl
  | some (.null _), some (.string _), some (.int _) => rfl
  | some (.null _), some (.string _), some (.string _) => rfl
  | some (.null _), some (.string _), some (.null _) => rfl
  | some (.null _), some (.string _), none => rfl
  | some (.null _), some (.null _), some (.bool true) => rfl
  | some (.null _), some (.null _), some (.bool false) => rfl
  | some (.null _), some (.null _), some (.int _) => rfl
  | some (.null _), some (.null _), some (.string _) => rfl
  | some (.null _), some (.null _), some (.null _) => rfl
  | some (.null _), some (.null _), none => rfl
  | some (.null _), none, some (.bool true) => rfl
  | some (.null _), none, some (.bool false) => rfl
  | some (.null _), none, some (.int _) => rfl
  | some (.null _), none, some (.string _) => rfl
  | some (.null _), none, some (.null _) => rfl
  | some (.null _), none, none => rfl
  | none, some (.bool true), some (.bool true) => rfl
  | none, some (.bool true), some (.bool false) => rfl
  | none, some (.bool true), some (.int _) => rfl
  | none, some (.bool true), some (.string _) => rfl
  | none, some (.bool true), some (.null _) => rfl
  | none, some (.bool true), none => rfl
  | none, some (.bool false), some (.bool true) => rfl
  | none, some (.bool false), some (.bool false) => rfl
  | none, some (.bool false), some (.int _) => rfl
  | none, some (.bool false), some (.string _) => rfl
  | none, some (.bool false), some (.null _) => rfl
  | none, some (.bool false), none => rfl
  | none, some (.int _), some (.bool true) => rfl
  | none, some (.int _), some (.bool false) => rfl
  | none, some (.int _), some (.int _) => rfl
  | none, some (.int _), some (.string _) => rfl
  | none, some (.int _), some (.null _) => rfl
  | none, some (.int _), none => rfl
  | none, some (.string _), some (.bool true) => rfl
  | none, some (.string _), some (.bool false) => rfl
  | none, some (.string _), some (.int _) => rfl
  | none, some (.string _), some (.string _) => rfl
  | none, some (.string _), some (.null _) => rfl
  | none, some (.string _), none => rfl
  | none, some (.null _), some (.bool true) => rfl
  | none, some (.null _), some (.bool false) => rfl
  | none, some (.null _), some (.int _) => rfl
  | none, some (.null _), some (.string _) => rfl
  | none, some (.null _), some (.null _) => rfl
  | none, some (.null _), none => rfl
  | none, none, some (.bool true) => rfl
  | none, none, some (.bool false) => rfl
  | none, none, some (.int _) => rfl
  | none, none, some (.string _) => rfl
  | none, none, some (.null _) => rfl
  | none, none, none => rfl

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
  | some (.bool false), some (.null _) => rfl
  | some (.bool false), none => rfl
  -- anything AND false
  | some (.int _), some (.bool false) => rfl
  | some (.string _), some (.bool false) => rfl
  | some (.null _), some (.bool false) => rfl
  | none, some (.bool false) => rfl
  -- true AND non-bool
  | some (.bool true), some (.int _) => rfl
  | some (.bool true), some (.string _) => rfl
  | some (.bool true), some (.null _) => rfl
  | some (.bool true), none => rfl
  -- non-bool AND true
  | some (.int _), some (.bool true) => rfl
  | some (.string _), some (.bool true) => rfl
  | some (.null _), some (.bool true) => rfl
  | none, some (.bool true) => rfl
  -- Non-bool cases
  | some (.int _), some (.int _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.string _), none => rfl
  | some (.null _), some (.int _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.null _), none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.null _) => rfl
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
  | some (.bool true), some (.null _) => rfl
  | some (.bool true), none => rfl
  -- anything OR true
  | some (.int _), some (.bool true) => rfl
  | some (.string _), some (.bool true) => rfl
  | some (.null _), some (.bool true) => rfl
  | none, some (.bool true) => rfl
  -- false OR non-bool
  | some (.bool false), some (.int _) => rfl
  | some (.bool false), some (.string _) => rfl
  | some (.bool false), some (.null _) => rfl
  | some (.bool false), none => rfl
  -- non-bool OR false
  | some (.int _), some (.bool false) => rfl
  | some (.string _), some (.bool false) => rfl
  | some (.null _), some (.bool false) => rfl
  | none, some (.bool false) => rfl
  -- Non-bool cases
  | some (.int _), some (.int _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.string _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.string _), none => rfl
  | some (.null _), some (.int _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.null _), none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.null _) => rfl
  | none, none => rfl


end SqlEquiv
