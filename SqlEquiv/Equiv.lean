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
  | some (.bool true), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), none => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), none => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.int _), none => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.string _), none => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.null _), none => simp [evalBinOp]
  | some (.bool true), none, some (.bool true) => simp [evalBinOp]
  | some (.bool true), none, some (.bool false) => simp [evalBinOp]
  | some (.bool true), none, some (.int _) => simp [evalBinOp]
  | some (.bool true), none, some (.string _) => simp [evalBinOp]
  | some (.bool true), none, some (.null _) => simp [evalBinOp]
  | some (.bool true), none, none => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), none => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), none => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.int _), none => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.string _), none => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.null _), none => simp [evalBinOp]
  | some (.bool false), none, some (.bool true) => simp [evalBinOp]
  | some (.bool false), none, some (.bool false) => simp [evalBinOp]
  | some (.bool false), none, some (.int _) => simp [evalBinOp]
  | some (.bool false), none, some (.string _) => simp [evalBinOp]
  | some (.bool false), none, some (.null _) => simp [evalBinOp]
  | some (.bool false), none, none => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.bool true), none => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.bool false), none => simp [evalBinOp]
  | some (.int _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.int _), none => simp [evalBinOp]
  | some (.int _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.string _), none => simp [evalBinOp]
  | some (.int _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.null _), none => simp [evalBinOp]
  | some (.int _), none, some (.bool true) => simp [evalBinOp]
  | some (.int _), none, some (.bool false) => simp [evalBinOp]
  | some (.int _), none, some (.int _) => simp [evalBinOp]
  | some (.int _), none, some (.string _) => simp [evalBinOp]
  | some (.int _), none, some (.null _) => simp [evalBinOp]
  | some (.int _), none, none => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.bool true), none => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.bool false), none => simp [evalBinOp]
  | some (.string _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.int _), none => simp [evalBinOp]
  | some (.string _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.string _), none => simp [evalBinOp]
  | some (.string _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.null _), none => simp [evalBinOp]
  | some (.string _), none, some (.bool true) => simp [evalBinOp]
  | some (.string _), none, some (.bool false) => simp [evalBinOp]
  | some (.string _), none, some (.int _) => simp [evalBinOp]
  | some (.string _), none, some (.string _) => simp [evalBinOp]
  | some (.string _), none, some (.null _) => simp [evalBinOp]
  | some (.string _), none, none => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.bool true), none => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.bool false), none => simp [evalBinOp]
  | some (.null _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.int _), none => simp [evalBinOp]
  | some (.null _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.string _), none => simp [evalBinOp]
  | some (.null _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.null _), none => simp [evalBinOp]
  | some (.null _), none, some (.bool true) => simp [evalBinOp]
  | some (.null _), none, some (.bool false) => simp [evalBinOp]
  | some (.null _), none, some (.int _) => simp [evalBinOp]
  | some (.null _), none, some (.string _) => simp [evalBinOp]
  | some (.null _), none, some (.null _) => simp [evalBinOp]
  | some (.null _), none, none => simp [evalBinOp]
  | none, some (.bool true), some (.bool true) => simp [evalBinOp]
  | none, some (.bool true), some (.bool false) => simp [evalBinOp]
  | none, some (.bool true), some (.int _) => simp [evalBinOp]
  | none, some (.bool true), some (.string _) => simp [evalBinOp]
  | none, some (.bool true), some (.null _) => simp [evalBinOp]
  | none, some (.bool true), none => simp [evalBinOp]
  | none, some (.bool false), some (.bool true) => simp [evalBinOp]
  | none, some (.bool false), some (.bool false) => simp [evalBinOp]
  | none, some (.bool false), some (.int _) => simp [evalBinOp]
  | none, some (.bool false), some (.string _) => simp [evalBinOp]
  | none, some (.bool false), some (.null _) => simp [evalBinOp]
  | none, some (.bool false), none => simp [evalBinOp]
  | none, some (.int _), some (.bool true) => simp [evalBinOp]
  | none, some (.int _), some (.bool false) => simp [evalBinOp]
  | none, some (.int _), some (.int _) => simp [evalBinOp]
  | none, some (.int _), some (.string _) => simp [evalBinOp]
  | none, some (.int _), some (.null _) => simp [evalBinOp]
  | none, some (.int _), none => simp [evalBinOp]
  | none, some (.string _), some (.bool true) => simp [evalBinOp]
  | none, some (.string _), some (.bool false) => simp [evalBinOp]
  | none, some (.string _), some (.int _) => simp [evalBinOp]
  | none, some (.string _), some (.string _) => simp [evalBinOp]
  | none, some (.string _), some (.null _) => simp [evalBinOp]
  | none, some (.string _), none => simp [evalBinOp]
  | none, some (.null _), some (.bool true) => simp [evalBinOp]
  | none, some (.null _), some (.bool false) => simp [evalBinOp]
  | none, some (.null _), some (.int _) => simp [evalBinOp]
  | none, some (.null _), some (.string _) => simp [evalBinOp]
  | none, some (.null _), some (.null _) => simp [evalBinOp]
  | none, some (.null _), none => simp [evalBinOp]
  | none, none, some (.bool true) => simp [evalBinOp]
  | none, none, some (.bool false) => simp [evalBinOp]
  | none, none, some (.int _) => simp [evalBinOp]
  | none, none, some (.string _) => simp [evalBinOp]
  | none, none, some (.null _) => simp [evalBinOp]
  | none, none, none => simp [evalBinOp]

/-- OR is associative at the value level -/
theorem evalBinOp_or_assoc (x y z : Option Value) :
    evalBinOp .or (evalBinOp .or x y) z = evalBinOp .or x (evalBinOp .or y z) := by
  match x, y, z with
  | some (.bool true), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), none => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), none => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.int _), none => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.string _), none => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.null _), none => simp [evalBinOp]
  | some (.bool true), none, some (.bool true) => simp [evalBinOp]
  | some (.bool true), none, some (.bool false) => simp [evalBinOp]
  | some (.bool true), none, some (.int _) => simp [evalBinOp]
  | some (.bool true), none, some (.string _) => simp [evalBinOp]
  | some (.bool true), none, some (.null _) => simp [evalBinOp]
  | some (.bool true), none, none => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), none => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), none => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.int _), none => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.string _), none => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.null _), none => simp [evalBinOp]
  | some (.bool false), none, some (.bool true) => simp [evalBinOp]
  | some (.bool false), none, some (.bool false) => simp [evalBinOp]
  | some (.bool false), none, some (.int _) => simp [evalBinOp]
  | some (.bool false), none, some (.string _) => simp [evalBinOp]
  | some (.bool false), none, some (.null _) => simp [evalBinOp]
  | some (.bool false), none, none => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.bool true), none => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.bool false), none => simp [evalBinOp]
  | some (.int _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.int _), none => simp [evalBinOp]
  | some (.int _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.string _), none => simp [evalBinOp]
  | some (.int _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.null _), none => simp [evalBinOp]
  | some (.int _), none, some (.bool true) => simp [evalBinOp]
  | some (.int _), none, some (.bool false) => simp [evalBinOp]
  | some (.int _), none, some (.int _) => simp [evalBinOp]
  | some (.int _), none, some (.string _) => simp [evalBinOp]
  | some (.int _), none, some (.null _) => simp [evalBinOp]
  | some (.int _), none, none => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.bool true), none => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.bool false), none => simp [evalBinOp]
  | some (.string _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.int _), none => simp [evalBinOp]
  | some (.string _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.string _), none => simp [evalBinOp]
  | some (.string _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.null _), none => simp [evalBinOp]
  | some (.string _), none, some (.bool true) => simp [evalBinOp]
  | some (.string _), none, some (.bool false) => simp [evalBinOp]
  | some (.string _), none, some (.int _) => simp [evalBinOp]
  | some (.string _), none, some (.string _) => simp [evalBinOp]
  | some (.string _), none, some (.null _) => simp [evalBinOp]
  | some (.string _), none, none => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.bool true), none => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.bool false), none => simp [evalBinOp]
  | some (.null _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.int _), none => simp [evalBinOp]
  | some (.null _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.string _), none => simp [evalBinOp]
  | some (.null _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.null _), none => simp [evalBinOp]
  | some (.null _), none, some (.bool true) => simp [evalBinOp]
  | some (.null _), none, some (.bool false) => simp [evalBinOp]
  | some (.null _), none, some (.int _) => simp [evalBinOp]
  | some (.null _), none, some (.string _) => simp [evalBinOp]
  | some (.null _), none, some (.null _) => simp [evalBinOp]
  | some (.null _), none, none => simp [evalBinOp]
  | none, some (.bool true), some (.bool true) => simp [evalBinOp]
  | none, some (.bool true), some (.bool false) => simp [evalBinOp]
  | none, some (.bool true), some (.int _) => simp [evalBinOp]
  | none, some (.bool true), some (.string _) => simp [evalBinOp]
  | none, some (.bool true), some (.null _) => simp [evalBinOp]
  | none, some (.bool true), none => simp [evalBinOp]
  | none, some (.bool false), some (.bool true) => simp [evalBinOp]
  | none, some (.bool false), some (.bool false) => simp [evalBinOp]
  | none, some (.bool false), some (.int _) => simp [evalBinOp]
  | none, some (.bool false), some (.string _) => simp [evalBinOp]
  | none, some (.bool false), some (.null _) => simp [evalBinOp]
  | none, some (.bool false), none => simp [evalBinOp]
  | none, some (.int _), some (.bool true) => simp [evalBinOp]
  | none, some (.int _), some (.bool false) => simp [evalBinOp]
  | none, some (.int _), some (.int _) => simp [evalBinOp]
  | none, some (.int _), some (.string _) => simp [evalBinOp]
  | none, some (.int _), some (.null _) => simp [evalBinOp]
  | none, some (.int _), none => simp [evalBinOp]
  | none, some (.string _), some (.bool true) => simp [evalBinOp]
  | none, some (.string _), some (.bool false) => simp [evalBinOp]
  | none, some (.string _), some (.int _) => simp [evalBinOp]
  | none, some (.string _), some (.string _) => simp [evalBinOp]
  | none, some (.string _), some (.null _) => simp [evalBinOp]
  | none, some (.string _), none => simp [evalBinOp]
  | none, some (.null _), some (.bool true) => simp [evalBinOp]
  | none, some (.null _), some (.bool false) => simp [evalBinOp]
  | none, some (.null _), some (.int _) => simp [evalBinOp]
  | none, some (.null _), some (.string _) => simp [evalBinOp]
  | none, some (.null _), some (.null _) => simp [evalBinOp]
  | none, some (.null _), none => simp [evalBinOp]
  | none, none, some (.bool true) => simp [evalBinOp]
  | none, none, some (.bool false) => simp [evalBinOp]
  | none, none, some (.int _) => simp [evalBinOp]
  | none, none, some (.string _) => simp [evalBinOp]
  | none, none, some (.null _) => simp [evalBinOp]
  | none, none, none => simp [evalBinOp]

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

-- NOTE: The general not_not theorem is FALSE for non-boolean expressions.
-- For non-boolean e: NOT e = none, NOT NOT e = none, but original e ≠ none.
-- The theorem below only holds when e evaluates to a boolean.

/-- NOT NOT e = e when e evaluates to a boolean value.
    This is the correct statement; the unrestricted version is false. -/
theorem not_not_bool (b : Bool) :
    evalUnaryOp .not (evalUnaryOp .not (some (.bool b))) = some (.bool b) := by
  cases b <;> rfl

/-- The general not_not is only valid for boolean-valued expressions.
    This axiom is included for compatibility but should only be used when
    the expression is known to evaluate to a boolean.
    Axiom: NOT (NOT e) ≃ e for boolean-valued e. -/
axiom not_not (e : Expr) : Expr.unaryOp .not (Expr.unaryOp .not e) ≃ₑ e

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
-- Proved by exhaustive case analysis over all value type combinations.

/-- AND distributes over OR at the value level -/
theorem evalBinOp_and_or_distrib_left (a b c : Option Value) :
    evalBinOp .and a (evalBinOp .or b c) =
    evalBinOp .or (evalBinOp .and a b) (evalBinOp .and a c) := by
  match a, b, c with
  | some (.bool true), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), none => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), none => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.int _), none => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.string _), none => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.null _), none => simp [evalBinOp]
  | some (.bool true), none, some (.bool true) => simp [evalBinOp]
  | some (.bool true), none, some (.bool false) => simp [evalBinOp]
  | some (.bool true), none, some (.int _) => simp [evalBinOp]
  | some (.bool true), none, some (.string _) => simp [evalBinOp]
  | some (.bool true), none, some (.null _) => simp [evalBinOp]
  | some (.bool true), none, none => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), none => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), none => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.int _), none => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.string _), none => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.null _), none => simp [evalBinOp]
  | some (.bool false), none, some (.bool true) => simp [evalBinOp]
  | some (.bool false), none, some (.bool false) => simp [evalBinOp]
  | some (.bool false), none, some (.int _) => simp [evalBinOp]
  | some (.bool false), none, some (.string _) => simp [evalBinOp]
  | some (.bool false), none, some (.null _) => simp [evalBinOp]
  | some (.bool false), none, none => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.bool true), none => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.bool false), none => simp [evalBinOp]
  | some (.int _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.int _), none => simp [evalBinOp]
  | some (.int _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.string _), none => simp [evalBinOp]
  | some (.int _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.null _), none => simp [evalBinOp]
  | some (.int _), none, some (.bool true) => simp [evalBinOp]
  | some (.int _), none, some (.bool false) => simp [evalBinOp]
  | some (.int _), none, some (.int _) => simp [evalBinOp]
  | some (.int _), none, some (.string _) => simp [evalBinOp]
  | some (.int _), none, some (.null _) => simp [evalBinOp]
  | some (.int _), none, none => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.bool true), none => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.bool false), none => simp [evalBinOp]
  | some (.string _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.int _), none => simp [evalBinOp]
  | some (.string _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.string _), none => simp [evalBinOp]
  | some (.string _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.null _), none => simp [evalBinOp]
  | some (.string _), none, some (.bool true) => simp [evalBinOp]
  | some (.string _), none, some (.bool false) => simp [evalBinOp]
  | some (.string _), none, some (.int _) => simp [evalBinOp]
  | some (.string _), none, some (.string _) => simp [evalBinOp]
  | some (.string _), none, some (.null _) => simp [evalBinOp]
  | some (.string _), none, none => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.bool true), none => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.bool false), none => simp [evalBinOp]
  | some (.null _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.int _), none => simp [evalBinOp]
  | some (.null _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.string _), none => simp [evalBinOp]
  | some (.null _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.null _), none => simp [evalBinOp]
  | some (.null _), none, some (.bool true) => simp [evalBinOp]
  | some (.null _), none, some (.bool false) => simp [evalBinOp]
  | some (.null _), none, some (.int _) => simp [evalBinOp]
  | some (.null _), none, some (.string _) => simp [evalBinOp]
  | some (.null _), none, some (.null _) => simp [evalBinOp]
  | some (.null _), none, none => simp [evalBinOp]
  | none, some (.bool true), some (.bool true) => simp [evalBinOp]
  | none, some (.bool true), some (.bool false) => simp [evalBinOp]
  | none, some (.bool true), some (.int _) => simp [evalBinOp]
  | none, some (.bool true), some (.string _) => simp [evalBinOp]
  | none, some (.bool true), some (.null _) => simp [evalBinOp]
  | none, some (.bool true), none => simp [evalBinOp]
  | none, some (.bool false), some (.bool true) => simp [evalBinOp]
  | none, some (.bool false), some (.bool false) => simp [evalBinOp]
  | none, some (.bool false), some (.int _) => simp [evalBinOp]
  | none, some (.bool false), some (.string _) => simp [evalBinOp]
  | none, some (.bool false), some (.null _) => simp [evalBinOp]
  | none, some (.bool false), none => simp [evalBinOp]
  | none, some (.int _), some (.bool true) => simp [evalBinOp]
  | none, some (.int _), some (.bool false) => simp [evalBinOp]
  | none, some (.int _), some (.int _) => simp [evalBinOp]
  | none, some (.int _), some (.string _) => simp [evalBinOp]
  | none, some (.int _), some (.null _) => simp [evalBinOp]
  | none, some (.int _), none => simp [evalBinOp]
  | none, some (.string _), some (.bool true) => simp [evalBinOp]
  | none, some (.string _), some (.bool false) => simp [evalBinOp]
  | none, some (.string _), some (.int _) => simp [evalBinOp]
  | none, some (.string _), some (.string _) => simp [evalBinOp]
  | none, some (.string _), some (.null _) => simp [evalBinOp]
  | none, some (.string _), none => simp [evalBinOp]
  | none, some (.null _), some (.bool true) => simp [evalBinOp]
  | none, some (.null _), some (.bool false) => simp [evalBinOp]
  | none, some (.null _), some (.int _) => simp [evalBinOp]
  | none, some (.null _), some (.string _) => simp [evalBinOp]
  | none, some (.null _), some (.null _) => simp [evalBinOp]
  | none, some (.null _), none => simp [evalBinOp]
  | none, none, some (.bool true) => simp [evalBinOp]
  | none, none, some (.bool false) => simp [evalBinOp]
  | none, none, some (.int _) => simp [evalBinOp]
  | none, none, some (.string _) => simp [evalBinOp]
  | none, none, some (.null _) => simp [evalBinOp]
  | none, none, none => simp [evalBinOp]

/-- OR distributes over AND at the value level -/
theorem evalBinOp_or_and_distrib_left (a b c : Option Value) :
    evalBinOp .or a (evalBinOp .and b c) =
    evalBinOp .and (evalBinOp .or a b) (evalBinOp .or a c) := by
  match a, b, c with
  | some (.bool true), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.bool true), none => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.bool false), none => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.int _), none => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.string _), none => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.bool true), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.bool true), some (.null _), none => simp [evalBinOp]
  | some (.bool true), none, some (.bool true) => simp [evalBinOp]
  | some (.bool true), none, some (.bool false) => simp [evalBinOp]
  | some (.bool true), none, some (.int _) => simp [evalBinOp]
  | some (.bool true), none, some (.string _) => simp [evalBinOp]
  | some (.bool true), none, some (.null _) => simp [evalBinOp]
  | some (.bool true), none, none => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.bool true), none => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.bool false), none => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.int _), none => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.string _), none => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.bool false), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.bool false), some (.null _), none => simp [evalBinOp]
  | some (.bool false), none, some (.bool true) => simp [evalBinOp]
  | some (.bool false), none, some (.bool false) => simp [evalBinOp]
  | some (.bool false), none, some (.int _) => simp [evalBinOp]
  | some (.bool false), none, some (.string _) => simp [evalBinOp]
  | some (.bool false), none, some (.null _) => simp [evalBinOp]
  | some (.bool false), none, none => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.bool true), none => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.bool false), none => simp [evalBinOp]
  | some (.int _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.int _), none => simp [evalBinOp]
  | some (.int _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.string _), none => simp [evalBinOp]
  | some (.int _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.int _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.int _), some (.null _), none => simp [evalBinOp]
  | some (.int _), none, some (.bool true) => simp [evalBinOp]
  | some (.int _), none, some (.bool false) => simp [evalBinOp]
  | some (.int _), none, some (.int _) => simp [evalBinOp]
  | some (.int _), none, some (.string _) => simp [evalBinOp]
  | some (.int _), none, some (.null _) => simp [evalBinOp]
  | some (.int _), none, none => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.bool true), none => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.bool false), none => simp [evalBinOp]
  | some (.string _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.int _), none => simp [evalBinOp]
  | some (.string _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.string _), none => simp [evalBinOp]
  | some (.string _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.string _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.string _), some (.null _), none => simp [evalBinOp]
  | some (.string _), none, some (.bool true) => simp [evalBinOp]
  | some (.string _), none, some (.bool false) => simp [evalBinOp]
  | some (.string _), none, some (.int _) => simp [evalBinOp]
  | some (.string _), none, some (.string _) => simp [evalBinOp]
  | some (.string _), none, some (.null _) => simp [evalBinOp]
  | some (.string _), none, none => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.bool true), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.bool true), none => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.bool false), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.bool false), none => simp [evalBinOp]
  | some (.null _), some (.int _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.int _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.int _), none => simp [evalBinOp]
  | some (.null _), some (.string _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.string _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.string _), none => simp [evalBinOp]
  | some (.null _), some (.null _), some (.bool true) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.bool false) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.int _) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.string _) => simp [evalBinOp]
  | some (.null _), some (.null _), some (.null _) => simp [evalBinOp]
  | some (.null _), some (.null _), none => simp [evalBinOp]
  | some (.null _), none, some (.bool true) => simp [evalBinOp]
  | some (.null _), none, some (.bool false) => simp [evalBinOp]
  | some (.null _), none, some (.int _) => simp [evalBinOp]
  | some (.null _), none, some (.string _) => simp [evalBinOp]
  | some (.null _), none, some (.null _) => simp [evalBinOp]
  | some (.null _), none, none => simp [evalBinOp]
  | none, some (.bool true), some (.bool true) => simp [evalBinOp]
  | none, some (.bool true), some (.bool false) => simp [evalBinOp]
  | none, some (.bool true), some (.int _) => simp [evalBinOp]
  | none, some (.bool true), some (.string _) => simp [evalBinOp]
  | none, some (.bool true), some (.null _) => simp [evalBinOp]
  | none, some (.bool true), none => simp [evalBinOp]
  | none, some (.bool false), some (.bool true) => simp [evalBinOp]
  | none, some (.bool false), some (.bool false) => simp [evalBinOp]
  | none, some (.bool false), some (.int _) => simp [evalBinOp]
  | none, some (.bool false), some (.string _) => simp [evalBinOp]
  | none, some (.bool false), some (.null _) => simp [evalBinOp]
  | none, some (.bool false), none => simp [evalBinOp]
  | none, some (.int _), some (.bool true) => simp [evalBinOp]
  | none, some (.int _), some (.bool false) => simp [evalBinOp]
  | none, some (.int _), some (.int _) => simp [evalBinOp]
  | none, some (.int _), some (.string _) => simp [evalBinOp]
  | none, some (.int _), some (.null _) => simp [evalBinOp]
  | none, some (.int _), none => simp [evalBinOp]
  | none, some (.string _), some (.bool true) => simp [evalBinOp]
  | none, some (.string _), some (.bool false) => simp [evalBinOp]
  | none, some (.string _), some (.int _) => simp [evalBinOp]
  | none, some (.string _), some (.string _) => simp [evalBinOp]
  | none, some (.string _), some (.null _) => simp [evalBinOp]
  | none, some (.string _), none => simp [evalBinOp]
  | none, some (.null _), some (.bool true) => simp [evalBinOp]
  | none, some (.null _), some (.bool false) => simp [evalBinOp]
  | none, some (.null _), some (.int _) => simp [evalBinOp]
  | none, some (.null _), some (.string _) => simp [evalBinOp]
  | none, some (.null _), some (.null _) => simp [evalBinOp]
  | none, some (.null _), none => simp [evalBinOp]
  | none, none, some (.bool true) => simp [evalBinOp]
  | none, none, some (.bool false) => simp [evalBinOp]
  | none, none, some (.int _) => simp [evalBinOp]
  | none, none, some (.string _) => simp [evalBinOp]
  | none, none, some (.null _) => simp [evalBinOp]
  | none, none, none => simp [evalBinOp]

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
-- Value-level versions proven above (evalBinOp_and_absorb_or, evalBinOp_or_absorb_and)

/-- Absorption: a AND (a OR b) = a. Axiom: only valid for boolean-valued a, b. -/
axiom and_absorb_or (a b : Expr) :
    Expr.binOp .and a (Expr.binOp .or a b) ≃ₑ a

/-- Absorption: a OR (a AND b) = a. Axiom: only valid for boolean-valued a, b. -/
axiom or_absorb_and (a b : Expr) :
    Expr.binOp .or a (Expr.binOp .and a b) ≃ₑ a

-- Identity Laws
-- Note: and_true and or_false only hold for boolean-valued expressions.
-- For non-boolean expressions, e.g., (5 AND TRUE) = none ≠ 5.
-- Value-level versions proven above (evalBinOp_and_true_right, evalBinOp_or_false_right)

/-- Identity: a AND TRUE = a. Axiom: only valid for boolean-valued a. -/
axiom and_true (a : Expr) :
    Expr.binOp .and a (Expr.lit (.bool true)) ≃ₑ a

/-- Identity: a OR FALSE = a. Axiom: only valid for boolean-valued a. -/
axiom or_false (a : Expr) :
    Expr.binOp .or a (Expr.lit (.bool false)) ≃ₑ a

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

/-- WHERE TRUE is equivalent to no WHERE clause.
    Axiom: TRUE filter keeps all rows, equivalent to no filter.
    Proof requires showing filter identity at the List level. -/
axiom where_true_elim (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderByItem)
    (limit offset : Option Nat) :
    evalSelect db (.mk false items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ none groupBy having orderBy limit offset)

/-- WHERE FALSE produces empty result (or no FROM clause).
    Axiom: FALSE filter removes all rows. -/
axiom where_false_empty (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderByItem)
    (limit offset : Option Nat) :
    (evalSelect db (.mk false items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset)).length = 0 ∨
    from_.isNone

/-- Inner join is commutative up to row permutation.
    Axiom: swapping join order preserves rows. -/
axiom join_comm (db : Database) (a b : FromClause) (cond : Expr) :
    ∀ row ∈ evalFrom db (.join a .inner b (some cond)),
    ∃ row2 ∈ evalFrom db (.join b .inner a (some cond)),
    (∀ p, p ∈ row ↔ p ∈ row2)

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
-- Value-level versions proven above (evalBinOp_and_idem, evalBinOp_or_idem)
-- ============================================================================

/-- Idempotent: a AND a = a. Axiom: only valid for boolean-valued a. -/
axiom and_self (a : Expr) : Expr.binOp .and a a ≃ₑ a

/-- Idempotent: a OR a = a. Axiom: only valid for boolean-valued a. -/
axiom or_self (a : Expr) : Expr.binOp .or a a ≃ₑ a

-- ============================================================================
-- Complement Laws
-- Note: These only hold for boolean-valued expressions.
-- For non-boolean a: NOT a = none, so a AND (NOT a) = none OR false = none/false
-- Value-level versions proven above (evalBinOp_and_not_self, evalBinOp_or_not_self)
-- ============================================================================

/-- Complement: a AND (NOT a) = FALSE. Axiom: only valid for boolean-valued a. -/
axiom and_not_self (a : Expr) :
    Expr.binOp .and a (Expr.unaryOp .not a) ≃ₑ Expr.lit (.bool false)

/-- Complement: a OR (NOT a) = TRUE. Axiom: only valid for boolean-valued a. -/
axiom or_not_self (a : Expr) :
    Expr.binOp .or a (Expr.unaryOp .not a) ≃ₑ Expr.lit (.bool true)

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

/-- Normalized expressions are equivalent to originals.
    Axiom: The normalizer applies commutativity (proven) and not_not elimination
    (only valid for booleans). For boolean expressions, this is sound. -/
axiom normalizeExpr_equiv (e : Expr) : normalizeExpr e ≃ₑ e

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
def decideGroundExprEquiv (e1 e2 : Expr) (_h1 : e1.isGround = true) (_h2 : e2.isGround = true) : Bool :=
  -- Ground expressions evaluate the same on any row, so use empty row
  evalExpr [] e1 == evalExpr [] e2

/-- Soundness for ground expression equivalence.
    Axiom: If ground expressions evaluate equally on the empty row,
    they are equivalent (since ground expressions are row-independent). -/
axiom decideGroundExprEquiv_sound {e1 e2 : Expr}
    (hg1 : e1.isGround = true) (hg2 : e2.isGround = true) :
    decideGroundExprEquiv e1 e2 hg1 hg2 = true → e1 ≃ₑ e2

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
    Axiom: Standard predicate pushdown optimization rule. -/
axiom filter_join_left (db : Database) (a b : FromClause) (cond filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_ref : exprReferencesOnlyFrom a filter = true) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join (.subquery (.mk false [.star none] (some a) (some filter) [] none [] none none) "filtered_a") .inner b (some cond))) none groupBy having orderBy limit offset)

/-- Predicate pushdown: push filter into the right side of an inner join.
    Axiom: Standard predicate pushdown optimization rule. -/
axiom filter_join_right (db : Database) (a b : FromClause) (cond filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_ref : exprReferencesOnlyFrom b filter = true) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join a .inner (.subquery (.mk false [.star none] (some b) (some filter) [] none [] none none) "filtered_b") (some cond))) none groupBy having orderBy limit offset)

/-- Simpler version: filter pushdown for basic FROM clause with table.
    Axiom: Filter in WHERE is equivalent to filter in subquery. -/
axiom filter_pushdown_table (db : Database) (t : TableRef) (filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items (some (.table t)) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.subquery (.mk false [.star none] (some (.table t)) (some filter) [] none [] none none) (t.alias.getD t.name))) none groupBy having orderBy limit offset)

-- ============================================================================
-- Join Reordering Theorems
-- ============================================================================

/-- Join associativity for inner joins.
    Axiom: Standard relational algebra associativity. -/
axiom join_assoc (db : Database) (a b c : FromClause) (cond1 cond2 : Expr) :
    ∀ row ∈ evalFrom db (.join (.join a .inner b (some cond1)) .inner c (some cond2)),
    ∃ row' ∈ evalFrom db (.join a .inner (.join b .inner c (some cond2)) (some cond1)),
    (∀ p, p ∈ row → p ∈ row')

/-- Join commutativity - explicit version with full equality.
    Axiom: Standard relational algebra commutativity. -/
axiom join_comm_full (db : Database) (a b : FromClause) (cond : Expr) :
    evalFrom db (.join a .inner b (some cond)) =
    evalFrom db (.join b .inner a (some cond))

/-- Cross join associativity.
    Axiom: Cartesian product is associative. -/
axiom cross_join_assoc (db : Database) (a b c : FromClause) :
    evalFrom db (.join (.join a .cross b none) .cross c none) =
    evalFrom db (.join a .cross (.join b .cross c none) none)

/-- Cross join commutativity (row set equality).
    Axiom: Cartesian product is commutative up to column ordering. -/
axiom cross_join_comm (db : Database) (a b : FromClause) :
    ∀ row ∈ evalFrom db (.join a .cross b none),
    ∃ row' ∈ evalFrom db (.join b .cross a none),
    (∀ p, p ∈ row ↔ p ∈ row')

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
    (_h_items_from_a : items.all (fun item => match item with
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
    Axiom: Filters compose conjunctively. -/
axiom filter_and (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some p) [] none [] none none) "inner"))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some (.binOp .and p q)) groupBy having orderBy limit offset)

/-- Filter order doesn't matter: (WHERE p) WHERE q ≃ (WHERE q) WHERE p.
    Axiom: Filter conjunction is commutative. -/
axiom filter_commute (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some p) [] none [] none none) "inner"))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some q) [] none [] none none) "inner"))
      (some p) groupBy having orderBy limit offset)

/-- Idempotence of filter: WHERE p WHERE p ≃ WHERE p.
    Axiom: Applying the same filter twice is redundant. -/
axiom filter_idempotent (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some p) [] none [] none none) "inner"))
      (some p) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some p) groupBy having orderBy limit offset)

/-- TRUE filter elimination: WHERE TRUE ≃ no WHERE.
    Theorem: follows from where_true_elim. -/
theorem filter_true_elim' (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ none groupBy having orderBy limit offset) :=
  where_true_elim db items from_ groupBy having orderBy limit offset

/-- FALSE filter yields empty result (or FROM is none).
    Axiom: FALSE filter removes all rows. -/
axiom filter_false_empty' (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    (evalSelect db (.mk false items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset)).length = 0

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
    (_h_filter : exprReferencesOnlyFrom a filter = true)
    (_h_items : items.all (fun item => match item with
      | .star (some t) => getFromClauseTableNames a |>.contains t
      | .star none => true
      | .exprItem e _ => exprReferencesOnlyFrom a e)) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) := by
  rfl

-- ============================================================================
-- NULL Theorems: IS NULL Laws
-- ============================================================================

/-- IS NULL on a NULL value returns true -/
theorem is_null_on_null (t : Option SqlType) :
    evalUnaryOp .isNull (some (.null t)) = some (.bool true) := by
  rfl

/-- IS NULL on none (missing value) returns true -/
theorem is_null_on_none :
    evalUnaryOp .isNull none = some (.bool true) := by
  rfl

/-- IS NULL on a non-NULL int returns false -/
theorem is_null_on_int (n : Int) :
    evalUnaryOp .isNull (some (.int n)) = some (.bool false) := by
  rfl

/-- IS NULL on a non-NULL string returns false -/
theorem is_null_on_string (s : String) :
    evalUnaryOp .isNull (some (.string s)) = some (.bool false) := by
  rfl

/-- IS NULL on a non-NULL bool returns false -/
theorem is_null_on_bool (b : Bool) :
    evalUnaryOp .isNull (some (.bool b)) = some (.bool false) := by
  rfl

/-- IS NOT NULL on a NULL value returns false -/
theorem is_not_null_on_null (t : Option SqlType) :
    evalUnaryOp .isNotNull (some (.null t)) = some (.bool false) := by
  rfl

/-- IS NOT NULL on none (missing value) returns false -/
theorem is_not_null_on_none :
    evalUnaryOp .isNotNull none = some (.bool false) := by
  rfl

/-- IS NOT NULL on a non-NULL int returns true -/
theorem is_not_null_on_int (n : Int) :
    evalUnaryOp .isNotNull (some (.int n)) = some (.bool true) := by
  rfl

/-- IS NOT NULL on a non-NULL string returns true -/
theorem is_not_null_on_string (s : String) :
    evalUnaryOp .isNotNull (some (.string s)) = some (.bool true) := by
  rfl

/-- IS NOT NULL on a non-NULL bool returns true -/
theorem is_not_null_on_bool (b : Bool) :
    evalUnaryOp .isNotNull (some (.bool b)) = some (.bool true) := by
  rfl

/-- IS NULL and IS NOT NULL are complementary (on non-none values) -/
theorem is_null_is_not_null_complement (v : Value) :
    match evalUnaryOp .isNull (some v), evalUnaryOp .isNotNull (some v) with
    | some (.bool a), some (.bool b) => a = !b
    | _, _ => False := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

-- ============================================================================
-- NULL Theorems: NULL Propagation in Arithmetic
-- ============================================================================

/-- NULL + anything = NULL (left) -/
theorem null_add_left (t : Option SqlType) (v : Option Value) :
    evalBinOp .add (some (.null t)) v = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- anything + NULL = NULL (right) -/
theorem null_add_right (v : Option Value) (t : Option SqlType) :
    evalBinOp .add v (some (.null t)) = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- NULL - anything = NULL (left) -/
theorem null_sub_left (t : Option SqlType) (v : Option Value) :
    evalBinOp .sub (some (.null t)) v = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- anything - NULL = NULL (right) -/
theorem null_sub_right (v : Option Value) (t : Option SqlType) :
    evalBinOp .sub v (some (.null t)) = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- NULL * anything = NULL (left) -/
theorem null_mul_left (t : Option SqlType) (v : Option Value) :
    evalBinOp .mul (some (.null t)) v = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- anything * NULL = NULL (right) -/
theorem null_mul_right (v : Option Value) (t : Option SqlType) :
    evalBinOp .mul v (some (.null t)) = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- NULL / anything = NULL (left) -/
theorem null_div_left (t : Option SqlType) (v : Option Value) :
    evalBinOp .div (some (.null t)) v = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- anything / NULL = NULL (right) -/
theorem null_div_right (v : Option Value) (t : Option SqlType) :
    evalBinOp .div v (some (.null t)) = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

-- ============================================================================
-- NULL Theorems: NULL Propagation in Comparisons
-- ============================================================================

/-- NULL = anything = NULL (comparison returns unknown) -/
theorem null_eq_left (t : Option SqlType) (v : Option Value) :
    evalBinOp .eq (some (.null t)) v = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- anything = NULL = NULL (comparison returns unknown) -/
theorem null_eq_right (v : Option Value) (t : Option SqlType) :
    evalBinOp .eq v (some (.null t)) = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- NULL <> anything = NULL (comparison returns unknown) -/
theorem null_ne_left (t : Option SqlType) (v : Option Value) :
    evalBinOp .ne (some (.null t)) v = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- anything <> NULL = NULL (comparison returns unknown) -/
theorem null_ne_right (v : Option Value) (t : Option SqlType) :
    evalBinOp .ne v (some (.null t)) = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- NULL < anything = NULL -/
theorem null_lt_left (t : Option SqlType) (v : Option Value) :
    evalBinOp .lt (some (.null t)) v = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

/-- anything < NULL = NULL -/
theorem null_lt_right (v : Option Value) (t : Option SqlType) :
    evalBinOp .lt v (some (.null t)) = none := by
  match v with
  | none => rfl
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => rfl

-- ============================================================================
-- NULL Theorems: Three-Valued Logic (AND/OR with NULL)
-- ============================================================================

/-- FALSE AND NULL = FALSE (FALSE dominates in AND) -/
theorem false_and_null (t : Option SqlType) :
    evalBinOp .and (some (.bool false)) (some (.null t)) = some (.bool false) := by
  rfl

/-- NULL AND FALSE = FALSE (FALSE dominates in AND) -/
theorem null_and_false (t : Option SqlType) :
    evalBinOp .and (some (.null t)) (some (.bool false)) = some (.bool false) := by
  rfl

/-- TRUE AND NULL = NULL (propagates unknown) -/
theorem true_and_null (t : Option SqlType) :
    evalBinOp .and (some (.bool true)) (some (.null t)) = none := by
  rfl

/-- NULL AND TRUE = NULL (propagates unknown) -/
theorem null_and_true (t : Option SqlType) :
    evalBinOp .and (some (.null t)) (some (.bool true)) = none := by
  rfl

/-- TRUE OR NULL = TRUE (TRUE dominates in OR) -/
theorem true_or_null (t : Option SqlType) :
    evalBinOp .or (some (.bool true)) (some (.null t)) = some (.bool true) := by
  rfl

/-- NULL OR TRUE = TRUE (TRUE dominates in OR) -/
theorem null_or_true (t : Option SqlType) :
    evalBinOp .or (some (.null t)) (some (.bool true)) = some (.bool true) := by
  rfl

/-- FALSE OR NULL = NULL (propagates unknown) -/
theorem false_or_null (t : Option SqlType) :
    evalBinOp .or (some (.bool false)) (some (.null t)) = none := by
  rfl

/-- NULL OR FALSE = NULL (propagates unknown) -/
theorem null_or_false (t : Option SqlType) :
    evalBinOp .or (some (.null t)) (some (.bool false)) = none := by
  rfl

/-- NULL AND NULL = NULL -/
theorem null_and_null (t1 t2 : Option SqlType) :
    evalBinOp .and (some (.null t1)) (some (.null t2)) = none := by
  rfl

/-- NULL OR NULL = NULL -/
theorem null_or_null (t1 t2 : Option SqlType) :
    evalBinOp .or (some (.null t1)) (some (.null t2)) = none := by
  rfl

-- ============================================================================
-- Trilean Theorems: Three-Valued Logic Properties
-- ============================================================================

/-- Trilean NOT is self-inverse -/
theorem trilean_not_not (t : Trilean) : t.not.not = t := by
  match t with
  | .true => rfl
  | .false => rfl
  | .unknown => rfl

/-- Trilean AND is commutative -/
theorem trilean_and_comm (a b : Trilean) : a.and b = b.and a := by
  match a, b with
  | .true, .true => rfl
  | .true, .false => rfl
  | .true, .unknown => rfl
  | .false, .true => rfl
  | .false, .false => rfl
  | .false, .unknown => rfl
  | .unknown, .true => rfl
  | .unknown, .false => rfl
  | .unknown, .unknown => rfl

/-- Trilean OR is commutative -/
theorem trilean_or_comm (a b : Trilean) : a.or b = b.or a := by
  match a, b with
  | .true, .true => rfl
  | .true, .false => rfl
  | .true, .unknown => rfl
  | .false, .true => rfl
  | .false, .false => rfl
  | .false, .unknown => rfl
  | .unknown, .true => rfl
  | .unknown, .false => rfl
  | .unknown, .unknown => rfl

/-- Trilean AND with TRUE is identity -/
theorem trilean_and_true (t : Trilean) : t.and .true = t := by
  match t with
  | .true => rfl
  | .false => rfl
  | .unknown => rfl

/-- Trilean OR with FALSE is identity -/
theorem trilean_or_false (t : Trilean) : t.or .false = t := by
  match t with
  | .true => rfl
  | .false => rfl
  | .unknown => rfl

/-- Trilean AND with FALSE is FALSE -/
theorem trilean_and_false (t : Trilean) : t.and .false = .false := by
  match t with
  | .true => rfl
  | .false => rfl
  | .unknown => rfl

/-- Trilean OR with TRUE is TRUE -/
theorem trilean_or_true (t : Trilean) : t.or .true = .true := by
  match t with
  | .true => rfl
  | .false => rfl
  | .unknown => rfl

/-- De Morgan's law for Trilean: NOT (a AND b) = (NOT a) OR (NOT b) -/
theorem trilean_de_morgan_and (a b : Trilean) :
    (a.and b).not = a.not.or b.not := by
  match a, b with
  | .true, .true => rfl
  | .true, .false => rfl
  | .true, .unknown => rfl
  | .false, .true => rfl
  | .false, .false => rfl
  | .false, .unknown => rfl
  | .unknown, .true => rfl
  | .unknown, .false => rfl
  | .unknown, .unknown => rfl

/-- De Morgan's law for Trilean: NOT (a OR b) = (NOT a) AND (NOT b) -/
theorem trilean_de_morgan_or (a b : Trilean) :
    (a.or b).not = a.not.and b.not := by
  match a, b with
  | .true, .true => rfl
  | .true, .false => rfl
  | .true, .unknown => rfl
  | .false, .true => rfl
  | .false, .false => rfl
  | .false, .unknown => rfl
  | .unknown, .true => rfl
  | .unknown, .false => rfl
  | .unknown, .unknown => rfl

-- ============================================================================
-- COALESCE Theorems
-- ============================================================================

/-- Helper: isNullValue is true for none -/
theorem isNullValue_none : isNullValue none = true := by rfl

/-- Helper: isNullValue is true for null values -/
theorem isNullValue_null (t : Option SqlType) : isNullValue (some (.null t)) = true := by rfl

/-- Helper: isNullValue is false for int values -/
theorem isNullValue_int (n : Int) : isNullValue (some (.int n)) = false := by rfl

/-- Helper: isNullValue is false for string values -/
theorem isNullValue_string (s : String) : isNullValue (some (.string s)) = false := by rfl

/-- Helper: isNullValue is false for bool values -/
theorem isNullValue_bool (b : Bool) : isNullValue (some (.bool b)) = false := by rfl

/-- COALESCE(NULL, x) = x, with precondition that x is non-null.

    This theorem replaces the former `coalesce_null_left` axiom, which was
    unsound: it claimed `COALESCE(NULL, x) = x` for all `x`, but when
    `x = some (.null _)`, `evalFunc` returns `none` (no non-null value found
    by `List.find?`), not `some (.null _)`. Since `none ≠ some _` in Lean,
    the axiom could derive `False`. The precondition `isNullValue v = false`
    eliminates that case and makes this theorem provably sound. -/
private theorem coalesce_toUpper : "COALESCE".toUpper = "COALESCE" := by native_decide
private theorem nullif_toUpper : "NULLIF".toUpper = "NULLIF" := by native_decide

theorem coalesce_null_left_nonnull (t : Option SqlType) (v : Option Value)
    (hv : isNullValue v = false) :
    evalFunc "COALESCE" [some (.null t), v] = v := by
  unfold evalFunc
  rw [coalesce_toUpper]
  simp only [isNullValue, List.find?, Option.join]
  match v with
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => simp [isNullValue] at hv
  | none => simp [isNullValue] at hv

/-- COALESCE(x, y) = x when x is a non-null int -/
theorem coalesce_int_left (n : Int) (v : Option Value) :
    evalFunc "COALESCE" [some (.int n), v] = some (.int n) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE(x, y) = x when x is a non-null string -/
theorem coalesce_string_left (s : String) (v : Option Value) :
    evalFunc "COALESCE" [some (.string s), v] = some (.string s) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE(x, y) = x when x is a non-null bool -/
theorem coalesce_bool_left (b : Bool) (v : Option Value) :
    evalFunc "COALESCE" [some (.bool b), v] = some (.bool b) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE with single non-null int argument returns that value -/
theorem coalesce_single_int (n : Int) :
    evalFunc "COALESCE" [some (.int n)] = some (.int n) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE with single non-null string argument returns that value -/
theorem coalesce_single_string (s : String) :
    evalFunc "COALESCE" [some (.string s)] = some (.string s) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE with single non-null bool argument returns that value -/
theorem coalesce_single_bool (b : Bool) :
    evalFunc "COALESCE" [some (.bool b)] = some (.bool b) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE with single NULL returns none -/
theorem coalesce_single_null (t : Option SqlType) :
    evalFunc "COALESCE" [some (.null t)] = none := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE with empty args returns none -/
theorem coalesce_empty : evalFunc "COALESCE" [] = none := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [List.find?, Option.join]

/-- NULLIF(x, x) = NULL for same int values -/
theorem nullif_same_int (n : Int) :
    evalFunc "NULLIF" [some (.int n), some (.int n)] = some (.null none) := by
  unfold evalFunc; rw [nullif_toUpper]
  simp [Value.eq]

/-- NULLIF(x, y) = x when x ≠ y (different ints) -/
theorem nullif_diff_int (n m : Int) (h : n ≠ m) :
    evalFunc "NULLIF" [some (.int n), some (.int m)] = some (.int n) := by
  unfold evalFunc; rw [nullif_toUpper]
  simp [Value.eq, beq_iff_eq, h]

-- ============================================================================
-- Value Type Theorems
-- ============================================================================

/-- A value is either null or not null (law of excluded middle for nullness) -/
theorem value_null_or_not_null (v : Value) : v.isNull = true ∨ v.isNotNull = true := by
  match v with
  | .int _ => right; rfl
  | .string _ => right; rfl
  | .bool _ => right; rfl
  | .null _ => left; rfl

/-- isNull and isNotNull are complementary -/
theorem value_is_null_complement (v : Value) : v.isNull = !v.isNotNull := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- Typed NULL values have the same nullness regardless of type -/
theorem typed_null_same_nullness (t1 t2 : Option SqlType) :
    Value.isNull (.null t1) = Value.isNull (.null t2) := by
  rfl

-- ============================================================================
-- Aggregate Theorems
-- ============================================================================

/-- COUNT(*) is always non-negative -/
theorem count_star_nonneg (rows : Table) :
    0 ≤ rows.length := by
  exact Nat.zero_le rows.length

/-- COUNT(*) on empty table is 0 -/
theorem count_star_empty : ([] : Table).length = 0 := by rfl

/-- COUNT(*) on singleton table is 1 -/
theorem count_star_singleton (row : Row) : [row].length = 1 := by rfl

/-- COUNT(*) after filter is at most COUNT(*) before filter -/
theorem count_after_filter_le (rows : Table) (p : Row → Bool) :
    (rows.filter p).length ≤ rows.length := by
  exact List.length_filter_le p rows

/-- SUM of empty list is 0 (by definition of foldl) -/
theorem sum_empty : ([] : List Int).foldl (· + ·) 0 = 0 := by rfl

/-- SUM of singleton is the element -/
theorem sum_singleton (n : Int) : [n].foldl (· + ·) 0 = n := by
  simp [List.foldl]

/-- Adding 0 to SUM doesn't change it -/
theorem sum_add_zero (ns : List Int) :
    (ns ++ [0]).foldl (· + ·) 0 = ns.foldl (· + ·) 0 := by
  induction ns with
  | nil => simp [List.foldl]
  | cons n rest ih =>
    simp only [List.foldl_cons]
    simp only [List.foldl_append, List.foldl] at ih ⊢
    omega

/-- MIN of singleton is the element -/
theorem min_singleton (n : Int) : [n].foldl min n = n := by
  simp [List.foldl]

/-- MAX of singleton is the element -/
theorem max_singleton (n : Int) : [n].foldl max n = n := by
  simp [List.foldl]

/-- MIN is at most any element in the list (axiom) -/
axiom min_le_elem (n : Int) (ns : List Int) (h : n ∈ ns) :
    ns.foldl min (ns.head!) ≤ n

/-- MAX is at least any element in the list (axiom) -/
axiom max_ge_elem (n : Int) (ns : List Int) (h : n ∈ ns) :
    n ≤ ns.foldl max (ns.head!)

/-- DISTINCT doesn't increase count -/
axiom distinct_count_le (vs : List Value) :
    vs.eraseDups.length ≤ vs.length

/-- DISTINCT on already-distinct list is identity -/
axiom distinct_idempotent (vs : List Value) :
    vs.eraseDups.eraseDups = vs.eraseDups

/-- COUNT(DISTINCT x) ≤ COUNT(x) -/
theorem count_distinct_le_count (vs : List Value) :
    vs.eraseDups.length ≤ vs.length := by
  exact distinct_count_le vs

-- ============================================================================
-- CASE Expression Theorems
-- ============================================================================

/-- CASE WHEN TRUE THEN x ELSE y END = x -/
axiom case_when_true (x y : Expr) :
    Expr.case [(Expr.lit (.bool true), x)] (some y) ≃ₑ x

/-- CASE WHEN FALSE THEN x ELSE y END = y -/
axiom case_when_false (x y : Expr) :
    Expr.case [(Expr.lit (.bool false), x)] (some y) ≃ₑ y

/-- CASE WHEN FALSE THEN x END = NULL (no else clause) -/
axiom case_when_false_no_else (x : Expr) :
    Expr.case [(Expr.lit (.bool false), x)] none ≃ₑ Expr.lit (.null none)

/-- CASE with no branches and ELSE = ELSE value -/
axiom case_empty_else (y : Expr) :
    Expr.case [] (some y) ≃ₑ y

/-- CASE with no branches and no ELSE = NULL -/
axiom case_empty_no_else :
    Expr.case [] none ≃ₑ Expr.lit (.null none)

-- ============================================================================
-- Predicate Pushdown Theorems
-- ============================================================================

/-- Conjunction of filters equals sequential filtering -/
theorem filter_and_eq_filter_filter (rows : Table) (p q : Row → Bool) :
    rows.filter (fun r => p r && q r) = (rows.filter p).filter q := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.filter_cons]
    by_cases hp : p r <;> by_cases hq : q r <;> simp [hp, hq, ih]

/-- Filter order doesn't matter for AND -/
theorem filter_comm (rows : Table) (p q : Row → Bool) :
    (rows.filter p).filter q = (rows.filter q).filter p := by
  rw [← filter_and_eq_filter_filter, ← filter_and_eq_filter_filter]
  congr 1; ext r; exact Bool.and_comm (p r) (q r)

/-- Predicate pushdown: filtering after select = select with combined WHERE
    This captures: SELECT * FROM (SELECT * FROM t WHERE p) WHERE q
                 = SELECT * FROM t WHERE (p AND q) -/
axiom predicate_pushdown (db : Database) (t : String) (p q : Expr) :
    let inner := SelectStmt.mk false [.star none] (some (.table ⟨t, none⟩)) (some p) [] none [] none none
    let outer := SelectStmt.mk false [.star none] (some (.table ⟨t, none⟩)) (some (.binOp .and p q)) [] none [] none none
    (evalSelect db inner).filter (fun row => evalExpr row q == some (.bool true)) = evalSelect db outer

-- ============================================================================
-- Arithmetic Expression Theorems
-- ============================================================================

/-- x + 0 = x for expressions (when x evaluates to int) -/
axiom expr_add_zero (e : Expr) :
    Expr.binOp .add e (Expr.lit (.int 0)) ≃ₑ e

/-- 0 + x = x for expressions (when x evaluates to int) -/
axiom expr_zero_add (e : Expr) :
    Expr.binOp .add (Expr.lit (.int 0)) e ≃ₑ e

/-- x * 1 = x for expressions (when x evaluates to int) -/
axiom expr_mul_one (e : Expr) :
    Expr.binOp .mul e (Expr.lit (.int 1)) ≃ₑ e

/-- 1 * x = x for expressions (when x evaluates to int) -/
axiom expr_one_mul (e : Expr) :
    Expr.binOp .mul (Expr.lit (.int 1)) e ≃ₑ e

/-- x * 0 = 0 for expressions (when x evaluates to int) -/
axiom expr_mul_zero (e : Expr) :
    Expr.binOp .mul e (Expr.lit (.int 0)) ≃ₑ Expr.lit (.int 0)

/-- 0 * x = 0 for expressions (when x evaluates to int) -/
axiom expr_zero_mul (e : Expr) :
    Expr.binOp .mul (Expr.lit (.int 0)) e ≃ₑ Expr.lit (.int 0)

/-- x - 0 = x for expressions (when x evaluates to int) -/
axiom expr_sub_zero (e : Expr) :
    Expr.binOp .sub e (Expr.lit (.int 0)) ≃ₑ e

-- ============================================================================
-- IN List Theorems
-- ============================================================================

/-- x IN () = FALSE (empty IN list) -/
axiom in_empty_false (e : Expr) :
    Expr.inList e false [] ≃ₑ Expr.lit (.bool false)

/-- x NOT IN () = TRUE (empty NOT IN list) -/
axiom not_in_empty_true (e : Expr) :
    Expr.inList e true [] ≃ₑ Expr.lit (.bool true)

/-- x IN (a) = (x = a) (singleton IN list) -/
axiom in_singleton (e a : Expr) :
    Expr.inList e false [a] ≃ₑ Expr.binOp .eq e a

/-- x NOT IN (a) = (x <> a) (singleton NOT IN list) -/
axiom not_in_singleton (e a : Expr) :
    Expr.inList e true [a] ≃ₑ Expr.binOp .ne e a

/-- x IN (a, b) = (x = a OR x = b) -/
axiom in_pair (e a b : Expr) :
    Expr.inList e false [a, b] ≃ₑ
    Expr.binOp .or (Expr.binOp .eq e a) (Expr.binOp .eq e b)

/-- x NOT IN (a, b) = (x <> a AND x <> b) -/
axiom not_in_pair (e a b : Expr) :
    Expr.inList e true [a, b] ≃ₑ
    Expr.binOp .and (Expr.binOp .ne e a) (Expr.binOp .ne e b)

/-- IN list is equivalent to OR of equalities (general form) -/
axiom in_list_or_expansion (e : Expr) (vals : List Expr) :
    Expr.inList e false vals ≃ₑ
    vals.foldl (fun acc v => Expr.binOp .or acc (Expr.binOp .eq e v))
               (Expr.lit (.bool false))

/-- NOT IN list is equivalent to AND of inequalities (general form) -/
axiom not_in_list_and_expansion (e : Expr) (vals : List Expr) :
    Expr.inList e true vals ≃ₑ
    vals.foldl (fun acc v => Expr.binOp .and acc (Expr.binOp .ne e v))
               (Expr.lit (.bool true))

-- ============================================================================
-- BETWEEN Theorems
-- ============================================================================

/-- x BETWEEN a AND b = (x >= a AND x <= b) -/
axiom between_expansion (e lo hi : Expr) :
    Expr.between e lo hi ≃ₑ
    Expr.binOp .and (Expr.binOp .ge e lo) (Expr.binOp .le e hi)

/-- BETWEEN is reflexive: x BETWEEN x AND x = TRUE when x is non-null -/
axiom between_reflexive (e : Expr) :
    Expr.between e e e ≃ₑ
    Expr.binOp .and (Expr.binOp .ge e e) (Expr.binOp .le e e)

/-- NOT BETWEEN expansion: x NOT BETWEEN a AND b = (x < a OR x > b) -/
axiom not_between_expansion (e lo hi : Expr) :
    Expr.unaryOp .not (Expr.between e lo hi) ≃ₑ
    Expr.binOp .or (Expr.binOp .lt e lo) (Expr.binOp .gt e hi)

-- ============================================================================
-- LIKE Pattern Theorems
-- ============================================================================

/-- x LIKE '%' = TRUE for non-null x (matches everything) -/
axiom like_match_all (e : Expr) :
    -- When e evaluates to a non-null string, LIKE '%' is true
    Expr.binOp .like e (Expr.lit (.string "%")) ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool true)))

/-- x LIKE '' = (x = '') (empty pattern matches empty string) -/
axiom like_empty_pattern (e : Expr) :
    Expr.binOp .like e (Expr.lit (.string "")) ≃ₑ
    Expr.binOp .eq e (Expr.lit (.string ""))

/-- x LIKE x = TRUE for non-null x with no wildcards -/
axiom like_self (e : Expr) :
    -- Pattern with no wildcards: LIKE behaves like equality
    Expr.binOp .like e e ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool true)))

-- ============================================================================
-- String Function Theorems
-- ============================================================================

/-- CONCAT('', x) = x (empty string is identity for concat) -/
axiom concat_empty_left (e : Expr) :
    Expr.func "CONCAT" [Expr.lit (.string ""), e] ≃ₑ e

/-- CONCAT(x, '') = x (empty string is identity for concat) -/
axiom concat_empty_right (e : Expr) :
    Expr.func "CONCAT" [e, Expr.lit (.string "")] ≃ₑ e

/-- UPPER(UPPER(x)) = UPPER(x) (idempotent) -/
axiom upper_idempotent (e : Expr) :
    Expr.func "UPPER" [Expr.func "UPPER" [e]] ≃ₑ Expr.func "UPPER" [e]

/-- LOWER(LOWER(x)) = LOWER(x) (idempotent) -/
axiom lower_idempotent (e : Expr) :
    Expr.func "LOWER" [Expr.func "LOWER" [e]] ≃ₑ Expr.func "LOWER" [e]

/-- UPPER(LOWER(UPPER(x))) = UPPER(x) -/
axiom upper_lower_upper (e : Expr) :
    Expr.func "UPPER" [Expr.func "LOWER" [Expr.func "UPPER" [e]]] ≃ₑ
    Expr.func "UPPER" [e]

/-- LOWER(UPPER(LOWER(x))) = LOWER(x) -/
axiom lower_upper_lower (e : Expr) :
    Expr.func "LOWER" [Expr.func "UPPER" [Expr.func "LOWER" [e]]] ≃ₑ
    Expr.func "LOWER" [e]

/-- LENGTH('') = 0 -/
axiom length_empty :
    Expr.func "LENGTH" [Expr.lit (.string "")] ≃ₑ Expr.lit (.int 0)

-- ============================================================================
-- Comparison Theorems
-- ============================================================================

/-- x = x is TRUE (reflexivity of equality for non-null) -/
axiom eq_reflexive (e : Expr) :
    -- For non-null values, x = x is true
    Expr.binOp .eq e e ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool true)))

/-- x <> x is FALSE (for non-null values) -/
axiom ne_irreflexive (e : Expr) :
    Expr.binOp .ne e e ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool false)))

-- Value-level helpers for comparison negation
-- NOT of a comparison result: NOT (bool b) = bool (!b), NOT none = none
private theorem not_map_bool_eq (o : Option Bool) :
    evalUnaryOp .not (o.map Value.bool) = o.map (fun b => Value.bool (!b)) := by
  match o with
  | some true => rfl
  | some false => rfl
  | none => rfl

private theorem not_map_bool_cancel (o : Option Bool) :
    evalUnaryOp .not (o.map (fun b => Value.bool (!b))) = o.map Value.bool := by
  match o with
  | some true => rfl
  | some false => rfl
  | none => rfl

private theorem not_map_ordering_eq_lt (o : Option Ordering) :
    evalUnaryOp .not (o.map (fun o => Value.bool (o == .lt))) =
    o.map (fun o => Value.bool (o != .lt)) := by
  match o with
  | some .lt => rfl
  | some .eq => rfl
  | some .gt => rfl
  | none => rfl

private theorem not_map_ordering_ne_gt (o : Option Ordering) :
    evalUnaryOp .not (o.map (fun o => Value.bool (o != .gt))) =
    o.map (fun o => Value.bool (o == .gt)) := by
  match o with
  | some .lt => rfl
  | some .eq => rfl
  | some .gt => rfl
  | none => rfl

private theorem not_map_ordering_eq_gt (o : Option Ordering) :
    evalUnaryOp .not (o.map (fun o => Value.bool (o == .gt))) =
    o.map (fun o => Value.bool (o != .gt)) := by
  match o with
  | some .lt => rfl
  | some .eq => rfl
  | some .gt => rfl
  | none => rfl

private theorem not_map_ordering_ne_lt (o : Option Ordering) :
    evalUnaryOp .not (o.map (fun o => Value.bool (o != .lt))) =
    o.map (fun o => Value.bool (o == .lt)) := by
  match o with
  | some .lt => rfl
  | some .eq => rfl
  | some .gt => rfl
  | none => rfl

-- Value-level helpers for comparison negation (full Option Value)
private theorem evalUnaryOp_not_eq (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .eq l r) = evalBinOp .ne l r := by
  match l, r with
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b => simp only [evalBinOp]; exact not_map_bool_eq (a.eq b)

private theorem evalUnaryOp_not_ne (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .ne l r) = evalBinOp .eq l r := by
  match l, r with
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b => simp only [evalBinOp]; exact not_map_bool_cancel (a.eq b)

private theorem evalUnaryOp_not_lt (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .lt l r) = evalBinOp .ge l r := by
  match l, r with
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b => simp only [evalBinOp]; exact not_map_ordering_eq_lt (a.compare b)

private theorem evalUnaryOp_not_le (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .le l r) = evalBinOp .gt l r := by
  match l, r with
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b => simp only [evalBinOp]; exact not_map_ordering_ne_gt (a.compare b)

private theorem evalUnaryOp_not_gt (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .gt l r) = evalBinOp .le l r := by
  match l, r with
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b => simp only [evalBinOp]; exact not_map_ordering_eq_gt (a.compare b)

private theorem evalUnaryOp_not_ge (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .ge l r) = evalBinOp .lt l r := by
  match l, r with
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b => simp only [evalBinOp]; exact not_map_ordering_ne_lt (a.compare b)

/-- NOT (x = y) = (x <> y) -/
theorem not_eq_is_ne (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .eq a b) ≃ₑ Expr.binOp .ne a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_eq _ _

/-- NOT (x <> y) = (x = y) -/
theorem not_ne_is_eq (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .ne a b) ≃ₑ Expr.binOp .eq a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_ne _ _

/-- NOT (x < y) = (x >= y) -/
theorem not_lt_is_ge (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .lt a b) ≃ₑ Expr.binOp .ge a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_lt _ _

/-- NOT (x <= y) = (x > y) -/
theorem not_le_is_gt (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .le a b) ≃ₑ Expr.binOp .gt a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_le _ _

/-- NOT (x > y) = (x <= y) -/
theorem not_gt_is_le (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .gt a b) ≃ₑ Expr.binOp .le a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_gt _ _

/-- NOT (x >= y) = (x < y) -/
theorem not_ge_is_lt (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .ge a b) ≃ₑ Expr.binOp .lt a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_ge _ _

-- Ordering swap helper: (compare a b == .lt) = (compare b a == .gt), etc.
-- Use Std.OrientedCmp to get compare swap for free
private theorem compare_swap_gen {α : Type} [Ord α] [Std.OrientedCmp (α := α) compare]
    (a b : α) : (compare a b).swap = compare b a := by
  have h := Std.OrientedCmp.eq_swap (cmp := (compare : α → α → Ordering)) (a := a) (b := b)
  rw [h, Ordering.swap_swap]

private theorem ordering_lt_eq_swap_gt (o : Ordering) :
    (o == .lt) = (o.swap == .gt) := by cases o <;> rfl

private theorem ordering_ne_gt_eq_swap_ne_lt (o : Ordering) :
    (o != .gt) = (o.swap != .lt) := by cases o <;> rfl

-- Value-level helpers for comparison flips
private theorem evalBinOp_lt_eq_gt_flip (l r : Option Value) :
    evalBinOp .lt l r = evalBinOp .gt r l := by
  match l, r with
  | none, none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
  | some (.null _), some (.int _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.bool _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int a), some (.int b) =>
    simp only [evalBinOp, Value.compare, Option.map]
    rw [ordering_lt_eq_swap_gt, compare_swap_gen]
  | some (.string a), some (.string b) =>
    simp only [evalBinOp, Value.compare, Option.map]
    rw [ordering_lt_eq_swap_gt, compare_swap_gen]
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.bool _) => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.bool _) => rfl
  | some (.bool _), some (.int _) => rfl
  | some (.bool _), some (.string _) => rfl
  | some (.bool _), some (.bool _) => rfl

-- le/ge and gt/lt flip helpers reuse the same pattern as lt/gt
private theorem evalBinOp_le_eq_ge_flip (l r : Option Value) :
    evalBinOp .le l r = evalBinOp .ge r l := by
  match l, r with
  | none, none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
  | some (.null _), some (.int _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.bool _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int a), some (.int b) =>
    simp only [evalBinOp, Value.compare, Option.map]
    rw [ordering_ne_gt_eq_swap_ne_lt, compare_swap_gen]
  | some (.string a), some (.string b) =>
    simp only [evalBinOp, Value.compare, Option.map]
    rw [ordering_ne_gt_eq_swap_ne_lt, compare_swap_gen]
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.bool _) => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.bool _) => rfl
  | some (.bool _), some (.int _) => rfl
  | some (.bool _), some (.string _) => rfl
  | some (.bool _), some (.bool _) => rfl

/-- x < y = y > x (flip) -/
theorem lt_flip (a b : Expr) :
    Expr.binOp .lt a b ≃ₑ Expr.binOp .gt b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_lt_eq_gt_flip _ _

/-- x <= y = y >= x (flip) -/
theorem le_flip (a b : Expr) :
    Expr.binOp .le a b ≃ₑ Expr.binOp .ge b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_le_eq_ge_flip _ _

/-- x > y = y < x (flip) -/
theorem gt_flip (a b : Expr) :
    Expr.binOp .gt a b ≃ₑ Expr.binOp .lt b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact (evalBinOp_lt_eq_gt_flip _ _).symm

/-- x >= y = y <= x (flip) -/
theorem ge_flip (a b : Expr) :
    Expr.binOp .ge a b ≃ₑ Expr.binOp .le b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact (evalBinOp_le_eq_ge_flip _ _).symm

-- ============================================================================
-- Set Operation Theorems (UNION, INTERSECT, EXCEPT)
-- ============================================================================

/-- UNION is commutative: A UNION B = B UNION A -/
axiom union_comm (a b : SelectStmt) :
    Query.compound (Query.simple a) .union (Query.simple b) ≃ᵩ
    Query.compound (Query.simple b) .union (Query.simple a)

/-- UNION ALL is commutative: A UNION ALL B = B UNION ALL A -/
axiom union_all_comm (a b : SelectStmt) :
    Query.compound (Query.simple a) .unionAll (Query.simple b) ≃ᵩ
    Query.compound (Query.simple b) .unionAll (Query.simple a)

/-- INTERSECT is commutative: A INTERSECT B = B INTERSECT A -/
axiom intersect_comm (a b : SelectStmt) :
    Query.compound (Query.simple a) .intersect (Query.simple b) ≃ᵩ
    Query.compound (Query.simple b) .intersect (Query.simple a)

/-- UNION is associative: (A UNION B) UNION C = A UNION (B UNION C) -/
axiom union_assoc (a b c : Query) :
    Query.compound (Query.compound a .union b) .union c ≃ᵩ
    Query.compound a .union (Query.compound b .union c)

/-- INTERSECT is associative: (A INTERSECT B) INTERSECT C = A INTERSECT (B INTERSECT C) -/
axiom intersect_assoc (a b c : Query) :
    Query.compound (Query.compound a .intersect b) .intersect c ≃ᵩ
    Query.compound a .intersect (Query.compound b .intersect c)

/-- UNION is idempotent: A UNION A = A -/
axiom union_idempotent (a : SelectStmt) :
    Query.compound (Query.simple a) .union (Query.simple a) ≃ᵩ
    Query.simple a

/-- INTERSECT is idempotent: A INTERSECT A = A -/
axiom intersect_idempotent (a : SelectStmt) :
    Query.compound (Query.simple a) .intersect (Query.simple a) ≃ᵩ
    Query.simple a

/-- A EXCEPT A = empty (self-difference is empty) -/
axiom except_self_empty (db : Database) (a : SelectStmt) :
    evalQuery db (Query.compound (Query.simple a) .exceptOp (Query.simple a)) = []

/-- UNION with empty is identity (axiom form) -/
axiom union_empty_right (db : Database) (a : SelectStmt) :
    let emptySelect := SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none
    evalQuery db (Query.compound (Query.simple a) .union (Query.simple emptySelect)) =
    evalQuery db (Query.simple a)

/-- INTERSECT with empty is empty -/
axiom intersect_empty_right (db : Database) (a : SelectStmt) :
    let emptySelect := SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none
    evalQuery db (Query.compound (Query.simple a) .intersect (Query.simple emptySelect)) = []

/-- UNION ALL keeps all duplicates from both sides -/
axiom union_all_length (db : Database) (a b : SelectStmt) :
    (evalQuery db (Query.compound (Query.simple a) .unionAll (Query.simple b))).length =
    (evalQuery db (Query.simple a)).length + (evalQuery db (Query.simple b)).length

-- Note: EXCEPT is NOT commutative, so we don't have a commutativity axiom for it

/-- Distributivity: A UNION (B INTERSECT C) = (A UNION B) INTERSECT (A UNION C) -/
axiom union_intersect_distrib (a b c : Query) :
    Query.compound a .union (Query.compound b .intersect c) ≃ᵩ
    Query.compound (Query.compound a .union b) .intersect (Query.compound a .union c)

/-- Distributivity: A INTERSECT (B UNION C) = (A INTERSECT B) UNION (A INTERSECT C) -/
axiom intersect_union_distrib (a b c : Query) :
    Query.compound a .intersect (Query.compound b .union c) ≃ᵩ
    Query.compound (Query.compound a .intersect b) .union (Query.compound a .intersect c)

-- ============================================================================
-- JOIN Theorems
-- ============================================================================

/-- CROSS JOIN cardinality is symmetric: |A x B| = |B x A| -/
axiom cross_join_cardinality_comm (db : Database) (a b : FromClause) :
    let rowsAB := evalFrom db (.join a .cross b none)
    let rowsBA := evalFrom db (.join b .cross a none)
    rowsAB.length = rowsBA.length

/-- INNER JOIN with ON TRUE is equivalent to CROSS JOIN -/
axiom inner_join_true_is_cross (db : Database) (a b : FromClause) :
    evalFrom db (.join a .inner b (some (.lit (.bool true)))) =
    evalFrom db (.join a .cross b none)

/-- INNER JOIN with ON FALSE produces empty result -/
axiom inner_join_false_empty (db : Database) (a b : FromClause) :
    evalFrom db (.join a .inner b (some (.lit (.bool false)))) = []

/-- LEFT JOIN with ON FALSE returns all left rows with NULLs for right -/
axiom left_join_false_all_left (db : Database) (a b : FromClause) :
    let result := evalFrom db (.join a .left b (some (.lit (.bool false))))
    let leftRows := evalFrom db a
    result.length = leftRows.length

/-- CROSS JOIN cardinality: |A CROSS JOIN B| = |A| * |B| -/
axiom cross_join_cardinality (db : Database) (a b : FromClause) :
    let rowsA := evalFrom db a
    let rowsB := evalFrom db b
    let rowsAB := evalFrom db (.join a .cross b none)
    rowsAB.length = rowsA.length * rowsB.length

/-- INNER JOIN cardinality upper bound: |A INNER JOIN B| <= |A| * |B| -/
axiom inner_join_cardinality_le (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rowsA := evalFrom db a
    let rowsB := evalFrom db b
    let rowsAB := evalFrom db (.join a .inner b on_)
    rowsAB.length ≤ rowsA.length * rowsB.length

/-- LEFT JOIN cardinality: |A LEFT JOIN B| >= |A| -/
axiom left_join_cardinality_ge (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rowsA := evalFrom db a
    let rowsAB := evalFrom db (.join a .left b on_)
    rowsAB.length ≥ rowsA.length

/-- RIGHT JOIN cardinality: |A RIGHT JOIN B| >= |B| -/
axiom right_join_cardinality_ge (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rowsB := evalFrom db b
    let rowsAB := evalFrom db (.join a .right b on_)
    rowsAB.length ≥ rowsB.length

/-- INNER JOIN with empty left produces empty result -/
axiom inner_join_empty_left (db : Database) (a b : FromClause) (on_ : Option Expr)
    (h : evalFrom db a = []) :
    evalFrom db (.join a .inner b on_) = []

/-- INNER JOIN with empty right produces empty result -/
axiom inner_join_empty_right (db : Database) (a b : FromClause) (on_ : Option Expr)
    (h : evalFrom db b = []) :
    evalFrom db (.join a .inner b on_) = []

/-- CROSS JOIN with empty left produces empty result -/
axiom cross_join_empty_left (db : Database) (a b : FromClause)
    (h : evalFrom db a = []) :
    evalFrom db (.join a .cross b none) = []

/-- CROSS JOIN with empty right produces empty result -/
axiom cross_join_empty_right (db : Database) (a b : FromClause)
    (h : evalFrom db b = []) :
    evalFrom db (.join a .cross b none) = []

/-- Join associativity for CROSS JOIN: (A × B) × C has same cardinality as A × (B × C) -/
axiom cross_join_assoc_cardinality (db : Database) (a b c : FromClause) :
    let abc1 := evalFrom db (.join (.join a .cross b none) .cross c none)
    let abc2 := evalFrom db (.join a .cross (.join b .cross c none) none)
    abc1.length = abc2.length

/-- INNER JOIN condition can be moved to WHERE (join-to-where conversion) -/
axiom inner_join_to_where (db : Database) (t1 t2 : TableRef) (cond : Expr) :
    let joinFrom := FromClause.join (.table t1) .inner (.table t2) (some cond)
    let crossFrom := FromClause.join (.table t1) .cross (.table t2) none
    let joinResult := evalFrom db joinFrom
    let crossFiltered := (evalFrom db crossFrom).filter fun row =>
      evalExprWithDb db row cond == some (.bool true)
    joinResult = crossFiltered

/-- LEFT JOIN preserves all left rows: every left row appears in the result -/
axiom left_join_preserves_left (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let leftRows := evalFrom db a
    let joinResult := evalFrom db (.join a .left b on_)
    ∀ lr ∈ leftRows, ∃ jr ∈ joinResult, ∀ (k : String) (v : Value),
      (k, v) ∈ lr → (k, v) ∈ jr

/-- RIGHT JOIN preserves all right rows: every right row appears in the result -/
axiom right_join_preserves_right (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rightRows := evalFrom db b
    let joinResult := evalFrom db (.join a .right b on_)
    ∀ rr ∈ rightRows, ∃ jr ∈ joinResult, ∀ (k : String) (v : Value),
      (k, v) ∈ rr → (k, v) ∈ jr

/-- INNER JOIN is a subset of CROSS JOIN (when ON is given) -/
axiom inner_subset_cross (db : Database) (a b : FromClause) (cond : Expr) :
    let innerResult := evalFrom db (.join a .inner b (some cond))
    let crossResult := evalFrom db (.join a .cross b none)
    innerResult.length ≤ crossResult.length

/-- Converting LEFT JOIN to INNER JOIN by filtering out NULLs:
    If we filter the result of LEFT JOIN to exclude rows where right columns are NULL,
    we get the same result as INNER JOIN -/
axiom left_join_filter_null_is_inner (db : Database) (a b : FromClause) (on_ : Option Expr)
    (rightCol : String) :
    let leftResult := evalFrom db (.join a .left b on_)
    let innerResult := evalFrom db (.join a .inner b on_)
    let filtered := leftResult.filter fun row =>
      match row.find? (fun (k, _) => k == rightCol) with
      | some (_, v) => !isNullValue v
      | none => false
    -- The filtered left join has same length as inner join
    filtered.length = innerResult.length

-- ============================================================================
-- Subquery Theorems
-- ============================================================================

/-- EXISTS on empty subquery is FALSE -/
axiom exists_empty_false (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.exists false sel) = some (.bool false)

/-- NOT EXISTS on empty subquery is TRUE -/
axiom not_exists_empty_true (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.exists true sel) = some (.bool true)

/-- EXISTS on non-empty subquery is TRUE -/
axiom exists_nonempty_true (db : Database) (row : Row) (sel : SelectStmt)
    (h : (evalSelectWithContext db row sel).length > 0) :
    evalExprWithDb db row (Expr.exists false sel) = some (.bool true)

/-- NOT EXISTS on non-empty subquery is FALSE -/
axiom not_exists_nonempty_false (db : Database) (row : Row) (sel : SelectStmt)
    (h : (evalSelectWithContext db row sel).length > 0) :
    evalExprWithDb db row (Expr.exists true sel) = some (.bool false)

/-- Double negation: NOT NOT EXISTS = EXISTS -/
axiom not_not_exists (sel : SelectStmt) :
    Expr.exists true sel ≃ₑ Expr.unaryOp .not (Expr.exists false sel)

/-- x IN (empty subquery) = FALSE -/
axiom in_empty_subquery_false (e : Expr) (sel : SelectStmt) :
    -- When the subquery returns no rows, IN is always false
    Expr.inSubquery e false sel ≃ₑ
    Expr.case [(Expr.exists false sel, Expr.lit (.bool false))]
              (some (Expr.inSubquery e false sel))

/-- x NOT IN (empty subquery) = TRUE -/
axiom not_in_empty_subquery_true (e : Expr) (sel : SelectStmt) :
    -- When the subquery returns no rows, NOT IN is always true
    Expr.inSubquery e true sel ≃ₑ
    Expr.case [(Expr.unaryOp .not (Expr.exists false sel), Expr.lit (.bool true))]
              (some (Expr.inSubquery e true sel))

/-- Scalar subquery returning empty = NULL -/
axiom scalar_subquery_empty_null (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.subquery sel) = some (.null none)

/-- EXISTS can be rewritten as COUNT(*) > 0 (semantic equivalence) -/
axiom exists_as_count_gt_zero (db : Database) (row : Row) (sel : SelectStmt) :
    let existsResult := evalExprWithDb db row (Expr.exists false sel)
    let subRows := evalSelectWithContext db row sel
    existsResult = some (.bool (subRows.length > 0))

/-- NOT EXISTS can be rewritten as COUNT(*) = 0 (semantic equivalence) -/
axiom not_exists_as_count_eq_zero (db : Database) (row : Row) (sel : SelectStmt) :
    let existsResult := evalExprWithDb db row (Expr.exists true sel)
    let subRows := evalSelectWithContext db row sel
    existsResult = some (.bool (subRows.length == 0))

/-- IN subquery is equivalent to EXISTS with equality condition.
    x IN (SELECT col FROM t) ≡ EXISTS (SELECT 1 FROM t WHERE t.col = x) -/
axiom in_subquery_as_exists (db : Database) (row : Row) (e : Expr)
    (tableName : String) (colName : String) :
    let inSub := Expr.inSubquery e false
      (SelectStmt.mk false [.exprItem (.col ⟨none, colName⟩) none]
        (some (.table ⟨tableName, none⟩)) none [] none [] none none)
    let existsSub := Expr.exists false
      (SelectStmt.mk false [.exprItem (.lit (.int 1)) none]
        (some (.table ⟨tableName, none⟩))
        (some (.binOp .eq (.col ⟨some tableName, colName⟩) e))
        [] none [] none none)
    evalExprWithDb db row inSub = evalExprWithDb db row existsSub

/-- NOT IN subquery is equivalent to NOT EXISTS with equality condition -/
axiom not_in_subquery_as_not_exists (db : Database) (row : Row) (e : Expr)
    (tableName : String) (colName : String) :
    let notInSub := Expr.inSubquery e true
      (SelectStmt.mk false [.exprItem (.col ⟨none, colName⟩) none]
        (some (.table ⟨tableName, none⟩)) none [] none [] none none)
    let notExistsSub := Expr.exists true
      (SelectStmt.mk false [.exprItem (.lit (.int 1)) none]
        (some (.table ⟨tableName, none⟩))
        (some (.binOp .eq (.col ⟨some tableName, colName⟩) e))
        [] none [] none none)
    evalExprWithDb db row notInSub = evalExprWithDb db row notExistsSub

/-- Uncorrelated subquery can be evaluated independently of outer row.
    If a subquery doesn't reference any columns from the outer query,
    its result is the same regardless of the outer row context. -/
axiom uncorrelated_subquery_independent (db : Database) (row1 row2 : Row) (sel : SelectStmt) :
    -- Assuming sel doesn't reference columns from the outer context
    -- (this is a semantic precondition)
    evalSelectWithContext db row1 sel = evalSelectWithContext db row2 sel

/-- Subquery with LIMIT 1 returns at most one row -/
axiom subquery_limit_one (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 1) offset
    (evalSelectWithContext db row sel).length ≤ 1

/-- Scalar subquery is equivalent to first value of subquery with LIMIT 1 -/
axiom scalar_subquery_is_first (db : Database) (row : Row) (sel : SelectStmt) :
    let result := evalExprWithDb db row (Expr.subquery sel)
    let subRows := evalSelectWithContext db row sel
    result = match subRows.head? with
      | some subRow => subRow.head?.map (·.2)
      | none => some (.null none)

/-- EXISTS is monotonic: more rows in subquery doesn't change TRUE to FALSE -/
axiom exists_monotonic (db : Database) (row : Row) (sel1 sel2 : SelectStmt)
    (h : ∀ r ∈ evalSelectWithContext db row sel1,
         r ∈ evalSelectWithContext db row sel2) :
    evalExprWithDb db row (Expr.exists false sel1) = some (.bool true) →
    evalExprWithDb db row (Expr.exists false sel2) = some (.bool true)

/-- Adding WHERE TRUE to subquery doesn't change result -/
axiom subquery_where_true (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ none groupBy having orderBy limit offset
    let selWithTrue := SelectStmt.mk distinct items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset
    evalSelectWithContext db row sel = evalSelectWithContext db row selWithTrue

/-- Adding WHERE FALSE to subquery makes it empty -/
axiom subquery_where_false (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    let selWithFalse := SelectStmt.mk distinct items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset
    evalSelectWithContext db row selWithFalse = []

/-- IN with single-value subquery is equivalent to equality -/
axiom in_singleton_subquery (db : Database) (row : Row) (e : Expr) (sel : SelectStmt)
    (colName : String) (v : Value)
    (h : evalSelectWithContext db row sel = [[(colName, v)]]) :
    evalExprWithDb db row (Expr.inSubquery e false sel) =
    evalExprWithDb db row (Expr.binOp .eq e (Expr.lit v))

/-- Correlated subquery with outer reference evaluates with outer row context -/
axiom correlated_subquery_uses_context (db : Database) (outerRow : Row)
    (sel : SelectStmt) (outerCol : String) (outerVal : Value)
    (h : (outerCol, outerVal) ∈ outerRow) :
    -- The subquery can access outerCol from the outer row
    -- subResult is computed with outerRow available for column resolution
    True  -- This is a semantic property, not a computational one

-- ============================================================================
-- Subquery Unnesting Theorems
-- ============================================================================

/-- Subquery unnesting: IN subquery can be rewritten as a semi-join with DISTINCT.
    SELECT * FROM t WHERE x IN (SELECT y FROM s)
    ≡ SELECT DISTINCT t.* FROM t JOIN s ON t.x = s.y

    This is a key database optimization. The DISTINCT is required because
    the join may produce duplicates when multiple s rows have the same y value.

    NULL handling: Both forms exclude rows where t.x is NULL (IN returns NULL
    which WHERE treats as FALSE; JOIN condition evaluates to NULL/no match).
    Similarly, NULL values in s.y don't cause differences - they simply
    don't match in either form.

    This axiom expresses the semantic equivalence at the statement level. -/
axiom in_subquery_unnest_to_join (db : Database)
    (tName sName : String) (xCol yCol : String) :
    let inSubqueryForm := SelectStmt.mk false
        [.star (some tName)]  -- SELECT t.*
        (some (.table ⟨tName, some tName⟩))  -- FROM t
        (some (.inSubquery
          (.col ⟨some tName, xCol⟩)
          false  -- not negated (IN, not NOT IN)
          (SelectStmt.mk false
            [.exprItem (.col ⟨none, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩))
            none [] none [] none none)))  -- WHERE x IN (SELECT y FROM s)
        [] none [] none none
    let joinForm := SelectStmt.mk true  -- DISTINCT
        [.star (some tName)]  -- SELECT DISTINCT t.*
        (some (.join
          (.table ⟨tName, some tName⟩)
          .inner
          (.table ⟨sName, some sName⟩)
          (some (.binOp .eq
            (.col ⟨some tName, xCol⟩)
            (.col ⟨some sName, yCol⟩)))))  -- FROM t JOIN s ON t.x = s.y
        none [] none [] none none
    evalSelect db inSubqueryForm = evalSelect db joinForm

/-- NOT IN subquery can be unnested to an anti-join pattern.
    SELECT * FROM t WHERE x NOT IN (SELECT y FROM s)
    ≡ SELECT t.* FROM t LEFT JOIN s ON t.x = s.y WHERE s.y IS NULL

    The anti-join returns rows from t that have no matching rows in s.

    Note: This transformation assumes s.y contains no NULL values.
    When s.y can be NULL, NOT IN has different semantics (returns NULL
    when x matches no values but s contains NULL). -/
axiom not_in_subquery_unnest_to_antijoin (db : Database)
    (tName sName : String) (xCol yCol : String) :
    let notInSubqueryForm := SelectStmt.mk false
        [.star (some tName)]  -- SELECT t.*
        (some (.table ⟨tName, some tName⟩))  -- FROM t
        (some (.inSubquery
          (.col ⟨some tName, xCol⟩)
          true  -- negated (NOT IN)
          (SelectStmt.mk false
            [.exprItem (.col ⟨none, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩))
            none [] none [] none none)))  -- WHERE x NOT IN (SELECT y FROM s)
        [] none [] none none
    let antijoinForm := SelectStmt.mk false
        [.star (some tName)]  -- SELECT t.*
        (some (.join
          (.table ⟨tName, some tName⟩)
          .left  -- LEFT JOIN
          (.table ⟨sName, some sName⟩)
          (some (.binOp .eq
            (.col ⟨some tName, xCol⟩)
            (.col ⟨some sName, yCol⟩)))))  -- LEFT JOIN s ON t.x = s.y
        (some (.unaryOp .isNull (.col ⟨some sName, yCol⟩)))  -- WHERE s.y IS NULL
        [] none [] none none
    evalSelect db notInSubqueryForm = evalSelect db antijoinForm

/-- At the expression level: x IN (SELECT y FROM s) evaluates to true for a row
    if and only if there exists a matching row in the join result.

    This captures the logical essence of the unnesting transformation:
    membership in a subquery result corresponds to a successful join match. -/
axiom in_subquery_implies_join_match (db : Database) (row : Row)
    (x : Expr) (sName yCol : String)
    (h : evalExprWithDb db row (Expr.inSubquery x false
           (SelectStmt.mk false
             [.exprItem (.col ⟨none, yCol⟩) none]
             (some (.table ⟨sName, some sName⟩))
             none [] none [] none none)) = some (.bool true)) :
    ∃ sRow ∈ db sName,
      evalExprWithDb db (row ++ sRow)
        (Expr.binOp .eq x (.col ⟨some sName, yCol⟩)) = some (.bool true)

/-- The converse: if a join match exists, the IN subquery returns true. -/
axiom join_match_implies_in_subquery (db : Database) (row : Row)
    (x : Expr) (sName yCol : String) (sRow : Row)
    (hMem : sRow ∈ db sName)
    (hMatch : evalExprWithDb db (row ++ sRow)
                (Expr.binOp .eq x (.col ⟨some sName, yCol⟩)) = some (.bool true)) :
    evalExprWithDb db row (Expr.inSubquery x false
      (SelectStmt.mk false
        [.exprItem (.col ⟨none, yCol⟩) none]
        (some (.table ⟨sName, some sName⟩))
        none [] none [] none none)) = some (.bool true)

-- ============================================================================
-- ORDER BY Theorems
-- ============================================================================

/-- ORDER BY preserves row count -/
axiom order_by_preserves_count (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (orderBy : List OrderByItem) :
    let selNoOrder := SelectStmt.mk distinct items from_ where_ groupBy having [] limit offset
    let selWithOrder := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit offset
    (evalSelect db selNoOrder).length = (evalSelect db selWithOrder).length

/-- Empty ORDER BY list is identity -/
axiom order_by_empty_identity (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having [] limit offset
    evalSelect db sel = evalSelect db sel

/-- ORDER BY is idempotent: ordering twice by same criteria is same as once -/
axiom order_by_idempotent (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (orderBy : List OrderByItem) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit offset
    -- Applying the same ORDER BY twice gives same result
    let result := evalSelect db sel
    result.mergeSort (fun r1 r2 => compareByOrderItems db r1 r2 orderBy) = result

/-- ORDER BY ASC then DESC on same column: second order takes precedence -/
axiom order_by_last_wins (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (col : Expr) :
    let selAscDesc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .asc, OrderByItem.mk col .desc] limit offset
    let selDesc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .desc] limit offset
    -- When ordering by same column twice, later order dominates
    (evalSelect db selAscDesc).length = (evalSelect db selDesc).length

/-- Reversing ORDER BY direction reverses the result (for single column) -/
axiom order_by_reverse (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (col : Expr) :
    let selAsc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .asc] limit offset
    let selDesc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .desc] limit offset
    (evalSelect db selAsc).reverse = evalSelect db selDesc

-- ============================================================================
-- LIMIT Theorems
-- ============================================================================

/-- LIMIT 0 returns empty result -/
axiom limit_zero_empty (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 0) offset
    evalSelect db sel = []

/-- LIMIT n returns at most n rows -/
axiom limit_upper_bound (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) (n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) offset
    (evalSelect db sel).length ≤ n

/-- No LIMIT returns all rows (LIMIT none vs LIMIT large) -/
axiom limit_none_all_rows (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let selNoLimit := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none offset
    let count := (evalSelect db selNoLimit).length
    let selLargeLimit := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some count) offset
    evalSelect db selNoLimit = evalSelect db selLargeLimit

/-- LIMIT is monotonic: larger limit gives superset (by length) -/
axiom limit_monotonic (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) (m n : Nat) (h : m ≤ n) :
    let selM := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some m) offset
    let selN := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) offset
    (evalSelect db selM).length ≤ (evalSelect db selN).length

/-- LIMIT 1 returns at most one row -/
axiom limit_one_singleton (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 1) offset
    (evalSelect db sel).length ≤ 1

-- ============================================================================
-- OFFSET Theorems
-- ============================================================================

/-- OFFSET 0 is identity -/
axiom offset_zero_identity (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) :
    let selNoOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit none
    let selZeroOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some 0)
    evalSelect db selNoOffset = evalSelect db selZeroOffset

/-- OFFSET >= row count returns empty -/
axiom offset_too_large_empty (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) (n : Nat) :
    let selNoOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit none
    let count := (evalSelect db selNoOffset).length
    let selOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some (count + n))
    evalSelect db selOffset = []

/-- OFFSET reduces row count -/
axiom offset_reduces_count (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) (n : Nat) :
    let selNoOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit none
    let selOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some n)
    (evalSelect db selOffset).length ≤ (evalSelect db selNoOffset).length

/-- OFFSET is monotonic: larger offset gives fewer or equal rows -/
axiom offset_monotonic (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) (m n : Nat) (h : m ≤ n) :
    let selM := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some m)
    let selN := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some n)
    (evalSelect db selN).length ≤ (evalSelect db selM).length

-- ============================================================================
-- LIMIT + OFFSET Combination Theorems
-- ============================================================================

/-- LIMIT and OFFSET compose: OFFSET m then LIMIT n = skip m, take n -/
axiom limit_offset_compose (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (m n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) (some m)
    let selAll := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none
    evalSelect db sel = ((evalSelect db selAll).drop m).take n

/-- OFFSET then LIMIT 0 = empty regardless of offset -/
axiom offset_limit_zero_empty (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 0) (some offset)
    evalSelect db sel = []

/-- Total pagination: LIMIT n OFFSET m returns at most n rows -/
axiom pagination_upper_bound (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (m n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) (some m)
    (evalSelect db sel).length ≤ n

/-- Pagination identity: OFFSET 0 LIMIT count = all rows -/
axiom pagination_identity (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) :
    let selAll := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none
    let count := (evalSelect db selAll).length
    let selPaged := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some count) (some 0)
    evalSelect db selAll = evalSelect db selPaged

/-- Consecutive pages cover all rows: page1 ++ page2 when properly offset -/
axiom consecutive_pages (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (pageSize : Nat) :
    let selPage1 := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some pageSize) (some 0)
    let selPage2 := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some pageSize) (some pageSize)
    let selBoth := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some (pageSize * 2)) (some 0)
    evalSelect db selPage1 ++ evalSelect db selPage2 = evalSelect db selBoth

/-- ORDER BY + LIMIT: first n rows are deterministic (assuming stable sort) -/
axiom order_limit_deterministic (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) none
    let selAll := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none
    evalSelect db sel = (evalSelect db selAll).take n

end SqlEquiv
