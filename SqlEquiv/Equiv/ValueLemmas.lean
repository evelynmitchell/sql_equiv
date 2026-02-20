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

-- ============================================================================
-- Associativity (Bool-restricted)
-- ============================================================================

-- Value-level associativity is only true for boolean inputs. Counterexample:
--   AND(NULL, AND(INT, BOOL)) = AND(NULL, none) = none
--   AND(AND(NULL, INT), BOOL) = AND(NULL, BOOL) = NULL ≠ none

/-- AND is associative at the value level for boolean inputs -/
theorem evalBinOp_and_assoc (a b c : Bool) :
    evalBinOp .and (evalBinOp .and (some (.bool a)) (some (.bool b))) (some (.bool c)) =
    evalBinOp .and (some (.bool a)) (evalBinOp .and (some (.bool b)) (some (.bool c))) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- OR is associative at the value level for boolean inputs -/
theorem evalBinOp_or_assoc (a b c : Bool) :
    evalBinOp .or (evalBinOp .or (some (.bool a)) (some (.bool b))) (some (.bool c)) =
    evalBinOp .or (some (.bool a)) (evalBinOp .or (some (.bool b)) (some (.bool c))) := by
  cases a <;> cases b <;> cases c <;> rfl

-- ============================================================================
-- Absorption Laws (proven — Bool-restricted inputs)
-- ============================================================================

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

-- ============================================================================
-- De Morgan's Laws (Bool-restricted)
-- ============================================================================

-- Value-level De Morgan fails for non-boolean inputs. Counterexample:
--   NOT(AND(int, null)) = NOT(NULL) = NULL
--   OR(NOT int, NOT null) = OR(none, NULL) = none ≠ NULL

/-- De Morgan's law: NOT (a AND b) = (NOT a) OR (NOT b) for boolean inputs -/
theorem evalUnaryOp_not_and (a b : Bool) :
    evalUnaryOp .not (evalBinOp .and (some (.bool a)) (some (.bool b))) =
    evalBinOp .or (evalUnaryOp .not (some (.bool a))) (evalUnaryOp .not (some (.bool b))) := by
  cases a <;> cases b <;> rfl

/-- De Morgan's law: NOT (a OR b) = (NOT a) AND (NOT b) for boolean inputs -/
theorem evalUnaryOp_not_or (a b : Bool) :
    evalUnaryOp .not (evalBinOp .or (some (.bool a)) (some (.bool b))) =
    evalBinOp .and (evalUnaryOp .not (some (.bool a))) (evalUnaryOp .not (some (.bool b))) := by
  cases a <;> cases b <;> rfl

-- ============================================================================
-- BoolOrNullOrNone De Morgan Helpers (for Comparison.lean)
-- ============================================================================

/-- A value is bool, null, or none (excludes int/string which break De Morgan) -/
def isBoolOrNullOrNone (v : Option Value) : Prop :=
  (∃ b, v = some (.bool b)) ∨ (∃ t, v = some (.null t)) ∨ v = none

/-- De Morgan NOT OR for BoolOrNullOrNone inputs -/
theorem evalUnaryOp_not_or_bnn (l r : Option Value)
    (hl : isBoolOrNullOrNone l) (hr : isBoolOrNullOrNone r) :
    evalUnaryOp .not (evalBinOp .or l r) =
    evalBinOp .and (evalUnaryOp .not l) (evalUnaryOp .not r) := by
  rcases hl with ⟨bl, rfl⟩ | ⟨tl, rfl⟩ | rfl
  · rcases hr with ⟨br, rfl⟩ | ⟨tr, rfl⟩ | rfl
    · cases bl <;> cases br <;> rfl
    · cases bl <;> rfl
    · cases bl <;> rfl
  · rcases hr with ⟨br, rfl⟩ | ⟨tr, rfl⟩ | rfl
    · cases br <;> rfl
    · rfl
    · rfl
  · rcases hr with ⟨br, rfl⟩ | ⟨tr, rfl⟩ | rfl
    · cases br <;> rfl
    · rfl
    · rfl

/-- De Morgan NOT AND for BoolOrNullOrNone inputs -/
theorem evalUnaryOp_not_and_bnn (l r : Option Value)
    (hl : isBoolOrNullOrNone l) (hr : isBoolOrNullOrNone r) :
    evalUnaryOp .not (evalBinOp .and l r) =
    evalBinOp .or (evalUnaryOp .not l) (evalUnaryOp .not r) := by
  rcases hl with ⟨bl, rfl⟩ | ⟨tl, rfl⟩ | rfl
  · rcases hr with ⟨br, rfl⟩ | ⟨tr, rfl⟩ | rfl
    · cases bl <;> cases br <;> rfl
    · cases bl <;> rfl
    · cases bl <;> rfl
  · rcases hr with ⟨br, rfl⟩ | ⟨tr, rfl⟩ | rfl
    · cases br <;> rfl
    · rfl
    · rfl
  · rcases hr with ⟨br, rfl⟩ | ⟨tr, rfl⟩ | rfl
    · cases br <;> rfl
    · rfl
    · rfl

/-- evalBinOp .eq always produces BoolOrNullOrNone -/
theorem evalBinOp_eq_isBoolOrNullOrNone (l r : Option Value) :
    isBoolOrNullOrNone (evalBinOp .eq l r) := by
  unfold isBoolOrNullOrNone
  cases l with
  | none => cases r with | none => exact Or.inr (Or.inr rfl) | some v => cases v <;> exact Or.inr (Or.inr rfl)
  | some v => cases r with
    | none => cases v <;> exact Or.inr (Or.inr rfl)
    | some w =>
      cases v <;> cases w <;> simp [evalBinOp, Value.eq]
      all_goals first
        | exact Or.inr (Or.inl ⟨_, rfl⟩)
        | (unfold Value.eq; split <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inr rfl))

/-- evalBinOp .ge always produces BoolOrNullOrNone -/
theorem evalBinOp_ge_isBoolOrNullOrNone (l r : Option Value) :
    isBoolOrNullOrNone (evalBinOp .ge l r) := by
  unfold isBoolOrNullOrNone
  cases l with
  | none => cases r with | none => exact Or.inr (Or.inr rfl) | some v => cases v <;> exact Or.inr (Or.inr rfl)
  | some v => cases r with
    | none => cases v <;> exact Or.inr (Or.inr rfl)
    | some w =>
      cases v <;> cases w <;> simp [evalBinOp, Value.compare]
      all_goals first
        | exact Or.inr (Or.inl ⟨_, rfl⟩)
        | (unfold Value.compare; split <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inr rfl))

/-- evalBinOp .le always produces BoolOrNullOrNone -/
theorem evalBinOp_le_isBoolOrNullOrNone (l r : Option Value) :
    isBoolOrNullOrNone (evalBinOp .le l r) := by
  unfold isBoolOrNullOrNone
  cases l with
  | none => cases r with | none => exact Or.inr (Or.inr rfl) | some v => cases v <;> exact Or.inr (Or.inr rfl)
  | some v => cases r with
    | none => cases v <;> exact Or.inr (Or.inr rfl)
    | some w =>
      cases v <;> cases w <;> simp [evalBinOp, Value.compare]
      all_goals first
        | exact Or.inr (Or.inl ⟨_, rfl⟩)
        | (unfold Value.compare; split <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inr rfl))

/-- evalBinOp .or preserves BoolOrNullOrNone -/
theorem evalBinOp_or_preserves_bnn (l r : Option Value)
    (hl : isBoolOrNullOrNone l) (hr : isBoolOrNullOrNone r) :
    isBoolOrNullOrNone (evalBinOp .or l r) := by
  unfold isBoolOrNullOrNone
  rcases hl with ⟨bl, rfl⟩ | ⟨tl, rfl⟩ | rfl
  · rcases hr with ⟨br, rfl⟩ | ⟨tr, rfl⟩ | rfl
    · exact Or.inl ⟨bl || br, rfl⟩
    · cases bl
      · exact Or.inr (Or.inl ⟨none, rfl⟩)
      · exact Or.inl ⟨true, rfl⟩
    · cases bl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨true, rfl⟩
  · rcases hr with ⟨br, rfl⟩ | ⟨tr, rfl⟩ | rfl
    · cases br
      · exact Or.inr (Or.inl ⟨none, rfl⟩)
      · exact Or.inl ⟨true, rfl⟩
    · exact Or.inr (Or.inl ⟨none, rfl⟩)
    · exact Or.inr (Or.inr rfl)
  · rcases hr with ⟨br, rfl⟩ | ⟨tr, rfl⟩ | rfl
    · cases br
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨true, rfl⟩
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inr rfl)

-- ============================================================================
-- Distributivity (Bool-restricted, for Session 2)
-- ============================================================================

/-- AND distributes over OR (left) for boolean inputs -/
theorem evalBinOp_and_or_distrib (a b c : Bool) :
    evalBinOp .and (some (.bool a)) (evalBinOp .or (some (.bool b)) (some (.bool c))) =
    evalBinOp .or (evalBinOp .and (some (.bool a)) (some (.bool b)))
                  (evalBinOp .and (some (.bool a)) (some (.bool c))) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- AND distributes over OR (right) for boolean inputs -/
theorem evalBinOp_and_or_distrib_right (a b c : Bool) :
    evalBinOp .and (evalBinOp .or (some (.bool a)) (some (.bool b))) (some (.bool c)) =
    evalBinOp .or (evalBinOp .and (some (.bool a)) (some (.bool c)))
                  (evalBinOp .and (some (.bool b)) (some (.bool c))) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- OR distributes over AND (left) for boolean inputs -/
theorem evalBinOp_or_and_distrib (a b c : Bool) :
    evalBinOp .or (some (.bool a)) (evalBinOp .and (some (.bool b)) (some (.bool c))) =
    evalBinOp .and (evalBinOp .or (some (.bool a)) (some (.bool b)))
                   (evalBinOp .or (some (.bool a)) (some (.bool c))) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- OR distributes over AND (right) for boolean inputs -/
theorem evalBinOp_or_and_distrib_right (a b c : Bool) :
    evalBinOp .or (evalBinOp .and (some (.bool a)) (some (.bool b))) (some (.bool c)) =
    evalBinOp .and (evalBinOp .or (some (.bool a)) (some (.bool c)))
                   (evalBinOp .or (some (.bool b)) (some (.bool c))) := by
  cases a <;> cases b <;> cases c <;> rfl

-- ============================================================================
-- Value.eq Symmetry
-- ============================================================================

/-- Value.eq is symmetric -/
theorem Value.eq_comm (a b : Value) : a.eq b = b.eq a := by
  cases a <;> cases b <;> simp [Value.eq]
  · exact Int.beq_comm ..
  · exact String.beq_comm ..
  · exact Bool.beq_comm ..

-- ============================================================================
-- evalBinOp .eq ↔ Value.eq Bridge Lemmas (for subquery unnesting proofs)
-- ============================================================================

/-- If evalBinOp .eq on two non-none values gives true, then Value.eq gives some true -/
theorem eq_true_of_evalBinOp_eq {v w : Value}
    (h : evalBinOp .eq (some v) (some w) = some (.bool true)) :
    v.eq w = some true := by
  cases v <;> cases w <;> simp [evalBinOp, Value.eq] at h ⊢ <;> exact h

/-- If Value.eq gives some true, then evalBinOp .eq gives true -/
theorem evalBinOp_eq_of_eq_true {v w : Value}
    (h : v.eq w = some true) :
    evalBinOp .eq (some v) (some w) = some (.bool true) := by
  cases v <;> cases w <;> simp [evalBinOp, Value.eq] at h ⊢ <;> exact h

/-- Value.eq returning some true means v is not null -/
theorem Value.eq_some_true_not_null_left {v w : Value}
    (h : v.eq w = some true) : ∀ t, v ≠ .null t := by
  intro t ht; subst ht; cases w <;> simp [Value.eq] at h

/-- Value.eq returning some true means w is not null -/
theorem Value.eq_some_true_not_null_right {v w : Value}
    (h : v.eq w = some true) : ∀ t, w ≠ .null t := by
  intro t ht; subst ht; cases v <;> simp [Value.eq] at h

/-- BEq (Option Bool) true equivalence: (ob == some true) = true ↔ ob = some true -/
theorem Option.beq_some_true_iff (ob : Option Bool) :
    (ob == some true) = true ↔ ob = some true := by
  cases ob with
  | none => constructor <;> intro h <;> contradiction
  | some b => cases b <;> (constructor <;> intro h <;> first | rfl | contradiction)

end SqlEquiv
