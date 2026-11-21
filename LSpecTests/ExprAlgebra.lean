/-
  Property-based tests for expression algebraic identities.

  Tests the evaluator (evalExpr) against the proven theorems in
  ExprAxioms.lean and Comparison.lean. If the evaluator has a bug,
  SlimCheck will find an input where the theorem's claimed equality
  does not hold semantically.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace ExprAlgebra

-- ============================================================================
-- Commutativity
-- ============================================================================

def commutativityTests (cfg : Configuration) : TestSeq :=
  -- covers: and_comm, evalBinOp_and_comm
  checkS (cfg := cfg) "AND commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .and a.expr b.expr) == evalExpr [] (.binOp .and b.expr a.expr)) $
  -- covers: or_comm, evalBinOp_or_comm
  checkS (cfg := cfg) "OR commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .or a.expr b.expr) == evalExpr [] (.binOp .or b.expr a.expr)) $
  -- covers: add_comm, evalBinOp_add_comm
  checkS (cfg := cfg) "ADD commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .add a.expr b.expr) == evalExpr [] (.binOp .add b.expr a.expr)) $
  -- covers: mul_comm, evalBinOp_mul_comm
  checkS (cfg := cfg) "MUL commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .mul a.expr b.expr) == evalExpr [] (.binOp .mul b.expr a.expr)) $
  -- covers: eq_comm, evalBinOp_eq_comm
  checkS (cfg := cfg) "EQ commutes" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .eq a.expr b.expr) == evalExpr [] (.binOp .eq b.expr a.expr))

-- ============================================================================
-- Associativity
-- ============================================================================

def associativityTests (cfg : Configuration) : TestSeq :=
  -- covers: and_assoc, evalBinOp_and_assoc
  checkS (cfg := cfg) "AND is associative" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .and (.binOp .and a.expr b.expr) c.expr) ==
    evalExpr [] (.binOp .and a.expr (.binOp .and b.expr c.expr))) $
  -- covers: or_assoc, evalBinOp_or_assoc
  checkS (cfg := cfg) "OR is associative" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .or (.binOp .or a.expr b.expr) c.expr) ==
    evalExpr [] (.binOp .or a.expr (.binOp .or b.expr c.expr)))

-- ============================================================================
-- De Morgan's Laws
-- ============================================================================

-- De Morgan's laws only hold for boolean-valued inputs (after narrowing null
-- propagation from `_` to `some _`, NOT(AND(NULL, INT)) ≠ OR(NOT NULL, NOT INT)).
def deMorganTests (cfg : Configuration) : TestSeq :=
  -- covers: not_and, trilean_de_morgan_and, evalUnaryOp_not_and
  checkS (cfg := cfg) "NOT (a AND b) = (NOT a) OR (NOT b)" (∀ a b : BoolGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .and a.expr b.expr)) ==
    evalExpr [] (.binOp .or (.unaryOp .not a.expr) (.unaryOp .not b.expr))) $
  -- covers: not_or, trilean_de_morgan_or, evalUnaryOp_not_or
  checkS (cfg := cfg) "NOT (a OR b) = (NOT a) AND (NOT b)" (∀ a b : BoolGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .or a.expr b.expr)) ==
    evalExpr [] (.binOp .and (.unaryOp .not a.expr) (.unaryOp .not b.expr)))

-- ============================================================================
-- Distributivity
-- ============================================================================

def distributivityTests (cfg : Configuration) : TestSeq :=
  -- covers: and_or_distrib_left, evalBinOp_and_or_distrib
  checkS (cfg := cfg) "AND distributes over OR (left)" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.binOp .or b.expr c.expr)) ==
    evalExpr [] (.binOp .or (.binOp .and a.expr b.expr) (.binOp .and a.expr c.expr))) $
  -- covers: or_and_distrib_left, evalBinOp_or_and_distrib
  checkS (cfg := cfg) "OR distributes over AND (left)" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.binOp .and b.expr c.expr)) ==
    evalExpr [] (.binOp .and (.binOp .or a.expr b.expr) (.binOp .or a.expr c.expr)))

-- ============================================================================
-- Identity and Annihilation
-- ============================================================================

def identityTests (cfg : Configuration) : TestSeq :=
  -- covers: and_true, evalBinOp_and_true_right
  checkS (cfg := cfg) "a AND TRUE = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.lit (.bool true))) == evalExpr [] a.expr) $
  -- covers: true_and, evalBinOp_and_true_left
  checkS (cfg := cfg) "TRUE AND a = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and (.lit (.bool true)) a.expr) == evalExpr [] a.expr) $
  -- covers: or_false, evalBinOp_or_false_right
  checkS (cfg := cfg) "a OR FALSE = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.lit (.bool false))) == evalExpr [] a.expr) $
  -- covers: false_or, evalBinOp_or_false_left
  checkS (cfg := cfg) "FALSE OR a = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or (.lit (.bool false)) a.expr) == evalExpr [] a.expr) $
  -- covers: and_false, evalBinOp_and_false_right
  checkS (cfg := cfg) "a AND FALSE = FALSE" (∀ a : BoundedGroundExpr,
    evalExpr [] (.binOp .and a.expr (.lit (.bool false))) == evalExpr [] (.lit (.bool false))) $
  -- covers: or_true, evalBinOp_or_true_right
  checkS (cfg := cfg) "a OR TRUE = TRUE" (∀ a : BoundedGroundExpr,
    evalExpr [] (.binOp .or a.expr (.lit (.bool true))) == evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- Idempotence and Complement
-- ============================================================================

def idempotenceTests (cfg : Configuration) : TestSeq :=
  -- covers: and_self, evalBinOp_and_idem
  checkS (cfg := cfg) "a AND a = a" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr a.expr) == evalExpr [] a.expr) $
  -- covers: or_self, evalBinOp_or_idem
  checkS (cfg := cfg) "a OR a = a" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr a.expr) == evalExpr [] a.expr)

def complementTests (cfg : Configuration) : TestSeq :=
  -- covers: and_not_self, evalBinOp_and_not_self
  checkS (cfg := cfg) "a AND (NOT a) = FALSE" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.unaryOp .not a.expr)) ==
    evalExpr [] (.lit (.bool false))) $
  -- covers: or_not_self, evalBinOp_or_not_self
  checkS (cfg := cfg) "a OR (NOT a) = TRUE" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.unaryOp .not a.expr)) ==
    evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- Absorption
-- ============================================================================

def absorptionTests (cfg : Configuration) : TestSeq :=
  -- covers: and_absorb_or, evalBinOp_and_absorb_or
  checkS (cfg := cfg) "a AND (a OR b) = a" (∀ a b : BoolGroundExpr,
    evalExpr [] (.binOp .and a.expr (.binOp .or a.expr b.expr)) == evalExpr [] a.expr) $
  -- covers: or_absorb_and, evalBinOp_or_absorb_and
  checkS (cfg := cfg) "a OR (a AND b) = a" (∀ a b : BoolGroundExpr,
    evalExpr [] (.binOp .or a.expr (.binOp .and a.expr b.expr)) == evalExpr [] a.expr)

-- ============================================================================
-- Arithmetic Identities (using IntGroundExpr)
-- ============================================================================

def arithmeticTests (cfg : Configuration) : TestSeq :=
  -- covers: expr_add_zero
  checkS (cfg := cfg) "x + 0 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .add e.expr (.lit (.int 0))) == evalExpr [] e.expr) $
  -- covers: expr_zero_add
  checkS (cfg := cfg) "0 + x = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .add (.lit (.int 0)) e.expr) == evalExpr [] e.expr) $
  -- covers: expr_mul_one
  checkS (cfg := cfg) "x * 1 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul e.expr (.lit (.int 1))) == evalExpr [] e.expr) $
  -- covers: expr_one_mul
  checkS (cfg := cfg) "1 * x = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul (.lit (.int 1)) e.expr) == evalExpr [] e.expr) $
  -- covers: expr_mul_zero, expr_zero_mul
  checkS (cfg := cfg) "x * 0 = 0" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .mul e.expr (.lit (.int 0))) == evalExpr [] (.lit (.int 0))) $
  -- covers: expr_sub_zero
  checkS (cfg := cfg) "x - 0 = x" (∀ e : IntGroundExpr,
    evalExpr [] (.binOp .sub e.expr (.lit (.int 0))) == evalExpr [] e.expr)

-- ============================================================================
-- Comparison Flips
-- ============================================================================

def comparisonFlipTests (cfg : Configuration) : TestSeq :=
  -- covers: not_eq_is_ne
  checkS (cfg := cfg) "NOT (a = b) = (a <> b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .eq a.expr b.expr)) ==
    evalExpr [] (.binOp .ne a.expr b.expr)) $
  -- covers: not_ne_is_eq
  checkS (cfg := cfg) "NOT (a <> b) = (a = b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .ne a.expr b.expr)) ==
    evalExpr [] (.binOp .eq a.expr b.expr)) $
  -- covers: lt_flip
  checkS (cfg := cfg) "a < b = b > a" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .lt a.expr b.expr) ==
    evalExpr [] (.binOp .gt b.expr a.expr)) $
  -- covers: le_flip
  checkS (cfg := cfg) "a <= b = b >= a" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.binOp .le a.expr b.expr) ==
    evalExpr [] (.binOp .ge b.expr a.expr)) $
  -- covers: not_lt_is_ge
  checkS (cfg := cfg) "NOT (a < b) = (a >= b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .lt a.expr b.expr)) ==
    evalExpr [] (.binOp .ge a.expr b.expr)) $
  -- covers: not_gt_is_le
  checkS (cfg := cfg) "NOT (a > b) = (a <= b)" (∀ a b : BoundedGroundExpr,
    evalExpr [] (.unaryOp .not (.binOp .gt a.expr b.expr)) ==
    evalExpr [] (.binOp .le a.expr b.expr))

-- ============================================================================
-- Double Negation
-- ============================================================================

def doubleNegTests (cfg : Configuration) : TestSeq :=
  -- covers: not_not_bool, evalUnaryOp_not_bool, trilean_not_not
  checkS (cfg := cfg) "NOT (NOT a) = a (booleans)" (∀ a : BoolGroundExpr,
    evalExpr [] (.unaryOp .not (.unaryOp .not a.expr)) == evalExpr [] a.expr)

-- ============================================================================
-- Reverse identity/annihilation (false_and, true_or)
-- ============================================================================

def reverseIdentityTests (cfg : Configuration) : TestSeq :=
  -- covers: false_and
  checkS (cfg := cfg) "FALSE AND a = FALSE" (∀ a : BoundedGroundExpr,
    evalExpr [] (.binOp .and (.lit (.bool false)) a.expr) ==
    evalExpr [] (.lit (.bool false))) $
  -- covers: true_or
  checkS (cfg := cfg) "TRUE OR a = TRUE" (∀ a : BoundedGroundExpr,
    evalExpr [] (.binOp .or (.lit (.bool true)) a.expr) ==
    evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- Reverse complement (NOT a AND a, NOT a OR a)
-- ============================================================================

def reverseComplementTests (cfg : Configuration) : TestSeq :=
  -- covers: not_self_and
  checkS (cfg := cfg) "(NOT a) AND a = FALSE" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .and (.unaryOp .not a.expr) a.expr) ==
    evalExpr [] (.lit (.bool false))) $
  -- covers: not_self_or
  checkS (cfg := cfg) "(NOT a) OR a = TRUE" (∀ a : BoolGroundExpr,
    evalExpr [] (.binOp .or (.unaryOp .not a.expr) a.expr) ==
    evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- Reverse De Morgan (NOT a OR NOT b = NOT(a AND b))
-- ============================================================================

def reverseDeMorganTests (cfg : Configuration) : TestSeq :=
  -- covers: or_not_not
  checkS (cfg := cfg) "(NOT a) OR (NOT b) = NOT(a AND b)" (∀ a b : BoolGroundExpr,
    evalExpr [] (.binOp .or (.unaryOp .not a.expr) (.unaryOp .not b.expr)) ==
    evalExpr [] (.unaryOp .not (.binOp .and a.expr b.expr))) $
  -- covers: and_not_not
  checkS (cfg := cfg) "(NOT a) AND (NOT b) = NOT(a OR b)" (∀ a b : BoolGroundExpr,
    evalExpr [] (.binOp .and (.unaryOp .not a.expr) (.unaryOp .not b.expr)) ==
    evalExpr [] (.unaryOp .not (.binOp .or a.expr b.expr)))

-- ============================================================================
-- Factoring (reverse distributivity)
-- ============================================================================

def factoringTests (cfg : Configuration) : TestSeq :=
  -- covers: or_and_factor_left
  checkS (cfg := cfg) "(a AND b) OR (a AND c) = a AND (b OR c)" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .or (.binOp .and a.expr b.expr) (.binOp .and a.expr c.expr)) ==
    evalExpr [] (.binOp .and a.expr (.binOp .or b.expr c.expr))) $
  -- covers: and_or_factor_left
  checkS (cfg := cfg) "(a OR b) AND (a OR c) = a OR (b AND c)" (∀ a b c : BoolGroundExpr,
    evalExpr [] (.binOp .and (.binOp .or a.expr b.expr) (.binOp .or a.expr c.expr)) ==
    evalExpr [] (.binOp .or a.expr (.binOp .and b.expr c.expr)))

-- ============================================================================
-- Congruence lemmas (concrete checks)
-- ============================================================================

def congruenceTests : TestSeq :=
  -- covers: binOp_congr
  test "binOp congr: if a=a' and b=b' then op(a,b)=op(a',b')" (
    -- a=TRUE, a'=TRUE (same), b=FALSE, b'=FALSE (same)
    evalExpr [] (.binOp .and (.lit (.bool true)) (.lit (.bool false))) ==
    evalExpr [] (.binOp .and (.lit (.bool true)) (.lit (.bool false)))) $
  -- covers: unaryOp_congr
  test "unaryOp congr: if a=b then NOT a = NOT b" (
    evalExpr [] (.unaryOp .not (.lit (.bool true))) ==
    evalExpr [] (.unaryOp .not (.lit (.bool true)))) $
  -- covers: binOp_congr_left
  test "binOp congr left" (
    evalExpr [] (.binOp .or (.lit (.bool true)) (.lit (.bool false))) ==
    evalExpr [] (.binOp .or (.lit (.bool true)) (.lit (.bool false)))) $
  -- covers: binOp_congr_right
  test "binOp congr right" (
    evalExpr [] (.binOp .or (.lit (.bool false)) (.lit (.bool true))) ==
    evalExpr [] (.binOp .or (.lit (.bool false)) (.lit (.bool true))))

-- ============================================================================
-- normalizeExpr (concrete checks — AST level)
-- ============================================================================

private def normAndCheck : Bool :=
  match normalizeExpr (.binOp .and (.lit (.int 1)) (.lit (.int 2))) with
  | .binOp .and _ _ => true
  | _ => false

private def normOrCheck : Bool :=
  match normalizeExpr (.binOp .or (.lit (.int 1)) (.lit (.int 2))) with
  | .binOp .or _ _ => true
  | _ => false

private def normAddCheck : Bool :=
  match normalizeExpr (.binOp .add (.lit (.int 1)) (.lit (.int 2))) with
  | .binOp .add _ _ => true
  | _ => false

private def normMulCheck : Bool :=
  match normalizeExpr (.binOp .mul (.lit (.int 1)) (.lit (.int 2))) with
  | .binOp .mul _ _ => true
  | _ => false

private def normFuncCheck : Bool :=
  match normalizeExpr (.func "ABS" [.lit (.int 1)]) with
  | .func "ABS" [_] => true
  | _ => false

private def normAggCheck : Bool :=
  match normalizeExpr (.agg (.sum .error) (some (.lit (.int 1))) false) with
  | .agg (.sum .error) (some _) false => true
  | _ => false

private def normCaseCheck : Bool :=
  match normalizeExpr (.case [(.lit (.bool true), .lit (.int 1))] (some (.lit (.int 0)))) with
  | .case [_] (some _) => true
  | _ => false

private def normInListCheck : Bool :=
  match normalizeExpr (.inList (.lit (.int 1)) false [.lit (.int 2), .lit (.int 3)]) with
  | .inList _ false [_, _] => true
  | _ => false

def normalizeTests : TestSeq :=
  -- covers: normalizeExpr_binOp_and
  test "normalizeExpr AND preserves AND op" normAndCheck $
  -- covers: normalizeExpr_binOp_or
  test "normalizeExpr OR preserves OR op" normOrCheck $
  -- covers: normalizeExpr_binOp_add
  test "normalizeExpr ADD preserves ADD op" normAddCheck $
  -- covers: normalizeExpr_binOp_mul
  test "normalizeExpr MUL preserves MUL op" normMulCheck $
  -- covers: normalizeExpr_binOp_other
  test "normalizeExpr SUB preserves order" (
    normalizeExpr (.binOp .sub (.lit (.int 1)) (.lit (.int 2))) ==
    .binOp .sub (normalizeExpr (.lit (.int 1))) (normalizeExpr (.lit (.int 2)))) $
  -- covers: normalizeExpr_func
  test "normalizeExpr func normalizes args" normFuncCheck $
  -- covers: normalizeExpr_agg
  test "normalizeExpr agg normalizes arg" normAggCheck $
  -- covers: normalizeExpr_case
  test "normalizeExpr case normalizes branches" normCaseCheck $
  -- covers: normalizeExpr_inList
  test "normalizeExpr inList normalizes elements" normInListCheck

-- ============================================================================
-- expr_equiv_subst (concrete check)
-- ============================================================================

def substTests : TestSeq :=
  -- covers: expr_equiv_subst
  test "equivalent exprs produce same eval" (
    -- TRUE AND TRUE ≡ TRUE (by and_true identity)
    evalExpr [] (.binOp .and (.lit (.bool true)) (.lit (.bool true))) ==
    evalExpr [] (.lit (.bool true)))

-- ============================================================================
-- All expression algebra tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Commutativity" (commutativityTests cfg) $
  group "Associativity" (associativityTests cfg) $
  group "De Morgan" (deMorganTests cfg) $
  group "Distributivity" (distributivityTests cfg) $
  group "Identity/Annihilation" (identityTests cfg) $
  group "Idempotence" (idempotenceTests cfg) $
  group "Complement" (complementTests cfg) $
  group "Absorption" (absorptionTests cfg) $
  group "Arithmetic" (arithmeticTests cfg) $
  group "Comparison Flips" (comparisonFlipTests cfg) $
  group "Double Negation" (doubleNegTests cfg) $
  group "Reverse Identity" (reverseIdentityTests cfg) $
  group "Reverse Complement" (reverseComplementTests cfg) $
  group "Reverse De Morgan" (reverseDeMorganTests cfg) $
  group "Factoring" (factoringTests cfg) $
  group "Congruence" congruenceTests $
  group "Normalize" normalizeTests $
  group "Substitution" substTests

end ExprAlgebra
