/-
  Property-based tests for SQL NULL propagation semantics.

  NULL handling is the trickiest part of SQL. These properties test
  evalBinOp/evalUnaryOp directly against theorems proven in
  Comparison.lean and ValueLemmas.lean.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace NullSemantics

-- ============================================================================
-- Arithmetic NULL propagation
-- ============================================================================

def nullArithTests (cfg : Configuration) : TestSeq :=
  -- covers: null_add_left
  check (cfg := cfg) "NULL + x = NULL" (∀ v : Value,
    evalBinOp .add (some (.null none)) (some v) == some (.null none)) $
  -- covers: null_add_right
  check (cfg := cfg) "x + NULL = NULL" (∀ v : Value,
    evalBinOp .add (some v) (some (.null none)) == some (.null none)) $
  -- covers: null_sub_left
  check (cfg := cfg) "NULL - x = NULL" (∀ v : Value,
    evalBinOp .sub (some (.null none)) (some v) == some (.null none)) $
  -- covers: null_sub_right
  check (cfg := cfg) "x - NULL = NULL" (∀ v : Value,
    evalBinOp .sub (some v) (some (.null none)) == some (.null none)) $
  -- covers: null_mul_left
  check (cfg := cfg) "NULL * x = NULL" (∀ v : Value,
    evalBinOp .mul (some (.null none)) (some v) == some (.null none)) $
  -- covers: null_mul_right
  check (cfg := cfg) "x * NULL = NULL" (∀ v : Value,
    evalBinOp .mul (some v) (some (.null none)) == some (.null none)) $
  -- covers: null_div_left
  check (cfg := cfg) "NULL / x = NULL" (∀ v : Value,
    evalBinOp .div (some (.null none)) (some v) == some (.null none)) $
  -- covers: null_div_right
  check (cfg := cfg) "x / NULL = NULL" (∀ v : Value,
    evalBinOp .div (some v) (some (.null none)) == some (.null none))

-- ============================================================================
-- Comparison NULL propagation
-- ============================================================================

def nullComparisonTests (cfg : Configuration) : TestSeq :=
  -- covers: null_eq_left
  check (cfg := cfg) "NULL = x = NULL" (∀ v : Value,
    evalBinOp .eq (some (.null none)) (some v) == some (.null none)) $
  -- covers: null_eq_right
  check (cfg := cfg) "x = NULL = NULL" (∀ v : Value,
    evalBinOp .eq (some v) (some (.null none)) == some (.null none)) $
  -- covers: null_lt_left
  check (cfg := cfg) "NULL < x = NULL" (∀ v : Value,
    evalBinOp .lt (some (.null none)) (some v) == some (.null none)) $
  -- covers: null_lt_right
  check (cfg := cfg) "x < NULL = NULL" (∀ v : Value,
    evalBinOp .lt (some v) (some (.null none)) == some (.null none))

-- ============================================================================
-- Three-valued logic with NULL
-- ============================================================================

def threeValuedLogicTests (cfg : Configuration) : TestSeq :=
  -- FALSE dominates AND, TRUE dominates OR
  -- covers: false_and_null, trilean_and_false
  check (cfg := cfg) "FALSE AND NULL = FALSE" (∀ t : Option SqlType,
    evalBinOp .and (some (.bool false)) (some (.null t)) == some (.bool false)) $
  -- covers: null_and_false
  check (cfg := cfg) "NULL AND FALSE = FALSE" (∀ t : Option SqlType,
    evalBinOp .and (some (.null t)) (some (.bool false)) == some (.bool false)) $
  -- covers: true_or_null, trilean_or_true
  check (cfg := cfg) "TRUE OR NULL = TRUE" (∀ t : Option SqlType,
    evalBinOp .or (some (.bool true)) (some (.null t)) == some (.bool true)) $
  -- covers: null_or_true
  check (cfg := cfg) "NULL OR TRUE = TRUE" (∀ t : Option SqlType,
    evalBinOp .or (some (.null t)) (some (.bool true)) == some (.bool true)) $
  -- Non-dominating cases: AND/OR with NULL propagates NULL (SQL three-valued logic)
  -- covers: true_and_null, trilean_and_true
  check (cfg := cfg) "TRUE AND NULL = NULL" (∀ t : Option SqlType,
    evalBinOp .and (some (.bool true)) (some (.null t)) == some (.null none)) $
  -- covers: null_and_true
  check (cfg := cfg) "NULL AND TRUE = NULL" (∀ t : Option SqlType,
    evalBinOp .and (some (.null t)) (some (.bool true)) == some (.null none)) $
  -- covers: false_or_null, trilean_or_false
  check (cfg := cfg) "FALSE OR NULL = NULL" (∀ t : Option SqlType,
    evalBinOp .or (some (.bool false)) (some (.null t)) == some (.null none)) $
  -- covers: null_or_false
  check (cfg := cfg) "NULL OR FALSE = NULL" (∀ t : Option SqlType,
    evalBinOp .or (some (.null t)) (some (.bool false)) == some (.null none)) $
  -- covers: null_and_null
  check (cfg := cfg) "NULL AND NULL = NULL" (∀ t1 t2 : Option SqlType,
    evalBinOp .and (some (.null t1)) (some (.null t2)) == some (.null none)) $
  -- covers: null_or_null
  check (cfg := cfg) "NULL OR NULL = NULL" (∀ t1 t2 : Option SqlType,
    evalBinOp .or (some (.null t1)) (some (.null t2)) == some (.null none))

-- ============================================================================
-- IS NULL / IS NOT NULL
-- ============================================================================

private def isNullComplement (v : Value) : Bool :=
  match evalUnaryOp .isNull (some v), evalUnaryOp .isNotNull (some v) with
  | some (.bool a), some (.bool b) => a == !b
  | _, _ => false

def isNullTests (cfg : Configuration) : TestSeq :=
  -- covers: is_null_is_not_null_complement, value_is_null_complement
  check (cfg := cfg) "IS NULL and IS NOT NULL are complementary" (∀ v : Value,
    isNullComplement v) $
  -- covers: is_null_on_null, isNullValue_null
  check (cfg := cfg) "IS NULL on NULL = TRUE" (∀ t : Option SqlType,
    evalUnaryOp .isNull (some (.null t)) == some (.bool true)) $
  -- covers: is_not_null_on_null
  check (cfg := cfg) "IS NOT NULL on NULL = FALSE" (∀ t : Option SqlType,
    evalUnaryOp .isNotNull (some (.null t)) == some (.bool false)) $
  -- covers: is_null_on_int, isNullValue_int
  check (cfg := cfg) "IS NULL on int = FALSE" (∀ n : Int,
    evalUnaryOp .isNull (some (.int n)) == some (.bool false)) $
  -- covers: is_not_null_on_int
  check (cfg := cfg) "IS NOT NULL on int = TRUE" (∀ n : Int,
    evalUnaryOp .isNotNull (some (.int n)) == some (.bool true))

-- ============================================================================
-- COALESCE
-- ============================================================================

def coalesceTests (cfg : Configuration) : TestSeq :=
  -- covers: coalesce_int_left
  check (cfg := cfg) "COALESCE(int, x) = int" (∀ n : Int, ∀ v : Value,
    evalFunc "COALESCE" [some (.int n), some v] == some (.int n)) $
  -- covers: coalesce_string_left
  check (cfg := cfg) "COALESCE(string, x) = string" (∀ v : Value,
    evalFunc "COALESCE" [some (.string "hello"), some v] == some (.string "hello")) $
  -- covers: coalesce_bool_left
  check (cfg := cfg) "COALESCE(bool, x) = bool" (∀ b : Bool, ∀ v : Value,
    evalFunc "COALESCE" [some (.bool b), some v] == some (.bool b)) $
  -- covers: coalesce_null_left_nonnull
  check (cfg := cfg) "COALESCE(NULL, int) = int" (∀ n : Int,
    evalFunc "COALESCE" [some (.null none), some (.int n)] == some (.int n))

-- ============================================================================
-- Scalar function tests (evalFunc)
-- ============================================================================

def nullifTests (cfg : Configuration) : TestSeq :=
  -- covers: nullif_same_int
  check (cfg := cfg) "NULLIF(n, n) = NULL" (∀ n : Int,
    evalFunc "NULLIF" [some (.int n), some (.int n)] == some (.null none)) $
  -- covers: nullif_diff_int
  check (cfg := cfg) "NULLIF(n, n+1) = n" (∀ n : Int,
    evalFunc "NULLIF" [some (.int n), some (.int (n + 1))] == some (.int n)) $
  check (cfg := cfg) "NULLIF(true, false) = true" (
    evalFunc "NULLIF" [some (.bool true), some (.bool false)] == some (.bool true)) $
  check (cfg := cfg) "NULLIF(true, true) = NULL" (
    evalFunc "NULLIF" [some (.bool true), some (.bool true)] == some (.null none))

private def absResultNonNeg (n : Int) : Bool :=
  match evalFunc "ABS" [some (.int n)] with
  | some (.int m) => decide (m >= 0)
  | _ => false

def absTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "ABS(n) >= 0" (∀ n : Int, absResultNonNeg n) $
  check (cfg := cfg) "ABS(-n) = ABS(n)" (∀ n : Int,
    evalFunc "ABS" [some (.int (-n))] == evalFunc "ABS" [some (.int n)])

def scalarNullTests : TestSeq :=
  -- covers: evalFunc ABS/LENGTH/UPPER/LOWER null propagation
  test "ABS(NULL) = NULL" (
    evalFunc "ABS" [some (.null none)] == some (.null none)) $
  test "LENGTH(NULL) = NULL" (
    evalFunc "LENGTH" [some (.null none)] == some (.null none)) $
  test "UPPER(NULL) = NULL" (
    evalFunc "UPPER" [some (.null none)] == some (.null none)) $
  test "LOWER(NULL) = NULL" (
    evalFunc "LOWER" [some (.null none)] == some (.null none)) $
  test "ABS(NULL::int) = NULL" (
    evalFunc "ABS" [some (.null (some .int))] == some (.null none)) $
  test "LENGTH(NULL::string) = NULL" (
    evalFunc "LENGTH" [some (.null (some .string))] == some (.null none))

def stringFuncTests : TestSeq :=
  test "LENGTH(hello) = 5" (
    evalFunc "LENGTH" [some (.string "hello")] == some (.int 5)) $
  -- covers: length_empty
  test "LENGTH empty = 0" (
    evalFunc "LENGTH" [some (.string "")] == some (.int 0)) $
  test "UPPER(hello) = HELLO" (
    evalFunc "UPPER" [some (.string "hello")] == some (.string "HELLO")) $
  test "LOWER(HELLO) = hello" (
    evalFunc "LOWER" [some (.string "HELLO")] == some (.string "hello")) $
  -- covers: upper_lower_upper
  test "UPPER(LOWER(s)) = UPPER(s)" (
    evalFunc "UPPER" [evalFunc "LOWER" [some (.string "Hello")]] ==
    evalFunc "UPPER" [some (.string "Hello")]) $
  -- covers: lower_upper_lower
  test "LOWER(UPPER(s)) = LOWER(s)" (
    evalFunc "LOWER" [evalFunc "UPPER" [some (.string "Hello")]] ==
    evalFunc "LOWER" [some (.string "Hello")]) $
  -- covers: concat_empty_right
  test "CONCAT(s, empty) = s" (
    evalFunc "CONCAT" [some (.string "hello"), some (.string "")] ==
    some (.string "hello")) $
  -- covers: concat_empty_left
  test "CONCAT(empty, s) = s" (
    evalFunc "CONCAT" [some (.string ""), some (.string "world")] ==
    some (.string "world"))

-- ============================================================================
-- IS NULL / IS NOT NULL on specific types
-- ============================================================================

def isNullTypedTests (_cfg : Configuration) : TestSeq :=
  -- covers: is_null_on_none
  test "IS NULL on none = TRUE" (
    evalUnaryOp .isNull none == some (.bool true)) $
  -- covers: is_null_on_string
  test "IS NULL on string = FALSE" (
    evalUnaryOp .isNull (some (.string "hello")) == some (.bool false)) $
  test "IS NULL on empty string = FALSE" (
    evalUnaryOp .isNull (some (.string "")) == some (.bool false)) $
  -- covers: is_null_on_bool
  test "IS NULL on true = FALSE" (
    evalUnaryOp .isNull (some (.bool true)) == some (.bool false)) $
  test "IS NULL on false = FALSE" (
    evalUnaryOp .isNull (some (.bool false)) == some (.bool false)) $
  -- covers: is_not_null_on_none
  test "IS NOT NULL on none = FALSE" (
    evalUnaryOp .isNotNull none == some (.bool false)) $
  -- covers: is_not_null_on_string
  test "IS NOT NULL on string = TRUE" (
    evalUnaryOp .isNotNull (some (.string "hello")) == some (.bool true)) $
  -- covers: is_not_null_on_bool
  test "IS NOT NULL on true = TRUE" (
    evalUnaryOp .isNotNull (some (.bool true)) == some (.bool true)) $
  test "IS NOT NULL on false = TRUE" (
    evalUnaryOp .isNotNull (some (.bool false)) == some (.bool true))

-- ============================================================================
-- NULL != propagation
-- ============================================================================

def nullNeTests (cfg : Configuration) : TestSeq :=
  -- covers: null_ne_left
  check (cfg := cfg) "NULL <> x = NULL" (∀ t : Option SqlType, ∀ v : Value,
    evalBinOp .ne (some (.null t)) (some v) == some (.null none)) $
  -- covers: null_ne_right
  check (cfg := cfg) "x <> NULL = NULL" (∀ v : Value, ∀ t : Option SqlType,
    evalBinOp .ne (some v) (some (.null t)) == some (.null none))

-- ============================================================================
-- isNullValue predicate
-- ============================================================================

def isNullValueTests (_cfg : Configuration) : TestSeq :=
  -- covers: isNullValue_none
  test "isNullValue none = true" (
    isNullValue none == true) $
  -- covers: isNullValue_string
  test "isNullValue string = false" (
    isNullValue (some (.string "hello")) == false) $
  -- covers: isNullValue_bool
  test "isNullValue true = false" (
    isNullValue (some (.bool true)) == false) $
  test "isNullValue false = false" (
    isNullValue (some (.bool false)) == false)

-- ============================================================================
-- COALESCE single-value and empty
-- ============================================================================

def coalesceSingleTests (cfg : Configuration) : TestSeq :=
  -- covers: coalesce_single_int
  check (cfg := cfg) "COALESCE(int) = int" (∀ n : Int,
    evalFunc "COALESCE" [some (.int n)] == some (.int n)) $
  -- covers: coalesce_single_string
  test "COALESCE(string) = string" (
    evalFunc "COALESCE" [some (.string "hello")] == some (.string "hello")) $
  test "COALESCE(empty string) = empty string" (
    evalFunc "COALESCE" [some (.string "")] == some (.string "")) $
  -- covers: coalesce_single_bool
  test "COALESCE(true) = true" (
    evalFunc "COALESCE" [some (.bool true)] == some (.bool true)) $
  test "COALESCE(false) = false" (
    evalFunc "COALESCE" [some (.bool false)] == some (.bool false)) $
  -- covers: coalesce_single_null
  check (cfg := cfg) "COALESCE(null) = none" (∀ t : Option SqlType,
    evalFunc "COALESCE" [some (.null t)] == none) $
  -- covers: coalesce_empty
  test "COALESCE() = none" (
    evalFunc "COALESCE" [] == none)

-- ============================================================================
-- Short-circuit: FALSE AND x, TRUE OR x
-- ============================================================================

def shortCircuitTests (cfg : Configuration) : TestSeq :=
  -- covers: evalBinOp_and_false_left
  check (cfg := cfg) "FALSE AND x = FALSE (any Option Value)" (∀ v : Value,
    evalBinOp .and (some (.bool false)) (some v) == some (.bool false)) $
  test "FALSE AND none = FALSE" (
    evalBinOp .and (some (.bool false)) none == some (.bool false)) $
  -- covers: evalBinOp_or_true_left
  check (cfg := cfg) "TRUE OR x = TRUE (any Option Value)" (∀ v : Value,
    evalBinOp .or (some (.bool true)) (some v) == some (.bool true)) $
  test "TRUE OR none = TRUE" (
    evalBinOp .or (some (.bool true)) none == some (.bool true))

-- ============================================================================
-- Trilean commutativity
-- ============================================================================

def trileanCommTests : TestSeq :=
  -- covers: trilean_and_comm
  test "trilean AND comm (T,F)" (Trilean.and .true .false == Trilean.and .false .true) $
  test "trilean AND comm (T,U)" (Trilean.and .true .unknown == Trilean.and .unknown .true) $
  test "trilean AND comm (F,U)" (Trilean.and .false .unknown == Trilean.and .unknown .false) $
  -- covers: trilean_or_comm
  test "trilean OR comm (T,F)" (Trilean.or .true .false == Trilean.or .false .true) $
  test "trilean OR comm (T,U)" (Trilean.or .true .unknown == Trilean.or .unknown .true) $
  test "trilean OR comm (F,U)" (Trilean.or .false .unknown == Trilean.or .unknown .false)

-- ============================================================================
-- Value-level helpers
-- ============================================================================

def valueHelperTests (cfg : Configuration) : TestSeq :=
  -- covers: Value.eq_comm
  check (cfg := cfg) "Value.eq is commutative" (∀ a b : Value,
    a.eq b == b.eq a) $
  -- covers: Int.beq_comm
  check (cfg := cfg) "Int BEq commutes" (∀ a b : Int,
    (a == b) == (b == a)) $
  -- covers: String.beq_comm
  test "String BEq commutes (hello,world)" (("hello" == "world") == ("world" == "hello")) $
  test "String BEq commutes (a,a)" (("a" == "a") == ("a" == "a")) $
  -- covers: Bool.beq_comm
  test "Bool BEq commutes (T,F)" ((true == false) == (false == true)) $
  test "Bool BEq commutes (T,T)" ((true == true) == (true == true))

-- ============================================================================
-- Value-level distributivity (Bool inputs only)
-- ============================================================================

def valueDistribTests : TestSeq :=
  -- covers: evalBinOp_and_or_distrib_right
  test "AND distributes over OR right (T,T,F)" (
    evalBinOp .and (evalBinOp .or (some (.bool true)) (some (.bool true))) (some (.bool false)) ==
    evalBinOp .or (evalBinOp .and (some (.bool true)) (some (.bool false))) (evalBinOp .and (some (.bool true)) (some (.bool false)))) $
  test "AND distributes over OR right (T,F,T)" (
    evalBinOp .and (evalBinOp .or (some (.bool true)) (some (.bool false))) (some (.bool true)) ==
    evalBinOp .or (evalBinOp .and (some (.bool true)) (some (.bool true))) (evalBinOp .and (some (.bool false)) (some (.bool true)))) $
  -- covers: evalBinOp_or_and_distrib_right
  test "OR distributes over AND right (T,F,T)" (
    evalBinOp .or (evalBinOp .and (some (.bool true)) (some (.bool false))) (some (.bool true)) ==
    evalBinOp .and (evalBinOp .or (some (.bool true)) (some (.bool true))) (evalBinOp .or (some (.bool false)) (some (.bool true)))) $
  test "OR distributes over AND right (F,F,F)" (
    evalBinOp .or (evalBinOp .and (some (.bool false)) (some (.bool false))) (some (.bool false)) ==
    evalBinOp .and (evalBinOp .or (some (.bool false)) (some (.bool false))) (evalBinOp .or (some (.bool false)) (some (.bool false))))

-- ============================================================================
-- BNN invariant preservation (concrete cases)
-- ============================================================================

private def isBNN (v : Option Value) : Bool :=
  match v with
  | some (.bool _) => true
  | some (.null _) => true
  | none => true
  | _ => false

def bnnInvariantTests (cfg : Configuration) : TestSeq :=
  -- covers: evalBinOp_eq_isBoolOrNullOrNone
  check (cfg := cfg) "eq result is BNN" (∀ a b : Value,
    isBNN (evalBinOp .eq (some a) (some b))) $
  test "eq none result is BNN" (isBNN (evalBinOp .eq none (some (.int 1)))) $
  -- covers: evalBinOp_ge_isBoolOrNullOrNone
  check (cfg := cfg) "ge result is BNN" (∀ a b : Value,
    isBNN (evalBinOp .ge (some a) (some b))) $
  -- covers: evalBinOp_le_isBoolOrNullOrNone
  check (cfg := cfg) "le result is BNN" (∀ a b : Value,
    isBNN (evalBinOp .le (some a) (some b))) $
  -- covers: evalBinOp_or_preserves_bnn
  test "or preserves BNN (bool, null)" (
    isBNN (evalBinOp .or (some (.bool true)) (some (.null none)))) $
  test "or preserves BNN (null, null)" (
    isBNN (evalBinOp .or (some (.null none)) (some (.null none)))) $
  test "or preserves BNN (none, bool)" (
    isBNN (evalBinOp .or none (some (.bool false))))

-- ============================================================================
-- De Morgan for BNN (value-level, concrete cases)
-- ============================================================================

def deMorganBnnTests : TestSeq :=
  -- covers: evalUnaryOp_not_or_bnn
  test "NOT(bool OR bool) = (NOT bool) AND (NOT bool)" (
    evalUnaryOp .not (evalBinOp .or (some (.bool true)) (some (.bool false))) ==
    evalBinOp .and (evalUnaryOp .not (some (.bool true))) (evalUnaryOp .not (some (.bool false)))) $
  test "NOT(null OR bool) = (NOT null) AND (NOT bool)" (
    evalUnaryOp .not (evalBinOp .or (some (.null none)) (some (.bool true))) ==
    evalBinOp .and (evalUnaryOp .not (some (.null none))) (evalUnaryOp .not (some (.bool true)))) $
  test "NOT(none OR bool) = (NOT none) AND (NOT bool)" (
    evalUnaryOp .not (evalBinOp .or none (some (.bool false))) ==
    evalBinOp .and (evalUnaryOp .not none) (evalUnaryOp .not (some (.bool false)))) $
  -- covers: evalUnaryOp_not_and_bnn
  test "NOT(bool AND null) = (NOT bool) OR (NOT null)" (
    evalUnaryOp .not (evalBinOp .and (some (.bool false)) (some (.null none))) ==
    evalBinOp .or (evalUnaryOp .not (some (.bool false))) (evalUnaryOp .not (some (.null none)))) $
  test "NOT(none AND none) = (NOT none) OR (NOT none)" (
    evalUnaryOp .not (evalBinOp .and none none) ==
    evalBinOp .or (evalUnaryOp .not none) (evalUnaryOp .not none))

-- ============================================================================
-- Value.eq bridge lemmas (concrete cases)
-- ============================================================================

private def eqBridgeCheck1 : Bool :=
  let v := Value.int 5; let w := Value.int 5
  match evalBinOp .eq (some v) (some w) with
  | some (.bool true) => v.eq w == some true
  | _ => true

private def eqBridgeCheck2 : Bool :=
  let v := Value.int 5; let w := Value.int 5
  match v.eq w with
  | some true => evalBinOp .eq (some v) (some w) == some (.bool true)
  | _ => true

private def eqBridgeCheck3 : Bool :=
  let v := Value.int 5; let w := Value.int 5
  match v.eq w with
  | some true => v != .null none
  | _ => true

private def eqBridgeCheck4 : Bool :=
  let v := Value.int 5; let w := Value.int 5
  match v.eq w with
  | some true => w != .null none
  | _ => true

def valueEqBridgeTests : TestSeq :=
  -- covers: eq_true_of_evalBinOp_eq
  test "evalBinOp eq true => Value.eq = some true (int)" eqBridgeCheck1 $
  -- covers: evalBinOp_eq_of_eq_true
  test "Value.eq = some true => evalBinOp eq = bool true (int)" eqBridgeCheck2 $
  -- covers: Value.eq_some_true_not_null_left
  test "Value.eq = some true => left not null" eqBridgeCheck3 $
  -- covers: Value.eq_some_true_not_null_right
  test "Value.eq = some true => right not null" eqBridgeCheck4 $
  -- covers: Option.beq_some_true_iff
  test "Option.beq some true iff (some true)" (
    ((some true : Option Bool) == some true) == true) $
  test "Option.beq some true iff (some false)" (
    ((some false : Option Bool) == some true) == false) $
  test "Option.beq some true iff (none)" (
    ((none : Option Bool) == some true) == false)

-- ============================================================================
-- value_null_or_not_null and typed_null_same_nullness
-- ============================================================================

def nullDisjunctionTests (cfg : Configuration) : TestSeq :=
  -- covers: value_null_or_not_null
  check (cfg := cfg) "every value is either null or not null" (∀ v : Value,
    v.isNull || v.isNotNull) $
  -- covers: typed_null_same_nullness
  check (cfg := cfg) "typed nulls have same nullness" (∀ t1 t2 : Option SqlType,
    Value.isNull (.null t1) == Value.isNull (.null t2))

-- ============================================================================
-- All NULL semantics tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Arithmetic NULL Propagation" (nullArithTests cfg) $
  group "Comparison NULL Propagation" (nullComparisonTests cfg) $
  group "Three-Valued Logic" (threeValuedLogicTests cfg) $
  group "IS NULL / IS NOT NULL" (isNullTests cfg) $
  group "IS NULL / IS NOT NULL Typed" (isNullTypedTests cfg) $
  group "NULL NE Propagation" (nullNeTests cfg) $
  group "isNullValue Predicate" (isNullValueTests cfg) $
  group "COALESCE" (coalesceTests cfg) $
  group "COALESCE Single/Empty" (coalesceSingleTests cfg) $
  group "Short-Circuit" (shortCircuitTests cfg) $
  group "Trilean Commutativity" trileanCommTests $
  group "Value Helpers" (valueHelperTests cfg) $
  group "Value Distributivity" valueDistribTests $
  group "BNN Invariants" (bnnInvariantTests cfg) $
  group "De Morgan BNN" deMorganBnnTests $
  group "Value.eq Bridge" valueEqBridgeTests $
  group "Null Disjunction" (nullDisjunctionTests cfg) $
  group "NULLIF" (nullifTests cfg) $
  group "ABS" (absTests cfg) $
  group "Scalar NULL Propagation" scalarNullTests $
  group "String Functions" stringFuncTests

end NullSemantics
