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
  check (cfg := cfg) "NULL + x = NULL" (∀ v : Value,
    evalBinOp .add (some (.null none)) (some v) == some (.null none)) $
  check (cfg := cfg) "x + NULL = NULL" (∀ v : Value,
    evalBinOp .add (some v) (some (.null none)) == some (.null none)) $
  check (cfg := cfg) "NULL - x = NULL" (∀ v : Value,
    evalBinOp .sub (some (.null none)) (some v) == some (.null none)) $
  check (cfg := cfg) "x - NULL = NULL" (∀ v : Value,
    evalBinOp .sub (some v) (some (.null none)) == some (.null none)) $
  check (cfg := cfg) "NULL * x = NULL" (∀ v : Value,
    evalBinOp .mul (some (.null none)) (some v) == some (.null none)) $
  check (cfg := cfg) "x * NULL = NULL" (∀ v : Value,
    evalBinOp .mul (some v) (some (.null none)) == some (.null none)) $
  check (cfg := cfg) "NULL / x = NULL" (∀ v : Value,
    evalBinOp .div (some (.null none)) (some v) == some (.null none)) $
  check (cfg := cfg) "x / NULL = NULL" (∀ v : Value,
    evalBinOp .div (some v) (some (.null none)) == some (.null none))

-- ============================================================================
-- Comparison NULL propagation
-- ============================================================================

def nullComparisonTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "NULL = x = NULL" (∀ v : Value,
    evalBinOp .eq (some (.null none)) (some v) == some (.null none)) $
  check (cfg := cfg) "x = NULL = NULL" (∀ v : Value,
    evalBinOp .eq (some v) (some (.null none)) == some (.null none)) $
  check (cfg := cfg) "NULL < x = NULL" (∀ v : Value,
    evalBinOp .lt (some (.null none)) (some v) == some (.null none)) $
  check (cfg := cfg) "x < NULL = NULL" (∀ v : Value,
    evalBinOp .lt (some v) (some (.null none)) == some (.null none))

-- ============================================================================
-- Three-valued logic with NULL
-- ============================================================================

def threeValuedLogicTests (cfg : Configuration) : TestSeq :=
  -- FALSE dominates AND, TRUE dominates OR
  check (cfg := cfg) "FALSE AND NULL = FALSE" (∀ t : Option SqlType,
    evalBinOp .and (some (.bool false)) (some (.null t)) == some (.bool false)) $
  check (cfg := cfg) "NULL AND FALSE = FALSE" (∀ t : Option SqlType,
    evalBinOp .and (some (.null t)) (some (.bool false)) == some (.bool false)) $
  check (cfg := cfg) "TRUE OR NULL = TRUE" (∀ t : Option SqlType,
    evalBinOp .or (some (.bool true)) (some (.null t)) == some (.bool true)) $
  check (cfg := cfg) "NULL OR TRUE = TRUE" (∀ t : Option SqlType,
    evalBinOp .or (some (.null t)) (some (.bool true)) == some (.bool true)) $
  -- Non-dominating cases: AND/OR with NULL propagates NULL (SQL three-valued logic)
  check (cfg := cfg) "TRUE AND NULL = NULL" (∀ t : Option SqlType,
    evalBinOp .and (some (.bool true)) (some (.null t)) == some (.null none)) $
  check (cfg := cfg) "NULL AND TRUE = NULL" (∀ t : Option SqlType,
    evalBinOp .and (some (.null t)) (some (.bool true)) == some (.null none)) $
  check (cfg := cfg) "FALSE OR NULL = NULL" (∀ t : Option SqlType,
    evalBinOp .or (some (.bool false)) (some (.null t)) == some (.null none)) $
  check (cfg := cfg) "NULL OR FALSE = NULL" (∀ t : Option SqlType,
    evalBinOp .or (some (.null t)) (some (.bool false)) == some (.null none)) $
  -- NULL AND/OR NULL = NULL
  check (cfg := cfg) "NULL AND NULL = NULL" (∀ t1 t2 : Option SqlType,
    evalBinOp .and (some (.null t1)) (some (.null t2)) == some (.null none)) $
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
  check (cfg := cfg) "IS NULL and IS NOT NULL are complementary" (∀ v : Value,
    isNullComplement v) $
  check (cfg := cfg) "IS NULL on NULL = TRUE" (∀ t : Option SqlType,
    evalUnaryOp .isNull (some (.null t)) == some (.bool true)) $
  check (cfg := cfg) "IS NOT NULL on NULL = FALSE" (∀ t : Option SqlType,
    evalUnaryOp .isNotNull (some (.null t)) == some (.bool false)) $
  check (cfg := cfg) "IS NULL on int = FALSE" (∀ n : Int,
    evalUnaryOp .isNull (some (.int n)) == some (.bool false)) $
  check (cfg := cfg) "IS NOT NULL on int = TRUE" (∀ n : Int,
    evalUnaryOp .isNotNull (some (.int n)) == some (.bool true))

-- ============================================================================
-- COALESCE
-- ============================================================================

def coalesceTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "COALESCE(int, x) = int" (∀ n : Int, ∀ v : Value,
    evalFunc "COALESCE" [some (.int n), some v] == some (.int n)) $
  check (cfg := cfg) "COALESCE(string, x) = string" (∀ v : Value,
    evalFunc "COALESCE" [some (.string "hello"), some v] == some (.string "hello")) $
  check (cfg := cfg) "COALESCE(bool, x) = bool" (∀ b : Bool, ∀ v : Value,
    evalFunc "COALESCE" [some (.bool b), some v] == some (.bool b)) $
  check (cfg := cfg) "COALESCE(NULL, int) = int" (∀ n : Int,
    evalFunc "COALESCE" [some (.null none), some (.int n)] == some (.int n))

-- ============================================================================
-- Scalar function tests (evalFunc)
-- ============================================================================

def nullifTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "NULLIF(n, n) = NULL" (∀ n : Int,
    evalFunc "NULLIF" [some (.int n), some (.int n)] == some (.null none)) $
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

def stringFuncTests : TestSeq :=
  test "LENGTH(hello) = 5" (
    evalFunc "LENGTH" [some (.string "hello")] == some (.int 5)) $
  test "LENGTH empty = 0" (
    evalFunc "LENGTH" [some (.string "")] == some (.int 0)) $
  test "UPPER(hello) = HELLO" (
    evalFunc "UPPER" [some (.string "hello")] == some (.string "HELLO")) $
  test "LOWER(HELLO) = hello" (
    evalFunc "LOWER" [some (.string "HELLO")] == some (.string "hello")) $
  test "UPPER(LOWER(s)) = UPPER(s)" (
    evalFunc "UPPER" [evalFunc "LOWER" [some (.string "Hello")]] ==
    evalFunc "UPPER" [some (.string "Hello")]) $
  test "LOWER(UPPER(s)) = LOWER(s)" (
    evalFunc "LOWER" [evalFunc "UPPER" [some (.string "Hello")]] ==
    evalFunc "LOWER" [some (.string "Hello")]) $
  test "CONCAT(s, empty) = s" (
    evalFunc "CONCAT" [some (.string "hello"), some (.string "")] ==
    some (.string "hello")) $
  test "CONCAT(empty, s) = s" (
    evalFunc "CONCAT" [some (.string ""), some (.string "world")] ==
    some (.string "world"))

-- ============================================================================
-- All NULL semantics tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Arithmetic NULL Propagation" (nullArithTests cfg) $
  group "Comparison NULL Propagation" (nullComparisonTests cfg) $
  group "Three-Valued Logic" (threeValuedLogicTests cfg) $
  group "IS NULL / IS NOT NULL" (isNullTests cfg) $
  group "COALESCE" (coalesceTests cfg) $
  group "NULLIF" (nullifTests cfg) $
  group "ABS" (absTests cfg) $
  group "String Functions" stringFuncTests

end NullSemantics
