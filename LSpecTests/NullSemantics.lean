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

def nullArithTests : TestSeq :=
  check "NULL + x = NULL" (∀ v : Value,
    evalBinOp .add (some (.null none)) (some v) == some (.null none)) $
  check "x + NULL = NULL" (∀ v : Value,
    evalBinOp .add (some v) (some (.null none)) == some (.null none)) $
  check "NULL - x = NULL" (∀ v : Value,
    evalBinOp .sub (some (.null none)) (some v) == some (.null none)) $
  check "x - NULL = NULL" (∀ v : Value,
    evalBinOp .sub (some v) (some (.null none)) == some (.null none)) $
  check "NULL * x = NULL" (∀ v : Value,
    evalBinOp .mul (some (.null none)) (some v) == some (.null none)) $
  check "x * NULL = NULL" (∀ v : Value,
    evalBinOp .mul (some v) (some (.null none)) == some (.null none)) $
  check "NULL / x = NULL" (∀ v : Value,
    evalBinOp .div (some (.null none)) (some v) == some (.null none)) $
  check "x / NULL = NULL" (∀ v : Value,
    evalBinOp .div (some v) (some (.null none)) == some (.null none))

-- ============================================================================
-- Comparison NULL propagation
-- ============================================================================

def nullComparisonTests : TestSeq :=
  check "NULL = x = NULL" (∀ v : Value,
    evalBinOp .eq (some (.null none)) (some v) == some (.null none)) $
  check "x = NULL = NULL" (∀ v : Value,
    evalBinOp .eq (some v) (some (.null none)) == some (.null none)) $
  check "NULL < x = NULL" (∀ v : Value,
    evalBinOp .lt (some (.null none)) (some v) == some (.null none)) $
  check "x < NULL = NULL" (∀ v : Value,
    evalBinOp .lt (some v) (some (.null none)) == some (.null none))

-- ============================================================================
-- Three-valued logic with NULL
-- ============================================================================

def threeValuedLogicTests : TestSeq :=
  -- FALSE dominates AND, TRUE dominates OR
  check "FALSE AND NULL = FALSE" (∀ t : Option SqlType,
    evalBinOp .and (some (.bool false)) (some (.null t)) == some (.bool false)) $
  check "NULL AND FALSE = FALSE" (∀ t : Option SqlType,
    evalBinOp .and (some (.null t)) (some (.bool false)) == some (.bool false)) $
  check "TRUE OR NULL = TRUE" (∀ t : Option SqlType,
    evalBinOp .or (some (.bool true)) (some (.null t)) == some (.bool true)) $
  check "NULL OR TRUE = TRUE" (∀ t : Option SqlType,
    evalBinOp .or (some (.null t)) (some (.bool true)) == some (.bool true)) $
  -- Non-dominating cases: AND/OR with NULL returns none (not a SQL NULL value)
  check "TRUE AND NULL = none" (∀ t : Option SqlType,
    evalBinOp .and (some (.bool true)) (some (.null t)) == none) $
  check "NULL AND TRUE = none" (∀ t : Option SqlType,
    evalBinOp .and (some (.null t)) (some (.bool true)) == none) $
  check "FALSE OR NULL = none" (∀ t : Option SqlType,
    evalBinOp .or (some (.bool false)) (some (.null t)) == none) $
  check "NULL OR FALSE = none" (∀ t : Option SqlType,
    evalBinOp .or (some (.null t)) (some (.bool false)) == none) $
  -- NULL AND/OR NULL = none
  check "NULL AND NULL = none" (∀ t1 t2 : Option SqlType,
    evalBinOp .and (some (.null t1)) (some (.null t2)) == none) $
  check "NULL OR NULL = none" (∀ t1 t2 : Option SqlType,
    evalBinOp .or (some (.null t1)) (some (.null t2)) == none)

-- ============================================================================
-- IS NULL / IS NOT NULL
-- ============================================================================

private def isNullComplement (v : Value) : Bool :=
  match evalUnaryOp .isNull (some v), evalUnaryOp .isNotNull (some v) with
  | some (.bool a), some (.bool b) => a == !b
  | _, _ => false

def isNullTests : TestSeq :=
  check "IS NULL and IS NOT NULL are complementary" (∀ v : Value,
    isNullComplement v) $
  check "IS NULL on NULL = TRUE" (∀ t : Option SqlType,
    evalUnaryOp .isNull (some (.null t)) == some (.bool true)) $
  check "IS NOT NULL on NULL = FALSE" (∀ t : Option SqlType,
    evalUnaryOp .isNotNull (some (.null t)) == some (.bool false)) $
  check "IS NULL on int = FALSE" (∀ n : Int,
    evalUnaryOp .isNull (some (.int n)) == some (.bool false)) $
  check "IS NOT NULL on int = TRUE" (∀ n : Int,
    evalUnaryOp .isNotNull (some (.int n)) == some (.bool true))

-- ============================================================================
-- COALESCE
-- ============================================================================

def coalesceTests : TestSeq :=
  check "COALESCE(int, x) = int" (∀ n : Int, ∀ v : Value,
    evalFunc "COALESCE" [some (.int n), some v] == some (.int n)) $
  check "COALESCE(string, x) = string" (∀ v : Value,
    evalFunc "COALESCE" [some (.string "hello"), some v] == some (.string "hello")) $
  check "COALESCE(bool, x) = bool" (∀ b : Bool, ∀ v : Value,
    evalFunc "COALESCE" [some (.bool b), some v] == some (.bool b)) $
  check "COALESCE(NULL, int) = int" (∀ n : Int,
    evalFunc "COALESCE" [some (.null none), some (.int n)] == some (.int n))

-- ============================================================================
-- All NULL semantics tests
-- ============================================================================

def allTests : TestSeq :=
  group "Arithmetic NULL Propagation" nullArithTests $
  group "Comparison NULL Propagation" nullComparisonTests $
  group "Three-Valued Logic" threeValuedLogicTests $
  group "IS NULL / IS NOT NULL" isNullTests $
  group "COALESCE" coalesceTests

end NullSemantics
