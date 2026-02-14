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
  check (cfg := slimCfg) "NULL + x = NULL" (∀ v : Value,
    evalBinOp .add (some (.null none)) (some v) == some (.null none)) $
  check (cfg := slimCfg) "x + NULL = NULL" (∀ v : Value,
    evalBinOp .add (some v) (some (.null none)) == some (.null none)) $
  check (cfg := slimCfg) "NULL - x = NULL" (∀ v : Value,
    evalBinOp .sub (some (.null none)) (some v) == some (.null none)) $
  check (cfg := slimCfg) "x - NULL = NULL" (∀ v : Value,
    evalBinOp .sub (some v) (some (.null none)) == some (.null none)) $
  check (cfg := slimCfg) "NULL * x = NULL" (∀ v : Value,
    evalBinOp .mul (some (.null none)) (some v) == some (.null none)) $
  check (cfg := slimCfg) "x * NULL = NULL" (∀ v : Value,
    evalBinOp .mul (some v) (some (.null none)) == some (.null none)) $
  check (cfg := slimCfg) "NULL / x = NULL" (∀ v : Value,
    evalBinOp .div (some (.null none)) (some v) == some (.null none)) $
  check (cfg := slimCfg) "x / NULL = NULL" (∀ v : Value,
    evalBinOp .div (some v) (some (.null none)) == some (.null none))

-- ============================================================================
-- Comparison NULL propagation
-- ============================================================================

def nullComparisonTests : TestSeq :=
  check (cfg := slimCfg) "NULL = x = NULL" (∀ v : Value,
    evalBinOp .eq (some (.null none)) (some v) == some (.null none)) $
  check (cfg := slimCfg) "x = NULL = NULL" (∀ v : Value,
    evalBinOp .eq (some v) (some (.null none)) == some (.null none)) $
  check (cfg := slimCfg) "NULL < x = NULL" (∀ v : Value,
    evalBinOp .lt (some (.null none)) (some v) == some (.null none)) $
  check (cfg := slimCfg) "x < NULL = NULL" (∀ v : Value,
    evalBinOp .lt (some v) (some (.null none)) == some (.null none))

-- ============================================================================
-- Three-valued logic with NULL
-- ============================================================================

def threeValuedLogicTests : TestSeq :=
  -- FALSE dominates AND, TRUE dominates OR
  check (cfg := slimCfg) "FALSE AND NULL = FALSE" (∀ t : Option SqlType,
    evalBinOp .and (some (.bool false)) (some (.null t)) == some (.bool false)) $
  check (cfg := slimCfg) "NULL AND FALSE = FALSE" (∀ t : Option SqlType,
    evalBinOp .and (some (.null t)) (some (.bool false)) == some (.bool false)) $
  check (cfg := slimCfg) "TRUE OR NULL = TRUE" (∀ t : Option SqlType,
    evalBinOp .or (some (.bool true)) (some (.null t)) == some (.bool true)) $
  check (cfg := slimCfg) "NULL OR TRUE = TRUE" (∀ t : Option SqlType,
    evalBinOp .or (some (.null t)) (some (.bool true)) == some (.bool true)) $
  -- Non-dominating cases: AND/OR with NULL propagates NULL (SQL three-valued logic)
  check (cfg := slimCfg) "TRUE AND NULL = NULL" (∀ t : Option SqlType,
    evalBinOp .and (some (.bool true)) (some (.null t)) == some (.null none)) $
  check (cfg := slimCfg) "NULL AND TRUE = NULL" (∀ t : Option SqlType,
    evalBinOp .and (some (.null t)) (some (.bool true)) == some (.null none)) $
  check (cfg := slimCfg) "FALSE OR NULL = NULL" (∀ t : Option SqlType,
    evalBinOp .or (some (.bool false)) (some (.null t)) == some (.null none)) $
  check (cfg := slimCfg) "NULL OR FALSE = NULL" (∀ t : Option SqlType,
    evalBinOp .or (some (.null t)) (some (.bool false)) == some (.null none)) $
  -- NULL AND/OR NULL = NULL
  check (cfg := slimCfg) "NULL AND NULL = NULL" (∀ t1 t2 : Option SqlType,
    evalBinOp .and (some (.null t1)) (some (.null t2)) == some (.null none)) $
  check (cfg := slimCfg) "NULL OR NULL = NULL" (∀ t1 t2 : Option SqlType,
    evalBinOp .or (some (.null t1)) (some (.null t2)) == some (.null none))

-- ============================================================================
-- IS NULL / IS NOT NULL
-- ============================================================================

private def isNullComplement (v : Value) : Bool :=
  match evalUnaryOp .isNull (some v), evalUnaryOp .isNotNull (some v) with
  | some (.bool a), some (.bool b) => a == !b
  | _, _ => false

def isNullTests : TestSeq :=
  check (cfg := slimCfg) "IS NULL and IS NOT NULL are complementary" (∀ v : Value,
    isNullComplement v) $
  check (cfg := slimCfg) "IS NULL on NULL = TRUE" (∀ t : Option SqlType,
    evalUnaryOp .isNull (some (.null t)) == some (.bool true)) $
  check (cfg := slimCfg) "IS NOT NULL on NULL = FALSE" (∀ t : Option SqlType,
    evalUnaryOp .isNotNull (some (.null t)) == some (.bool false)) $
  check (cfg := slimCfg) "IS NULL on int = FALSE" (∀ n : Int,
    evalUnaryOp .isNull (some (.int n)) == some (.bool false)) $
  check (cfg := slimCfg) "IS NOT NULL on int = TRUE" (∀ n : Int,
    evalUnaryOp .isNotNull (some (.int n)) == some (.bool true))

-- ============================================================================
-- COALESCE
-- ============================================================================

def coalesceTests : TestSeq :=
  check (cfg := slimCfg) "COALESCE(int, x) = int" (∀ n : Int, ∀ v : Value,
    evalFunc "COALESCE" [some (.int n), some v] == some (.int n)) $
  check (cfg := slimCfg) "COALESCE(string, x) = string" (∀ v : Value,
    evalFunc "COALESCE" [some (.string "hello"), some v] == some (.string "hello")) $
  check (cfg := slimCfg) "COALESCE(bool, x) = bool" (∀ b : Bool, ∀ v : Value,
    evalFunc "COALESCE" [some (.bool b), some v] == some (.bool b)) $
  check (cfg := slimCfg) "COALESCE(NULL, int) = int" (∀ n : Int,
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
