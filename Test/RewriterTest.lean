/-
  Tests for the Certified Expression Rewriter
-/
import SqlEquiv
import Test.Common

namespace RewriterTest

open SqlEquiv
open Test

-- ============================================================================
-- Test Helpers
-- ============================================================================

/-- Test that certifiedRewrite produces the expected output expression -/
private def testRewrite (name : String) (input expected : Expr) : TestResult :=
  let ⟨result, _proof⟩ := certifiedRewrite input
  if result == expected then .pass name
  else .fail name s!"Expected: {expected.toSql}, Got: {result.toSql}"

-- ============================================================================
-- BinOp Simplification Tests
-- ============================================================================

private def binOpTests : List TestResult := [
  -- AND FALSE → FALSE
  testRewrite "and_false (x AND FALSE → FALSE)"
    (.binOp .and (col "x") (boolLit false))
    (boolLit false),

  testRewrite "false_and (FALSE AND x → FALSE)"
    (.binOp .and (boolLit false) (col "x"))
    (boolLit false),

  -- OR TRUE → TRUE
  testRewrite "or_true (x OR TRUE → TRUE)"
    (.binOp .or (col "x") (boolLit true))
    (boolLit true),

  testRewrite "true_or (TRUE OR x → TRUE)"
    (.binOp .or (boolLit true) (col "x"))
    (boolLit true),

  -- LIKE empty pattern → EQ
  testRewrite "like_empty_pattern (x LIKE '' → x = '')"
    (.binOp .like (col "x") (strLit ""))
    (.binOp .eq (col "x") (strLit "")),

  -- No simplification cases
  testRewrite "and_no_change (x AND y unchanged)"
    (.binOp .and (col "x") (col "y"))
    (.binOp .and (col "x") (col "y")),

  testRewrite "or_no_change (x OR y unchanged)"
    (.binOp .or (col "x") (col "y"))
    (.binOp .or (col "x") (col "y")),

  -- Overlapping pattern: FALSE AND FALSE → FALSE (first match wins)
  testRewrite "false_and_false (FALSE AND FALSE → FALSE)"
    (.binOp .and (boolLit false) (boolLit false))
    (boolLit false)
]

-- ============================================================================
-- UnaryOp Simplification Tests
-- ============================================================================

private def unaryOpTests : List TestResult := [
  -- NOT(comparison) → flipped comparison
  testRewrite "not_eq_is_ne (NOT(a = b) → a <> b)"
    (.unaryOp .not (.binOp .eq (col "a") (col "b")))
    (.binOp .ne (col "a") (col "b")),

  testRewrite "not_ne_is_eq (NOT(a <> b) → a = b)"
    (.unaryOp .not (.binOp .ne (col "a") (col "b")))
    (.binOp .eq (col "a") (col "b")),

  testRewrite "not_lt_is_ge (NOT(a < b) → a >= b)"
    (.unaryOp .not (.binOp .lt (col "a") (col "b")))
    (.binOp .ge (col "a") (col "b")),

  testRewrite "not_le_is_gt (NOT(a <= b) → a > b)"
    (.unaryOp .not (.binOp .le (col "a") (col "b")))
    (.binOp .gt (col "a") (col "b")),

  testRewrite "not_gt_is_le (NOT(a > b) → a <= b)"
    (.unaryOp .not (.binOp .gt (col "a") (col "b")))
    (.binOp .le (col "a") (col "b")),

  testRewrite "not_ge_is_lt (NOT(a >= b) → a < b)"
    (.unaryOp .not (.binOp .ge (col "a") (col "b")))
    (.binOp .lt (col "a") (col "b")),

  -- NOT(BETWEEN) → OR(LT, GT)
  testRewrite "not_between_expansion (NOT(x BETWEEN 1 AND 10) → x < 1 OR x > 10)"
    (.unaryOp .not (.between (col "x") (intLit 1) (intLit 10)))
    (.binOp .or (.binOp .lt (col "x") (intLit 1)) (.binOp .gt (col "x") (intLit 10))),

  -- NOT(EXISTS) → flipped flag
  let sel : SelectStmt := ⟨false, [SelectItem.star none], none, none, [], none, [], none, none⟩
  testRewrite "not_exists_flip (NOT(EXISTS sel) → NOT EXISTS sel)"
    (.unaryOp .not (.«exists» false sel))
    (.«exists» true sel),

  let sel : SelectStmt := ⟨false, [SelectItem.star none], none, none, [], none, [], none, none⟩
  testRewrite "not_not_exists_flip (NOT(NOT EXISTS sel) → EXISTS sel)"
    (.unaryOp .not (.«exists» true sel))
    (.«exists» false sel),

  -- No simplification for NOT on non-comparison
  testRewrite "not_col_no_change (NOT(x) unchanged)"
    (.unaryOp .not (col "x"))
    (.unaryOp .not (col "x")),

  -- IS NULL / IS NOT NULL unchanged
  testRewrite "isNull_no_change (x IS NULL unchanged)"
    (.unaryOp .isNull (col "x"))
    (.unaryOp .isNull (col "x"))
]

-- ============================================================================
-- BETWEEN Simplification Tests
-- ============================================================================

private def betweenTests : List TestResult := [
  -- BETWEEN always expands
  testRewrite "between_expansion (x BETWEEN 1 AND 10 → x >= 1 AND x <= 10)"
    (.between (col "x") (intLit 1) (intLit 10))
    (.binOp .and (.binOp .ge (col "x") (intLit 1)) (.binOp .le (col "x") (intLit 10))),

  -- Type-mismatched BETWEEN still expands (unconditional)
  testRewrite "between_type_mismatch (x BETWEEN FALSE AND 10 → x >= FALSE AND x <= 10)"
    (.between (col "x") (boolLit false) (intLit 10))
    (.binOp .and (.binOp .ge (col "x") (boolLit false)) (.binOp .le (col "x") (intLit 10)))
]

-- ============================================================================
-- IN List Simplification Tests
-- ============================================================================

private def inListTests : List TestResult := [
  testRewrite "in_empty_false (x IN () → FALSE)"
    (.inList (col "x") false [])
    (boolLit false),

  testRewrite "not_in_empty_true (x NOT IN () → TRUE)"
    (.inList (col "x") true [])
    (boolLit true),

  testRewrite "in_singleton (x IN (1) → x = 1)"
    (.inList (col "x") false [intLit 1])
    (.binOp .eq (col "x") (intLit 1)),

  testRewrite "not_in_singleton (x NOT IN (1) → x <> 1)"
    (.inList (col "x") true [intLit 1])
    (.binOp .ne (col "x") (intLit 1)),

  -- Multi-element IN list unchanged
  testRewrite "in_multi_no_change (x IN (1, 2) unchanged)"
    (.inList (col "x") false [intLit 1, intLit 2])
    (.inList (col "x") false [intLit 1, intLit 2])
]

-- ============================================================================
-- CASE Simplification Tests
-- ============================================================================

private def caseTests : List TestResult := [
  testRewrite "case_when_true (CASE WHEN TRUE THEN x ELSE y → x)"
    (.«case» [(.lit (.bool true), col "x")] (some (col "y")))
    (col "x"),

  testRewrite "case_when_false (CASE WHEN FALSE THEN x ELSE y → y)"
    (.«case» [(.lit (.bool false), col "x")] (some (col "y")))
    (col "y"),

  testRewrite "case_when_false_no_else (CASE WHEN FALSE THEN x → NULL)"
    (.«case» [(.lit (.bool false), col "x")] none)
    (.lit (.null none)),

  testRewrite "case_empty_else (CASE ELSE y → y)"
    (.«case» [] (some (col "y")))
    (col "y"),

  testRewrite "case_empty_no_else (CASE → NULL)"
    (.«case» [] none)
    (.lit (.null none)),

  -- Multi-branch CASE unchanged
  testRewrite "case_multi_no_change (multi-branch CASE unchanged)"
    (.«case» [(col "c1", col "r1"), (col "c2", col "r2")] (some (col "d")))
    (.«case» [(col "c1", col "r1"), (col "c2", col "r2")] (some (col "d")))
]

-- ============================================================================
-- Conditional Boolean Identity Tests
-- ============================================================================

private def conditionalBoolTests : List TestResult := [
  -- Guard passes: IS_NULL is definitely bool
  testRewrite "and_true (IS_NULL(x) AND TRUE → IS_NULL(x))"
    (.binOp .and (.unaryOp .isNull (col "x")) (boolLit true))
    (.unaryOp .isNull (col "x")),

  testRewrite "true_and (TRUE AND IS_NULL(x) → IS_NULL(x))"
    (.binOp .and (boolLit true) (.unaryOp .isNull (col "x")))
    (.unaryOp .isNull (col "x")),

  testRewrite "or_false (IS_NULL(x) OR FALSE → IS_NULL(x))"
    (.binOp .or (.unaryOp .isNull (col "x")) (boolLit false))
    (.unaryOp .isNull (col "x")),

  testRewrite "false_or (FALSE OR IS_NULL(x) → IS_NULL(x))"
    (.binOp .or (boolLit false) (.unaryOp .isNull (col "x")))
    (.unaryOp .isNull (col "x")),

  -- NOT NOT with definitely bool inner
  testRewrite "not_not_isNull (NOT NOT IS_NULL(x) → IS_NULL(x))"
    (.unaryOp .not (.unaryOp .not (.unaryOp .isNull (col "x"))))
    (.unaryOp .isNull (col "x")),

  let sel : SelectStmt := ⟨false, [SelectItem.star none], none, none, [], none, [], none, none⟩
  testRewrite "not_not_exists (NOT NOT EXISTS sel → EXISTS sel)"
    (.unaryOp .not (.unaryOp .not (.«exists» false sel)))
    (.«exists» false sel),

  -- Guard fails: col is NOT definitely bool → unchanged
  testRewrite "and_true_col_unchanged (col AND TRUE unchanged)"
    (.binOp .and (col "x") (boolLit true))
    (.binOp .and (col "x") (boolLit true)),

  -- Guard fails: comparison is NOT definitely bool
  testRewrite "and_true_eq_unchanged ((a = b) AND TRUE unchanged)"
    (.binOp .and (.binOp .eq (col "a") (col "b")) (boolLit true))
    (.binOp .and (.binOp .eq (col "a") (col "b")) (boolLit true)),

  -- Guard fails: NOT NOT col unchanged
  testRewrite "not_not_col_unchanged (NOT NOT col unchanged)"
    (.unaryOp .not (.unaryOp .not (col "x")))
    (.unaryOp .not (.unaryOp .not (col "x"))),

  -- Bool literal: TRUE AND TRUE → TRUE (guard passes, lit is definitely bool)
  testRewrite "and_true_lit (TRUE AND TRUE → TRUE)"
    (.binOp .and (boolLit true) (boolLit true))
    (boolLit true)
]

-- ============================================================================
-- Conditional Arithmetic Identity Tests
-- ============================================================================

private def conditionalArithTests : List TestResult := [
  -- Guard passes: int literals are definitely int
  testRewrite "add_zero (5 + 0 → 5)"
    (.binOp .add (intLit 5) (intLit 0))
    (intLit 5),

  testRewrite "zero_add (0 + 5 → 5)"
    (.binOp .add (intLit 0) (intLit 5))
    (intLit 5),

  testRewrite "mul_one (5 * 1 → 5)"
    (.binOp .mul (intLit 5) (intLit 1))
    (intLit 5),

  testRewrite "one_mul (1 * 5 → 5)"
    (.binOp .mul (intLit 1) (intLit 5))
    (intLit 5),

  testRewrite "sub_zero (5 - 0 → 5)"
    (.binOp .sub (intLit 5) (intLit 0))
    (intLit 5),

  -- Guard fails: col is NOT definitely int → unchanged
  testRewrite "add_zero_col_unchanged (col + 0 unchanged)"
    (.binOp .add (col "x") (intLit 0))
    (.binOp .add (col "x") (intLit 0)),

  -- Nested: (3 + 2) + 0 → (3 + 2), since 3+2 is definitely int
  testRewrite "add_zero_nested ((3 + 2) + 0 → 3 + 2)"
    (.binOp .add (.binOp .add (intLit 3) (intLit 2)) (intLit 0))
    (.binOp .add (intLit 3) (intLit 2))
]

-- ============================================================================
-- Bottom-Up + Conditional Composition Tests
-- ============================================================================

private def compositionTests : List TestResult := [
  -- NOT NOT IS_NULL(x) AND TRUE → IS_NULL(x)
  -- Inner: NOT NOT IS_NULL(x) → IS_NULL(x) (conditional NOT-NOT)
  -- Then: IS_NULL(x) AND TRUE → IS_NULL(x) (conditional AND TRUE)
  testRewrite "composition_not_not_and_true (NOT NOT IS_NULL(x) AND TRUE → IS_NULL(x))"
    (.binOp .and (.unaryOp .not (.unaryOp .not (.unaryOp .isNull (col "x")))) (boolLit true))
    (.unaryOp .isNull (col "x"))
]

-- ============================================================================
-- Bottom-Up Recursion Tests
-- ============================================================================

private def recursionTests : List TestResult := [
  -- NOT(x = y) AND FALSE → FALSE
  -- Inner: NOT(EQ) → NE, then outer: NE AND FALSE → FALSE
  testRewrite "bottom_up_not_eq_and_false (NOT(x = y) AND FALSE → FALSE)"
    (.binOp .and (.unaryOp .not (.binOp .eq (col "x") (col "y"))) (boolLit false))
    (boolLit false),

  -- TRUE OR NOT(a < b) → TRUE
  -- Inner: NOT(LT) → GE, then outer: TRUE OR GE → TRUE
  testRewrite "bottom_up_true_or_not_lt (TRUE OR NOT(a < b) → TRUE)"
    (.binOp .or (boolLit true) (.unaryOp .not (.binOp .lt (col "a") (col "b"))))
    (boolLit true),

  -- BETWEEN inside AND: (x BETWEEN 1 AND 10) AND FALSE → FALSE
  -- Inner: BETWEEN expands, then outer: AND FALSE → FALSE
  testRewrite "bottom_up_between_and_false ((x BETWEEN 1 AND 10) AND FALSE → FALSE)"
    (.binOp .and (.between (col "x") (intLit 1) (intLit 10)) (boolLit false))
    (boolLit false),

  -- Nested NOT(NOT(x = y)): inner NOT(EQ) → NE, outer NOT(NE) → EQ
  testRewrite "bottom_up_not_not_eq (NOT(NOT(x = y)) → x = y)"
    (.unaryOp .not (.unaryOp .not (.binOp .eq (col "x") (col "y"))))
    (.binOp .eq (col "x") (col "y")),

  -- Nested NOT(NOT(a > b)): inner NOT(GT) → LE, outer NOT(LE) → GT
  testRewrite "bottom_up_not_not_gt (NOT(NOT(a > b)) → a > b)"
    (.unaryOp .not (.unaryOp .not (.binOp .gt (col "a") (col "b"))))
    (.binOp .gt (col "a") (col "b"))
]

-- ============================================================================
-- Idempotency Tests
-- ============================================================================

private def idempotencyTests : List TestResult := [
  -- Already-simple expressions return unchanged
  testRewrite "idempotent_col (column unchanged)"
    (col "x") (col "x"),

  testRewrite "idempotent_lit (literal unchanged)"
    (intLit 42) (intLit 42),

  testRewrite "idempotent_eq (a = b unchanged)"
    (.binOp .eq (col "a") (col "b"))
    (.binOp .eq (col "a") (col "b")),

  testRewrite "idempotent_countstar (COUNT(*) unchanged)"
    .countStar .countStar,

  -- Double rewrite produces same result
  let input := .binOp .and (.unaryOp .not (.binOp .eq (col "x") (col "y"))) (boolLit false)
  let ⟨first, _⟩ := certifiedRewrite input
  let ⟨second, _⟩ := certifiedRewrite first
  if second == first then .pass "idempotent_double_rewrite (rewriting twice = rewriting once)"
  else .fail "idempotent_double_rewrite" s!"First: {first.toSql}, Second: {second.toSql}"
]

-- ============================================================================
-- Leaf Node Tests
-- ============================================================================

private def leafTests : List TestResult := [
  testRewrite "leaf_func (func unchanged)"
    (.func "UPPER" [col "x"])
    (.func "UPPER" [col "x"]),

  testRewrite "leaf_agg (agg unchanged)"
    (.agg .sum (some (col "x")) false)
    (.agg .sum (some (col "x")) false),

  let sel : SelectStmt := ⟨false, [SelectItem.star none], none, none, [], none, [], none, none⟩
  testRewrite "leaf_subquery (subquery unchanged)"
    (.subquery sel) (.subquery sel),

  testRewrite "leaf_null (null unchanged)"
    nullLit nullLit,

  testRewrite "leaf_string (string unchanged)"
    (strLit "hello") (strLit "hello")
]

-- ============================================================================
-- Test Suite
-- ============================================================================

def allTests : List TestResult :=
  binOpTests ++ unaryOpTests ++ betweenTests ++ inListTests ++
  caseTests ++ conditionalBoolTests ++ conditionalArithTests ++
  compositionTests ++ recursionTests ++ idempotencyTests ++ leafTests

def runRewriterTests : IO (Nat × Nat) :=
  runTests "Certified Rewriter Tests" allTests

end RewriterTest
