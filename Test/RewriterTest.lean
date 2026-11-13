/-
  Tests for the Certified Expression Rewriter
-/
import SqlEquiv
import Test.Common

namespace RewriterTest

open SqlEquiv
open Test

-- ============================================================================
-- Axiom Guard
-- ============================================================================

-- Compile-time regression guards for the trust base (#212, #237).
-- The rewriter's correctness proof must not depend on compiler trust
-- (`Lean.ofReduceBool` / `Lean.trustCompiler`, i.e. `native_decide`) or on
-- `sorryAx`. Since #212 the evaluator's termination is kernel-checked (size-
-- guarded callbacks), so expression-level theorems are sorry-free.
/--
info: 'SqlEquiv.certifiedRewriteAux_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms certifiedRewriteAux_equiv

/--
info: 'SqlEquiv.evalSelect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms evalSelect

-- SELECT-level theorems still inherit `sorryAx` from the two SELECT bridge
-- lemmas (`evalSelect_eq_evalSelectCore`, `evalSelectWithContext_eq_
-- evalSelectCore`), pending #212 phase 2. Remove `sorryAx` here when they close.
/--
info: 'SqlEquiv.select_where_congr' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms select_where_congr

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
  let sel : SubQuery := .simple ⟨false, [SelectItem.star none], none, none, [], none, [], none, none⟩
  testRewrite "not_exists_flip (NOT(EXISTS sel) → NOT EXISTS sel)"
    (.unaryOp .not (.«exists» false sel))
    (.«exists» true sel),

  let sel : SubQuery := .simple ⟨false, [SelectItem.star none], none, none, [], none, [], none, none⟩
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

  let sel : SubQuery := .simple ⟨false, [SelectItem.star none], none, none, [], none, [], none, none⟩
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

  let sel : SubQuery := .simple ⟨false, [SelectItem.star none], none, none, [], none, [], none, none⟩
  testRewrite "leaf_subquery (subquery unchanged)"
    (.subquery sel) (.subquery sel),

  testRewrite "leaf_null (null unchanged)"
    nullLit nullLit,

  testRewrite "leaf_string (string unchanged)"
    (strLit "hello") (strLit "hello")
]

-- ============================================================================
-- Subexpression Recursion Tests (Phase 2b)
-- ============================================================================

private def subexprRecursionTests : List TestResult := [
  -- Func: recurse into args
  testRewrite "func_recursion (UPPER(x OR TRUE) → UPPER(TRUE))"
    (.func "UPPER" [.binOp .or (col "x") (boolLit true)])
    (.func "UPPER" [boolLit true]),

  -- Func: multi-arg recursion
  testRewrite "func_multi_arg_recursion (CONCAT(x AND FALSE, y OR TRUE) → CONCAT(FALSE, TRUE))"
    (.func "CONCAT" [.binOp .and (col "x") (boolLit false), .binOp .or (col "y") (boolLit true)])
    (.func "CONCAT" [boolLit false, boolLit true]),

  -- Agg: recurse into arg
  testRewrite "agg_recursion (SUM(x BETWEEN 1 AND 10) → SUM(x >= 1 AND x <= 10))"
    (.agg .sum (some (.between (col "x") (intLit 1) (intLit 10))) false)
    (.agg .sum (some (.binOp .and (.binOp .ge (col "x") (intLit 1)) (.binOp .le (col "x") (intLit 10)))) false),

  -- Agg: none arg unchanged
  testRewrite "agg_no_arg (COUNT(*) style SUM(none) unchanged)"
    (.agg .sum none false)
    (.agg .sum none false),

  -- WindowFn: recurse into arg
  let spec : WindowSpec := .mk [] []
  testRewrite "windowFn_recursion (ROW_NUMBER(x AND FALSE) → ROW_NUMBER(FALSE))"
    (.windowFn .rowNumber (some (.binOp .and (col "x") (boolLit false))) spec)
    (.windowFn .rowNumber (some (boolLit false)) spec),

  -- WindowFn: none arg unchanged
  let spec : WindowSpec := .mk [] []
  testRewrite "windowFn_no_arg (ROW_NUMBER(none) unchanged)"
    (.windowFn .rowNumber none spec)
    (.windowFn .rowNumber none spec),

  -- InSubquery: recurse into expression
  let sel : SubQuery := .simple ⟨false, [SelectItem.star none], none, none, [], none, [], none, none⟩
  testRewrite "inSubquery_recursion ((x OR TRUE) IN subquery → TRUE IN subquery)"
    (.inSubquery (.binOp .or (col "x") (boolLit true)) false sel)
    (.inSubquery (boolLit true) false sel),

  -- InList: recurse into vals
  testRewrite "inList_vals_recursion (x IN (NOT(a=b), c) → x IN (a<>b, c))"
    (.inList (col "x") false [.unaryOp .not (.binOp .eq (col "a") (col "b")), col "c"])
    (.inList (col "x") false [.binOp .ne (col "a") (col "b"), col "c"]),

  -- InList: recurse into both expr and vals, then singleton rule fires
  testRewrite "inList_expr_and_vals_recursion ((x AND FALSE) IN (NOT(a=b)) → FALSE = (a<>b))"
    (.inList (.binOp .and (col "x") (boolLit false)) false [.unaryOp .not (.binOp .eq (col "a") (col "b"))])
    (.binOp .eq (boolLit false) (.binOp .ne (col "a") (col "b"))),

  -- CASE: recurse into branch condition
  testRewrite "case_condition_recursion (CASE WHEN NOT(a=b) THEN r ELSE d → CASE WHEN a<>b THEN r ELSE d)"
    (.«case» [(.unaryOp .not (.binOp .eq (col "a") (col "b")), col "r")] (some (col "d")))
    (.«case» [(.binOp .ne (col "a") (col "b"), col "r")] (some (col "d"))),

  -- CASE: recurse into branch result
  testRewrite "case_result_recursion (CASE WHEN c THEN (x AND FALSE) ELSE d → CASE WHEN c THEN FALSE ELSE d)"
    (.«case» [(col "c", .binOp .and (col "x") (boolLit false))] (some (col "d")))
    (.«case» [(col "c", boolLit false)] (some (col "d"))),

  -- CASE: recurse into else clause
  testRewrite "case_else_recursion (CASE WHEN c THEN r ELSE (x OR TRUE) → CASE WHEN c THEN r ELSE TRUE)"
    (.«case» [(col "c", col "r")] (some (.binOp .or (col "x") (boolLit true))))
    (.«case» [(col "c", col "r")] (some (boolLit true))),

  -- CASE: condition rewrites to TRUE → simplifyCaseExpr fires
  testRewrite "case_compose_true (CASE WHEN (x OR TRUE) THEN r ELSE d → r)"
    (.«case» [(.binOp .or (col "x") (boolLit true), col "r")] (some (col "d")))
    (col "r"),

  -- CASE: condition rewrites to FALSE → simplifyCaseExpr fires
  testRewrite "case_compose_false (CASE WHEN (x AND FALSE) THEN r ELSE d → d)"
    (.«case» [(.binOp .and (col "x") (boolLit false), col "r")] (some (col "d")))
    (col "d")
]

-- ============================================================================
-- Test Suite
-- ============================================================================

def allTests : List TestResult :=
  binOpTests ++ unaryOpTests ++ betweenTests ++ inListTests ++
  caseTests ++ conditionalBoolTests ++ conditionalArithTests ++
  compositionTests ++ recursionTests ++ idempotencyTests ++ leafTests ++
  subexprRecursionTests

def runRewriterTests : IO (Nat × Nat) :=
  runTests "Certified Rewriter Tests" allTests

end RewriterTest
