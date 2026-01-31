/-
  Tests for Expression Normalization (PR A)
-/
import SqlEquiv
import Test.Common

namespace ExprNormalizationTest

open SqlEquiv
open Test

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Create a simple column reference -/
def col (name : String) : Expr := .col ⟨none, name⟩

/-- Create a qualified column reference -/
def qcol (table : String) (name : String) : Expr := .col ⟨some table, name⟩

/-- Create an integer literal -/
def intLit (n : Int) : Expr := .lit (.int n)

/-- Create a boolean literal -/
def boolLit (b : Bool) : Expr := .lit (.bool b)

/-- Create a string literal -/
def strLit (s : String) : Expr := .lit (.string s)

-- ============================================================================
-- Idempotency Tests
-- ============================================================================

def testIdempotencySimpleAnd : TestResult :=
  let expr := Expr.binOp .and (col "a") (col "b")
  let once := normalizeExprCanonical expr
  let twice := normalizeExprCanonical once
  if once == twice then
    .pass "Idempotency: simple AND"
  else
    .fail "Idempotency: simple AND" s!"normalize^2 != normalize: {repr once} vs {repr twice}"

def testIdempotencyNestedAnd : TestResult :=
  let expr := Expr.binOp .and (col "a") (Expr.binOp .and (col "b") (col "c"))
  let once := normalizeExprCanonical expr
  let twice := normalizeExprCanonical once
  if once == twice then
    .pass "Idempotency: nested AND"
  else
    .fail "Idempotency: nested AND" s!"normalize^2 != normalize: {repr once} vs {repr twice}"

def testIdempotencyMixedAndOr : TestResult :=
  let expr := Expr.binOp .or
    (Expr.binOp .and (col "a") (col "b"))
    (Expr.binOp .and (col "c") (col "d"))
  let once := normalizeExprCanonical expr
  let twice := normalizeExprCanonical once
  if once == twice then
    .pass "Idempotency: mixed AND/OR"
  else
    .fail "Idempotency: mixed AND/OR" s!"normalize^2 != normalize: {repr once} vs {repr twice}"

def testIdempotencyCommutativeOps : TestResult :=
  let expr := Expr.binOp .add
    (Expr.binOp .mul (col "x") (intLit 2))
    (Expr.binOp .mul (col "y") (intLit 3))
  let once := normalizeExprCanonical expr
  let twice := normalizeExprCanonical once
  if once == twice then
    .pass "Idempotency: commutative ops (add/mul)"
  else
    .fail "Idempotency: commutative ops" s!"normalize^2 != normalize: {repr once} vs {repr twice}"

def testIdempotencyDeepNesting : TestResult :=
  -- a AND (b AND (c AND d))
  let expr := Expr.binOp .and (col "a")
    (Expr.binOp .and (col "b")
      (Expr.binOp .and (col "c") (col "d")))
  let once := normalizeExprCanonical expr
  let twice := normalizeExprCanonical once
  if once == twice then
    .pass "Idempotency: deep nesting"
  else
    .fail "Idempotency: deep nesting" s!"normalize^2 != normalize: {repr once} vs {repr twice}"

-- ============================================================================
-- Commutativity Tests (same result regardless of operand order)
-- ============================================================================

def testCommutativityAnd : TestResult :=
  let expr1 := Expr.binOp .and (col "a") (col "b")
  let expr2 := Expr.binOp .and (col "b") (col "a")
  let norm1 := normalizeExprCanonical expr1
  let norm2 := normalizeExprCanonical expr2
  if norm1 == norm2 then
    .pass "Commutativity: a AND b = b AND a"
  else
    .fail "Commutativity: AND" s!"{repr norm1} != {repr norm2}"

def testCommutativityOr : TestResult :=
  let expr1 := Expr.binOp .or (col "x") (col "y")
  let expr2 := Expr.binOp .or (col "y") (col "x")
  let norm1 := normalizeExprCanonical expr1
  let norm2 := normalizeExprCanonical expr2
  if norm1 == norm2 then
    .pass "Commutativity: x OR y = y OR x"
  else
    .fail "Commutativity: OR" s!"{repr norm1} != {repr norm2}"

def testCommutativityAdd : TestResult :=
  let expr1 := Expr.binOp .add (col "a") (col "b")
  let expr2 := Expr.binOp .add (col "b") (col "a")
  let norm1 := normalizeExprCanonical expr1
  let norm2 := normalizeExprCanonical expr2
  if norm1 == norm2 then
    .pass "Commutativity: a + b = b + a"
  else
    .fail "Commutativity: ADD" s!"{repr norm1} != {repr norm2}"

def testCommutativityMul : TestResult :=
  let expr1 := Expr.binOp .mul (col "x") (col "y")
  let expr2 := Expr.binOp .mul (col "y") (col "x")
  let norm1 := normalizeExprCanonical expr1
  let norm2 := normalizeExprCanonical expr2
  if norm1 == norm2 then
    .pass "Commutativity: x * y = y * x"
  else
    .fail "Commutativity: MUL" s!"{repr norm1} != {repr norm2}"

def testCommutativityEq : TestResult :=
  let expr1 := Expr.binOp .eq (col "a") (col "b")
  let expr2 := Expr.binOp .eq (col "b") (col "a")
  let norm1 := normalizeExprCanonical expr1
  let norm2 := normalizeExprCanonical expr2
  if norm1 == norm2 then
    .pass "Commutativity: a = b <==> b = a"
  else
    .fail "Commutativity: EQ" s!"{repr norm1} != {repr norm2}"

def testCommutativityNe : TestResult :=
  let expr1 := Expr.binOp .ne (col "a") (col "b")
  let expr2 := Expr.binOp .ne (col "b") (col "a")
  let norm1 := normalizeExprCanonical expr1
  let norm2 := normalizeExprCanonical expr2
  if norm1 == norm2 then
    .pass "Commutativity: a != b <==> b != a"
  else
    .fail "Commutativity: NE" s!"{repr norm1} != {repr norm2}"

def testCommutativityNestedAnd : TestResult :=
  -- (a AND b) AND c should equal c AND (b AND a) after normalization
  let expr1 := Expr.binOp .and (Expr.binOp .and (col "a") (col "b")) (col "c")
  let expr2 := Expr.binOp .and (col "c") (Expr.binOp .and (col "b") (col "a"))
  let norm1 := normalizeExprCanonical expr1
  let norm2 := normalizeExprCanonical expr2
  if norm1 == norm2 then
    .pass "Commutativity: (a AND b) AND c = c AND (b AND a)"
  else
    .fail "Commutativity: nested AND" s!"{repr norm1} != {repr norm2}"

-- ============================================================================
-- Determinism Tests (same input always produces same output)
-- ============================================================================

def testDeterminism : TestResult :=
  let expr := Expr.binOp .and
    (Expr.binOp .or (col "a") (col "b"))
    (Expr.binOp .or (col "c") (col "d"))
  let results := List.range 10 |>.map (fun _ => normalizeExprCanonical expr)
  let first := results.head?
  match first with
  | none => .fail "Determinism" "No results"
  | some f =>
    if results.all (· == f) then
      .pass "Determinism: 10 identical normalizations"
    else
      .fail "Determinism" "Results differ across invocations"

-- ============================================================================
-- Expression Type Coverage Tests
-- ============================================================================

def testNormalizeLiteral : TestResult :=
  let expr := intLit 42
  let norm := normalizeExprCanonical expr
  if norm == expr then
    .pass "Literal unchanged"
  else
    .fail "Literal normalization" s!"Expected {repr expr}, got {repr norm}"

def testNormalizeColumn : TestResult :=
  let expr := col "x"
  let norm := normalizeExprCanonical expr
  if norm == expr then
    .pass "Column unchanged"
  else
    .fail "Column normalization" s!"Expected {repr expr}, got {repr norm}"

def testNormalizeCountStar : TestResult :=
  let expr := Expr.countStar
  let norm := normalizeExprCanonical expr
  if norm == expr then
    .pass "COUNT(*) unchanged"
  else
    .fail "COUNT(*) normalization" s!"Expected {repr expr}, got {repr norm}"

def testNormalizeUnaryOp : TestResult :=
  let expr := Expr.unaryOp .not (Expr.binOp .and (col "b") (col "a"))
  let norm := normalizeExprCanonical expr
  -- Should normalize the inner AND
  let expected := Expr.unaryOp .not (Expr.binOp .and (col "a") (col "b"))
  if norm == expected then
    .pass "Unary op: normalizes inner expression"
  else
    .fail "Unary op normalization" s!"Expected {repr expected}, got {repr norm}"

def testNormalizeFunction : TestResult :=
  let expr := Expr.func "CONCAT" [col "b", col "a"]
  let norm := normalizeExprCanonical expr
  -- Function args are not reordered (functions may not be commutative)
  if norm == expr then
    .pass "Function: args preserved (not commutative)"
  else
    .fail "Function normalization" s!"Expected {repr expr}, got {repr norm}"

def testNormalizeAggregate : TestResult :=
  let expr := Expr.agg .sum (some (Expr.binOp .add (col "b") (col "a"))) false
  let norm := normalizeExprCanonical expr
  -- Should normalize the inner ADD (commutative)
  let expected := Expr.agg .sum (some (Expr.binOp .add (col "a") (col "b"))) false
  if norm == expected then
    .pass "Aggregate: normalizes inner expression"
  else
    .fail "Aggregate normalization" s!"Expected {repr expected}, got {repr norm}"

def testNormalizeCase : TestResult :=
  let expr := Expr.case
    [(Expr.binOp .and (col "b") (col "a"), intLit 1)]
    (some (intLit 0))
  let norm := normalizeExprCanonical expr
  -- Should normalize conditions and results
  let expected := Expr.case
    [(Expr.binOp .and (col "a") (col "b"), intLit 1)]
    (some (intLit 0))
  if norm == expected then
    .pass "CASE: normalizes conditions"
  else
    .fail "CASE normalization" s!"Expected {repr expected}, got {repr norm}"

def testNormalizeInList : TestResult :=
  let expr := Expr.inList (Expr.binOp .add (col "b") (col "a")) false [intLit 1, intLit 2]
  let norm := normalizeExprCanonical expr
  let expected := Expr.inList (Expr.binOp .add (col "a") (col "b")) false [intLit 1, intLit 2]
  if norm == expected then
    .pass "IN list: normalizes expression"
  else
    .fail "IN list normalization" s!"Expected {repr expected}, got {repr norm}"

def testNormalizeBetween : TestResult :=
  let expr := Expr.between (Expr.binOp .add (col "b") (col "a")) (intLit 1) (intLit 10)
  let norm := normalizeExprCanonical expr
  let expected := Expr.between (Expr.binOp .add (col "a") (col "b")) (intLit 1) (intLit 10)
  if norm == expected then
    .pass "BETWEEN: normalizes expression"
  else
    .fail "BETWEEN normalization" s!"Expected {repr expected}, got {repr norm}"

def testNormalizeWindowFn : TestResult :=
  -- Window function with commutative expressions in arg and partition by
  let expr := Expr.windowFn .sum
    (some (Expr.binOp .add (col "b") (col "a")))
    (WindowSpec.mk
      [Expr.binOp .mul (col "y") (col "x")]  -- partition by
      [OrderByItem.mk (col "z") .asc])        -- order by
  let norm := normalizeExprCanonical expr
  let expected := Expr.windowFn .sum
    (some (Expr.binOp .add (col "a") (col "b")))  -- normalized
    (WindowSpec.mk
      [Expr.binOp .mul (col "x") (col "y")]       -- normalized
      [OrderByItem.mk (col "z") .asc])
  if norm == expected then
    .pass "Window function: normalizes arg and partition by"
  else
    .fail "Window function normalization" s!"Expected {repr expected}, got {repr norm}"

-- ============================================================================
-- Weight-Based Ordering Tests
-- ============================================================================

def testWeightLiteralBeforeColumn : TestResult :=
  -- 1 AND x should stay as 1 AND x (literal before column)
  let expr := Expr.binOp .and (intLit 1) (col "x")
  let norm := normalizeExprCanonical expr
  if norm == expr then
    .pass "Weight: literal before column"
  else
    .fail "Weight ordering" s!"Expected {repr expr}, got {repr norm}"

def testWeightColumnBeforeBinOp : TestResult :=
  -- x AND (a + b) - column should come before binop in sorted order
  let expr := Expr.binOp .and (col "x") (Expr.binOp .add (col "a") (col "b"))
  let norm := normalizeExprCanonical expr
  -- x has weight 1, (a + b) has weight 2, so x should come first
  if norm == expr then
    .pass "Weight: column before binop"
  else
    .fail "Weight ordering" s!"Expected {repr expr}, got {repr norm}"

def testWeightReorderingWithLiterals : TestResult :=
  -- (a + b) AND 1 should become 1 AND (a + b)
  let expr := Expr.binOp .and (Expr.binOp .add (col "a") (col "b")) (intLit 1)
  let norm := normalizeExprCanonical expr
  let expected := Expr.binOp .and (intLit 1) (Expr.binOp .add (col "a") (col "b"))
  if norm == expected then
    .pass "Weight: reorders literal before binop"
  else
    .fail "Weight reordering" s!"Expected {repr expected}, got {repr norm}"

-- ============================================================================
-- Non-Commutative Operators (should not reorder)
-- ============================================================================

def testNonCommutativeSub : TestResult :=
  let expr := Expr.binOp .sub (col "b") (col "a")
  let norm := normalizeExprCanonical expr
  -- SUB is not commutative, order preserved
  if norm == expr then
    .pass "Non-commutative: SUB preserves order"
  else
    .fail "SUB commutativity" s!"Expected {repr expr}, got {repr norm}"

def testNonCommutativeDiv : TestResult :=
  let expr := Expr.binOp .div (col "b") (col "a")
  let norm := normalizeExprCanonical expr
  if norm == expr then
    .pass "Non-commutative: DIV preserves order"
  else
    .fail "DIV commutativity" s!"Expected {repr expr}, got {repr norm}"

def testNonCommutativeLt : TestResult :=
  let expr := Expr.binOp .lt (col "b") (col "a")
  let norm := normalizeExprCanonical expr
  if norm == expr then
    .pass "Non-commutative: LT preserves order"
  else
    .fail "LT commutativity" s!"Expected {repr expr}, got {repr norm}"

-- ============================================================================
-- Test Runner
-- ============================================================================

def allTests : List TestResult := [
  -- Idempotency
  testIdempotencySimpleAnd,
  testIdempotencyNestedAnd,
  testIdempotencyMixedAndOr,
  testIdempotencyCommutativeOps,
  testIdempotencyDeepNesting,
  -- Commutativity
  testCommutativityAnd,
  testCommutativityOr,
  testCommutativityAdd,
  testCommutativityMul,
  testCommutativityEq,
  testCommutativityNe,
  testCommutativityNestedAnd,
  -- Determinism
  testDeterminism,
  -- Expression type coverage
  testNormalizeLiteral,
  testNormalizeColumn,
  testNormalizeCountStar,
  testNormalizeUnaryOp,
  testNormalizeFunction,
  testNormalizeAggregate,
  testNormalizeCase,
  testNormalizeInList,
  testNormalizeBetween,
  testNormalizeWindowFn,
  -- Weight-based ordering
  testWeightLiteralBeforeColumn,
  testWeightColumnBeforeBinOp,
  testWeightReorderingWithLiterals,
  -- Non-commutative operators
  testNonCommutativeSub,
  testNonCommutativeDiv,
  testNonCommutativeLt
]

def runExprNormalizationTests : IO (Nat × Nat) := do
  runTests "Expression Normalization Tests" allTests

end ExprNormalizationTest
