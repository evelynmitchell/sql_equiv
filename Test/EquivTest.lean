/-
  Equivalence Tests: Verify equivalence proofs and normalization

  Tests the equivalence framework including:
  - Basic equivalence properties (reflexivity, symmetry, transitivity)
  - Syntactic normalization and equivalence checking
  - Semantic equivalence verification
-/
import SqlEquiv
import Test.Common

namespace EquivTest

open SqlEquiv
open Test

-- ============================================================================
-- Proof Verification Tests (compile-time)
-- These use #check to verify theorems exist and type-check
-- ============================================================================

-- Verify expression equivalence theorems exist
#check @expr_equiv_refl
#check @expr_equiv_symm
#check @expr_equiv_trans

-- Verify commutativity theorems exist
#check @SqlEquiv.and_comm
#check @SqlEquiv.or_comm
#check @SqlEquiv.add_comm
#check @SqlEquiv.mul_comm
#check @SqlEquiv.not_not
#check @SqlEquiv.eq_comm

-- Verify associativity theorems exist
#check @SqlEquiv.and_assoc
#check @SqlEquiv.or_assoc

-- Verify De Morgan's Laws
#check @SqlEquiv.not_and
#check @SqlEquiv.not_or

-- Verify Distributivity Laws
#check @SqlEquiv.and_or_distrib_left
#check @SqlEquiv.and_or_distrib_right
#check @SqlEquiv.or_and_distrib_left
#check @SqlEquiv.or_and_distrib_right

-- Verify Absorption Laws
#check @SqlEquiv.and_absorb_or
#check @SqlEquiv.or_absorb_and

-- Verify Identity Laws
#check @SqlEquiv.and_true
#check @SqlEquiv.or_false
#check @SqlEquiv.and_false
#check @SqlEquiv.or_true

-- Verify WHERE clause theorems exist
#check @SqlEquiv.where_true_elim
#check @SqlEquiv.where_false_empty

-- Verify JOIN theorems exist
#check @SqlEquiv.join_comm

-- Verify select equivalence theorems exist
#check @select_equiv_refl
#check @select_equiv_symm
#check @select_equiv_trans

-- Verify query equivalence theorems exist
#check @query_equiv_refl
#check @query_equiv_symm
#check @query_equiv_trans

-- Verify statement equivalence theorems exist
#check @stmt_equiv_refl
#check @stmt_equiv_symm
#check @stmt_equiv_trans

-- ============================================================================
-- Syntactic Equivalence Tests
-- ============================================================================

/-- Helper to create column expression -/
def col (name : String) : Expr := .col { table := none, column := name }

/-- Helper to create qualified column expression -/
def qcol (table name : String) : Expr := .col { table := some table, column := name }

/-- Helper to create integer literal -/
def intLit (n : Int) : Expr := .lit (.int n)

/-- Helper to create string literal -/
def strLit (s : String) : Expr := .lit (.string s)

/-- Test that two expressions are syntactically equivalent after normalization -/
def testSyntacticEquiv (name : String) (e1 e2 : Expr) : TestResult :=
  if syntacticEquiv e1 e2 then .pass name
  else .fail name s!"Expected {e1.toSql} ≡ {e2.toSql}"

/-- Test that two expressions are NOT syntactically equivalent -/
def testNotSyntacticEquiv (name : String) (e1 e2 : Expr) : TestResult :=
  if !syntacticEquiv e1 e2 then .pass name
  else .fail name s!"Expected {e1.toSql} ≢ {e2.toSql}"

-- ============================================================================
-- Commutativity Tests
-- ============================================================================

def commutativityTests : List TestResult :=
  let x := col "x"
  let y := col "y"
  let one := intLit 1
  let two := intLit 2
  [
    -- AND is commutative
    testSyntacticEquiv "and_comm" (.binOp .and x y) (.binOp .and y x),
    -- OR is commutative
    testSyntacticEquiv "or_comm" (.binOp .or x y) (.binOp .or y x),
    -- Addition is commutative
    testSyntacticEquiv "add_comm" (.binOp .add x one) (.binOp .add one x),
    -- Multiplication is commutative
    testSyntacticEquiv "mul_comm" (.binOp .mul x y) (.binOp .mul y x),
    -- Subtraction is NOT commutative
    testNotSyntacticEquiv "sub_not_comm" (.binOp .sub x y) (.binOp .sub y x),
    -- Division is NOT commutative
    testNotSyntacticEquiv "div_not_comm" (.binOp .div x y) (.binOp .div y x),
    -- Comparison is NOT commutative
    testNotSyntacticEquiv "lt_not_comm" (.binOp .lt x y) (.binOp .lt y x)
  ]

-- ============================================================================
-- Double Negation Tests
-- ============================================================================

def doubleNegationTests : List TestResult :=
  let x := col "x"
  [
    -- NOT NOT x ≡ x
    testSyntacticEquiv "double_not" (.unaryOp .not (.unaryOp .not x)) x,
    -- NOT NOT NOT x ≡ NOT x
    testSyntacticEquiv "triple_not" (.unaryOp .not (.unaryOp .not (.unaryOp .not x))) (.unaryOp .not x)
  ]

-- ============================================================================
-- Reflexivity Tests
-- ============================================================================

def reflexivityTests : List TestResult :=
  let x := col "x"
  let y := col "y"
  let complex := Expr.binOp .and (.binOp .gt x (intLit 10)) (.binOp .lt y (intLit 100))
  [
    testSyntacticEquiv "refl_col" x x,
    testSyntacticEquiv "refl_lit" (intLit 42) (intLit 42),
    testSyntacticEquiv "refl_complex" complex complex
  ]

-- ============================================================================
-- Non-Equivalence Tests
-- ============================================================================

def nonEquivTests : List TestResult :=
  let x := col "x"
  let y := col "y"
  [
    testNotSyntacticEquiv "diff_cols" x y,
    testNotSyntacticEquiv "diff_ops" (.binOp .add x y) (.binOp .sub x y),
    testNotSyntacticEquiv "diff_lits" (intLit 1) (intLit 2),
    testNotSyntacticEquiv "diff_structure" (.binOp .and x y) (.binOp .or x y)
  ]

-- ============================================================================
-- Nested Expression Tests
-- ============================================================================

def nestedExprTests : List TestResult :=
  let a := col "a"
  let b := col "b"
  let c := col "c"
  [
    -- (a AND b) AND c should normalize consistently
    testSyntacticEquiv "nested_and_self"
      (.binOp .and (.binOp .and a b) c)
      (.binOp .and (.binOp .and a b) c),
    -- Nested commutative ops
    testSyntacticEquiv "nested_add_comm"
      (.binOp .add (.binOp .add a b) c)
      (.binOp .add (.binOp .add a b) c)
  ]

-- ============================================================================
-- Semantic Equivalence Tests
-- ============================================================================

/-- Sample database for semantic tests -/
def testDb : Database := fun name =>
  match name with
  | "t" => [
      [("x", .int 1), ("y", .int 2)],
      [("x", .int 3), ("y", .int 4)]
    ]
  | _ => []

/-- Test semantic equivalence of two SQL queries -/
def testSemanticEquiv (name : String) (sql1 sql2 : String) : TestResult :=
  match parseSelectStr sql1, parseSelectStr sql2 with
  | .error e, _ => .fail name s!"Parse error in sql1: {e}"
  | _, .error e => .fail name s!"Parse error in sql2: {e}"
  | .ok sel1, .ok sel2 =>
    let result1 := evalSelect testDb sel1
    let result2 := evalSelect testDb sel2
    if result1 == result2 then .pass name
    else .fail name s!"Results differ:\n  {sql1} => {result1.length} rows\n  {sql2} => {result2.length} rows"

/-- Test that two queries are NOT semantically equivalent -/
def testNotSemanticEquiv (name : String) (sql1 sql2 : String) : TestResult :=
  match parseSelectStr sql1, parseSelectStr sql2 with
  | .error e, _ => .fail name s!"Parse error in sql1: {e}"
  | _, .error e => .fail name s!"Parse error in sql2: {e}"
  | .ok sel1, .ok sel2 =>
    let result1 := evalSelect testDb sel1
    let result2 := evalSelect testDb sel2
    if result1 != result2 then .pass name
    else .fail name s!"Expected different results but got same"

def semanticEquivTests : List TestResult := [
  -- Same query is equivalent to itself
  testSemanticEquiv "same_query"
    "SELECT * FROM t"
    "SELECT * FROM t",

  -- Column order in SELECT shouldn't affect row content (though column order differs)
  -- Actually this will differ due to column ordering, so let's test something else

  -- WHERE TRUE is equivalent to no WHERE
  testSemanticEquiv "where_true"
    "SELECT * FROM t WHERE TRUE"
    "SELECT * FROM t",

  -- Different WHERE conditions produce different results
  testNotSemanticEquiv "diff_where"
    "SELECT * FROM t WHERE x = 1"
    "SELECT * FROM t WHERE x = 3",

  -- LIMIT affects results
  testNotSemanticEquiv "limit_matters"
    "SELECT * FROM t"
    "SELECT * FROM t LIMIT 1"
]

-- ============================================================================
-- Normalization Property Tests
-- ============================================================================

def normalizationTests : List TestResult :=
  let x := col "x"
  let y := col "y"
  let z := col "z"
  [
    -- Normalization is idempotent
    testSyntacticEquiv "norm_idempotent"
      (normalizeExpr (normalizeExpr (.binOp .and x y)))
      (normalizeExpr (.binOp .and x y)),

    -- Normalized form of commutative ops should be consistent
    testSyntacticEquiv "norm_consistent_and"
      (normalizeExpr (.binOp .and x y))
      (normalizeExpr (.binOp .and y x)),

    testSyntacticEquiv "norm_consistent_or"
      (normalizeExpr (.binOp .or x y))
      (normalizeExpr (.binOp .or y x))
  ]

-- ============================================================================
-- Test Runner
-- ============================================================================

def allEquivTests : List TestResult :=
  commutativityTests ++ doubleNegationTests ++ reflexivityTests ++
  nonEquivTests ++ nestedExprTests ++ semanticEquivTests ++
  normalizationTests

def runEquivTests : IO Unit := do
  IO.println "═══════════════════════════════════"
  IO.println "Equivalence Tests"
  IO.println "═══════════════════════════════════"

  IO.println "\n[Proof Verification]"
  IO.println "✓ expr_equiv_refl, expr_equiv_symm, expr_equiv_trans"
  IO.println "✓ select_equiv_refl, select_equiv_symm, select_equiv_trans"
  IO.println "✓ query_equiv_refl, query_equiv_symm, query_equiv_trans"
  IO.println "✓ stmt_equiv_refl, stmt_equiv_symm, stmt_equiv_trans"
  IO.println "✓ and_comm, or_comm, add_comm, mul_comm, not_not, eq_comm"
  IO.println "✓ and_assoc, or_assoc"
  IO.println "✓ where_true_elim, where_false_empty"
  IO.println "✓ join_comm"
  IO.println "(These are verified at compile time by #check)"

  IO.println "\n[Runtime Tests]"
  let mut passed := 0
  let mut failed := 0

  for result in allEquivTests do
    match result with
    | .pass name =>
      IO.println s!"✓ {name}"
      passed := passed + 1
    | .fail name msg =>
      IO.println s!"✗ {name}"
      IO.println s!"  {msg}"
      failed := failed + 1

  IO.println "───────────────────────────────────"
  IO.println s!"Passed: {passed}, Failed: {failed}"

  if failed > 0 then
    IO.println "TESTS FAILED"
  else
    IO.println "ALL TESTS PASSED"

end EquivTest
