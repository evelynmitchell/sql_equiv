/-
  Axiom Coverage Tests: Runtime tests exercising axioms in Equiv.lean

  Most tests evaluate both sides of an axiom's claimed equality/equivalence
  with concrete values and verify they match. Some axioms involve properties
  (e.g., monotonicity, subset inclusion) tested via weaker but meaningful
  runtime checks (e.g., row count comparisons). Where an axiom's claim
  disagrees with the current evaluator (e.g., CASE none vs null, CONCAT),
  both sides are compared and the mismatch is documented.

  These tests guard against semantic drift between the axioms in `Equiv.lean`
  and the evaluator implementation. They are complemented by the `#check`
  coverage in `EquivTest.lean`, which ensures the referenced axioms still
  exist with the expected names and types.
-/
import SqlEquiv
import Test.Common

namespace AxiomCoverageTest

open SqlEquiv
open Test

-- ============================================================================
-- Test Database
-- ============================================================================

def usersTable : Table := [
  [("id", .int 1), ("name", .string "Alice"), ("age", .int 30)],
  [("id", .int 2), ("name", .string "Bob"), ("age", .int 25)],
  [("id", .int 3), ("name", .string "Carol"), ("age", .int 35)]
]

def ordersTable : Table := [
  [("id", .int 1), ("user_id", .int 1), ("amount", .int 100)],
  [("id", .int 2), ("user_id", .int 1), ("amount", .int 200)],
  [("id", .int 3), ("user_id", .int 2), ("amount", .int 150)]
]

def emptyTable : Table := []

def productsTable : Table := [
  [("id", .int 10), ("name", .string "Widget"), ("price", .int 50)],
  [("id", .int 20), ("name", .string "Gadget"), ("price", .int 75)]
]

def testDb : Database := fun name =>
  match name with
  | "users" => usersTable
  | "orders" => ordersTable
  | "products" => productsTable
  | "empty" => emptyTable
  | _ => []

-- ============================================================================
-- Test Helpers
-- ============================================================================

def showOptVal : Option Value → String
  | some v => v.toSql
  | none => "none"

/-- Test that two expressions evaluate equally on a given row -/
def testExprEquiv (name : String) (e1 e2 : Expr) (row : Row) : TestResult :=
  let r1 := evalExpr row e1
  let r2 := evalExpr row e2
  if r1 == r2 then .pass name
  else .fail name s!"Expected equal: {showOptVal r1} vs {showOptVal r2}"

/-- Test that two expressions evaluate equally on a given row with database context -/
def testExprEquivDb (name : String) (e1 e2 : Expr) (db : Database) (row : Row) : TestResult :=
  let r1 := evalExprWithDb db row e1
  let r2 := evalExprWithDb db row e2
  if r1 == r2 then .pass name
  else .fail name s!"Expected equal: {showOptVal r1} vs {showOptVal r2}"

/-- Test that two queries produce equal results -/
def testQueryEquiv (name : String) (q1 q2 : Query) (db : Database) : TestResult :=
  let r1 := evalQuery db q1
  let r2 := evalQuery db q2
  if r1 == r2 then .pass name
  else .fail name s!"Results differ: {r1.length} rows vs {r2.length} rows"

/-- Test that two select statements produce equal results -/
def testSelectEquiv (name : String) (s1 s2 : SelectStmt) (db : Database) : TestResult :=
  let r1 := evalSelect db s1
  let r2 := evalSelect db s2
  if r1 == r2 then .pass name
  else .fail name s!"Results differ: {r1.length} rows vs {r2.length} rows"

/-- Test a length property -/
def testLengthEq (name : String) (actual expected : Nat) : TestResult :=
  if actual == expected then .pass name
  else .fail name s!"Expected length {expected}, got {actual}"

/-- Test a length inequality -/
def testLengthLe (name : String) (actual bound : Nat) : TestResult :=
  if actual ≤ bound then .pass name
  else .fail name s!"Expected {actual} ≤ {bound}"

def testLengthGe (name : String) (actual bound : Nat) : TestResult :=
  if actual ≥ bound then .pass name
  else .fail name s!"Expected {actual} ≥ {bound}"

/-- Test bag equivalence: two queries produce permutation-equivalent results.
    Compares multiplicities of each distinct row. -/
def testQueryBagEquiv (name : String) (q1 q2 : Query) (db : Database) : TestResult :=
  let r1 := evalQuery db q1
  let r2 := evalQuery db q2
  if r1.length != r2.length then
    .fail name s!"Bag equiv failed: {r1.length} vs {r2.length} rows"
  else
    let distinctRows := (r1 ++ r2).eraseDups
    let countsMatch := distinctRows.all (fun row => r1.count row == r2.count row)
    if countsMatch then .pass name
    else .fail name s!"Bag equiv failed: differing row multiplicities with {r1.length} rows"

/-- Test set equivalence: two queries produce results with the same membership.
    Compares deduplicated results via membership. -/
def testQuerySetEquiv (name : String) (q1 q2 : Query) (db : Database) : TestResult :=
  let r1 := (evalQuery db q1).eraseDups
  let r2 := (evalQuery db q2).eraseDups
  let sameMembers := r1.all (fun row => r2.contains row)
    && r2.all (fun row => r1.contains row)
  if sameMembers then .pass name
  else .fail name s!"Set equiv failed: membership differs"

-- ============================================================================
-- Sample expressions and rows
-- ============================================================================

def intRow : Row := [("x", .int 5), ("y", .int 3), ("z", .int 0)]
def strRow : Row := [("s", .string "hello"), ("t", .string "WORLD")]
def boolRow : Row := [("a", .bool true), ("b", .bool false)]
def nullRow : Row := [("n", .null none), ("x", .int 42)]

def eInt5 : Expr := .lit (.int 5)
def eInt3 : Expr := .lit (.int 3)
def eInt0 : Expr := .lit (.int 0)
def eInt1 : Expr := .lit (.int 1)
def eTrue : Expr := .lit (.bool true)
def eFalse : Expr := .lit (.bool false)
def eNull : Expr := .lit (.null none)
def eStr : Expr := .lit (.string "hello")
def eStrEmpty : Expr := .lit (.string "")

-- ============================================================================
-- 1. Arithmetic Identity Tests
-- ============================================================================

def arithmeticTests : List TestResult :=
  [
    -- expr_add_zero: e + 0 ≃ₑ e
    testExprEquiv "expr_add_zero (int)"
      (.binOp .add eInt5 eInt0) eInt5 [],
    testExprEquiv "expr_add_zero (col)"
      (.binOp .add (col "x") eInt0) (col "x") intRow,

    -- expr_zero_add: 0 + e ≃ₑ e
    testExprEquiv "expr_zero_add (int)"
      (.binOp .add eInt0 eInt3) eInt3 [],
    testExprEquiv "expr_zero_add (col)"
      (.binOp .add eInt0 (col "x")) (col "x") intRow,

    -- expr_mul_one: e * 1 ≃ₑ e
    testExprEquiv "expr_mul_one (int)"
      (.binOp .mul eInt5 eInt1) eInt5 [],
    testExprEquiv "expr_mul_one (col)"
      (.binOp .mul (col "x") eInt1) (col "x") intRow,

    -- expr_one_mul: 1 * e ≃ₑ e
    testExprEquiv "expr_one_mul (int)"
      (.binOp .mul eInt1 eInt3) eInt3 [],

    -- expr_mul_zero: e * 0 ≃ₑ 0
    testExprEquiv "expr_mul_zero (int)"
      (.binOp .mul eInt5 eInt0) eInt0 [],
    testExprEquiv "expr_mul_zero (col)"
      (.binOp .mul (col "x") eInt0) eInt0 intRow,

    -- expr_zero_mul: 0 * e ≃ₑ 0
    testExprEquiv "expr_zero_mul (int)"
      (.binOp .mul eInt0 eInt5) eInt0 [],

    -- expr_sub_zero: e - 0 ≃ₑ e
    testExprEquiv "expr_sub_zero (int)"
      (.binOp .sub eInt5 eInt0) eInt5 [],
    testExprEquiv "expr_sub_zero (col)"
      (.binOp .sub (col "x") eInt0) (col "x") intRow
  ]

-- ============================================================================
-- 2. Comparison Axiom Tests
-- ============================================================================

def comparisonTests : List TestResult :=
  [
    -- eq_reflexive: e = e ≃ₑ CASE WHEN IS NULL e THEN NULL ELSE TRUE
    testExprEquiv "eq_reflexive (int)"
      (.binOp .eq eInt5 eInt5)
      (.case [(.unaryOp .isNull eInt5, eNull)] (some eTrue))
      [],
    testExprEquiv "eq_reflexive (col)"
      (.binOp .eq (col "x") (col "x"))
      (.case [(.unaryOp .isNull (col "x"), eNull)] (some eTrue))
      intRow,

    -- ne_irreflexive: e <> e ≃ₑ CASE WHEN IS NULL e THEN NULL ELSE FALSE
    testExprEquiv "ne_irreflexive (int)"
      (.binOp .ne eInt5 eInt5)
      (.case [(.unaryOp .isNull eInt5, eNull)] (some eFalse))
      [],

    -- not_eq_is_ne: NOT (a = b) ≃ₑ (a <> b)
    testExprEquiv "not_eq_is_ne"
      (.unaryOp .not (.binOp .eq eInt5 eInt3))
      (.binOp .ne eInt5 eInt3) [],

    -- not_ne_is_eq: NOT (a <> b) ≃ₑ (a = b)
    testExprEquiv "not_ne_is_eq"
      (.unaryOp .not (.binOp .ne eInt5 eInt3))
      (.binOp .eq eInt5 eInt3) [],

    -- not_lt_is_ge: NOT (a < b) ≃ₑ (a >= b)
    testExprEquiv "not_lt_is_ge"
      (.unaryOp .not (.binOp .lt eInt5 eInt3))
      (.binOp .ge eInt5 eInt3) [],

    -- not_le_is_gt: NOT (a <= b) ≃ₑ (a > b)
    testExprEquiv "not_le_is_gt"
      (.unaryOp .not (.binOp .le eInt5 eInt3))
      (.binOp .gt eInt5 eInt3) [],

    -- not_gt_is_le: NOT (a > b) ≃ₑ (a <= b)
    testExprEquiv "not_gt_is_le"
      (.unaryOp .not (.binOp .gt eInt5 eInt3))
      (.binOp .le eInt5 eInt3) [],

    -- not_ge_is_lt: NOT (a >= b) ≃ₑ (a < b)
    testExprEquiv "not_ge_is_lt"
      (.unaryOp .not (.binOp .ge eInt5 eInt3))
      (.binOp .lt eInt5 eInt3) [],

    -- lt_flip: a < b ≃ₑ b > a
    testExprEquiv "lt_flip"
      (.binOp .lt eInt3 eInt5)
      (.binOp .gt eInt5 eInt3) [],

    -- le_flip: a <= b ≃ₑ b >= a
    testExprEquiv "le_flip"
      (.binOp .le eInt3 eInt5)
      (.binOp .ge eInt5 eInt3) [],

    -- gt_flip: a > b ≃ₑ b < a
    testExprEquiv "gt_flip"
      (.binOp .gt eInt5 eInt3)
      (.binOp .lt eInt3 eInt5) [],

    -- ge_flip: a >= b ≃ₑ b <= a
    testExprEquiv "ge_flip"
      (.binOp .ge eInt5 eInt3)
      (.binOp .le eInt3 eInt5) []
  ]

-- ============================================================================
-- 3. CASE Expression Tests
-- ============================================================================

def caseTests : List TestResult :=
  [
    -- case_when_true: CASE WHEN TRUE THEN x ELSE y END = x
    testExprEquiv "case_when_true"
      (.case [(eTrue, eInt5)] (some eInt3))
      eInt5 [],

    -- case_when_false: CASE WHEN FALSE THEN x ELSE y END = y
    testExprEquiv "case_when_false"
      (.case [(eFalse, eInt5)] (some eInt3))
      eInt3 [],

    -- case_when_false_no_else: CASE WHEN FALSE THEN x END ≃ₑ NULL
    -- Axiom claims equivalence with Expr.lit (.null none).
    -- Compare both sides: evalExpr on the CASE form vs evalExpr on the axiom's RHS.
    -- Known mismatch (issue #23): evalExpr returns none while lit (.null none) => some (.null none).
    -- This test fails (rather than silently passing) so that resolving issue #23 is surfaced in CI.
    let caseFalseNoElse := evalExpr [] (.case [(eFalse, eInt5)] none)
    let axiomRhs := evalExpr [] (.lit (.null none))
    if caseFalseNoElse == axiomRhs then .pass "case_when_false_no_else"
    else .fail "case_when_false_no_else (issue #23)"
      s!"Evaluator/axiom mismatch: CASE={showOptVal caseFalseNoElse} vs NULL lit={showOptVal axiomRhs}",

    -- case_empty_else: CASE ELSE y END = y
    testExprEquiv "case_empty_else"
      (.case [] (some eInt5))
      eInt5 [],

    -- case_empty_no_else: CASE END ≃ₑ NULL
    -- Same mismatch as case_when_false_no_else (issue #23)
    let caseEmptyNoElse := evalExpr [] (.case [] none)
    let axiomRhs2 := evalExpr [] (.lit (.null none))
    if caseEmptyNoElse == axiomRhs2 then .pass "case_empty_no_else"
    else .fail "case_empty_no_else (issue #23)"
      s!"Evaluator/axiom mismatch: CASE={showOptVal caseEmptyNoElse} vs NULL lit={showOptVal axiomRhs2}"
  ]

-- ============================================================================
-- 4. Boolean Algebra Tests
-- ============================================================================

def boolAlgebraTests : List TestResult :=
  [
    -- and_self: a AND a ≃ₑ a
    testExprEquiv "and_self (true)"
      (.binOp .and eTrue eTrue) eTrue [],
    testExprEquiv "and_self (false)"
      (.binOp .and eFalse eFalse) eFalse [],

    -- or_self: a OR a ≃ₑ a
    testExprEquiv "or_self (true)"
      (.binOp .or eTrue eTrue) eTrue [],
    testExprEquiv "or_self (false)"
      (.binOp .or eFalse eFalse) eFalse [],

    -- and_not_self: a AND (NOT a) ≃ₑ FALSE
    testExprEquiv "and_not_self (true)"
      (.binOp .and eTrue (.unaryOp .not eTrue))
      eFalse [],
    testExprEquiv "and_not_self (false)"
      (.binOp .and eFalse (.unaryOp .not eFalse))
      eFalse [],

    -- or_not_self: a OR (NOT a) ≃ₑ TRUE
    testExprEquiv "or_not_self (true)"
      (.binOp .or eTrue (.unaryOp .not eTrue))
      eTrue [],
    testExprEquiv "or_not_self (false)"
      (.binOp .or eFalse (.unaryOp .not eFalse))
      eTrue []
  ]

-- ============================================================================
-- 5. IN/NOT IN Tests
-- ============================================================================

def inListTests : List TestResult :=
  [
    -- in_empty_false: x IN () ≃ₑ FALSE
    testExprEquiv "in_empty_false"
      (.inList eInt5 false []) eFalse [],

    -- not_in_empty_true: x NOT IN () ≃ₑ TRUE
    testExprEquiv "not_in_empty_true"
      (.inList eInt5 true []) eTrue [],

    -- in_singleton: x IN (a) ≃ₑ (x = a)
    testExprEquiv "in_singleton (match)"
      (.inList eInt5 false [eInt5])
      (.binOp .eq eInt5 eInt5) [],
    testExprEquiv "in_singleton (no match)"
      (.inList eInt5 false [eInt3])
      (.binOp .eq eInt5 eInt3) [],

    -- not_in_singleton: x NOT IN (a) ≃ₑ (x <> a)
    testExprEquiv "not_in_singleton"
      (.inList eInt5 true [eInt3])
      (.binOp .ne eInt5 eInt3) [],

    -- in_pair: x IN (a, b) ≃ₑ (x = a OR x = b)
    testExprEquiv "in_pair"
      (.inList eInt5 false [eInt3, eInt5])
      (.binOp .or (.binOp .eq eInt5 eInt3) (.binOp .eq eInt5 eInt5)) [],

    -- not_in_pair: x NOT IN (a, b) ≃ₑ (x <> a AND x <> b)
    testExprEquiv "not_in_pair"
      (.inList eInt5 true [eInt3, eInt1])
      (.binOp .and (.binOp .ne eInt5 eInt3) (.binOp .ne eInt5 eInt1)) [],

    -- in_list_or_expansion: IN list = OR of equalities
    testExprEquiv "in_list_or_expansion"
      (.inList eInt5 false [eInt1, eInt3, eInt5])
      ([eInt1, eInt3, eInt5].foldl
        (fun acc v => .binOp .or acc (.binOp .eq eInt5 v))
        eFalse) [],

    -- not_in_list_and_expansion: NOT IN list = AND of inequalities
    testExprEquiv "not_in_list_and_expansion"
      (.inList eInt5 true [eInt1, eInt3])
      ([eInt1, eInt3].foldl
        (fun acc v => .binOp .and acc (.binOp .ne eInt5 v))
        eTrue) []
  ]

-- ============================================================================
-- 6. BETWEEN Tests
-- ============================================================================

def betweenTests : List TestResult :=
  [
    -- between_expansion: x BETWEEN a AND b ≃ₑ (x >= a AND x <= b)
    testExprEquiv "between_expansion (in range)"
      (.between eInt3 eInt1 eInt5)
      (.binOp .and (.binOp .ge eInt3 eInt1) (.binOp .le eInt3 eInt5)) [],
    testExprEquiv "between_expansion (out of range)"
      (.between eInt0 eInt1 eInt5)
      (.binOp .and (.binOp .ge eInt0 eInt1) (.binOp .le eInt0 eInt5)) [],

    -- between_reflexive: x BETWEEN x AND x ≃ₑ (x >= x AND x <= x)
    testExprEquiv "between_reflexive"
      (.between eInt5 eInt5 eInt5)
      (.binOp .and (.binOp .ge eInt5 eInt5) (.binOp .le eInt5 eInt5)) [],

    -- not_between_expansion: NOT (x BETWEEN a AND b) ≃ₑ (x < a OR x > b)
    testExprEquiv "not_between_expansion"
      (.unaryOp .not (.between eInt0 eInt1 eInt5))
      (.binOp .or (.binOp .lt eInt0 eInt1) (.binOp .gt eInt0 eInt5)) []
  ]

-- ============================================================================
-- 7. String Function Tests
-- ============================================================================

def stringFuncTests : List TestResult :=
  let eHello := Expr.lit (.string "hello")
  let eEmpty := Expr.lit (.string "")
  [
    -- concat_empty_left: CONCAT('', e) ≃ₑ e (for string-valued e)
    testExprEquiv "concat_empty_left (string)"
      (.func "CONCAT" [eEmpty, eHello]) eHello [],
    -- concat_empty_left with null: CONCAT('', NULL) = NULL
    testExprEquiv "concat_empty_left (null)"
      (.func "CONCAT" [eEmpty, Expr.lit (.null none)]) (Expr.lit (.null none)) [],
    -- concat_empty_left with typed null: CONCAT('', NULL::int) = NULL (type lost)
    testExprEquiv "concat_empty_left (typed null)"
      (.func "CONCAT" [eEmpty, Expr.lit (.null (some .int))]) (Expr.lit (.null none)) [],

    -- concat_empty_right: CONCAT(e, '') ≃ₑ e (for string-valued e)
    testExprEquiv "concat_empty_right (string)"
      (.func "CONCAT" [eHello, eEmpty]) eHello [],
    -- concat_empty_right with null: CONCAT(NULL, '') = NULL
    testExprEquiv "concat_empty_right (null)"
      (.func "CONCAT" [Expr.lit (.null none), eEmpty]) (Expr.lit (.null none)) [],
    -- concat_empty_right with typed null: CONCAT(NULL::int, '') = NULL (type lost)
    testExprEquiv "concat_empty_right (typed null)"
      (.func "CONCAT" [Expr.lit (.null (some .int)), eEmpty]) (Expr.lit (.null none)) [],

    -- BinOp.concat path (parser emits || as binop): '' || 'hello' = 'hello'
    testExprEquiv "concat_empty_left (binop)"
      (.binOp .concat eEmpty eHello) eHello [],
    testExprEquiv "concat_empty_right (binop)"
      (.binOp .concat eHello eEmpty) eHello [],

    -- upper_idempotent: UPPER(UPPER(e)) ≃ₑ UPPER(e)
    testExprEquiv "upper_idempotent"
      (.func "UPPER" [.func "UPPER" [eHello]])
      (.func "UPPER" [eHello]) [],

    -- lower_idempotent: LOWER(LOWER(e)) ≃ₑ LOWER(e)
    testExprEquiv "lower_idempotent"
      (.func "LOWER" [.func "LOWER" [eHello]])
      (.func "LOWER" [eHello]) [],

    -- upper_lower_upper: UPPER(LOWER(UPPER(e))) ≃ₑ UPPER(e)
    testExprEquiv "upper_lower_upper"
      (.func "UPPER" [.func "LOWER" [.func "UPPER" [eHello]]])
      (.func "UPPER" [eHello]) [],

    -- lower_upper_lower: LOWER(UPPER(LOWER(e))) ≃ₑ LOWER(e)
    testExprEquiv "lower_upper_lower"
      (.func "LOWER" [.func "UPPER" [.func "LOWER" [eHello]]])
      (.func "LOWER" [eHello]) [],

    -- length_empty: LENGTH('') ≃ₑ 0
    testExprEquiv "length_empty"
      (.func "LENGTH" [eEmpty])
      (.lit (.int 0)) [],

    -- length_concat: LENGTH(CONCAT(a, b)) ≃ₑ LENGTH(a) + LENGTH(b)
    testExprEquiv "length_concat (strings)"
      (.func "LENGTH" [.func "CONCAT" [eHello, Expr.lit (.string "world")]])
      (.binOp .add (.func "LENGTH" [eHello]) (.func "LENGTH" [Expr.lit (.string "world")])) [],
    testExprEquiv "length_concat (null)"
      (.func "LENGTH" [.func "CONCAT" [Expr.lit (.null none), eHello]])
      (.binOp .add (.func "LENGTH" [Expr.lit (.null none)]) (.func "LENGTH" [eHello])) [],
    testExprEquiv "length_concat (empty)"
      (.func "LENGTH" [.func "CONCAT" [eEmpty, eHello]])
      (.binOp .add (.func "LENGTH" [eEmpty]) (.func "LENGTH" [eHello])) [],
    -- Non-string inputs: both sides reduce to none (int) or null (typed null)
    testExprEquiv "length_concat (int args)"
      (.func "LENGTH" [.func "CONCAT" [Expr.lit (.int 5), Expr.lit (.string "world")]])
      (.binOp .add (.func "LENGTH" [Expr.lit (.int 5)]) (.func "LENGTH" [Expr.lit (.string "world")])) [],
    testExprEquiv "length_concat (typed null)"
      (.func "LENGTH" [.func "CONCAT" [Expr.lit (.null (some .int)), Expr.lit (.string "world")]])
      (.binOp .add (.func "LENGTH" [Expr.lit (.null (some .int))]) (.func "LENGTH" [Expr.lit (.string "world")])) []
  ]

-- ============================================================================
-- 8. LIKE Tests
-- ============================================================================

def likeTests : List TestResult :=
  let eHello := Expr.lit (.string "hello")
  let ePct := Expr.lit (.string "%")
  let eEmpty := Expr.lit (.string "")
  [
    -- like_match_all: e LIKE '%' ≃ₑ CASE WHEN IS NULL e THEN NULL ELSE TRUE
    testExprEquiv "like_match_all"
      (.binOp .like eHello ePct)
      (.case [(.unaryOp .isNull eHello, eNull)] (some eTrue)) [],

    -- like_empty_pattern: e LIKE '' ≃ₑ (e = '')
    testExprEquiv "like_empty_pattern (empty)"
      (.binOp .like eEmpty eEmpty)
      (.binOp .eq eEmpty eEmpty) [],
    testExprEquiv "like_empty_pattern (non-empty)"
      (.binOp .like eHello eEmpty)
      (.binOp .eq eHello eEmpty) [],

    -- like_self: e LIKE e ≃ₑ CASE WHEN IS NULL e THEN NULL ELSE TRUE
    testExprEquiv "like_self"
      (.binOp .like eHello eHello)
      (.case [(.unaryOp .isNull eHello, eNull)] (some eTrue)) []
  ]

-- ============================================================================
-- 9. Set Operation Tests
-- ============================================================================

def mkSimpleSelect (tableName : String) : SelectStmt :=
  .mk false [.star none] (some (.table ⟨tableName, none⟩)) none [] none [] none none

def mkEmptySelect : SelectStmt :=
  .mk false [.star none] none (some (.lit (.bool false))) [] none [] none none

def setOpTests : List TestResult :=
  let selUsers := mkSimpleSelect "users"
  let selOrders := mkSimpleSelect "orders"
  let selEmpty := mkEmptySelect
  -- Same-schema, overlapping subsets of users (#180): age > 25 → {Alice, Carol},
  -- age < 35 → {Alice, Bob}; intersection {Alice}.
  let selOld : SelectStmt := .mk false [.star none] (some (.table ⟨"users", none⟩))
    (some (.binOp .gt (.col ⟨none, "age"⟩) (.lit (.int 25)))) [] none [] none none
  let selYoung : SelectStmt := .mk false [.star none] (some (.table ⟨"users", none⟩))
    (some (.binOp .lt (.col ⟨none, "age"⟩) (.lit (.int 35)))) [] none [] none none
  [
    -- union_comm: A UNION B ≃ᵇ B UNION A (bag equiv)
    testQueryBagEquiv "union_comm"
      (.compound (.simple selUsers) .union (.simple selOrders))
      (.compound (.simple selOrders) .union (.simple selUsers))
      testDb,

    -- union_all_comm: A UNION ALL B ≃ᵇ B UNION ALL A (bag equiv)
    testQueryBagEquiv "union_all_comm"
      (.compound (.simple selUsers) .unionAll (.simple selOrders))
      (.compound (.simple selOrders) .unionAll (.simple selUsers))
      testDb,

    -- intersect_comm: A INTERSECT B ≃ˢ B INTERSECT A (set equiv)
    testQuerySetEquiv "intersect_comm"
      (.compound (.simple selOld) .intersect (.simple selYoung))
      (.compound (.simple selYoung) .intersect (.simple selOld))
      testDb,
    -- Non-vacuity guard (#180): the intersection above is non-empty
    testLengthGe "intersect_comm_nonempty"
      (evalQuery testDb (.compound (.simple selOld) .intersect (.simple selYoung))).length 1,

    -- union_assoc: (A UNION B) UNION C ≃ᵇ A UNION (B UNION C) (bag equiv)
    testQueryBagEquiv "union_assoc"
      (.compound (.compound (.simple selUsers) .union (.simple selOrders)) .union (.simple selEmpty))
      (.compound (.simple selUsers) .union (.compound (.simple selOrders) .union (.simple selEmpty)))
      testDb,

    -- intersect_assoc: (A ∩ B) ∩ C ≃ᵩ A ∩ (B ∩ C) (exact equiv)
    testQueryEquiv "intersect_assoc"
      (.compound (.compound (.simple selUsers) .intersect (.simple selOld)) .intersect (.simple selYoung))
      (.compound (.simple selUsers) .intersect (.compound (.simple selOld) .intersect (.simple selYoung)))
      testDb,
    -- Non-vacuity guard (#180): the associated intersection is non-empty
    testLengthGe "intersect_assoc_nonempty"
      (evalQuery testDb (.compound (.compound (.simple selUsers) .intersect (.simple selOld))
        .intersect (.simple selYoung))).length 1,

    -- union_idempotent: A UNION A ≃ˢ A (set equiv)
    testQuerySetEquiv "union_idempotent"
      (.compound (.simple selUsers) .union (.simple selUsers))
      (.simple selUsers)
      testDb,

    -- intersect_idempotent: A INTERSECT A ≃ˢ A (set equiv; downgraded from ≃ᵩ
    -- by #223 — INTERSECT now deduplicates, so exact equality fails on
    -- duplicate-bearing inputs)
    testQuerySetEquiv "intersect_idempotent"
      (.compound (.simple selUsers) .intersect (.simple selUsers))
      (.simple selUsers)
      testDb,

    -- except_self_empty: A EXCEPT A = []
    testLengthEq "except_self_empty"
      (evalQuery testDb (.compound (.simple selUsers) .exceptOp (.simple selUsers))).length
      0,

    -- union_empty_right: A UNION empty ≃ˢ A (set equiv)
    testQuerySetEquiv "union_empty_right"
      (.compound (.simple selUsers) .union (.simple selEmpty))
      (.simple selUsers)
      testDb,

    -- intersect_empty_right: A INTERSECT empty = []
    testLengthEq "intersect_empty_right"
      (evalQuery testDb (.compound (.simple selUsers) .intersect (.simple selEmpty))).length
      0,

    -- union_all_length: |A UNION ALL B| = |A| + |B|
    testLengthEq "union_all_length"
      (evalQuery testDb (.compound (.simple selUsers) .unionAll (.simple selOrders))).length
      ((evalQuery testDb (.simple selUsers)).length +
       (evalQuery testDb (.simple selOrders)).length),

    -- union_intersect_distrib: A UNION (B ∩ C) ≃ˢ (A ∪ B) ∩ (A ∪ C) (set equiv)
    testQuerySetEquiv "union_intersect_distrib"
      (.compound (.simple selUsers) .union
        (.compound (.simple selOrders) .intersect (.simple selUsers)))
      (.compound
        (.compound (.simple selUsers) .union (.simple selOrders))
        .intersect
        (.compound (.simple selUsers) .union (.simple selUsers)))
      testDb,

    -- intersect_union_distrib: A ∩ (B ∪ C) ≃ˢ (A ∩ B) ∪ (A ∩ C) (set equiv)
    testQuerySetEquiv "intersect_union_distrib"
      (.compound (.simple selUsers) .intersect
        (.compound (.simple selOrders) .union (.simple selUsers)))
      (.compound
        (.compound (.simple selUsers) .intersect (.simple selOrders))
        .union
        (.compound (.simple selUsers) .intersect (.simple selUsers)))
      testDb
  ]

-- ============================================================================
-- 10. LIMIT/OFFSET Tests
-- ============================================================================

def mkSelectWithLimitOffset (tableName : String) (limit : Option Nat) (offset : Option Nat) : SelectStmt :=
  .mk false [.star none] (some (.table ⟨tableName, none⟩)) none [] none [] limit offset

def mkSelectFull (distinct : Bool) (tableName : String) (where_ : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) (offset : Option Nat) : SelectStmt :=
  .mk distinct [.star none] (some (.table ⟨tableName, none⟩)) where_ [] none orderBy limit offset

def limitOffsetTests : List TestResult :=
  let selAll := mkSelectWithLimitOffset "users" none none
  let allRows := evalSelect testDb selAll
  [
    -- limit_zero_empty: LIMIT 0 = []
    testLengthEq "limit_zero_empty"
      (evalSelect testDb (mkSelectWithLimitOffset "users" (some 0) none)).length
      0,

    -- limit_upper_bound: LIMIT n => |result| ≤ n
    testLengthLe "limit_upper_bound (2)"
      (evalSelect testDb (mkSelectWithLimitOffset "users" (some 2) none)).length
      2,
    testLengthLe "limit_upper_bound (1)"
      (evalSelect testDb (mkSelectWithLimitOffset "users" (some 1) none)).length
      1,

    -- limit_none_all_rows: no limit = LIMIT count
    testSelectEquiv "limit_none_all_rows"
      selAll
      (mkSelectWithLimitOffset "users" (some allRows.length) none)
      testDb,

    -- limit_monotonic: m ≤ n => |LIMIT m| ≤ |LIMIT n|
    testLengthLe "limit_monotonic (1 ≤ 2)"
      (evalSelect testDb (mkSelectWithLimitOffset "users" (some 1) none)).length
      (evalSelect testDb (mkSelectWithLimitOffset "users" (some 2) none)).length,

    -- limit_one_singleton: LIMIT 1 => |result| ≤ 1
    testLengthLe "limit_one_singleton"
      (evalSelect testDb (mkSelectWithLimitOffset "users" (some 1) none)).length
      1,

    -- limit_offset_compose: LIMIT n OFFSET m = (all.drop m).take n
    let composed := evalSelect testDb (mkSelectWithLimitOffset "users" (some 1) (some 1))
    let expected := (allRows.drop 1).take 1
    if composed == expected then .pass "limit_offset_compose"
    else .fail "limit_offset_compose" s!"Results differ: {composed.length} vs {expected.length}",

    -- offset_zero_identity: OFFSET 0 = no offset
    testSelectEquiv "offset_zero_identity"
      (mkSelectWithLimitOffset "users" none none)
      (mkSelectWithLimitOffset "users" none (some 0))
      testDb,

    -- offset_too_large_empty: OFFSET >= count => []
    testLengthEq "offset_too_large_empty"
      (evalSelect testDb (mkSelectWithLimitOffset "users" none (some (allRows.length + 1)))).length
      0,

    -- offset_reduces_count: |OFFSET n| ≤ |no offset|
    testLengthLe "offset_reduces_count"
      (evalSelect testDb (mkSelectWithLimitOffset "users" none (some 1))).length
      allRows.length,

    -- offset_monotonic: m ≤ n => |OFFSET n| ≤ |OFFSET m|
    testLengthLe "offset_monotonic"
      (evalSelect testDb (mkSelectWithLimitOffset "users" none (some 2))).length
      (evalSelect testDb (mkSelectWithLimitOffset "users" none (some 1))).length,

    -- offset_limit_zero_empty: LIMIT 0 OFFSET n = []
    testLengthEq "offset_limit_zero_empty"
      (evalSelect testDb (mkSelectWithLimitOffset "users" (some 0) (some 1))).length
      0
  ]

-- ============================================================================
-- 11. Pagination Tests
-- ============================================================================

def paginationTests : List TestResult :=
  let selAll := mkSelectWithLimitOffset "users" none none
  let allRows := evalSelect testDb selAll
  [
    -- pagination_upper_bound: LIMIT n OFFSET m => |result| ≤ n
    testLengthLe "pagination_upper_bound"
      (evalSelect testDb (mkSelectWithLimitOffset "users" (some 2) (some 1))).length
      2,

    -- pagination_identity: OFFSET 0 LIMIT count = all
    testSelectEquiv "pagination_identity"
      selAll
      (mkSelectWithLimitOffset "users" (some allRows.length) (some 0))
      testDb,

    -- consecutive_pages: page1 ++ page2 = first 2*pageSize
    let page1 := evalSelect testDb (mkSelectWithLimitOffset "users" (some 1) (some 0))
    let page2 := evalSelect testDb (mkSelectWithLimitOffset "users" (some 1) (some 1))
    let both := evalSelect testDb (mkSelectWithLimitOffset "users" (some 2) (some 0))
    if page1 ++ page2 == both then .pass "consecutive_pages"
    else .fail "consecutive_pages" s!"page1({page1.length}) ++ page2({page2.length}) ≠ both({both.length})"
  ]

-- ============================================================================
-- 12. ORDER BY Tests
-- ============================================================================

def orderByTests : List TestResult :=
  let orderAsc := [OrderByItem.mk (col "age") .asc]
  let orderDesc := [OrderByItem.mk (col "age") .desc]
  let selNoOrder := mkSelectFull false "users" none [] none none
  let selAsc := mkSelectFull false "users" none orderAsc none none
  let selDesc := mkSelectFull false "users" none orderDesc none none
  [
    -- order_by_preserves_count: |ORDER BY| = |no order|
    testLengthEq "order_by_preserves_count"
      (evalSelect testDb selAsc).length
      (evalSelect testDb selNoOrder).length,


    -- order_by_length_invariant: different ORDER BY clauses produce same row count
    testLengthEq "order_by_length_invariant"
      (evalSelect testDb (mkSelectFull false "users" none
        [OrderByItem.mk (col "age") .asc, OrderByItem.mk (col "age") .desc] none none)).length
      (evalSelect testDb selDesc).length,


    -- order_limit_deterministic: ORDER BY + LIMIT n = (ORDER BY all).take n
    let selAscLimit2 := mkSelectFull false "users" none orderAsc (some 2) none
    let limitResult := evalSelect testDb selAscLimit2
    let allSorted := evalSelect testDb selAsc
    if limitResult == allSorted.take 2 then .pass "order_limit_deterministic"
    else .fail "order_limit_deterministic" "LIMIT result ≠ take from sorted"
  ]

-- ============================================================================
-- 13. Join Property Tests
-- ============================================================================

def joinTests : List TestResult :=
  let tUsers := FromClause.table ⟨"users", none⟩
  let tOrders := FromClause.table ⟨"orders", none⟩
  let tEmpty := FromClause.table ⟨"empty", none⟩
  let tProducts := FromClause.table ⟨"products", none⟩
  let condTrue := Expr.lit (.bool true)
  let condFalse := Expr.lit (.bool false)
  [
    -- cross_join_cardinality_comm: |A × B| = |B × A|
    testLengthEq "cross_join_cardinality_comm"
      (evalFrom testDb (.join tUsers .cross tOrders none)).length
      (evalFrom testDb (.join tOrders .cross tUsers none)).length,

    -- cross_join_cardinality: |A × B| = |A| * |B|
    testLengthEq "cross_join_cardinality"
      (evalFrom testDb (.join tUsers .cross tOrders none)).length
      ((evalFrom testDb tUsers).length * (evalFrom testDb tOrders).length),

    -- cross_join_assoc_cardinality: (A × B) × C has same count as A × (B × C)
    -- (#180: used the empty table, so both sides were 0.) 3 × 3 × 2 = 18.
    testLengthEq "cross_join_assoc_cardinality"
      (evalFrom testDb (.join (.join tUsers .cross tOrders none) .cross tProducts none)).length
      (evalFrom testDb (.join tUsers .cross (.join tOrders .cross tProducts none) none)).length,
    testLengthEq "cross_join_assoc_cardinality_nonempty"
      (evalFrom testDb (.join (.join tUsers .cross tOrders none) .cross tProducts none)).length 18,

    -- inner_join_true_is_cross: INNER JOIN ON TRUE = CROSS JOIN
    testLengthEq "inner_join_true_is_cross"
      (evalFrom testDb (.join tUsers .inner tOrders (some condTrue))).length
      (evalFrom testDb (.join tUsers .cross tOrders none)).length,

    -- inner_join_false_empty: INNER JOIN ON FALSE = []
    testLengthEq "inner_join_false_empty"
      (evalFrom testDb (.join tUsers .inner tOrders (some condFalse))).length
      0,

    -- left_join_false_all_left: LEFT JOIN ON FALSE preserves left count
    testLengthEq "left_join_false_all_left"
      (evalFrom testDb (.join tUsers .left tOrders (some condFalse))).length
      (evalFrom testDb tUsers).length,

    -- inner_join_cardinality_le: |INNER JOIN| ≤ |A| * |B|
    testLengthLe "inner_join_cardinality_le"
      (evalFrom testDb (.join tUsers .inner tOrders (some condTrue))).length
      ((evalFrom testDb tUsers).length * (evalFrom testDb tOrders).length),

    -- left_join_cardinality_ge: |LEFT JOIN| ≥ |A|
    testLengthGe "left_join_cardinality_ge"
      (evalFrom testDb (.join tUsers .left tOrders (some condTrue))).length
      (evalFrom testDb tUsers).length,

    -- right_join_cardinality_ge: |RIGHT JOIN| ≥ |B|
    testLengthGe "right_join_cardinality_ge"
      (evalFrom testDb (.join tUsers .right tOrders (some condTrue))).length
      (evalFrom testDb tOrders).length,

    -- inner_join_empty_left: INNER JOIN with empty left = []
    testLengthEq "inner_join_empty_left"
      (evalFrom testDb (.join tEmpty .inner tUsers (some condTrue))).length
      0,

    -- inner_join_empty_right: INNER JOIN with empty right = []
    testLengthEq "inner_join_empty_right"
      (evalFrom testDb (.join tUsers .inner tEmpty (some condTrue))).length
      0,

    -- cross_join_empty_left: CROSS JOIN with empty left = []
    testLengthEq "cross_join_empty_left"
      (evalFrom testDb (.join tEmpty .cross tUsers none)).length
      0,

    -- cross_join_empty_right: CROSS JOIN with empty right = []
    testLengthEq "cross_join_empty_right"
      (evalFrom testDb (.join tUsers .cross tEmpty none)).length
      0,

    -- inner_subset_cross: |INNER JOIN| ≤ |CROSS JOIN|
    testLengthLe "inner_subset_cross"
      (evalFrom testDb (.join tUsers .inner tOrders (some condTrue))).length
      (evalFrom testDb (.join tUsers .cross tOrders none)).length,

    -- inner_join_to_where: JOIN ON cond = CROSS JOIN filtered by cond
    let joinCond := Expr.binOp .eq
      (Expr.col ⟨some "users", "id"⟩) (Expr.col ⟨some "orders", "user_id"⟩)
    let tUsersAliased := FromClause.table ⟨"users", some "users"⟩
    let tOrdersAliased := FromClause.table ⟨"orders", some "orders"⟩
    let joinResult := evalFrom testDb (.join tUsersAliased .inner tOrdersAliased (some joinCond))
    let crossResult := evalFrom testDb (.join tUsersAliased .cross tOrdersAliased none)
    let crossFiltered := crossResult.filter fun row =>
      evalExprWithDb testDb row joinCond == some (.bool true)
    if joinResult == crossFiltered then .pass "inner_join_to_where"
    else .fail "inner_join_to_where"
      s!"Join({joinResult.length}) ≠ Filtered cross({crossFiltered.length})",

    -- left_join_preserves_left: every left row appears in LEFT JOIN result
    let leftRows := evalFrom testDb tUsers
    let leftJoinResult := evalFrom testDb (.join tUsers .left tOrders (some condTrue))
    testLengthGe "left_join_preserves_left"
      leftJoinResult.length leftRows.length,

    -- right_join_preserves_right: every right row appears in RIGHT JOIN result
    let rightRows := evalFrom testDb tOrders
    let rightJoinResult := evalFrom testDb (.join tUsers .right tOrders (some condTrue))
    testLengthGe "right_join_preserves_right"
      rightJoinResult.length rightRows.length,

    -- left_join_filter_null_is_inner:
    -- Filter LEFT JOIN result to exclude rows where right side is NULL => same count as INNER JOIN
    let tUA := FromClause.table ⟨"users", some "users"⟩
    let tOA := FromClause.table ⟨"orders", some "orders"⟩
    let jCond2 := Expr.binOp .eq
      (Expr.col ⟨some "users", "id"⟩) (Expr.col ⟨some "orders", "user_id"⟩)
    let leftJoinOnId := evalFrom testDb (.join tUA .left tOA (some jCond2))
    let innerJoinOnId := evalFrom testDb (.join tUA .inner tOA (some jCond2))
    let filtered := leftJoinOnId.filter fun row =>
      match row.find? (fun (k, _) => k == "orders.id") with
      | some (_, v) => !isNullValue v
      | none =>
        match row.find? (fun (k, _) => k == "id") with
        | some (_, v) => !isNullValue v
        | none => false
    -- Both should have the same number of matching rows
    testLengthEq "left_join_filter_null_is_inner"
      filtered.length innerJoinOnId.length,

    -- cross_join_comm: every row in A×B has a corresponding row in B×A (full row-set equality)
    let ab := evalFrom testDb (.join tUsers .cross tOrders none)
    let ba := evalFrom testDb (.join tOrders .cross tUsers none)
    let normalizeRow' (r : Row) : Row := r.mergeSort (fun a b => a.1 < b.1)
    let rowKey' (r : Row) : String := (normalizeRow' r).foldl (fun acc (k, v) => acc ++ k ++ "=" ++ v.toSql ++ ",") ""
    let normAB := (ab.map normalizeRow').mergeSort (fun a b => rowKey' a < rowKey' b)
    let normBA := (ba.map normalizeRow').mergeSort (fun a b => rowKey' a < rowKey' b)
    if normAB == normBA then .pass "cross_join_comm"
    else .fail "cross_join_comm" s!"Row sets differ after normalizing: {ab.length} vs {ba.length} rows",

    -- join_comm_full: DELETED (unsound — strict Table equality fails due to column ordering)
    -- Use cross_join_comm (membership-based, already proved) for commutativity.

    -- cross_join_assoc: (A × B) × C = A × (B × C) (full row-set equality)
    -- Use three non-empty tables so the test is non-vacuous
    let tProducts := FromClause.table ⟨"products", none⟩
    let abc1 := evalFrom testDb (.join (.join tUsers .cross tOrders none) .cross tProducts none)
    let abc2 := evalFrom testDb (.join tUsers .cross (.join tOrders .cross tProducts none) none)
    let normalizeRowJ (r : Row) : Row := r.mergeSort (fun a b => a.1 < b.1)
    let rowKeyJ (r : Row) : String := (normalizeRowJ r).foldl (fun acc (k, v) => acc ++ k ++ "=" ++ v.toSql ++ ",") ""
    let normAbc1 := (abc1.map normalizeRowJ).mergeSort (fun a b => rowKeyJ a < rowKeyJ b)
    let normAbc2 := (abc2.map normalizeRowJ).mergeSort (fun a b => rowKeyJ a < rowKeyJ b)
    if normAbc1 == normAbc2 then .pass "cross_join_assoc"
    else .fail "cross_join_assoc" s!"Row sets differ: {abc1.length} vs {abc2.length} rows",

    -- join_assoc: associativity for inner joins (full row-set equality)
    -- Use three non-empty tables with ON TRUE so the test is non-vacuous
    let tProducts2 := FromClause.table ⟨"products", none⟩
    let r1' := evalFrom testDb (.join (.join tUsers .inner tOrders (some condTrue)) .inner tProducts2 (some condTrue))
    let r2' := evalFrom testDb (.join tUsers .inner (.join tOrders .inner tProducts2 (some condTrue)) (some condTrue))
    let normalizeRowJ2 (r : Row) : Row := r.mergeSort (fun a b => a.1 < b.1)
    let rowKeyJ2 (r : Row) : String := (normalizeRowJ2 r).foldl (fun acc (k, v) => acc ++ k ++ "=" ++ v.toSql ++ ",") ""
    let normR1 := (r1'.map normalizeRowJ2).mergeSort (fun a b => rowKeyJ2 a < rowKeyJ2 b)
    let normR2 := (r2'.map normalizeRowJ2).mergeSort (fun a b => rowKeyJ2 a < rowKeyJ2 b)
    if normR1 == normR2 then .pass "join_assoc"
    else .fail "join_assoc" s!"Row sets differ: {r1'.length} vs {r2'.length} rows"
  ]

-- ============================================================================
-- 14. Filter Operation Tests
-- ============================================================================

def filterTests : List TestResult :=
  let tUsers := "users"
  let pTrue := Expr.lit (.bool true)
  let pFalse := Expr.lit (.bool false)
  let pAge30 := Expr.binOp .gt (col "age") (.lit (.int 25))
  [
    -- filter_and: (WHERE p) WHERE q = WHERE (p AND q)
    -- Note: subquery wrapping may change column names; compare row counts
    let innerSel := SelectStmt.mk false [.star none]
      (some (.table ⟨tUsers, none⟩)) (some pAge30) [] none [] none none
    let outerWithQ := SelectStmt.mk false [.star none]
      (some (.subquery (.simple innerSel) "inner")) (some pTrue) [] none [] none none
    let combined := SelectStmt.mk false [.star none]
      (some (.table ⟨tUsers, none⟩)) (some (.binOp .and pAge30 pTrue)) [] none [] none none
    testLengthEq "filter_and"
      (evalSelect testDb outerWithQ).length
      (evalSelect testDb combined).length,

    -- filter_commute: (WHERE p) WHERE q = (WHERE q) WHERE p
    let innerP := SelectStmt.mk false [.star none]
      (some (.table ⟨tUsers, none⟩)) (some pAge30) [] none [] none none
    let outerQ := SelectStmt.mk false [.star none]
      (some (.subquery (.simple innerP) "inner")) (some pTrue) [] none [] none none
    let innerQ := SelectStmt.mk false [.star none]
      (some (.table ⟨tUsers, none⟩)) (some pTrue) [] none [] none none
    let outerP := SelectStmt.mk false [.star none]
      (some (.subquery (.simple innerQ) "inner")) (some pAge30) [] none [] none none
    testLengthEq "filter_commute"
      (evalSelect testDb outerQ).length
      (evalSelect testDb outerP).length,

    -- filter_idempotent: (WHERE p) WHERE p = WHERE p
    -- Note: subquery wrapping may change column names; compare row counts
    let innerIdent := SelectStmt.mk false [.star none]
      (some (.table ⟨tUsers, none⟩)) (some pAge30) [] none [] none none
    let outerIdent := SelectStmt.mk false [.star none]
      (some (.subquery (.simple innerIdent) "inner")) (some pAge30) [] none [] none none
    let singleFilter := SelectStmt.mk false [.star none]
      (some (.table ⟨tUsers, none⟩)) (some pAge30) [] none [] none none
    testLengthEq "filter_idempotent"
      (evalSelect testDb outerIdent).length
      (evalSelect testDb singleFilter).length,

    -- filter_false_empty': WHERE FALSE = []
    testLengthEq "filter_false_empty'"
      (evalSelect testDb (SelectStmt.mk false [.star none]
        (some (.table ⟨tUsers, none⟩)) (some pFalse) [] none [] none none)).length
      0
  ]

-- ============================================================================
-- 15. Subquery Operation Tests
-- ============================================================================

def subqueryTests : List TestResult :=
  let emptySubSel := SelectStmt.mk false [.star none]
    (some (.table ⟨"empty", none⟩)) none [] none [] none none
  let nonemptySubSel := SelectStmt.mk false [.star none]
    (some (.table ⟨"users", none⟩)) none [] none [] none none
  let testRow : Row := [("x", .int 1)]
  [
    -- exists_empty_false: EXISTS (empty) = FALSE
    let r := evalExprWithDb testDb testRow (.exists false (.simple emptySubSel))
    if r == some (.bool false) then .pass "exists_empty_false"
    else .fail "exists_empty_false" s!"Expected FALSE, got {showOptVal r}",

    -- not_exists_empty_true: NOT EXISTS (empty) = TRUE
    let r := evalExprWithDb testDb testRow (.exists true (.simple emptySubSel))
    if r == some (.bool true) then .pass "not_exists_empty_true"
    else .fail "not_exists_empty_true" s!"Expected TRUE, got {showOptVal r}",

    -- exists_nonempty_true: EXISTS (nonempty) = TRUE
    let r := evalExprWithDb testDb testRow (.exists false (.simple nonemptySubSel))
    if r == some (.bool true) then .pass "exists_nonempty_true"
    else .fail "exists_nonempty_true" s!"Expected TRUE, got {showOptVal r}",

    -- not_exists_nonempty_false: NOT EXISTS (nonempty) = FALSE
    let r := evalExprWithDb testDb testRow (.exists true (.simple nonemptySubSel))
    if r == some (.bool false) then .pass "not_exists_nonempty_false"
    else .fail "not_exists_nonempty_false" s!"Expected FALSE, got {showOptVal r}",

    -- not_not_exists: NOT EXISTS sel ≃ₑ NOT (EXISTS sel)
    testExprEquivDb "not_not_exists"
      (.exists true (.simple nonemptySubSel))
      (.unaryOp .not (.exists false (.simple nonemptySubSel)))
      testDb testRow,

    -- in_empty_subquery_false: test semantics
    -- When subquery is empty, IN should evaluate to FALSE
    let inEmptyExpr := Expr.inSubquery (.lit (.int 999)) false (.simple emptySubSel)
    let r := evalExprWithDb testDb testRow inEmptyExpr
    if r == some (.bool false) then .pass "in_empty_subquery_false"
    else .fail "in_empty_subquery_false" s!"Expected FALSE, got {showOptVal r}",

    -- not_in_empty_subquery_true: NOT IN empty subquery = TRUE
    let notInEmptyExpr := Expr.inSubquery (.lit (.int 999)) true (.simple emptySubSel)
    let r := evalExprWithDb testDb testRow notInEmptyExpr
    if r == some (.bool true) then .pass "not_in_empty_subquery_true"
    else .fail "not_in_empty_subquery_true" s!"Expected TRUE, got {showOptVal r}",

    -- scalar_subquery_empty_null: scalar subquery on empty = NULL
    let scalarEmpty := Expr.subquery (.simple emptySubSel)
    let r := evalExprWithDb testDb testRow scalarEmpty
    if r == some (.null none) then .pass "scalar_subquery_empty_null"
    else .fail "scalar_subquery_empty_null" s!"Expected NULL, got {showOptVal r}",

    -- exists_as_count_gt_zero: EXISTS = (count > 0)
    let existsResult := evalExprWithDb testDb testRow (.exists false (.simple nonemptySubSel))
    let subRows := evalSelectWithContext testDb testRow nonemptySubSel
    let expected := some (.bool (subRows.length > 0))
    if existsResult == expected then .pass "exists_as_count_gt_zero"
    else .fail "exists_as_count_gt_zero"
      s!"EXISTS={showOptVal existsResult}, expected={showOptVal expected}",

    -- not_exists_as_count_eq_zero: NOT EXISTS = (count == 0)
    let notExistsResult := evalExprWithDb testDb testRow (.exists true (.simple emptySubSel))
    let subRows := evalSelectWithContext testDb testRow emptySubSel
    let expected := some (.bool (subRows.length == 0))
    if notExistsResult == expected then .pass "not_exists_as_count_eq_zero"
    else .fail "not_exists_as_count_eq_zero"
      s!"NOT EXISTS={showOptVal notExistsResult}, expected={showOptVal expected}",

    -- subquery_limit_one: LIMIT 1 => at most 1 row
    let selLimit1 := SelectStmt.mk false [.star none]
      (some (.table ⟨"users", none⟩)) none [] none [] (some 1) none
    testLengthLe "subquery_limit_one"
      (evalSelectWithContext testDb testRow selLimit1).length 1,

    -- scalar_subquery_is_first: scalar subquery = first value
    let selOneCol := SelectStmt.mk false
      [.exprItem (col "id") none]
      (some (.table ⟨"users", none⟩)) none [] none [] (some 1) none
    let scalarResult := evalExprWithDb testDb testRow (.subquery (.simple selOneCol))
    let subRows := evalSelectWithContext testDb testRow selOneCol
    let expectedVal := match subRows.head? with
      | some subRow => subRow.head?.map (·.2)
      | none => some (.null none)
    if scalarResult == expectedVal then .pass "scalar_subquery_is_first"
    else .fail "scalar_subquery_is_first"
      s!"Scalar={showOptVal scalarResult}, expected={showOptVal expectedVal}",

    -- subquery_where_true: WHERE TRUE doesn't change subquery result
    let selNoWhere := SelectStmt.mk false [.star none]
      (some (.table ⟨"users", none⟩)) none [] none [] none none
    let selWhereTrue := SelectStmt.mk false [.star none]
      (some (.table ⟨"users", none⟩)) (some (.lit (.bool true))) [] none [] none none
    let r1 := evalSelectWithContext testDb testRow selNoWhere
    let r2 := evalSelectWithContext testDb testRow selWhereTrue
    if r1 == r2 then .pass "subquery_where_true"
    else .fail "subquery_where_true" "WHERE TRUE changed result",

    -- subquery_where_false: WHERE FALSE makes subquery empty
    let selWhereFalse := SelectStmt.mk false [.star none]
      (some (.table ⟨"users", none⟩)) (some (.lit (.bool false))) [] none [] none none
    testLengthEq "subquery_where_false"
      (evalSelectWithContext testDb testRow selWhereFalse).length 0,

    -- in_singleton_subquery: IN (single value subquery) = equality
    -- Test by constructing a subquery that returns exactly one value
    let singleValSel := SelectStmt.mk false
      [.exprItem (.lit (.int 42)) (some "val")]
      none none [] none [] (some 1) none
    let inResult := evalExprWithDb testDb testRow
      (.inSubquery (.lit (.int 42)) false (.simple singleValSel))
    if inResult == some (.bool true) then .pass "in_singleton_subquery"
    else .fail "in_singleton_subquery" s!"Expected TRUE, got {showOptVal inResult}",

    -- correlated_subquery_uses_context: commented out (axiom asserts True, no dependents)

    -- exists_monotonic: if sel1 ⊆ sel2 and EXISTS sel1 = TRUE, then EXISTS sel2 = TRUE
    -- Subset: orders WHERE amount > 100 (1 row: amount=200)
    -- Superset: all orders (3 rows, includes the subset)
    let subsetSel := SelectStmt.mk false [.star none]
      (some (.table ⟨"orders", none⟩))
      (some (.binOp .gt (col "amount") (.lit (.int 100))))
      [] none [] none none
    let supersetSel := SelectStmt.mk false [.star none]
      (some (.table ⟨"orders", none⟩))
      none [] none [] none none
    let existsSubset := evalExprWithDb testDb testRow (.exists false (.simple subsetSel))
    let existsSuperset := evalExprWithDb testDb testRow (.exists false (.simple supersetSel))
    -- Monotonicity: EXISTS subset = TRUE implies EXISTS superset = TRUE
    if existsSubset == some (.bool true) && existsSuperset == some (.bool true)
    then .pass "exists_monotonic"
    else .fail "exists_monotonic"
      s!"Expected both TRUE: subset={showOptVal existsSubset}, superset={showOptVal existsSuperset}"
  ]

-- ============================================================================
-- 16. Normalization/Decision Tests
-- ============================================================================

def normalizationDecisionTests : List TestResult :=
  [
    -- normalizeExpr_equiv: normalized form evaluates same as original
    -- (#180: was evaluated on intRow, where AND returns none on both sides.)
    -- `b AND a` is not in normal order, so normalizeExpr actually swaps it.
    let e := Expr.binOp .and (col "b") (col "a")
    let ne := normalizeExpr e
    testExprEquiv "normalizeExpr_equiv (AND)" ne e boolRow,
    (let e := Expr.binOp .and (col "b") (col "a")
     if normalizeExpr e != e && (evalExpr boolRow e).isSome then .pass "normalizeExpr_equiv (AND) nonvacuous"
     else .fail "normalizeExpr_equiv (AND) nonvacuous" "normalizeExpr left it unchanged or it evaluates to none"),

    let e := Expr.binOp .or (col "a") (col "b")
    let ne := normalizeExpr e
    testExprEquiv "normalizeExpr_equiv (OR)" ne e boolRow,

    -- syntacticEquiv_implies_equiv: syntactically equiv => semantically equiv
    let e1 := Expr.binOp .add (col "x") (col "y")
    let e2 := Expr.binOp .add (col "y") (col "x")
    if syntacticEquiv e1 e2 then
      testExprEquiv "syntacticEquiv_implies_equiv" e1 e2 intRow
    else .fail "syntacticEquiv_implies_equiv" "Not syntactically equivalent",

    -- ground_expr_eval_independent: ground expressions give same result on any row
    let groundExpr := Expr.binOp .add (.lit (.int 2)) (.lit (.int 3))
    let r1 := evalExpr [] groundExpr
    let r2 := evalExpr intRow groundExpr
    if r1 == r2 then .pass "ground_expr_eval_independent"
    else .fail "ground_expr_eval_independent"
      s!"Different on empty vs intRow: {showOptVal r1} vs {showOptVal r2}",

    -- decideGroundExprEquiv_sound: exercise decideGroundExprEquiv and verify it agrees with eval
    let e1 := Expr.binOp .add (.lit (.int 2)) (.lit (.int 3))
    let e2 := Expr.lit (.int 5)
    let h1 := e1.isGround
    let h2 := e2.isGround
    if h1 && h2 then
      let decided := decideGroundExprEquiv e1 e2 (by native_decide) (by native_decide)
      let evalsEqual := evalExpr [] e1 == evalExpr [] e2
      if decided == evalsEqual then .pass "decideGroundExprEquiv_sound"
      else .fail "decideGroundExprEquiv_sound"
        s!"decideGroundExprEquiv={decided} but evalExpr equal={evalsEqual}"
    else .fail "decideGroundExprEquiv_sound"
      s!"Expressions not ground: e1.isGround={h1}, e2.isGround={h2}"
  ]

-- ============================================================================
-- 17. Predicate Pushdown Tests
-- ============================================================================

def predicatePushdownTests : List TestResult :=
  [
    -- filter_pushdown_table: filter in WHERE = filter in subquery
    -- Subquery wrapping may change column names; compare row counts
    let tRef : TableRef := ⟨"users", none⟩
    let filterExpr := Expr.binOp .gt (col "age") (.lit (.int 25))
    let sel1 := SelectStmt.mk false [.star none]
      (some (.table tRef)) (some filterExpr) [] none [] none none
    let innerSel := SelectStmt.mk false [.star none]
      (some (.table tRef)) (some filterExpr) [] none [] none none
    let sel2 := SelectStmt.mk false [.star none]
      (some (.subquery (.simple innerSel) (tRef.alias.getD tRef.name))) none [] none [] none none
    testLengthEq "filter_pushdown_table"
      (evalSelect testDb sel1).length
      (evalSelect testDb sel2).length,

    -- predicate_pushdown: filtering after select with combined WHERE
    let inner := SelectStmt.mk false [.star none]
      (some (.table ⟨"users", none⟩))
      (some (Expr.binOp .gt (col "age") (.lit (.int 20))))
      [] none [] none none
    let innerResult := evalSelect testDb inner
    let furtherFiltered := innerResult.filter
      (fun row => evalExpr row (Expr.binOp .lt (col "age") (.lit (.int 35))) == some (.bool true))
    let combinedSel := SelectStmt.mk false [.star none]
      (some (.table ⟨"users", none⟩))
      (some (.binOp .and
        (Expr.binOp .gt (col "age") (.lit (.int 20)))
        (Expr.binOp .lt (col "age") (.lit (.int 35)))))
      [] none [] none none
    let combinedResult := evalSelect testDb combinedSel
    if furtherFiltered.length == combinedResult.length
    then .pass "predicate_pushdown"
    else .fail "predicate_pushdown"
      s!"Filtered({furtherFiltered.length}) ≠ Combined({combinedResult.length})",

    -- filter_join_left: filtering a join result by a left-only predicate should yield the
    -- same rows as joining the pre-filtered left table with the right table.
    -- This exercises the semantic property behind the filter_join_left axiom.
    let tU := FromClause.table ⟨"users", some "u"⟩
    let tO := FromClause.table ⟨"orders", some "o"⟩
    let joinCond := Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id")
    let leftFilter := Expr.binOp .gt (qcol "u" "age") (.lit (.int 25))
    -- Approach: join then filter vs filter-left then join (both via evalFrom)
    let allJoined := evalFrom testDb (.join tU .inner tO (some joinCond))
    let filteredAfter := allJoined.filter fun row =>
      evalExprWithDb testDb row leftFilter == some (.bool true)
    let leftFiltered := (evalFrom testDb tU).filter fun row =>
      evalExprWithDb testDb row leftFilter == some (.bool true)
    let joinedAfterFilter := leftFiltered.flatMap fun lr =>
      (evalFrom testDb tO).filterMap fun rr =>
        let combined := lr ++ rr
        if evalExprWithDb testDb combined joinCond == some (.bool true) then some combined
        else none
    testLengthEq "filter_join_left"
      filteredAfter.length joinedAfterFilter.length,

    -- filter_join_right: filtering a join result by a right-only predicate should yield the
    -- same rows as joining the left table with the pre-filtered right table.
    -- This exercises the semantic property behind the filter_join_right axiom.
    let tU2 := FromClause.table ⟨"users", some "u"⟩
    let tO2 := FromClause.table ⟨"orders", some "o"⟩
    let joinCond2 := Expr.binOp .eq (qcol "u" "id") (qcol "o" "user_id")
    let rightFilter := Expr.binOp .gt (qcol "o" "amount") (.lit (.int 100))
    let allJoined2 := evalFrom testDb (.join tU2 .inner tO2 (some joinCond2))
    let filteredAfter2 := allJoined2.filter fun row =>
      evalExprWithDb testDb row rightFilter == some (.bool true)
    let rightFiltered := (evalFrom testDb tO2).filter fun row =>
      evalExprWithDb testDb row rightFilter == some (.bool true)
    let joinedAfterFilter2 := (evalFrom testDb tU2).flatMap fun lr =>
      rightFiltered.filterMap fun rr =>
        let combined := lr ++ rr
        if evalExprWithDb testDb combined joinCond2 == some (.bool true) then some combined
        else none
    testLengthEq "filter_join_right"
      filteredAfter2.length joinedAfterFilter2.length
  ]

-- ============================================================================
-- Additional axiom tests: not_not, and_true, or_false, etc.
-- ============================================================================

def additionalLogicTests : List TestResult :=
  [
    -- not_not: NOT NOT e ≃ₑ e (for boolean-valued)
    testExprEquiv "not_not (true)"
      (.unaryOp .not (.unaryOp .not eTrue)) eTrue [],
    testExprEquiv "not_not (false)"
      (.unaryOp .not (.unaryOp .not eFalse)) eFalse [],

    -- and_true: a AND TRUE ≃ₑ a (for boolean-valued)
    testExprEquiv "and_true (true)"
      (.binOp .and eTrue eTrue) eTrue [],
    testExprEquiv "and_true (false)"
      (.binOp .and eFalse eTrue) eFalse [],

    -- or_false: a OR FALSE ≃ₑ a (for boolean-valued)
    testExprEquiv "or_false (true)"
      (.binOp .or eTrue eFalse) eTrue [],
    testExprEquiv "or_false (false)"
      (.binOp .or eFalse eFalse) eFalse [],

    -- and_absorb_or: a AND (a OR b) ≃ₑ a (for boolean)
    testExprEquiv "and_absorb_or (true, true)"
      (.binOp .and eTrue (.binOp .or eTrue eTrue)) eTrue [],
    testExprEquiv "and_absorb_or (false, true)"
      (.binOp .and eFalse (.binOp .or eFalse eTrue)) eFalse [],

    -- or_absorb_and: a OR (a AND b) ≃ₑ a (for boolean)
    testExprEquiv "or_absorb_and (true, false)"
      (.binOp .or eTrue (.binOp .and eTrue eFalse)) eTrue [],
    testExprEquiv "or_absorb_and (false, true)"
      (.binOp .or eFalse (.binOp .and eFalse eTrue)) eFalse [],

    -- where_true_elim: WHERE TRUE = no WHERE
    testSelectEquiv "where_true_elim"
      (SelectStmt.mk false [.star none] (some (.table ⟨"users", none⟩))
        (some (.lit (.bool true))) [] none [] none none)
      (SelectStmt.mk false [.star none] (some (.table ⟨"users", none⟩))
        none [] none [] none none)
      testDb,

    -- where_false_empty: WHERE FALSE has 0 rows (or no FROM)
    testLengthEq "where_false_empty"
      (evalSelect testDb (SelectStmt.mk false [.star none]
        (some (.table ⟨"users", none⟩))
        (some (.lit (.bool false))) [] none [] none none)).length
      0,

    -- evalBinOp_and_assoc: value-level AND associativity
    let vx := some (.bool true : Value)
    let vy := some (.bool false : Value)
    let vz := some (.bool true : Value)
    if evalBinOp .and (evalBinOp .and vx vy) vz ==
       evalBinOp .and vx (evalBinOp .and vy vz)
    then .pass "evalBinOp_and_assoc"
    else .fail "evalBinOp_and_assoc" "AND not associative",

    -- evalBinOp_or_assoc: value-level OR associativity
    let vx2 := some (.bool true : Value)
    let vy2 := some (.bool false : Value)
    let vz2 := some (.bool true : Value)
    if evalBinOp .or (evalBinOp .or vx2 vy2) vz2 ==
       evalBinOp .or vx2 (evalBinOp .or vy2 vz2)
    then .pass "evalBinOp_or_assoc"
    else .fail "evalBinOp_or_assoc" "OR not associative",

    -- and_or_distrib_left: a AND (b OR c) ≃ₑ (a AND b) OR (a AND c)
    testExprEquiv "and_or_distrib_left"
      (.binOp .and eTrue (.binOp .or eFalse eTrue))
      (.binOp .or (.binOp .and eTrue eFalse) (.binOp .and eTrue eTrue)) [],

    -- and_or_distrib_right: (a OR b) AND c ≃ₑ (a AND c) OR (b AND c)
    testExprEquiv "and_or_distrib_right"
      (.binOp .and (.binOp .or eTrue eFalse) eTrue)
      (.binOp .or (.binOp .and eTrue eTrue) (.binOp .and eFalse eTrue)) [],

    -- or_and_distrib_left: a OR (b AND c) ≃ₑ (a OR b) AND (a OR c)
    testExprEquiv "or_and_distrib_left"
      (.binOp .or eFalse (.binOp .and eTrue eFalse))
      (.binOp .and (.binOp .or eFalse eTrue) (.binOp .or eFalse eFalse)) [],

    -- or_and_distrib_right: (a AND b) OR c ≃ₑ (a OR c) AND (b OR c)
    testExprEquiv "or_and_distrib_right"
      (.binOp .or (.binOp .and eTrue eFalse) eTrue)
      (.binOp .and (.binOp .or eTrue eTrue) (.binOp .or eFalse eTrue)) [],

    -- min_le_elem: MIN ≤ every element in the list
    let ns : List Int := [5, 3, 8, 1]
    let minVal := List.foldl min ns.head! ns
    if ns.all (fun n => minVal ≤ n) then .pass "min_le_elem"
    else .fail "min_le_elem" s!"MIN {minVal} is not ≤ all elements in {ns}",

    -- max_ge_elem: MAX ≥ every element in the list
    let ns2 : List Int := [5, 3, 8, 1]
    let maxVal := List.foldl max ns2.head! ns2
    if ns2.all (fun n => n ≤ maxVal) then .pass "max_ge_elem"
    else .fail "max_ge_elem" s!"MAX {maxVal} is not ≥ all elements in {ns2}",

    -- distinct_count_le: |eraseDups| ≤ |original|
    let vs : List Value := [.int 1, .int 2, .int 1, .int 3]
    if vs.eraseDups.length ≤ vs.length then .pass "distinct_count_le"
    else .fail "distinct_count_le" "eraseDups increased length",

    -- distinct_idempotent: eraseDups twice = once
    let vs2 : List Value := [.int 1, .int 2, .int 1]
    if vs2.eraseDups.eraseDups == vs2.eraseDups then .pass "distinct_idempotent"
    else .fail "distinct_idempotent" "eraseDups not idempotent"
  ]

-- ============================================================================
-- Subquery Unnesting Tests
-- ============================================================================

def subqueryUnnestingTests : List TestResult :=
  let unnestRow : Row := [("x", .int 1)]
  [
    -- in_subquery_as_exists: x IN (SELECT t.col FROM t) = EXISTS (SELECT 1 FROM t WHERE t.col = x)
    -- Uses qualified column references and no table alias, matching the theorem signature
    let inSub := Expr.inSubquery (.lit (.int 1)) false
      (.simple (SelectStmt.mk false [.exprItem (.col ⟨some "orders", "user_id"⟩) none]
        (some (.table ⟨"orders", none⟩)) none [] none [] none none))
    let existsSub := Expr.exists false
      (.simple (SelectStmt.mk false [.exprItem (.lit (.int 1)) none]
        (some (.table ⟨"orders", none⟩))
        (some (.binOp .eq (.col ⟨some "orders", "user_id"⟩) (.lit (.int 1))))
        [] none [] none none))
    let inResult := evalExprWithDb testDb unnestRow inSub
    let existsResult := evalExprWithDb testDb unnestRow existsSub
    if inResult == existsResult then .pass "in_subquery_as_exists"
    else .fail "in_subquery_as_exists"
      s!"IN={showOptVal inResult}, EXISTS={showOptVal existsResult}",

    -- not_in_subquery_as_not_exists
    let notInSub := Expr.inSubquery (.lit (.int 999)) true
      (.simple (SelectStmt.mk false [.exprItem (.col ⟨some "orders", "user_id"⟩) none]
        (some (.table ⟨"orders", none⟩)) none [] none [] none none))
    let notExistsSub := Expr.exists true
      (.simple (SelectStmt.mk false [.exprItem (.lit (.int 1)) none]
        (some (.table ⟨"orders", none⟩))
        (some (.binOp .eq (.col ⟨some "orders", "user_id"⟩) (.lit (.int 999))))
        [] none [] none none))
    let notInResult := evalExprWithDb testDb unnestRow notInSub
    let notExistsResult := evalExprWithDb testDb unnestRow notExistsSub
    if notInResult == notExistsResult then .pass "not_in_subquery_as_not_exists"
    else .fail "not_in_subquery_as_not_exists"
      s!"NOT IN={showOptVal notInResult}, NOT EXISTS={showOptVal notExistsResult}"
  ]

-- ============================================================================
-- Semantics Unfold Tests (axioms: evalExprWithDb_lit, evalExprWithDb_binOp, evalExprWithDb_unaryOp)
-- ============================================================================

def semanticsUnfoldTests : List TestResult :=
  let db := testDb
  let row := [("x", .int 5), ("y", .int 3)]
  [
    -- evalExprWithDb_lit: evalExprWithDb db row (lit v) = some v
    let r := evalExprWithDb db row (.lit (.int 42))
    if r == some (.int 42) then .pass "evalExprWithDb_lit (int)"
    else .fail "evalExprWithDb_lit (int)" s!"Expected some 42, got {showOptVal r}",

    let r := evalExprWithDb db row (.lit (.string "hello"))
    if r == some (.string "hello") then .pass "evalExprWithDb_lit (string)"
    else .fail "evalExprWithDb_lit (string)" s!"Expected some hello, got {showOptVal r}",

    let r := evalExprWithDb db row (.lit (.bool true))
    if r == some (.bool true) then .pass "evalExprWithDb_lit (bool)"
    else .fail "evalExprWithDb_lit (bool)" s!"Expected some true, got {showOptVal r}",

    let r := evalExprWithDb db row (.lit (.null none))
    if r == some (.null none) then .pass "evalExprWithDb_lit (null)"
    else .fail "evalExprWithDb_lit (null)" s!"Expected some null, got {showOptVal r}",

    -- evalExprWithDb_binOp: evalExprWithDb db row (binOp op l r) = evalBinOp op (evalExprWithDb db row l) (evalExprWithDb db row r)
    let l := Expr.lit (.int 3)
    let r_ := Expr.lit (.int 5)
    let direct := evalExprWithDb db row (.binOp .add l r_)
    let stepwise := evalBinOp .add (evalExprWithDb db row l) (evalExprWithDb db row r_)
    if direct == stepwise then .pass "evalExprWithDb_binOp (add)"
    else .fail "evalExprWithDb_binOp (add)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    let l := Expr.lit (.bool true)
    let r_ := Expr.lit (.bool false)
    let direct := evalExprWithDb db row (.binOp .and l r_)
    let stepwise := evalBinOp .and (evalExprWithDb db row l) (evalExprWithDb db row r_)
    if direct == stepwise then .pass "evalExprWithDb_binOp (and)"
    else .fail "evalExprWithDb_binOp (and)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    let l := Expr.lit (.int 10)
    let r_ := Expr.lit (.int 3)
    let direct := evalExprWithDb db row (.binOp .gt l r_)
    let stepwise := evalBinOp .gt (evalExprWithDb db row l) (evalExprWithDb db row r_)
    if direct == stepwise then .pass "evalExprWithDb_binOp (gt)"
    else .fail "evalExprWithDb_binOp (gt)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    -- evalExprWithDb_unaryOp: evalExprWithDb db row (unaryOp op e) = evalUnaryOp op (evalExprWithDb db row e)
    let e := Expr.lit (.bool true)
    let direct := evalExprWithDb db row (.unaryOp .not e)
    let stepwise := evalUnaryOp .not (evalExprWithDb db row e)
    if direct == stepwise then .pass "evalExprWithDb_unaryOp (NOT)"
    else .fail "evalExprWithDb_unaryOp (NOT)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    let e := Expr.lit (.int 5)
    let direct := evalExprWithDb db row (.unaryOp .neg e)
    let stepwise := evalUnaryOp .neg (evalExprWithDb db row e)
    if direct == stepwise then .pass "evalExprWithDb_unaryOp (NEG)"
    else .fail "evalExprWithDb_unaryOp (NEG)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    let e := Expr.lit (.null none)
    let direct := evalExprWithDb db row (.unaryOp .isNull e)
    let stepwise := evalUnaryOp .isNull (evalExprWithDb db row e)
    if direct == stepwise then .pass "evalExprWithDb_unaryOp (IS NULL)"
    else .fail "evalExprWithDb_unaryOp (IS NULL)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    -- evalExprWithDb_case: evalExprWithDb db row (case branches else_) = evalCase db row branches else_
    let branches := [(Expr.lit (.bool true), Expr.lit (.int 1))]
    let else_ := some (Expr.lit (.int 0))
    let direct := evalExprWithDb db row (.case branches else_)
    let stepwise := evalCase db row branches else_
    if direct == stepwise then .pass "evalExprWithDb_case (true branch)"
    else .fail "evalExprWithDb_case (true branch)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    let branches := [(Expr.lit (.bool false), Expr.lit (.int 1))]
    let else_ := some (Expr.lit (.int 0))
    let direct := evalExprWithDb db row (.case branches else_)
    let stepwise := evalCase db row branches else_
    if direct == stepwise then .pass "evalExprWithDb_case (false branch)"
    else .fail "evalExprWithDb_case (false branch)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    -- evalCase_nil_some: evalCase db row [] (some e) = evalExprWithDb db row e
    let e := Expr.lit (.int 42)
    let direct := evalCase db row [] (some e)
    let stepwise := evalExprWithDb db row e
    if direct == stepwise then .pass "evalCase_nil_some (lit int)"
    else .fail "evalCase_nil_some (lit int)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    -- evalCase_nil_none: evalCase db row [] none = some (.null none)
    let direct := evalCase db row [] none
    if direct == some (.null none) then .pass "evalCase_nil_none (returns null)"
    else .fail "evalCase_nil_none (returns null)" s!"Expected some null, got {showOptVal direct}",

    -- evalCase_cons_true: when cond evals to true, returns result
    let cond := Expr.lit (.bool true)
    let result := Expr.lit (.int 99)
    let rest := [(Expr.lit (.bool false), Expr.lit (.int 0))]
    let else_ := some (Expr.lit (.int (-1)))
    let direct := evalCase db row ((cond, result) :: rest) else_
    let expected := evalExprWithDb db row result
    if direct == expected then .pass "evalCase_cons_true (returns result)"
    else .fail "evalCase_cons_true (returns result)" s!"Direct={showOptVal direct}, Expected={showOptVal expected}",

    -- evalCase_cons_false: when cond evals to false, recurses to rest
    let cond := Expr.lit (.bool false)
    let result := Expr.lit (.int 99)
    let rest := [(Expr.lit (.bool true), Expr.lit (.int 42))]
    let else_ := some (Expr.lit (.int (-1)))
    let direct := evalCase db row ((cond, result) :: rest) else_
    let expected := evalCase db row rest else_
    if direct == expected then .pass "evalCase_cons_false (skips to rest)"
    else .fail "evalCase_cons_false (skips to rest)" s!"Direct={showOptVal direct}, Expected={showOptVal expected}",

    -- evalExprWithDb_func: evalExprWithDb db row (func name args) = evalFunc name (args.map (evalExprWithDb db row))
    let args := [Expr.lit (.string "hello")]
    let direct := evalExprWithDb db row (.func "LENGTH" args)
    let stepwise := evalFunc "LENGTH" (args.map (evalExprWithDb db row))
    if direct == stepwise then .pass "evalExprWithDb_func (LENGTH)"
    else .fail "evalExprWithDb_func (LENGTH)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    let args := [Expr.lit (.string "hello")]
    let direct := evalExprWithDb db row (.func "UPPER" args)
    let stepwise := evalFunc "UPPER" (args.map (evalExprWithDb db row))
    if direct == stepwise then .pass "evalExprWithDb_func (UPPER)"
    else .fail "evalExprWithDb_func (UPPER)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    -- evalExprWithDb_between: evalExprWithDb db row (between e lo hi) matches BETWEEN semantics
    let e := Expr.lit (.int 5)
    let lo := Expr.lit (.int 1)
    let hi := Expr.lit (.int 10)
    let direct := evalExprWithDb db row (.between e lo hi)
    let ev := evalExprWithDb db row e
    let elo := evalExprWithDb db row lo
    let ehi := evalExprWithDb db row hi
    let stepwise := evalBinOp .and (evalBinOp .ge ev elo) (evalBinOp .le ev ehi)
    if direct == stepwise then .pass "evalExprWithDb_between (5 BETWEEN 1 AND 10)"
    else .fail "evalExprWithDb_between (5 BETWEEN 1 AND 10)" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}",

    let e := Expr.lit (.int 15)
    let lo := Expr.lit (.int 1)
    let hi := Expr.lit (.int 10)
    let direct := evalExprWithDb db row (.between e lo hi)
    if direct == some (.bool false) then .pass "evalExprWithDb_between (15 BETWEEN 1 AND 10 = false)"
    else .fail "evalExprWithDb_between (15 BETWEEN 1 AND 10 = false)" s!"Expected some false, got {showOptVal direct}",

    -- evalExprWithDb_inList: evalExprWithDb db row (inList e neg vals) matches IN semantics
    let e := Expr.lit (.int 2)
    let vals := [Expr.lit (.int 1), Expr.lit (.int 2), Expr.lit (.int 3)]
    let direct := evalExprWithDb db row (.inList e false vals)
    let ev := evalExprWithDb db row e
    let stepwise := vals.foldl (fun acc vi =>
      evalBinOp .or acc (evalBinOp .eq ev (evalExprWithDb db row vi))
    ) (some (.bool false))
    if direct == stepwise then .pass "evalExprWithDb_inList (2 IN (1,2,3))"
    else .fail "evalExprWithDb_inList (2 IN (1,2,3))" s!"Direct={showOptVal direct}, Stepwise={showOptVal stepwise}"
  ]

-- ============================================================================
-- Equiv Additional Tests (axioms: join_comm, in_subquery_unnest_to_join,
-- not_in_subquery_unnest_to_antijoin, in_subquery_implies_join_match,
-- join_match_implies_in_subquery)
-- ============================================================================

def equivAdditionalTests : List TestResult :=
  [
    -- join_comm: swapping INNER JOIN sides preserves row set (with column normalization)
    let tU := FromClause.table ⟨"users", some "u"⟩
    let tO := FromClause.table ⟨"orders", some "o"⟩
    let jCond := Expr.binOp .eq (.col ⟨some "u", "id"⟩) (.col ⟨some "o", "user_id"⟩)
    let r1 := evalFrom testDb (.join tU .inner tO (some jCond))
    let r2 := evalFrom testDb (.join tO .inner tU (some jCond))
    let norm1 := (r1.map normalizeRow).mergeSort (fun a b => rowKey a < rowKey b)
    let norm2 := (r2.map normalizeRow).mergeSort (fun a b => rowKey a < rowKey b)
    -- Forward: every row in r1 has match in r2
    let fwd := norm1.all (fun r => norm2.any (fun o => o == r))
    if fwd then .pass "join_comm (forward)"
    else .fail "join_comm (forward)" s!"Row sets differ: {r1.length} vs {r2.length}",

    -- join_comm backward
    let tU := FromClause.table ⟨"users", some "u"⟩
    let tO := FromClause.table ⟨"orders", some "o"⟩
    let jCond := Expr.binOp .eq (.col ⟨some "u", "id"⟩) (.col ⟨some "o", "user_id"⟩)
    let r1 := evalFrom testDb (.join tU .inner tO (some jCond))
    let r2 := evalFrom testDb (.join tO .inner tU (some jCond))
    let norm1 := (r1.map normalizeRow).mergeSort (fun a b => rowKey a < rowKey b)
    let norm2 := (r2.map normalizeRow).mergeSort (fun a b => rowKey a < rowKey b)
    let bwd := norm2.all (fun r => norm1.any (fun o => o == r))
    if bwd then .pass "join_comm (backward)"
    else .fail "join_comm (backward)" s!"Row sets differ: {r2.length} vs {r1.length}",

    -- in_subquery_unnest_to_join: SELECT t.* WHERE t.x IN (SELECT s.y) ≡ SELECT DISTINCT t.* JOIN s ON t.x = s.y
    let inSubqueryForm := SelectStmt.mk false [.star (some "users")]
      (some (.table ⟨"users", some "users"⟩))
      (some (.inSubquery (.col ⟨some "users", "id"⟩) false
        (.simple (SelectStmt.mk false [.exprItem (.col ⟨none, "user_id"⟩) none]
          (some (.table ⟨"orders", some "orders"⟩))
          none [] none [] none none))))
      [] none [] none none
    let joinForm := SelectStmt.mk true [.star (some "users")]
      (some (.join
        (.table ⟨"users", some "users"⟩) .inner
        (.table ⟨"orders", some "orders"⟩)
        (some (.binOp .eq (.col ⟨some "users", "id"⟩) (.col ⟨some "orders", "user_id"⟩)))))
      none [] none [] none none
    let r1 := evalSelect testDb inSubqueryForm
    let r2 := evalSelect testDb joinForm
    if r1 == r2 then .pass "in_subquery_unnest_to_join (users/orders)"
    else .fail "in_subquery_unnest_to_join (users/orders)"
      s!"IN subquery={r1.length} rows, JOIN={r2.length} rows",

    -- not_in_subquery_unnest_to_antijoin: NOT IN ≡ LEFT JOIN + IS NULL
    let notInForm := SelectStmt.mk false [.star (some "users")]
      (some (.table ⟨"users", some "users"⟩))
      (some (.inSubquery (.col ⟨some "users", "id"⟩) true
        (.simple (SelectStmt.mk false [.exprItem (.col ⟨none, "user_id"⟩) none]
          (some (.table ⟨"orders", some "orders"⟩))
          none [] none [] none none))))
      [] none [] none none
    let antijoinForm := SelectStmt.mk false [.star (some "users")]
      (some (.join
        (.table ⟨"users", some "users"⟩) .left
        (.table ⟨"orders", some "orders"⟩)
        (some (.binOp .eq (.col ⟨some "users", "id"⟩) (.col ⟨some "orders", "user_id"⟩)))))
      (some (.unaryOp .isNull (.col ⟨some "orders", "user_id"⟩)))
      [] none [] none none
    let r1 := evalSelect testDb notInForm
    let r2 := evalSelect testDb antijoinForm
    if r1 == r2 then .pass "not_in_subquery_unnest_to_antijoin (users/orders)"
    else .fail "not_in_subquery_unnest_to_antijoin (users/orders)"
      s!"NOT IN={r1.length} rows, Antijoin={r2.length} rows",

    -- in_subquery_implies_join_match: if IN returns true, a matching row exists
    -- Uses qualified column ref and evalFrom for qualified rows (matching theorem signature)
    let testRow : Row := [("x", .int 1)]
    let inExpr := Expr.inSubquery (.lit (.int 1)) false
      (.simple (SelectStmt.mk false [.exprItem (.col ⟨some "orders", "user_id"⟩) none]
        (some (.table ⟨"orders", some "orders"⟩))
        none [] none [] none none))
    let inResult := evalExprWithDb testDb testRow inExpr
    -- Check that a matching row exists using evalFrom (qualified rows)
    let qualifiedRows := evalFrom testDb (.table ⟨"orders", some "orders"⟩)
    let matchExists := qualifiedRows.any fun sRow =>
      evalExprWithDb testDb (testRow ++ sRow)
        (.binOp .eq (.lit (.int 1)) (.col ⟨some "orders", "user_id"⟩)) == some (.bool true)
    if inResult == some (.bool true) && matchExists then
      .pass "in_subquery_implies_join_match (value 1 in orders.user_id)"
    else .fail "in_subquery_implies_join_match (value 1 in orders.user_id)"
      s!"IN={showOptVal inResult}, matchExists={matchExists}",

    -- join_match_implies_in_subquery: if a matching row exists, IN returns true
    let testRow : Row := [("x", .int 2)]
    -- orders table has user_id=2, so there exists a match via evalFrom (qualified rows)
    let qualifiedRows := evalFrom testDb (.table ⟨"orders", some "orders"⟩)
    let matchRow := qualifiedRows.find? fun sRow =>
      evalExprWithDb testDb (testRow ++ sRow)
        (.binOp .eq (.lit (.int 2)) (.col ⟨some "orders", "user_id"⟩)) == some (.bool true)
    let inExpr := Expr.inSubquery (.lit (.int 2)) false
      (.simple (SelectStmt.mk false [.exprItem (.col ⟨some "orders", "user_id"⟩) none]
        (some (.table ⟨"orders", some "orders"⟩))
        none [] none [] none none))
    let inResult := evalExprWithDb testDb testRow inExpr
    match matchRow with
    | some _ =>
      if inResult == some (.bool true) then
        .pass "join_match_implies_in_subquery (value 2 in orders.user_id)"
      else .fail "join_match_implies_in_subquery (value 2 in orders.user_id)"
        s!"Match exists but IN={showOptVal inResult}"
    | none => .fail "join_match_implies_in_subquery (value 2 in orders.user_id)"
        "No matching row found in orders"
  ]

-- ============================================================================
-- Infrastructure Axiom Tests (evalSelect decomposition)
-- ============================================================================

def infrastructureAxiomTests : List TestResult :=
  let selAll := mkSelectWithLimitOffset "users" none none
  let allRows := evalSelect testDb selAll
  let orderAsc := [OrderByItem.mk (col "age") .asc]
  let orderDesc := [OrderByItem.mk (col "age") .desc]
  [
    -- evalSelect_limit_offset: LIMIT n OFFSET m = (all.drop m).take n
    let sel := mkSelectWithLimitOffset "users" (some 2) (some 1)
    let result := evalSelect testDb sel
    let expected := (allRows.drop 1).take 2
    if result == expected then .pass "evalSelect_limit_offset (LIMIT 2 OFFSET 1)"
    else .fail "evalSelect_limit_offset (LIMIT 2 OFFSET 1)" s!"got {result.length} expected {expected.length}",

    -- evalSelect_limit_offset: LIMIT none case
    let sel := mkSelectWithLimitOffset "users" none (some 1)
    let result := evalSelect testDb sel
    let expected := allRows.drop 1
    if result == expected then .pass "evalSelect_limit_offset (no limit, OFFSET 1)"
    else .fail "evalSelect_limit_offset (no limit, OFFSET 1)" s!"got {result.length} expected {expected.length}",

    -- evalSelect_orderBy_length: different ORDER BY, same row count
    let selAsc := mkSelectFull false "users" none orderAsc none none
    let selDesc := mkSelectFull false "users" none orderDesc none none
    testLengthEq "evalSelect_orderBy_length (ASC vs DESC)"
      (evalSelect testDb selAsc).length
      (evalSelect testDb selDesc).length,

    -- evalSelect_orderBy_length: with LIMIT
    let selAscLim := mkSelectFull false "users" none orderAsc (some 2) none
    let selDescLim := mkSelectFull false "users" none orderDesc (some 2) none
    testLengthEq "evalSelect_orderBy_length (ASC vs DESC with LIMIT)"
      (evalSelect testDb selAscLim).length
      (evalSelect testDb selDescLim).length,

    -- evalSelect_where_congr: two equivalent WHERE clauses produce same result
    -- TRUE filter vs no filter should give same result
    let selTrue := SelectStmt.mk false [.star none] (some (.table ⟨"users", none⟩))
      (some (.lit (.bool true))) [] none [] none none
    let selNone := SelectStmt.mk false [.star none] (some (.table ⟨"users", none⟩))
      none [] none [] none none
    testSelectEquiv "evalSelect_where_congr (WHERE TRUE vs no WHERE)"
      selTrue selNone testDb,

    -- evalSelect_filter_all_false: WHERE FALSE with no aggregates = empty result
    let selFalse := SelectStmt.mk false [.star none] (some (.table ⟨"users", none⟩))
      (some (.lit (.bool false))) [] none [] none none
    testLengthEq "evalSelect_filter_all_false (WHERE FALSE = empty)"
      (evalSelect testDb selFalse).length
      0,

    -- evalSelect_filter_all_false: with ORDER BY
    let selFalseOrd := SelectStmt.mk false [.star none] (some (.table ⟨"users", none⟩))
      (some (.lit (.bool false))) [] none orderAsc none none
    testLengthEq "evalSelect_filter_all_false (WHERE FALSE + ORDER BY = empty)"
      (evalSelect testDb selFalseOrd).length
      0,

    -- Regression: aggregate query with WHERE FALSE should NOT produce empty result
    -- SELECT COUNT(*) FROM users WHERE FALSE → should return 1 row (with count 0)
    let selAggFalse := SelectStmt.mk false
      [.exprItem .countStar (some "cnt")]
      (some (.table ⟨"users", none⟩))
      (some (.lit (.bool false))) [] none [] none none
    testLengthEq "evalSelect_agg_where_false_not_empty (aggregate WHERE FALSE = 1 row)"
      (evalSelect testDb selAggFalse).length
      1,

    -- evalQuery_simple: simple query evaluates same as evalSelect
    let selUsers := mkSimpleSelect "users"
    let queryResult := evalQuery testDb (.simple selUsers)
    let selectResult := evalSelect testDb selUsers
    if queryResult == selectResult then .pass "evalQuery_simple (users)"
    else .fail "evalQuery_simple (users)" s!"Results differ: {queryResult.length} vs {selectResult.length} rows",

    -- evalQuery_compound: UNION ALL decomposes to append
    let selUsers := mkSimpleSelect "users"
    let selOrders := mkSimpleSelect "orders"
    let compoundResult := evalQuery testDb (.compound (.simple selUsers) .unionAll (.simple selOrders))
    let expectedResult := evalQuery testDb (.simple selUsers) ++ evalQuery testDb (.simple selOrders)
    if compoundResult == expectedResult then .pass "evalQuery_compound (UNION ALL = append)"
    else .fail "evalQuery_compound (UNION ALL = append)" s!"Results differ: {compoundResult.length} vs {expectedResult.length} rows",

    -- evalQuery_compound: INTERSECT decomposes to filter+contains+eraseDups (#223)
    let selUsers := mkSimpleSelect "users"
    let selOrders := mkSimpleSelect "orders"
    let intersectResult := evalQuery testDb (.compound (.simple selUsers) .intersect (.simple selOrders))
    let usersResult := evalQuery testDb (.simple selUsers)
    let ordersResult := evalQuery testDb (.simple selOrders)
    let expectedIntersect := (usersResult.filter (ordersResult.contains ·)).eraseDups
    if intersectResult == expectedIntersect then .pass "evalQuery_compound (INTERSECT = filter+contains+eraseDups)"
    else .fail "evalQuery_compound (INTERSECT = filter+contains+eraseDups)" s!"Results differ: {intersectResult.length} vs {expectedIntersect.length} rows",

    -- evalQuery_compound: UNION decomposes to append+eraseDups
    let selUsers := mkSimpleSelect "users"
    let selOrders := mkSimpleSelect "orders"
    let unionResult := evalQuery testDb (.compound (.simple selUsers) .union (.simple selOrders))
    let usersResult := evalQuery testDb (.simple selUsers)
    let ordersResult := evalQuery testDb (.simple selOrders)
    let expectedUnion := (usersResult ++ ordersResult).eraseDups
    if unionResult == expectedUnion then .pass "evalQuery_compound (UNION = append+eraseDups)"
    else .fail "evalQuery_compound (UNION = append+eraseDups)" s!"Results differ: {unionResult.length} vs {expectedUnion.length} rows",

    -- evalQuery_compound: EXCEPT decomposes to filter+!contains+eraseDups (#223)
    let selUsers := mkSimpleSelect "users"
    let selOrders := mkSimpleSelect "orders"
    let exceptResult := evalQuery testDb (.compound (.simple selUsers) .exceptOp (.simple selOrders))
    let usersResult := evalQuery testDb (.simple selUsers)
    let ordersResult := evalQuery testDb (.simple selOrders)
    let expectedExcept := (usersResult.filter (!ordersResult.contains ·)).eraseDups
    if exceptResult == expectedExcept then .pass "evalQuery_compound (EXCEPT = filter+!contains+eraseDups)"
    else .fail "evalQuery_compound (EXCEPT = filter+!contains+eraseDups)" s!"Results differ: {exceptResult.length} vs {expectedExcept.length} rows",

    -- evalFrom_cross_join: CROSS JOIN = flatMap/map
    let tU := FromClause.table ⟨"users", none⟩
    let tO := FromClause.table ⟨"orders", none⟩
    let crossResult := evalFrom testDb (.join tU .cross tO none)
    let rightRows := evalFrom testDb tO
    let manualCross := (evalFrom testDb tU).flatMap fun lr =>
      rightRows.map fun rr => lr ++ rr
    if crossResult == manualCross then .pass "evalFrom_cross_join (users × orders)"
    else .fail "evalFrom_cross_join (users × orders)" s!"Results differ: {crossResult.length} vs {manualCross.length} rows",

    -- evalFrom_inner_join: INNER JOIN = flatMap/filterMap
    let tU := FromClause.table ⟨"users", none⟩
    let tO := FromClause.table ⟨"orders", none⟩
    let condTrue := Expr.lit (.bool true)
    let innerResult := evalFrom testDb (.join tU .inner tO (some condTrue))
    let rightRows := evalFrom testDb tO
    let manualInner := (evalFrom testDb tU).flatMap fun lr =>
      rightRows.filterMap fun rr =>
        let combined := lr ++ rr
        match evalExprWithDb testDb combined condTrue with
        | some (.bool true) => some combined
        | _ => none
    if innerResult == manualInner then .pass "evalFrom_inner_join (users INNER orders ON TRUE)"
    else .fail "evalFrom_inner_join (users INNER orders ON TRUE)" s!"Results differ: {innerResult.length} vs {manualInner.length} rows",

    -- evalFrom_left_join: LEFT JOIN decomposes into flatMap with NULL padding
    let tU := FromClause.table ⟨"users", none⟩
    let tO := FromClause.table ⟨"orders", none⟩
    let condFalse := Expr.lit (.bool false)
    let leftResult := evalFrom testDb (.join tU .left tO (some condFalse))
    let rightRows := evalFrom testDb tO
    let manualLeft := (evalFrom testDb tU).flatMap fun lr =>
      let matchingRows := rightRows.filterMap fun rr =>
        let combined := lr ++ rr
        match evalExprWithDb testDb combined condFalse with
        | some (.bool true) => some combined
        | _ => none
      if matchingRows.isEmpty then
        match rightRows.head? with
        | some rightRow => [lr ++ rightRow.map fun (k, _) => (k, .null none)]
        | none => [lr]
      else
        matchingRows
    if leftResult == manualLeft
    then .pass "evalFrom_left_join (LEFT JOIN ON FALSE = NULL padding)"
    else .fail "evalFrom_left_join (LEFT JOIN ON FALSE = NULL padding)"
      s!"Results differ: {leftResult.length} vs {manualLeft.length} rows",

    -- evalFrom_left_join: LEFT JOIN with real predicate (some matches, some NULL-padded)
    let tU := FromClause.table ⟨"users", none⟩
    let tO := FromClause.table ⟨"orders", none⟩
    -- users.id = orders.user_id — user 1 matches 2 orders, user 2 matches 1, user 3 matches 0
    let cond := Expr.binOp .eq (qcol "users" "id") (qcol "orders" "user_id")
    let leftResult := evalFrom testDb (.join tU .left tO (some cond))
    let rightRows := evalFrom testDb tO
    let manualLeft := (evalFrom testDb tU).flatMap fun lr =>
      let matchingRows := rightRows.filterMap fun rr =>
        let combined := lr ++ rr
        match evalExprWithDb testDb combined cond with
        | some (.bool true) => some combined
        | _ => none
      if matchingRows.isEmpty then
        match rightRows.head? with
        | some rightRow => [lr ++ rightRow.map fun (k, _) => (k, .null none)]
        | none => [lr]
      else
        matchingRows
    if leftResult == manualLeft
    then .pass "evalFrom_left_join (LEFT JOIN with matches and NULL padding)"
    else .fail "evalFrom_left_join (LEFT JOIN with matches and NULL padding)"
      s!"Results differ: {leftResult.length} vs {manualLeft.length} rows",

    -- evalFrom_left_join: LEFT JOIN with on_ = none (all rows combine, no NULL padding)
    let tU := FromClause.table ⟨"users", none⟩
    let tO := FromClause.table ⟨"orders", none⟩
    let leftResult := evalFrom testDb (.join tU .left tO none)
    let rightRows := evalFrom testDb tO
    let manualLeft := (evalFrom testDb tU).flatMap fun lr =>
      let matchingRows := rightRows.filterMap fun rr =>
        let combined := lr ++ rr
        some combined
      if matchingRows.isEmpty then
        match rightRows.head? with
        | some rightRow => [lr ++ rightRow.map fun (k, _) => (k, .null none)]
        | none => [lr]
      else
        matchingRows
    if leftResult == manualLeft
    then .pass "evalFrom_left_join (LEFT JOIN with no ON = cross)"
    else .fail "evalFrom_left_join (LEFT JOIN with no ON = cross)"
      s!"Results differ: {leftResult.length} vs {manualLeft.length} rows",

    -- evalFrom_right_join: RIGHT JOIN with matches (exercises `else matchingRows`)
    let tU := FromClause.table ⟨"users", none⟩
    let tO := FromClause.table ⟨"orders", none⟩
    let cond := Expr.binOp .eq (qcol "users" "id") (qcol "orders" "user_id")
    let rightResult := evalFrom testDb (.join tU .right tO (some cond))
    let leftRows := evalFrom testDb tU
    let manualRight := (evalFrom testDb tO).flatMap fun rr =>
      let matchingRows := leftRows.filterMap fun lr =>
        let combined := lr ++ rr
        match evalExprWithDb testDb combined cond with
        | some (.bool true) => some combined
        | _ => none
      if matchingRows.isEmpty then
        match leftRows.head? with
        | some leftRow => [leftRow.map (fun (k, _) => (k, .null none)) ++ rr]
        | none => [rr]
      else
        matchingRows
    if rightResult == manualRight
    then .pass "evalFrom_right_join (RIGHT JOIN with matches)"
    else .fail "evalFrom_right_join (RIGHT JOIN with matches)"
      s!"Results differ: {rightResult.length} vs {manualRight.length} rows",

    -- evalFrom_right_join: RIGHT JOIN with ON FALSE (exercises NULL padding)
    let tU := FromClause.table ⟨"users", none⟩
    let tO := FromClause.table ⟨"orders", none⟩
    let condFalse := Expr.lit (.bool false)
    let rightResult := evalFrom testDb (.join tU .right tO (some condFalse))
    let leftRows := evalFrom testDb tU
    let manualRight := (evalFrom testDb tO).flatMap fun rr =>
      let matchingRows := leftRows.filterMap fun lr =>
        let combined := lr ++ rr
        match evalExprWithDb testDb combined condFalse with
        | some (.bool true) => some combined
        | _ => none
      if matchingRows.isEmpty then
        match leftRows.head? with
        | some leftRow => [leftRow.map (fun (k, _) => (k, .null none)) ++ rr]
        | none => [rr]
      else
        matchingRows
    if rightResult == manualRight
    then .pass "evalFrom_right_join (RIGHT JOIN ON FALSE = NULL padding)"
    else .fail "evalFrom_right_join (RIGHT JOIN ON FALSE = NULL padding)"
      s!"Results differ: {rightResult.length} vs {manualRight.length} rows",

    -- evalFrom_right_join: RIGHT JOIN with on_ = none (exercises none branch)
    let tU := FromClause.table ⟨"users", none⟩
    let tO := FromClause.table ⟨"orders", none⟩
    let rightResult := evalFrom testDb (.join tU .right tO none)
    let leftRows := evalFrom testDb tU
    let manualRight := (evalFrom testDb tO).flatMap fun rr =>
      let matchingRows := leftRows.filterMap fun lr =>
        let combined := lr ++ rr
        some combined
      if matchingRows.isEmpty then
        match leftRows.head? with
        | some leftRow => [leftRow.map (fun (k, _) => (k, .null none)) ++ rr]
        | none => [rr]
      else
        matchingRows
    if rightResult == manualRight
    then .pass "evalFrom_right_join (RIGHT JOIN with no ON = cross)"
    else .fail "evalFrom_right_join (RIGHT JOIN with no ON = cross)"
      s!"Results differ: {rightResult.length} vs {manualRight.length} rows"
  ]

-- ============================================================================
-- All Tests
-- ============================================================================

def allAxiomCoverageTests : List TestResult :=
  arithmeticTests ++
  comparisonTests ++
  caseTests ++
  boolAlgebraTests ++
  inListTests ++
  betweenTests ++
  stringFuncTests ++
  likeTests ++
  setOpTests ++
  limitOffsetTests ++
  paginationTests ++
  orderByTests ++
  joinTests ++
  filterTests ++
  subqueryTests ++
  normalizationDecisionTests ++
  predicatePushdownTests ++
  additionalLogicTests ++
  subqueryUnnestingTests ++
  semanticsUnfoldTests ++
  equivAdditionalTests ++
  infrastructureAxiomTests

def runAxiomCoverageTests : IO (Nat × Nat) :=
  runTests "Axiom Coverage Tests" allAxiomCoverageTests

end AxiomCoverageTest
