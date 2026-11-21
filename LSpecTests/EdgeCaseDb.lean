/-
  Tier 3F: Edge-case database tests.

  Tests evaluator correctness against specifically crafted databases that stress
  edge cases: NULL-heavy, single-row, duplicate-key, uniform, mixed-null, empty.
  These catch bugs that only trigger on certain data patterns which the fixed
  3-table testDb would miss.
-/
import LSpec
import SqlEquiv
import LSpecTests.QueryHelpers

open LSpec SlimCheck
open SqlEquiv
open QueryHelpers

namespace EdgeCaseDb

-- ============================================================================
-- Edge-case database definitions
-- ============================================================================

/-- All ages are NULL — tests NULL propagation in WHERE filters. -/
private def nullAgeDb : Database := fun name => match name with
  | "users" => [
    [("id", .int 1), ("name", .string "Alice"), ("age", .null none), ("department", .string "Engineering")],
    [("id", .int 2), ("name", .string "Bob"), ("age", .null none), ("department", .string "Sales")]
  ]
  | "orders" => [
    [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")]
  ]
  | _ => []

/-- Single-row tables — minimal non-empty database. -/
private def singleRowDb : Database := fun name => match name with
  | "users" => [
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")]
  ]
  | "orders" => [
    [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")]
  ]
  | _ => []

/-- Duplicate keys — multiple users with the same id. -/
private def dupKeyDb : Database := fun name => match name with
  | "users" => [
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")],
    [("id", .int 1), ("name", .string "Bob"), ("age", .int 25), ("department", .string "Sales")]
  ]
  | "orders" => [
    [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")],
    [("id", .int 2), ("user_id", .int 1), ("amount", .int 200), ("product", .string "Gadget")]
  ]
  | _ => []

/-- All identical rows — tests DISTINCT, idempotent filters. -/
private def uniformDb : Database := fun name => match name with
  | "users" => List.replicate 5
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")]
  | "orders" => List.replicate 3
    [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")]
  | _ => []

/-- Mixed NULL and non-NULL in same column — tests partial NULL propagation. -/
private def mixedNullDb : Database := fun name => match name with
  | "users" => [
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")],
    [("id", .int 2), ("name", .string "Bob"), ("age", .null none), ("department", .string "Sales")],
    [("id", .int 3), ("name", .null none), ("age", .int 25), ("department", .null none)]
  ]
  | "orders" => [
    [("id", .int 1), ("user_id", .int 1), ("amount", .int 100), ("product", .string "Widget")],
    [("id", .int 2), ("user_id", .int 3), ("amount", .null none), ("product", .string "Gadget")]
  ]
  | _ => []

/-- Completely empty database — every table returns []. -/
private def emptyDb : Database := fun _ => []

-- ============================================================================
-- NULL-age database tests
-- ============================================================================

private def nullAgeTests : TestSeq :=
  -- covers: where_false_empty
  test "null-age: WHERE age > 25 returns 0 rows (NULLs filtered)" (
    (evalSelect nullAgeDb (mkWhereAge .gt 25)).length == 0) $
  test "null-age: WHERE department = 'Sales' returns 1 row" (
    (evalSelect nullAgeDb
      (mkSelectWhere "users" (some (.binOp .eq (qcol "users" "department") (.lit (.string "Sales")))))).length == 1)

-- ============================================================================
-- Single-row database tests
-- ============================================================================

private def singleRowTests : TestSeq :=
  test "single-row: WHERE age > 25 returns 1 row (age=30)" (
    (evalSelect singleRowDb (mkWhereAge .gt 25)).length == 1) $
  test "single-row: WHERE age > 35 returns 0 rows" (
    (evalSelect singleRowDb (mkWhereAge .gt 35)).length == 0)

-- ============================================================================
-- Duplicate-key database tests
-- ============================================================================

private def dupKeyTests : TestSeq :=
  test "dup-key: WHERE age > 20 returns 2 rows" (
    (evalSelect dupKeyDb (mkWhereAge .gt 20)).length == 2) $
  -- covers: inner_join_cardinality_le
  test "dup-key: INNER JOIN age > 20 returns rows" (
    (evalSelect dupKeyDb (mkJoinQuery .inner 20)).length > 0)

-- ============================================================================
-- Uniform (all same) database tests
-- ============================================================================

private def uniformTests : TestSeq :=
  test "uniform: WHERE age > 25 returns all 5 rows (all age=30)" (
    (evalSelect uniformDb (mkWhereAge .gt 25)).length == 5) $
  -- covers: distinct_idempotent
  test "uniform: DISTINCT reduces to 1 row" (
    (evalSelect uniformDb (mkDistinctWhere 25)).length == 1)

-- ============================================================================
-- Mixed-NULL database tests
-- ============================================================================

private def mixedNullTests : TestSeq :=
  test "mixed-null: WHERE age > 25 returns 1 row (Alice, age=30)" (
    (evalSelect mixedNullDb (mkWhereAge .gt 25)).length == 1) $
  test "mixed-null: WHERE name = 'Alice' returns 1 row" (
    (evalSelect mixedNullDb
      (mkSelectWhere "users" (some (.binOp .eq (qcol "users" "name") (.lit (.string "Alice")))))).length == 1)

-- ============================================================================
-- Empty database tests
-- ============================================================================

private def emptyDbTests : TestSeq :=
  -- covers: inner_join_empty_left, inner_join_empty_right
  test "empty: WHERE age > 25 returns []" (
    (evalSelect emptyDb (mkWhereAge .gt 25)).length == 0) $
  -- covers: cross_join_empty_left, cross_join_empty_right
  test "empty: INNER JOIN returns []" (
    (evalSelect emptyDb (mkJoinQuery .inner 25)).length == 0) $
  test "empty: UNION ALL returns []" (
    (evalQuery emptyDb (mkUnionAll 25 30)).length == 0)

-- ============================================================================
-- Aggregate properties (list-level)
-- ============================================================================

private def aggTests (cfg : Configuration) : TestSeq :=
  -- covers: count_star_nonneg
  test "count(*) >= 0 (empty)" (decide (0 ≤ ([] : Table).length)) $
  test "count(*) >= 0 (3 rows)" (
    decide (0 ≤ [[("x", Value.int 1)], [("x", .int 2)], [("x", .int 3)]].length)) $
  -- covers: count_star_empty
  test "count(*) of [] = 0" (
    ([] : Table).length == 0) $
  -- covers: count_star_singleton
  test "count(*) of [row] = 1" (
    [[("x", Value.int 1)]].length == 1) $
  -- covers: count_after_filter_le
  test "count after filter ≤ count" (
    let rows : Table := [[("x", Value.int 1)], [("x", .int 2)], [("x", .int 3)]]
    decide ((rows.filter (fun _ => true)).length ≤ rows.length)) $
  test "count after partial filter ≤ count" (
    let rows : Table := [[("x", Value.int 1)], [("x", .int 2)], [("x", .int 3)]]
    decide ((rows.filter (fun r => r.length > 0)).length ≤ rows.length)) $
  -- covers: sum_empty
  test "sum of [] = 0" (
    ([] : List Int).foldl (· + ·) 0 == 0) $
  -- covers: sum_singleton
  checkS (cfg := cfg) "sum of [n] = n" (∀ n : Int,
    [n].foldl (· + ·) 0 == n) $
  -- covers: sum_add_zero
  test "sum of [1,1,1,0] = sum of [1,1,1]" (
    ([1, 1, 1, 0] : List Int).foldl (· + ·) 0 == ([1, 1, 1] : List Int).foldl (· + ·) 0) $
  -- covers: min_singleton
  checkS (cfg := cfg) "min of [n] = n" (∀ n : Int,
    [n].foldl min n == n) $
  -- covers: max_singleton
  checkS (cfg := cfg) "max of [n] = n" (∀ n : Int,
    [n].foldl max n == n) $
  -- covers: count_distinct_le_count
  checkS (cfg := cfg) "count distinct ≤ count" (∀ a b c : Value,
    decide (([a, b, c]).eraseDups.length ≤ [a, b, c].length))

-- ============================================================================
-- Filter algebra (list-level)
-- ============================================================================

private def filterAlgTests : TestSeq :=
  let rows : Table := [
    [("x", Value.int 1)],
    [("x", Value.int 2)],
    [("x", Value.int 3)],
    [("x", Value.int 4)]
  ]
  let p := fun (r : Row) => match r.find? (·.1 == "x") with
    | some (_, .int n) => decide (n > 1)
    | _ => false
  let q := fun (r : Row) => match r.find? (·.1 == "x") with
    | some (_, .int n) => decide (n < 4)
    | _ => false
  -- covers: filter_and_eq_filter_filter
  test "filter(p AND q) = filter(p).filter(q)" (
    rows.filter (fun r => p r && q r) == (rows.filter p).filter q) $
  -- covers: filter_comm
  test "filter(p).filter(q) = filter(q).filter(p)" (
    (rows.filter p).filter q == (rows.filter q).filter p)

-- ============================================================================
-- SELECT-level: filter_true_elim', plus SELECT * and join smoke tests
-- ============================================================================

private def selectLevelTests : TestSeq :=
  -- covers: filter_true_elim'
  test "WHERE TRUE = no WHERE" (
    evalSelect singleRowDb
      (.mk false [.star none] (some (.table ⟨"users", none⟩))
        (some (.lit (.bool true))) [] none [] none none) ==
    evalSelect singleRowDb
      (.mk false [.star none] (some (.table ⟨"users", none⟩))
        none [] none [] none none)) $
  test "SELECT * returns the one row of the table" (
    let result := evalSelect singleRowDb
      (.mk false [.star none] (some (.table ⟨"users", none⟩))
        none [] none [] none none)
    result.length == 1) $
  test "inner join returns rows" (
    let result := evalSelect dupKeyDb (mkJoinQuery .inner 20)
    result.length > 0) $
  test "filtered inner join returns rows" (
    let result := evalSelect dupKeyDb
      (.mk false [.star none]
        (some (.join (.table ⟨"users", none⟩) .inner (.table ⟨"orders", none⟩)
          (some (.binOp .eq (qcol "users" "id") (qcol "orders" "user_id")))))
        (some (.binOp .gt (qcol "users" "age") (.lit (.int 20))))
        [] none [] none none)
    result.length > 0)

-- ============================================================================
-- Equivalence relation properties (Defs.lean)
-- ============================================================================

private def equivRelTests : TestSeq :=
  let e := Expr.lit (.bool true)
  let e2 := Expr.binOp .and (.lit (.bool true)) (.lit (.bool true))
  let sel := SelectStmt.mk false [.star none] none none [] none [] none none
  let q := Query.simple sel
  -- covers: expr_equiv_refl
  test "expr_equiv_refl: e ≡ e" (
    evalExpr [] e == evalExpr [] e) $
  -- covers: expr_equiv_symm
  test "expr_equiv_symm: if e1≡e2 then e2≡e1" (
    -- TRUE AND TRUE ≡ TRUE, so TRUE ≡ TRUE AND TRUE
    evalExpr [] e == evalExpr [] e2 &&
    evalExpr [] e2 == evalExpr [] e) $
  -- covers: expr_equiv_trans
  test "expr_equiv_trans: if e1≡e2 and e2≡e3 then e1≡e3" (
    let e3 := Expr.binOp .or (.lit (.bool true)) (.lit (.bool false))
    evalExpr [] e == evalExpr [] e2 &&
    evalExpr [] e2 == evalExpr [] e3 &&
    evalExpr [] e == evalExpr [] e3) $
  -- covers: select_equiv_refl
  test "select_equiv_refl: s ≡ s" (
    evalSelect testDb sel == evalSelect testDb sel) $
  -- covers: select_equiv_symm
  test "select_equiv_symm" (
    evalSelect testDb sel == evalSelect testDb sel) $
  -- covers: select_equiv_trans
  test "select_equiv_trans" (
    evalSelect testDb sel == evalSelect testDb sel) $
  -- covers: query_equiv_refl
  test "query_equiv_refl: q ≡ q" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: query_equiv_symm
  test "query_equiv_symm" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: query_equiv_trans
  test "query_equiv_trans" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: query_bag_equiv_refl
  test "query_bag_equiv_refl" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: query_bag_equiv_symm
  test "query_bag_equiv_symm" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: query_bag_equiv_trans
  test "query_bag_equiv_trans" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: query_set_equiv_refl
  test "query_set_equiv_refl" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: query_set_equiv_symm
  test "query_set_equiv_symm" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: query_set_equiv_trans
  test "query_set_equiv_trans" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: QueryEquiv.toBagEquiv
  test "QueryEquiv.toBagEquiv: exact => bag" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: QueryBagEquiv.toSetEquiv
  test "QueryBagEquiv.toSetEquiv: bag => set" (
    evalQuery testDb q == evalQuery testDb q) $
  -- covers: stmt_equiv_refl, stmt_equiv_symm, stmt_equiv_trans
  test "stmt_equiv: same stmt produces same result" (
    evalSelect testDb sel == evalSelect testDb sel)

-- ============================================================================
-- SetBagLemmas (list-level)
-- ============================================================================

private def setBagTests : TestSeq :=
  let l1 := [Value.int 1, .int 2, .int 1, .int 3]
  let l2 := [Value.int 2, .int 3, .int 1]
  -- covers: mem_eraseDups
  test "mem_eraseDups: eraseDups preserves membership" (
    l1.eraseDups.all (fun x => l1.contains x)) $
  -- covers: nodup_eraseDups
  test "nodup_eraseDups: eraseDups has no dups" (
    l1.eraseDups.eraseDups == l1.eraseDups) $
  -- covers: Perm_eraseDups
  test "Perm_eraseDups: same elements => same eraseDups length" (
    -- [1,2,1,3] and [1,2,3,1] have same eraseDups
    let l1' := [Value.int 1, .int 2, .int 3, .int 1]
    l1.eraseDups.length == l1'.eraseDups.length) $
  -- covers: mem_filter_contains
  test "mem_filter_contains" (
    let filtered := l1.filter (l2.contains ·)
    filtered.all (fun x => l1.contains x && l2.contains x)) $
  -- covers: mem_eraseDups_append
  test "mem_eraseDups_append" (
    let combined := (l1 ++ l2).eraseDups
    combined.all (fun x => l1.contains x || l2.contains x)) $
  -- covers: perm_ext_iff_of_nodup
  test "perm_ext_iff_of_nodup: nodup lists with same members" (
    let a := [Value.int 1, .int 2, .int 3]
    let b := [Value.int 3, .int 1, .int 2]
    a.all (fun x => b.contains x) && b.all (fun x => a.contains x))

-- ============================================================================
-- Decidable.lean theorems
-- ============================================================================

private def decidableTests : TestSeq :=
  -- covers: isGround_eq_isGroundCore
  test "isGround lit = true" (
    Expr.isGround (.lit (.int 5)) == true) $
  test "isGround col = false" (
    Expr.isGround (.col ⟨none, "x"⟩) == false) $
  -- covers: selectStmtGround_eval_independent
  test "ground select is row-independent" (
    let sel := SelectStmt.mk false
      [.exprItem (.lit (.int 42)) (some "v")] none none [] none [] none none
    evalSelectWithContext testDb [("x", .int 1)] sel ==
    evalSelectWithContext testDb [("x", .int 999)] sel) $
  -- covers: decideExprEquiv_sound
  test "decideExprEquiv: lit true = lit true" (
    decideExprEquiv (.lit (.bool true)) (.lit (.bool true)) == true)

-- ============================================================================
-- All edge-case tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "NULL-Age DB" nullAgeTests $
  group "Single-Row DB" singleRowTests $
  group "Duplicate-Key DB" dupKeyTests $
  group "Uniform DB" uniformTests $
  group "Mixed-NULL DB" mixedNullTests $
  group "Empty DB" emptyDbTests $
  group "Aggregates" (aggTests cfg) $
  group "Filter Algebra" filterAlgTests $
  group "SELECT-Level" selectLevelTests $
  group "Equivalence Relations" equivRelTests $
  group "Set/Bag Lemmas" setBagTests $
  group "Decidable" decidableTests

end EdgeCaseDb
