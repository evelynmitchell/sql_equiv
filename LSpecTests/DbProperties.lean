/-
  Property tests over random databases (#245).

  `≃ₑ`, `≃ₛ`, `≃ᵩ` and the statement laws quantify over every database, but the other property
  tests sample a handful of hand-written ones (`QueryHelpers.testDb`, the `EdgeCaseDb`
  fixtures, the rewriter sweep's `sweepRealDb`). Here the database is drawn by `genGenDb`:
  random contents of the fixed schema `users` / `orders` / `products` / `t(a)`, with empty and
  one-row tables, duplicate keys, dangling and NULL foreign keys, and typed and untyped NULLs.

  Each group has vacuity guards over a fixed batch of generated databases (`genDbBatch`): the
  data must exercise what the property is about (non-empty results, matches and non-matches,
  NULL keys). And each group has a mutant that must be caught: a wrong variant of the law,
  checked with the same comparison on the same batch.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators
import LSpecTests.QueryHelpers
import LSpecTests.RewriterProperties

open LSpec SlimCheck
open SqlEquiv

namespace DbProperties

open RewriterProperties QueryHelpers

/-- A database property evaluates whole queries per sample, so its sample count is capped. -/
def dbCfg (cfg : Configuration) (cap : Nat) : Configuration :=
  { cfg with numInst := min cfg.numInst cap }

/-- The batch the vacuity guards and mutant checks run over. -/
def batch : List GenDb := genDbBatch 300

/-- How many databases of the batch satisfy `p`. -/
def countIn (p : GenDb → Bool) : Nat := (batch.filter p).length

private def parseSel (s : String) : SelectStmt :=
  match parseSelectStr s with
  | .ok x => x
  | .error e => panic! s!"parseSel: {e}"

-- ============================================================================
-- 1. The certified rewriter, over random databases
-- ============================================================================

/-- Does the certified rewriter keep `e`'s value in every sweep row, over `db`? -/
def rewriteOkOn (db : Database) (e : Expr) : Bool :=
  sweepRows.all fun r => evalExprWithDb db r e == evalExprWithDb db r (certifiedRewrite e).val

/-- Whether `e` has a subquery (its value can depend on the database). -/
private partial def mentionsSubquery : Expr → Bool
  | .exists _ _ | .inSubquery _ _ _ | .subquery _ => true
  | .binOp _ l r => mentionsSubquery l || mentionsSubquery r
  | .unaryOp _ e => mentionsSubquery e
  | .func _ args => args.any mentionsSubquery
  | .inList e _ vs => mentionsSubquery e || vs.any mentionsSubquery
  | .between a b c => mentionsSubquery a || mentionsSubquery b || mentionsSubquery c
  | .case bs e => bs.any (fun (c, r) => mentionsSubquery c || mentionsSubquery r) ||
      (e.map mentionsSubquery).getD false
  | _ => false

/-- The sweep cases whose value depends on the database: the rewriter's `EXISTS` and
    `IN (subquery)` arms. -/
def subquerySweepCases : List Expr := sweepCases.filter mentionsSubquery

/-- A wrong rewrite: `x IN (sq)` → `EXISTS (sq)`, which ignores `x`. -/
def inToExistsMutant (e : Expr) : Expr :=
  match e with
  | .inSubquery _ false sq => .exists false sq
  | _ => (certifiedRewrite e).val

def rewriterTests (cfg : Configuration) : TestSeq :=
  let tNonEmpty := countIn fun g => !(evalSubQueryWithContext g.db [] subqNonEmpty).isEmpty
  let inValues := batch.map fun g =>
    evalExprWithDb g.db [] (.inSubquery (.lit (.int 2)) false subqNonEmpty)
  let mutantCaught := countIn fun g => subquerySweepCases.any fun e =>
    sweepRows.any fun r => evalExprWithDb g.db r e != evalExprWithDb g.db r (inToExistsMutant e)
  test s!"vacuity: t is empty in some databases and not in others ({tNonEmpty} of {batch.length} non-empty)"
    (tNonEmpty ≥ batch.length / 4 && tNonEmpty + batch.length / 10 ≤ batch.length) $
  test "vacuity: `2 IN (SELECT a FROM t)` is TRUE, FALSE and NULL across the batch"
    (inValues.contains (some (.bool true)) && inValues.contains (some (.bool false)) &&
      inValues.any fun v => match v with | some (.null _) => true | _ => false) $
  test s!"vacuity: {subquerySweepCases.length} sweep cases depend on the database"
    (subquerySweepCases.length ≥ 500) $
  test s!"mutant `x IN (sq) → EXISTS (sq)` is caught ({mutantCaught} databases)" (mutantCaught > 0) $
  checkS (cfg := dbCfg cfg 2000) "random db: rewriter in context (ColumnGroundExpr)"
    (∀ g : GenDb, ∀ e : ColumnGroundExpr, (rewriteContexts e.expr).all (rewriteOkOn g.db)) $
  checkS (cfg := dbCfg cfg 100) "random db: rewriter on the sweep cases with subqueries"
    (∀ g : GenDb, subquerySweepCases.all (rewriteOkOn g.db))

-- ============================================================================
-- 2. Subquery laws (StatementAxioms), on random contents of the subquery's table
-- ============================================================================

/-- `SELECT a FROM t` for `k = 0` (NULLs of `t` included), else `SELECT a FROM t WHERE
    a > k - 1`: empty or not depending on the data. -/
def selGt (k : Nat) : SelectStmt :=
  if k == 0 then parseSel "SELECT a FROM t" else parseSel s!"SELECT a FROM t WHERE a > {k - 1}"

/-- `not_not_exists`, `in_empty_subquery_false`, `not_in_empty_subquery_true` at one database,
    threshold and probe value. -/
def subqueryLawsHold (g : GenDb) (k v : Nat) : Bool :=
  let sq : SubQuery := .simple (selGt k)
  let e : Expr := .lit (.int v)
  let ev := evalExprWithDb g.db []
  ev (.exists true sq) == ev (.unaryOp .not (.exists false sq)) &&
  ev (.inSubquery e false sq) ==
    ev (.case [(.unaryOp .not (.exists false sq), .lit (.bool false))] (some (.inSubquery e false sq))) &&
  ev (.inSubquery e true sq) ==
    ev (.case [(.unaryOp .not (.exists false sq), .lit (.bool true))] (some (.inSubquery e true sq)))

/-- A wrong law: `x NOT IN (SELECT a FROM t)` = `NOT EXISTS (SELECT a FROM t WHERE a = x)`,
    which ignores a NULL in `t`. -/
def notInAsNotExistsHolds (g : GenDb) (v : Nat) : Bool :=
  evalExprWithDb g.db [] (.inSubquery (.lit (.int v)) true (.simple (selGt 0))) ==
    evalExprWithDb g.db []
      (.unaryOp .not (.exists false (.simple (parseSel s!"SELECT a FROM t WHERE a = {v}"))))

def subqueryTests (cfg : Configuration) : TestSeq :=
  let empties := countIn fun g => (evalSelect g.db (selGt 3)).isEmpty
  let withNull := countIn fun g => (evalSelect g.db (selGt 0)).any fun r =>
    r.any fun (_, v) => v.isNull
  let mutantCaught := countIn fun g => (List.range 7).any fun v => !notInAsNotExistsHolds g v
  test s!"vacuity: `SELECT a FROM t WHERE a > 2` is empty in some databases and not in others ({empties} empty)"
    (empties ≥ batch.length / 10 && empties + batch.length / 10 ≤ batch.length) $
  test s!"vacuity: `SELECT a FROM t` returns a NULL in {withNull} databases" (withNull ≥ batch.length / 10) $
  test s!"mutant `NOT IN = NOT EXISTS` is caught ({mutantCaught} databases)" (mutantCaught > 0) $
  checkS (cfg := dbCfg cfg 5000) "random db: not_not_exists, in/not_in_empty_subquery laws"
    (∀ g : GenDb, ∀ k v : SmallNat, subqueryLawsHold g k.val v.val)

-- ============================================================================
-- 3. Select-level relations
-- ============================================================================

/-- `SELECT * FROM users WHERE users.age > a AND users.age < b`, in either order. -/
def ageBetween (a b : Int) (swap : Bool) : SelectStmt :=
  let p := Expr.binOp .gt (qcol "users" "age") (.lit (.int a))
  let q := Expr.binOp .lt (qcol "users" "age") (.lit (.int b))
  mkSelectWhere "users" (some (if swap then .binOp .and q p else .binOp .and p q))

/-- `users CROSS JOIN orders WHERE users.id = orders.user_id AND users.age > a`: an inner join
    written as a filtered cross join. With `keepOn := false`, the mutant that drops the join
    condition. -/
def crossJoinWhere (a : Int) (keepOn : Bool) : SelectStmt :=
  let onCond := Expr.binOp .eq (qcol "users" "id") (qcol "orders" "user_id")
  let ageCond := Expr.binOp .gt (qcol "users" "age") (.lit (.int a))
  .mk false [.star none]
    (some (.join (.table ⟨"users", none⟩) .cross (.table ⟨"orders", none⟩) none))
    (some (if keepOn then .binOp .and onCond ageCond else ageCond)) [] none [] none none

def selectLevelHold (g : GenDb) (a : Int) (b n k : Nat) : Bool :=
  let db := g.db
  let distinctRows := evalSelect db (mkDistinctWhere a)
  let plainRows := evalSelect db (mkSelectWhere "users" (some (.binOp .gt (qcol "users" "age") (.lit (.int a)))))
  let ordered := evalSelect db (mkOrderLimitOffset none none)
  -- AND commutes in WHERE
  evalSelect db (ageBetween a (a + b) false) == evalSelect db (ageBetween a (a + b) true) &&
  -- an inner join is a filtered cross join
  evalSelect db (mkJoinQuery .inner a) == evalSelect db (crossJoinWhere a true) &&
  -- DISTINCT: no duplicate rows, nothing lost
  (distinctRows.map Row.valueKey).eraseDups.length == distinctRows.length &&
  plainRows.all (fun r => (distinctRows.map Row.valueKey).contains r.valueKey) &&
  -- UNION ALL adds the lengths
  (evalQuery db (mkUnionAll a (a + b))).length ==
    (evalSelect db (mkWhereAge .gt a)).length + (evalSelect db (mkWhereAge .gt (a + b))).length &&
  -- ORDER BY permutes; LIMIT/OFFSET cut the ordered rows
  (ordered.map Row.valueKey).isPerm ((g.users.map fun r => r.map fun (c, v) => (s!"users.{c}", v)).map Row.valueKey) &&
  evalSelect db (mkOrderLimitOffset (some n) (some k)) == (ordered.drop k).take n &&
  -- a LEFT JOIN keeps every left row
  (evalSelect db (mkJoinQuery .left (-1000))).length ≥
    (g.users.filter fun r => match r.lookup "age" with | some (.int x) => x > -1000 | _ => false).length

def selectTests (cfg : Configuration) : TestSeq :=
  let joinNonEmpty := countIn fun g => !(evalSelect g.db (mkJoinQuery .inner 0)).isEmpty
  let filterPartial := countIn fun g =>
    let r := (evalSelect g.db (mkWhereAge .gt 28)).length
    0 < r && r < g.users.length
  let distinctShrinks := countIn fun g =>
    (evalSelect g.db (mkDistinctWhere 0)).length < (evalSelect g.db (mkWhereAge .gt 0)).length
  let mutantCaught := countIn fun g =>
    evalSelect g.db (mkJoinQuery .inner 0) != evalSelect g.db (crossJoinWhere 0 false)
  test s!"vacuity: the inner join matches rows in {joinNonEmpty} databases" (joinNonEmpty ≥ batch.length / 4) $
  test s!"vacuity: `age > 28` keeps some but not all users in {filterPartial} databases"
    (filterPartial ≥ batch.length / 10) $
  test s!"vacuity: DISTINCT removes duplicates in {distinctShrinks} databases" (distinctShrinks > 0) $
  test s!"mutant `inner join = cross join without ON` is caught ({mutantCaught} databases)"
    (mutantCaught > 0) $
  checkS (cfg := dbCfg cfg 5000) "random db: WHERE AND, joins, DISTINCT, UNION ALL, ORDER BY / LIMIT"
    (∀ g : GenDb, ∀ a : AgeInt, ∀ b n k : SmallNat, selectLevelHold g a.val b.val n.val k.val)

-- ============================================================================
-- 4. Unnesting theorems (StatementAxioms), with t = users(id), s = orders(user_id)
-- ============================================================================

private def subqUserIds : SubQuery :=
  .simple (.mk false [.exprItem (.col ⟨some "orders", "user_id"⟩) none]
    (some (.table ⟨"orders", some "orders"⟩)) none [] none [] none none)

/-- `SELECT DISTINCT users.* FROM users WHERE users.id IN (SELECT orders.user_id FROM orders)`,
    the left side of `in_subquery_unnest_to_join`. -/
def inForm : SelectStmt :=
  .mk true [.star (some "users")] (some (.table ⟨"users", some "users"⟩))
    (some (.inSubquery (.col ⟨some "users", "id"⟩) false subqUserIds)) [] none [] none none

/-- Its right side, `SELECT DISTINCT users.* FROM users JOIN orders ON users.id =
    orders.user_id`; with `distinct := false`, the mutant that drops DISTINCT. -/
def joinForm (distinct : Bool := true) : SelectStmt :=
  .mk distinct [.star (some "users")]
    (some (.join (.table ⟨"users", some "users"⟩) .inner (.table ⟨"orders", some "orders"⟩)
      (some (.binOp .eq (.col ⟨some "users", "id"⟩) (.col ⟨some "orders", "user_id"⟩)))))
    none [] none [] none none

/-- `SELECT users.* FROM users WHERE users.id NOT IN (SELECT orders.user_id FROM orders)`. -/
def notInForm : SelectStmt :=
  .mk false [.star (some "users")] (some (.table ⟨"users", some "users"⟩))
    (some (.inSubquery (.col ⟨some "users", "id"⟩) true subqUserIds)) [] none [] none none

/-- `SELECT users.* FROM users LEFT JOIN orders ON users.id = orders.user_id
    WHERE orders.user_id IS NULL`. -/
def antijoinForm : SelectStmt :=
  .mk false [.star (some "users")]
    (some (.join (.table ⟨"users", some "users"⟩) .left (.table ⟨"orders", some "orders"⟩)
      (some (.binOp .eq (.col ⟨some "users", "id"⟩) (.col ⟨some "orders", "user_id"⟩)))))
    (some (.unaryOp .isNull (.col ⟨some "orders", "user_id"⟩))) [] none [] none none

/-- The data preconditions of `not_in_subquery_unnest_to_antijoin`: no NULL `users.id`, no NULL
    `orders.user_id`. -/
def antijoinPre (g : GenDb) : Bool :=
  g.users.all (fun r => match r.lookup "id" with | some v => !v.isNull | none => false) &&
  g.orders.all (fun r => match r.lookup "user_id" with | some v => !v.isNull | none => false)

def inJoinAgree (g : GenDb) (distinct : Bool := true) : Bool :=
  ((evalSelect g.db inForm).map Row.valueKey).isPerm
    ((evalSelect g.db (joinForm distinct)).map Row.valueKey)

def unnestTests (cfg : Configuration) : TestSeq :=
  let inNonEmpty := countIn fun g => !(evalSelect g.db inForm).isEmpty
  let preHolds := countIn fun g => antijoinPre g && !(evalSelect g.db notInForm).isEmpty
  let preFails := countIn fun g => !antijoinPre g
  let noDistinctCaught := countIn fun g => !inJoinAgree g false
  let noPreCaught := countIn fun g => evalSelect g.db notInForm != evalSelect g.db antijoinForm
  test s!"vacuity: the IN form has rows in {inNonEmpty} databases" (inNonEmpty ≥ batch.length / 4) $
  test s!"vacuity: NOT IN preconditions hold with rows in {preHolds} databases, fail in {preFails}"
    (preHolds ≥ batch.length / 10 && preFails ≥ batch.length / 10) $
  test s!"mutant `join form without DISTINCT` is caught ({noDistinctCaught} databases)"
    (noDistinctCaught > 0) $
  test s!"mutant `antijoin without the NOT NULL preconditions` is caught ({noPreCaught} databases)"
    (noPreCaught > 0) $
  checkS (cfg := dbCfg cfg 5000) "random db: in_subquery_unnest_to_join (bag of rows)"
    (∀ g : GenDb, inJoinAgree g) $
  checkS (cfg := dbCfg cfg 5000) "random db: not_in_subquery_unnest_to_antijoin (under its preconditions)"
    (∀ g : GenDb, !antijoinPre g || evalSelect g.db notInForm == evalSelect g.db antijoinForm)

def allTests (cfg : Configuration) : TestSeq :=
  group "Rewriter" (rewriterTests cfg) $
  group "Subquery laws" (subqueryTests cfg) $
  group "Select-level relations" (selectTests cfg) $
  group "Unnesting" (unnestTests cfg)

end DbProperties
