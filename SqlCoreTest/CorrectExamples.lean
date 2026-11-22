/-
  Elaborator correctness (#309): the theorem `SqlBridge.Correct.elabStmt_correct` is not vacuous on
  the bridge test schema. Its hypotheses about names hold (`WellNamed`), and parsed queries of the
  corpus are in the fragment and elaborate.
-/
import SqlBridge.Correct
import SqlBridge.CorrectOrder
import SqlBridge.CorrectJoin
import SqlBridge.CorrectAgg
import SqlBridge.CorrectGroup
import SqlBridge.CorrectGroupOrder
import SqlBridge.CorrectGrouped
import SqlBridge.CorrectDistinct
import SqlBridge.CorrectSetOp
import SqlBridge.CorrectSub
import SqlBridge.CorrectDerived
import SqlBridge.Coverage
import SqlBridge.Spider
import SqlCoreTest.BridgeDiffTest

namespace SqlCoreTest.CorrectExamples
open SqlBridge SqlBridge.Correct SqlCoreTest.BridgeDiff
open SqlBridge.CorrectOrder (itemsNamed outName)
open SqlBridge.CorrectJoin (fromFragment joinStmt itemsStar)
open SqlBridge.CorrectAgg (aggItems aggStmt itemExpr)
open SqlBridge.CorrectGroup (groupItems groupStmt havingFragment colRefs)
open SqlBridge.CorrectGrouped (groupedItems groupedStmt isMinMax itemAggFragment)
open SqlBridge.CorrectAgg (aggFragment)

/-- The test schema's column names have no dots and are distinct ignoring case. -/
example : WellNamed named :=
  ⟨fun T => by cases T <;> decide, fun T => by cases T <;> decide +kernel⟩

/-- The test schema does not fold names; `fold = id` keeps names equal ignoring case. -/
example : ∀ s, (named.fold s).toLower = s.toLower := fun _ => rfl

/-- The parsed statement is `SELECT e₁, …, eₖ FROM t [AS a] [WHERE p]` with fragment expressions,
    and it elaborates: `elabStmt_correct` applies to it. -/
def inFragment (sql : String) : Bool :=
  match SqlEquiv.parse sql with
  | .ok stmt@(.query (.simple (.mk false items (some (.table ⟨name, al⟩)) wh [] none [] none none))) =>
    itemsFragment items && wh.all isFragment && stmt == fragmentStmt items name al wh &&
      (elabStmt named stmt).toBool
  | _ => false

#guard inFragment "SELECT name, age FROM users"
#guard inFragment "SELECT name FROM users WHERE age > 25"
#guard inFragment "SELECT name FROM users WHERE age > 25 AND department = 'Engineering'"
#guard inFragment "SELECT name FROM users WHERE NOT (age < 30) OR department = 'Sales'"
#guard inFragment "SELECT u.name FROM users u WHERE u.age = 30"
#guard inFragment "SELECT name FROM items WHERE price > 2"
#guard inFragment "SELECT Name FROM singer WHERE Age > 20"
#guard inFragment "SELECT name, age >= 30, NULL FROM users WHERE TRUE"

-- Outside #309's single-table shape: arithmetic, `*`, `DISTINCT`, joins (joins are covered by
-- `elabStmt_correct_join` since #352 step 2; see `stmtShape` below).
#guard !inFragment "SELECT age + 1 FROM users"
#guard !inFragment "SELECT * FROM users"
#guard !inFragment "SELECT DISTINCT name FROM users"
#guard !inFragment "SELECT u.name FROM users u JOIN orders o ON u.id = o.user_id"

/-- The shape of `elabStmt_correct_join` (roadmap steps 1 and 2, #352): fragment items or `*`
    (#407; `itemsStar`), `FROM` (tables under inner and cross joins), `WHERE`; `ORDER BY` keys
    that are column references; named items (so no `*`) when there is an `ORDER BY`. -/
def stmtShape : SqlEquiv.Stmt → Bool
  | stmt@(.query (.simple (.mk false items (some f) wh [] none orderBy lim off))) =>
    itemsStar items && fromFragment f && wh.all isFragment &&
      orderBy.all (fun o => match o.expr with | .col _ => true | _ => false) &&
      (orderBy.isEmpty || itemsNamed items) && stmt == joinStmt items f wh orderBy lim off
  | _ => false

/-- The shape of `elabStmt_correct_agg` (roadmap step 3a): aggregates only, no `GROUP BY`. -/
def aggShape : SqlEquiv.Stmt → Bool
  | stmt@(.query (.simple (.mk false items (some f) wh [] none [] none none))) =>
    aggItems items && !items.isEmpty && fromFragment f && wh.all isFragment &&
      stmt == aggStmt items f wh
  | _ => false

/-- `BareOk` (sqlite assumed): every item column is a key; or no `MIN`/`MAX` anywhere; or exactly one
    in the items and `HAVING`, not DISTINCT, in a mode that picks a row, and no other in `ORDER BY`. -/
def bareOkB (items : List SqlEquiv.SelectItem) (groupBy : List SqlEquiv.Expr)
    (having : Option SqlEquiv.Expr) (orderBy : List SqlEquiv.OrderByItem) : Bool :=
  (colRefs items).all (fun c => groupBy.contains (.col c)) ||
    (items.all (fun it => (SqlEquiv.minMaxCalls (itemExpr it)).isEmpty) &&
      having.all (fun h => (SqlEquiv.minMaxCalls h).isEmpty) &&
      orderBy.all (fun o => (SqlEquiv.minMaxCalls o.expr).isEmpty)) ||
    (match SqlEquiv.selectMinMaxCalls items having with
     | [(w, m, some arg, false)] =>
       m.bareRow && ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
         orderBy.map SqlEquiv.OrderByItem.expr).eraseDups.filter isMinMax ==
           [.agg (if w then .max m else .min m) (some arg) false]
     | _ => false)

/-- `OrderKeyOk`'s column case: a `GROUP BY` column that every item named like it (in either
    evaluator, ignoring case) is. -/
def keyColB (items : List SqlEquiv.SelectItem) (groupBy : List SqlEquiv.Expr) : SqlEquiv.Expr → Bool
  | .col c => groupBy.contains (.col c) && items.all fun it =>
      !((outName it).toLower == c.column.toLower ||
        (SqlBridge.CorrectGrouped.itemColName it).toLower == c.column.toLower) ||
        itemExpr it == .col c
  | _ => false

/-- The shape of `elabStmt_correct_grouped` (roadmap steps 3b-1 to 3b-6, 3c): column keys, items
    aggregates or columns, an optional `HAVING` in `havingFragment`, `ORDER BY` aggregates, an
    optional `LIMIT`/`OFFSET`; with sort keys, no output name dotted or starting with
    `__group_orderkey_` (ignoring case); with a bare column (an item column not grouped), no
    `MIN`/`MAX` anywhere, or exactly one, not DISTINCT, in a mode that picks a row (`BareOk`). -/
def groupedShape : SqlEquiv.Stmt → Bool
  | stmt@(.query (.simple (.mk false items (some f) wh groupBy having orderBy lim off))) =>
    groupedItems items && !groupBy.isEmpty &&
      groupBy.all (fun | .col _ => true | _ => false) && fromFragment f && wh.all isFragment &&
      having.all (havingFragment groupBy) &&
      orderBy.all (fun o => aggFragment o.expr || keyColB items groupBy o.expr) &&
      (orderBy.isEmpty || items.all (fun it => decide ('.' ∉ (outName it).toList) &&
        !"__group_orderkey_".toList.isPrefixOf (outName it).toLower.toList)) &&
      bareOkB items groupBy having orderBy &&
      stmt == groupedStmt items f wh groupBy having orderBy lim off
  | _ => false

/-- The shape of `elabStmt_correct_aggBare` (roadmap steps 3b-6, 3c): no `GROUP BY`, items aggregates or
    columns, at least one aggregate, bare columns as `BareOk` allows, nothing after `WHERE`. -/
def aggBareShape : SqlEquiv.Stmt → Bool
  | stmt@(.query (.simple (.mk false items (some f) wh [] none [] none none))) =>
    groupedItems items && items.any (fun it => itemAggFragment (itemExpr it)) && fromFragment f &&
      wh.all isFragment && bareOkB items [] none [] &&
      stmt == groupedStmt items f wh [] none [] none none
  | _ => false

/-- The shape of `elabStmt_correct_distinct` (roadmap step 5): `SELECT DISTINCT` of fragment
    items over a `FROM` tree, an optional `WHERE`, nothing after it. -/
def distinctShape : SqlEquiv.Stmt → Bool
  | stmt@(.query (.simple (.mk true items (some f) wh [] none [] none none))) =>
    itemsFragment items && fromFragment f && wh.all isFragment &&
      stmt == SqlBridge.CorrectDistinct.distinctStmt items f wh
  | _ => false

/-- `SqlBridge.CorrectSetOp.Leaf`: a branch of a set operation is a statement of
    `elabStmt_correct_join`, `_distinct`, `_agg` or `_grouped` without `ORDER BY`, `LIMIT` or
    `OFFSET`, and in the grouped case without an `AVG` item or an `AVG` comparison in
    `HAVING`. -/
def leafShape : SqlEquiv.Query → Bool
  | q@(.simple (.mk _ items _ _ _ _ [] none none)) =>
    stmtShape (.query q) || distinctShape (.query q) || aggShape (.query q) ||
      (groupedShape (.query q) &&
        (items.all fun it => !SqlBridge.CorrectAvg.avgFragment (itemExpr it)) &&
        match q with
        | .simple (.mk _ _ _ _ _ having _ _ _) => having.all fun h => !SqlBridge.CorrectGroup.hasCmpAvg h
        | _ => false)
  | _ => false

/-- `SqlBridge.CorrectSetOp.SetOpTree Leaf`, with at least one set operation. -/
partial def setOpTreeShape : SqlEquiv.Query → Bool
  | .compound l _ r => subTree l && subTree r
  | _ => false
where
  subTree : SqlEquiv.Query → Bool
    | .compound l _ r => subTree l && subTree r
    | q => leafShape q

/-- The shape of `elabStmt_correct_setOp`: `UNION [ALL]`, `INTERSECT` and `EXCEPT`, nested, over
    such branches; no `ORDER BY`/`LIMIT` over the whole. -/
def setOpShape : SqlEquiv.Stmt → Bool
  | .query q => setOpTreeShape q
  | _ => false

/-- `SqlBridge.CorrectSub.BodyOk`: a statement of `elabStmt_correct_join` (with `ORDER BY`
    columns and `LIMIT` / `OFFSET`, #411), of `elabStmt_correct_agg` (without them), or a
    grouped one (#409: item columns all keys, no `AVG` item or `AVG` comparison in `HAVING`;
    `ORDER BY` and `LIMIT` as the grouped theorem takes them, #411). -/
def bodyOkB : SqlEquiv.SelectStmt → Bool
  | .mk false items (some f) wh [] none [] none none =>
    (itemsFragment items || (aggItems items && !items.isEmpty)) && fromFragment f &&
      wh.all isFragment
  | .mk false items (some f) wh [] none orderBy _ _ =>
    -- #411: a plain body with `ORDER BY` columns and `LIMIT` / `OFFSET`
    itemsFragment items && fromFragment f && wh.all isFragment &&
      orderBy.all (fun o => match o.expr with | .col _ => true | _ => false) &&
      (orderBy.isEmpty || itemsNamed items)
  | .mk false items (some f) wh groupBy having orderBy _ _ =>
    !groupBy.isEmpty && CorrectGrouped.groupedItems items &&
      items.all (fun it => !CorrectAvg.avgFragment (itemExpr it)) &&
      groupBy.all (fun | .col _ => true | _ => false) &&
      (CorrectGroup.colRefs items).all (fun c => groupBy.contains (.col c)) && fromFragment f &&
      wh.all isFragment && having.all (CorrectGroup.havingFragment groupBy) &&
      having.all (fun h => !CorrectGroup.hasCmpAvg h) &&
      -- #411: `ORDER BY` aggregates or uncaptured key columns, `LIMIT` / `OFFSET`
      orderBy.all (fun o => aggFragment o.expr || keyColB items groupBy o.expr) &&
      (orderBy.isEmpty || items.all (fun it => decide ('.' ∉ (outName it).toList) &&
        !"__group_orderkey_".toList.isPrefixOf (outName it).toLower.toList))
  | _ => false

/-- `SqlBridge.CorrectSub.NodeOk` (sqlite assumed, for the scalar node). -/
def nodeOkB : SqlEquiv.Expr → Bool
  | .inSubquery e _ sq => isFragment e && subBodyOkB sq
  | .subquery (.simple b) => bodyOkB b
  | _ => false
where
  /-- `SqlBridge.CorrectSub.SubBodyOk` (#410): a `BodyOk` statement or a set operation over
      such bodies. -/
  subBodyOkB : SqlEquiv.SubQuery → Bool
    | .simple b => bodyOkB b
    | .compound l _ r => subBodyOkB l && subBodyOkB r

/-- An expression next to the node: in the fragment, not referring to the hidden column. -/
def besideB (a : SqlEquiv.Expr) : Bool :=
  isFragment a && SqlBridge.CorrectSub.noRefTo String.toLower "?subquery?" a

/-- `SqlBridge.CorrectSub.SubWhere` (steps 6b and 6c, names folded to lowercase): one subquery
    node, alone, on the right of a comparison, or either under `AND`. -/
def subWhereB : SqlEquiv.Expr → Bool
  | .binOp .and a b => (subWhereB a && besideB b) || (besideB a && subWhereB b)
  | .binOp op a nd =>
    (match elabBinOp op with | .ok (.cmp _) => true | _ => false) && besideB a && nodeOkB nd
  | w => nodeOkB w

/-- `SqlBridge.CorrectSub.AvgBody`: `SELECT AVG(e) FROM f [WHERE p]`. -/
def avgBodyB : SqlEquiv.SelectStmt → Bool
  | .mk false [.exprItem a _] (some f) wh [] none [] none none =>
    SqlBridge.CorrectAvg.avgFragment a && fromFragment f && wh.all isFragment
  | _ => false

/-- The syntactic part of `SqlBridge.CorrectSub.AvgWhere` (sqlite assumed): a scalar node over
    an `AVG` body on the right of a comparison with a column or an integer literal, alone or
    under `AND`. The theorem also asks that the operand is not a decimal (`NonDecimalIn`; no
    column of the test schemas, or of Spider's, is one) and that the average's denominator is
    at most `10¹⁶` (`AvgBound`), which depends on the data. -/
def avgWhereB : SqlEquiv.Expr → Bool
  | .binOp .and a b => (avgWhereB a && besideB b) || (besideB a && avgWhereB b)
  | .binOp op a (.subquery (.simple b)) =>
    (match elabBinOp op with | .ok (.cmp _) => true | _ => false) && besideB a &&
      (match a with | .col _ | .lit (.int _) => true | _ => false) && avgBodyB b
  | _ => false

/-- `SqlBridge.CorrectSub.AnySubWhere`, as far as a shape can tell. -/
def anySubWhereB (w : SqlEquiv.Expr) : Bool := subWhereB w || avgWhereB w

/-- The shape of `elabStmt_correct_grouped_inSub`: a statement of `elabStmt_correct_grouped`
    with such a `WHERE`. -/
def groupedInSubShape : SqlEquiv.Stmt → Bool
  | .query (.simple (.mk false items (some f) (some w) groupBy having orderBy lim off)) =>
    anySubWhereB w &&
      groupedShape (.query (.simple (.mk false items (some f) none groupBy having orderBy lim off)))
  | _ => false

/-- The shape of `elabStmt_correct_inSub`: a statement of `elabStmt_correct_join` with such a
    `WHERE`. -/
def inSubShape : SqlEquiv.Stmt → Bool
  | .query (.simple (.mk false items (some f) (some w) [] none orderBy _ _)) =>
    itemsFragment items && fromFragment f && anySubWhereB w &&
      orderBy.all (fun o => match o.expr with | .col _ => true | _ => false) &&
      (orderBy.isEmpty || itemsNamed items)
  | _ => false

/-- The shape of `elabStmt_correct_distinct_inSub`. -/
def distinctInSubShape : SqlEquiv.Stmt → Bool
  | .query (.simple (.mk true items (some f) (some w) [] none [] none none)) =>
    itemsFragment items && fromFragment f && anySubWhereB w
  | _ => false

/-- The shape of `elabStmt_correct_agg_inSub`. -/
def aggInSubShape : SqlEquiv.Stmt → Bool
  | .query (.simple (.mk false items (some f) (some w) [] none [] none none)) =>
    aggItems items && !items.isEmpty && fromFragment f && anySubWhereB w
  | _ => false

/-- The shape of `elabStmt_correct_aggBare_inSub`. -/
def aggBareInSubShape : SqlEquiv.Stmt → Bool
  | .query (.simple (.mk false items (some f) (some w) [] none [] none none)) =>
    groupedItems items && items.any (fun it => itemAggFragment (itemExpr it)) && fromFragment f &&
      bareOkB items [] none [] && anySubWhereB w
  | _ => false

/-- The shape of `elabStmt_correct_countDerived` (#412): `COUNT(*)` items over a derived table
    whose body is a `SubBodyOk` one, without `WHERE`. -/
def countDerivedShape : SqlEquiv.Stmt → Bool
  | .query (.simple (.mk false items (some (.subquery sq _)) none [] none [] none none)) =>
    SqlBridge.CorrectDerived.countItems items && !items.isEmpty && nodeOkB.subBodyOkB sq
  | _ => false

/-- A statement has the shape of one of the elaborator-correctness theorems. -/
def anyShape (s : SqlEquiv.Stmt) : Bool :=
  stmtShape s || aggShape s || aggBareShape s || groupedShape s || distinctShape s ||
    setOpShape s || inSubShape s || distinctInSubShape s || aggInSubShape s ||
    aggBareInSubShape s || groupedInSubShape s || countDerivedShape s

/-- `SqlBridge.Coverage.outsideFragment` (the Spider coverage report, #352) finds no feature
    outside the fragment exactly when the statement has the theorem's shape, and its copy of
    `itemsNamed` agrees with the theorem's. -/
def coverageAgrees (sql : String) : Bool :=
  match SqlEquiv.parse sql with
  | .ok stmt =>
    (SqlBridge.Coverage.outsideFragment stmt).isEmpty ==
      anyShape stmt &&
      match stmt with
      | .query (.simple s) => SqlBridge.Coverage.itemsNamed s.items == itemsNamed s.items
      | _ => true
  | .error _ => false

#guard [ "SELECT name, age FROM users", "SELECT name FROM users WHERE age > 25",
  "SELECT name FROM users WHERE NOT (age < 30) OR department = 'Sales'",
  "SELECT u.name FROM users u WHERE u.age = 30", "SELECT name, age >= 30, NULL FROM users WHERE TRUE",
  "SELECT age + 1 FROM users", "SELECT * FROM users", "SELECT DISTINCT name FROM users",
  "SELECT u.name FROM users u JOIN orders o ON u.id = o.user_id",
  "SELECT u.name FROM users u CROSS JOIN orders o WHERE u.id = o.user_id ORDER BY u.name",
  "SELECT u.name FROM users u LEFT JOIN orders o ON u.id = o.user_id",
  "SELECT u.name FROM users u JOIN orders o ON u.id + 1 = o.user_id",
  "SELECT name FROM users ORDER BY age LIMIT 2", "SELECT name FROM users LIMIT 2 OFFSET 1",
  "SELECT name AS n, age FROM users WHERE age > 1 ORDER BY n DESC, age NULLS FIRST",
  "SELECT name FROM users ORDER BY age + 1", "SELECT age > 30 FROM users ORDER BY age",
  "SELECT age > 30 FROM users LIMIT 1", "SELECT COUNT(*) FROM users",
  "SELECT COUNT(DISTINCT department), MAX(age), MIN(name), SUM(age) FROM users WHERE age > 1",
  "SELECT COUNT(*) FROM users u JOIN orders o ON u.id = o.user_id", "SELECT AVG(age) FROM users",
  "SELECT SUM(DISTINCT age) FROM users", "SELECT MAX(age), name FROM users",
  "SELECT COUNT(*) FROM users LIMIT 1", "SELECT SUM(age + 1) FROM users",
  "SELECT COUNT(*) + 1 FROM users",
  "SELECT department, COUNT(*), MAX(age) FROM users WHERE age > 1 GROUP BY department",
  "SELECT u.department, COUNT(DISTINCT o.product) FROM users u JOIN orders o ON u.id = o.user_id GROUP BY u.department",
  "SELECT name, COUNT(*) FROM users GROUP BY department",
  "SELECT department FROM users GROUP BY department HAVING COUNT(*) > 1",
  "SELECT department, COUNT(*) FROM users GROUP BY department ORDER BY COUNT(*) DESC LIMIT 1",
  "SELECT department FROM users GROUP BY department ORDER BY MAX(age), COUNT(*) LIMIT 2 OFFSET 1",
  "SELECT department AS d FROM users GROUP BY department ORDER BY SUM(age + 1)",
  "SELECT department FROM users GROUP BY department ORDER BY department",
  "SELECT department FROM users GROUP BY department ORDER BY AVG(age)",
  "SELECT department FROM users GROUP BY department HAVING COUNT(*) > 1 ORDER BY COUNT(*)",
  "SELECT department AS __Group_OrderKey_0 FROM users GROUP BY department ORDER BY COUNT(*)",
  "SELECT department FROM users GROUP BY department LIMIT 1",
  "SELECT name, COUNT(*) FROM users GROUP BY department HAVING COUNT(*) > 1 ORDER BY COUNT(*) LIMIT 2",
  "SELECT name, MAX(age) FROM users GROUP BY department",
  "SELECT name FROM users GROUP BY department ORDER BY MIN(age)",
  "SELECT name FROM users GROUP BY department HAVING MAX(age) > 1",
  "SELECT department, AVG(age) FROM users GROUP BY department",
  "SELECT department FROM users GROUP BY department HAVING NOT (COUNT(*) <= 1) OR department = 'x'",
  "SELECT department FROM users GROUP BY department HAVING name = 'x'",
  "SELECT department FROM users GROUP BY department HAVING AVG(age) > 1",
  "SELECT department FROM users GROUP BY department", "SELECT name FROM users WHERE age IS NULL",
  "SELECT name FROM users WHERE age IN (1, 2)", "SELECT name FROM users WHERE age BETWEEN 1 AND 2",
  "SELECT name FROM users WHERE name LIKE 'a%'", "SELECT 1",
  "SELECT name FROM users WHERE id IN (SELECT user_id FROM orders)",
  "SELECT name FROM users UNION SELECT product FROM orders",
  "SELECT name FROM users UNION SELECT product FROM orders ORDER BY 1 LIMIT 3",
  "SELECT * FROM users u JOIN orders o ON u.id = o.user_id WHERE o.amount > 1 LIMIT 2",
  "SELECT u.* FROM users u", "SELECT * FROM users ORDER BY name", "SELECT DISTINCT * FROM users",
  "SELECT * FROM users UNION SELECT * FROM users" ].all coverageAgrees

/-- The features `outsideFragment` lists for a statement. -/
def features (sql : String) : List String :=
  match SqlEquiv.parse sql with
  | .ok s => SqlBridge.Coverage.outsideFragment s
  | .error _ => ["parse error"]

#guard features "SELECT name FROM users ORDER BY age LIMIT 2" == []
#guard features "SELECT name FROM users ORDER BY age + 1" == ["ORDER BY expression", "arithmetic"]
#guard features "SELECT age > 30 FROM users ORDER BY age" == ["unnamed item with ORDER BY"]
#guard features "SELECT u.name FROM users u JOIN orders o ON u.id = o.user_id" == []
#guard features "SELECT u.name FROM users u LEFT JOIN orders o ON u.id = o.user_id" == ["outer join"]
#guard features "SELECT COUNT(*), MAX(age) FROM users WHERE age > 1" == []
-- plain `DISTINCT` is in the fragment (step 5, up to row order); not with `ORDER BY`, `LIMIT`,
-- `GROUP BY` or an aggregate item
#guard features "SELECT DISTINCT department FROM users WHERE age > 20" == []
#guard features "SELECT DISTINCT u.name FROM users u JOIN orders o ON u.id = o.user_id" == []
#guard features "SELECT DISTINCT department FROM users LIMIT 1" == ["DISTINCT"]
#guard features "SELECT DISTINCT department FROM users ORDER BY department" == ["DISTINCT"]
#guard features "SELECT DISTINCT department FROM users GROUP BY department" ==
  ["DISTINCT", "aggregate/GROUP BY"]
#guard features "SELECT DISTINCT COUNT(*) FROM users" == ["aggregate/GROUP BY"]
-- `BETWEEN` is in the fragment (step 4), in `WHERE` and in `HAVING`; `IN (list)` is not
#guard features "SELECT name FROM users WHERE age BETWEEN 25 AND 30" == []
#guard features "SELECT department FROM users GROUP BY department HAVING COUNT(*) BETWEEN 1 AND 2" == []
#guard features "SELECT name FROM users WHERE age BETWEEN 25 AND age + 1" == ["arithmetic"]
#guard features "SELECT name FROM users WHERE age IN (1, 2)" == ["IN list"]
-- `AVG` as an item is in the fragment (step 3c); in `HAVING` only as `AVG(c) op k` (step 6c,
-- `HavingAvgOk`); not in `ORDER BY`
#guard features "SELECT AVG(age) FROM users" == []
#guard features "SELECT department, AVG(age) FROM users GROUP BY department" == []
#guard features "SELECT department FROM users GROUP BY department HAVING AVG(age) > 1" == []
#guard features "SELECT department FROM users GROUP BY department HAVING 1 < AVG(age)" ==
  ["AVG", "aggregate/GROUP BY"]
#guard features "SELECT department FROM users GROUP BY department HAVING AVG(age) > MIN(age)" ==
  ["AVG", "aggregate/GROUP BY"]
#guard features "SELECT department FROM users GROUP BY department HAVING AVG(DISTINCT age) > 1" != []
#guard features "SELECT department FROM users GROUP BY department HAVING AVG(age) > 1.5" != []
#guard features "SELECT SUM(age + 1) FROM users" == ["arithmetic"]
#guard features "SELECT department, COUNT(*) FROM users GROUP BY department" == []
-- a bare column (steps 3b-4, 3b-5): in the fragment without MIN/MAX; next to one MIN/MAX only in
-- the sqlite dialect, whose MIN/MAX picks the row (`MinMaxMode.bareRow`), and not next to two, or
-- to one DISTINCT
#guard features "SELECT name, COUNT(*) FROM users GROUP BY department" == []
#guard features "SELECT name, MAX(age) FROM users GROUP BY department" == ["aggregate/GROUP BY"]

/-- `features` under the sqlite dialect, with the check that the report agrees with the shape. -/
def featuresSqlite (sql : String) : List String :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok s =>
    let fs := SqlBridge.Coverage.outsideFragment s
    if fs.isEmpty == anyShape s then fs else ["disagrees"]
  | .error _ => ["parse error"]

#guard featuresSqlite "SELECT name, MAX(age) FROM users GROUP BY department" == []
#guard featuresSqlite "SELECT name, MAX(age) FROM users GROUP BY department HAVING MAX(age) > 1" == []
-- `ORDER BY MIN(age)` alone: `SqlEquiv` reads the first row, sqlite the extreme one (T9, open)
#guard featuresSqlite "SELECT name FROM users GROUP BY department ORDER BY MIN(age)" ==
  ["ORDER BY expression", "aggregate/GROUP BY"]
#guard featuresSqlite "SELECT name, MAX(age), MIN(age) FROM users GROUP BY department" ==
  ["aggregate/GROUP BY"]
#guard featuresSqlite "SELECT name, MAX(DISTINCT age) FROM users GROUP BY department" ==
  ["aggregate/GROUP BY"]
#guard featuresSqlite "SELECT name, MAX(age) FROM users GROUP BY department ORDER BY MIN(age)" ==
  ["ORDER BY expression", "aggregate/GROUP BY", "unnamed item with ORDER BY"]
#guard features "SELECT department FROM users GROUP BY department HAVING COUNT(*) > 1 AND MAX(age) < 60" == []
#guard features "SELECT department FROM users GROUP BY department HAVING SUM(age + 1) > 1" == ["arithmetic"]

/-! ### A Spider-shaped schema (#351)

Spider's schemas (`SqlBridge.Spider.schemaOf`) store names lowercased and fold references with
`String.toLower`, as sqlite's names are case-insensitive. The theorem's hypotheses hold for them:
the fold keeps names equal ignoring case, the names are well formed, and a database that answers
every spelling of a table name alike relates (here an empty one, to show `DbRel` is satisfiable
under folding; `SqlEquiv` looks a table up by the name as written, registry row 20). -/

open SqlBridge.Spider in
def singerSchema : NamedSchema :=
  { schemaOf #[⟨"singer", #[("singer_id", .int), ("name", .text), ("age", .int)]⟩,
      ⟨"song", #[("title", .text), ("singer_id", .int)]⟩] with
    config := SqlEquiv.Dialect.sqlite.config }

example : ∀ s, (singerSchema.fold s).toLower = s.toLower := string_toLower_toLower

example : WellNamed singerSchema := by
  constructor <;> (simp only [singerSchema, SqlBridge.Spider.schemaOf]; decide +kernel)

example : DbRel singerSchema (fun _ => []) (fun _ => []) := fun _ _ _ => .nil

/-- With an `ORDER BY` or a join, the theorems also ask the fold to identify exactly the names
    equal ignoring case (`String.toLower` does) ... -/
example : ∀ x y, singerSchema.fold x = singerSchema.fold y ↔ x.toLower = y.toLower :=
  fun _ _ => Iff.rfl

/-- ... and, with a join, the column names to be their own folds (Spider lowercases them). -/
example : ∀ T j, singerSchema.fold (singerSchema.S.columns T j).name =
    (singerSchema.S.columns T j).name := by
  simp only [singerSchema, SqlBridge.Spider.schemaOf]; decide +kernel

/-- The two hypotheses of an `AVG` comparison (`SqlBridge.CorrectSub.AvgWhere`) hold here: no
    column is a decimal, so a column is not one among the columns of any `FROM` tree
    (`NonDecimalIn`); and over a table of at most `10¹⁶` rows the average of a column has a
    denominator within the bound (`AvgBound`). -/
theorem singerSchema_noDecimal : ∀ T j, (singerSchema.S.columns T j).type ≠ .decimal := by
  simp only [singerSchema, SqlBridge.Spider.schemaOf]; decide +kernel

example (f : SqlEquiv.FromClause) (hff : fromFragment f = true) (c : SqlEquiv.ColumnRef) :
    SqlBridge.CorrectSub.NonDecimalIn singerSchema f (.col c) :=
  SqlBridge.CorrectSub.nonDecimalIn_col singerSchema singerSchema_noDecimal hff c

example {D : SqlCore.Database singerSchema.S} (hD : D.Conforms)
    (hB : ∀ T, (D T).length ≤ 10 ^ SqlEquiv.avgPlaces) :
    SqlBridge.CorrectSub.AvgBound singerSchema D
      (.mk false [.exprItem (.agg (.avg .asInt) (some (.col ⟨none, "age"⟩)) false) none]
        (some (.table ⟨"singer", none⟩)) none [] none [] none none) :=
  SqlBridge.CorrectSub.avgBound_of_rows singerSchema (fun _ _ => Iff.rfl) hD rfl rfl
    (fun _ h => by cases h)
    (SqlBridge.CorrectSub.nonDecimalIn_col singerSchema singerSchema_noDecimal rfl _)
    (fun qf cf Rf h hRf => SqlBridge.CorrectSub.fromRows_table singerSchema _ hB _ qf cf Rf h hRf)

/-- The hypothesis of a `HAVING AVG(c) op k` (`SqlBridge.CorrectGrouped.HavingAvgOk`) holds
    here over a table of at most `10¹⁶` rows. -/
example {D : SqlCore.Database singerSchema.S} (hB : ∀ T, (D T).length ≤ 10 ^ SqlEquiv.avgPlaces)
    (having : Option SqlEquiv.Expr) :
    SqlBridge.CorrectGrouped.HavingAvgOk singerSchema D (.table ⟨"singer", none⟩) having :=
  fun _ => ⟨singerSchema_noDecimal, fun qf cf Rf h hRf =>
    SqlBridge.CorrectSub.fromRows_table singerSchema _ hB _ qf cf Rf h hRf⟩

-- a branch of a set operation takes no `AVG` comparison in `HAVING` (`Leaf.grouped`)
#guard featuresSqlite ("SELECT age FROM singer GROUP BY age HAVING avg(singer_id) > 1 " ++
  "UNION SELECT age FROM singer") == [SqlBridge.Coverage.setOpBranch]

/-- Mixed-case references, as Spider writes them, are in the fragment and elaborate under the
    folding schema, so `elabStmt_correct` applies to them. -/
def inFragmentSpider (sql : String) : Bool :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok stmt@(.query (.simple (.mk false items (some (.table ⟨name, al⟩)) wh [] none [] none none))) =>
    itemsFragment items && wh.all isFragment && stmt == fragmentStmt items name al wh &&
      (elabStmt singerSchema stmt).toBool
  | _ => false

#guard inFragmentSpider "SELECT Name FROM Singer WHERE Age > 20"
#guard inFragmentSpider "SELECT T1.name FROM SINGER AS T1 WHERE t1.AGE >= 30 OR T1.Name = 'Joe'"
#guard inFragmentSpider "SELECT singer_id, NAME FROM singer"
#guard !inFragmentSpider "SELECT Name FROM Singers"

/-- Spider-shaped queries with `ORDER BY` / `LIMIT` / `OFFSET` (roadmap step 1) and joins (step 2)
    have the shape of `elabStmt_correct_join` and elaborate under the folding schema. -/
def orderedSpider (sql : String) : Bool :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok stmt => stmtShape stmt && (elabStmt singerSchema stmt).toBool
  | .error _ => false

#guard orderedSpider "SELECT Name FROM Singer ORDER BY Age DESC LIMIT 1"
#guard orderedSpider "SELECT T1.name FROM SINGER AS T1 WHERE T1.age > 20 ORDER BY t1.AGE, T1.Name"
#guard orderedSpider "SELECT name AS n FROM singer ORDER BY n LIMIT 3 OFFSET 1"
#guard orderedSpider "SELECT name, age FROM singer LIMIT 2"
#guard !orderedSpider "SELECT name FROM singer ORDER BY age + 1"

-- Spider-shaped joins (roadmap step 2) have the shape of `elabStmt_correct_join` and elaborate.
#guard orderedSpider
  "SELECT T2.Title , T1.Name FROM singer AS T1 JOIN song AS T2 ON T1.Singer_ID = T2.Singer_ID"
#guard orderedSpider ("SELECT T1.name FROM SINGER AS T1 JOIN song AS T2 ON t1.singer_id = " ++
  "T2.SINGER_ID WHERE T2.title = 'x' ORDER BY T1.age DESC LIMIT 1")
#guard orderedSpider "SELECT title, name FROM singer CROSS JOIN song"
#guard orderedSpider "SELECT a.name FROM singer AS a JOIN singer AS b ON a.age < b.age"
-- An unqualified column of both tables is ambiguous: the elaborator rejects it.
#guard !orderedSpider "SELECT singer_id FROM singer JOIN song ON singer.singer_id = song.singer_id"

-- `SELECT *` (#407, `elabStmt_correct_star`): over a table or a join, next to other items, with
-- `WHERE` and `LIMIT`, and as a branch of a set operation (`Leaf.plain`).
#guard orderedSpider "SELECT * FROM Singer"
#guard orderedSpider ("SELECT * FROM singer AS T1 JOIN song AS T2 ON T1.Singer_ID = " ++
  "T2.singer_id WHERE T2.title = 'x' AND Age > 20")
#guard orderedSpider "SELECT name, *, age FROM singer WHERE age > 20 LIMIT 2 OFFSET 1"
#guard orderedSpider "SELECT * FROM singer CROSS JOIN song"
#guard featuresSqlite "SELECT * FROM singer" == []
#guard featuresSqlite ("SELECT * FROM singer AS T1 JOIN song AS T2 ON T1.singer_id = " ++
  "T2.singer_id WHERE T2.title = 'x' UNION SELECT * FROM singer AS T1 JOIN song AS T2 ON " ++
  "T1.singer_id = T2.singer_id WHERE T2.title = 'y'") == []
#guard match SqlEquiv.parse ("SELECT * FROM singer UNION SELECT * FROM singer WHERE age > 1")
    (dialect := .sqlite) with
  | .ok s => setOpShape s && (elabStmt singerSchema s).toBool
  | .error _ => false
-- Outside: `t.*`, `*` with `ORDER BY`, `DISTINCT` or `GROUP BY`, next to a subquery in `WHERE`
-- (`inSubShape` keeps `itemsFragment`), and in a subquery body (the outer row would show).
#guard !orderedSpider "SELECT T1.* FROM singer AS T1"
#guard featuresSqlite "SELECT T1.* FROM singer AS T1" == [SqlBridge.Coverage.star]
#guard !orderedSpider "SELECT * FROM singer ORDER BY age"
#guard featuresSqlite "SELECT * FROM singer ORDER BY age" ==
  [SqlBridge.Coverage.star, SqlBridge.Coverage.unnamedItem]
#guard featuresSqlite "SELECT DISTINCT * FROM singer" == [SqlBridge.Coverage.star]
#guard featuresSqlite "SELECT * FROM singer GROUP BY age" ==
  [SqlBridge.Coverage.star, SqlBridge.Coverage.aggregate]
#guard featuresSqlite "SELECT * FROM singer WHERE singer_id IN (SELECT singer_id FROM song)" ==
  [SqlBridge.Coverage.star]
#guard featuresSqlite "SELECT name FROM singer WHERE singer_id IN (SELECT * FROM song)" ==
  [SqlBridge.Coverage.star]
#guard featuresSqlite "SELECT *, count(*) FROM singer" != []

/-- Spider-shaped aggregates without `GROUP BY` (roadmap step 3a) have the shape of
    `elabStmt_correct_agg` and elaborate under the folding schema. -/
def aggSpider (sql : String) : Bool :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok stmt => aggShape stmt && (elabStmt singerSchema stmt).toBool
  | .error _ => false

#guard aggSpider "SELECT count(*) FROM singer"
#guard aggSpider "SELECT COUNT(*) FROM Singer WHERE Age > 20"
#guard aggSpider "SELECT max(age), min(Name), sum(AGE), count(name) FROM singer"
#guard aggSpider ("SELECT count(DISTINCT T2.title) FROM singer AS T1 JOIN song AS T2 ON " ++
  "T1.singer_id = T2.singer_id WHERE T1.age > 20")
-- Outside step 3a: `AVG`, grouping, a bare column next to an aggregate, `SUM` of text.
#guard !aggSpider "SELECT avg(age) FROM singer"
#guard !aggSpider "SELECT count(*) FROM singer GROUP BY name"
#guard !aggSpider "SELECT max(age), name FROM singer"
#guard !aggSpider "SELECT sum(name) FROM singer"

/-- Spider-shaped grouped queries (roadmap steps 3b-1 to 3b-5) have the shape of
    `elabStmt_correct_grouped` and elaborate under the folding schema. -/
def groupedSpider (sql : String) : Bool :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok stmt => groupedShape stmt && (elabStmt singerSchema stmt).toBool
  | .error _ => false

-- 3b-1: keys and aggregates
#guard groupedSpider "SELECT age, count(*) FROM singer GROUP BY age"
#guard groupedSpider "SELECT Age, max(name), min(singer_id) FROM Singer WHERE age > 20 GROUP BY Age"
#guard groupedSpider ("SELECT T1.name, count(*) FROM singer AS T1 JOIN song AS T2 ON " ++
  "T1.singer_id = T2.singer_id GROUP BY T1.name")
-- 3b-2: `HAVING`
#guard groupedSpider "SELECT age FROM singer GROUP BY age HAVING count(*) > 1"
#guard groupedSpider ("SELECT T1.name FROM singer AS T1 JOIN song AS T2 ON T1.singer_id = " ++
  "T2.singer_id GROUP BY T1.name HAVING COUNT(*) >= 2 AND max(T2.title) <> 'x'")
-- 3b-3: ordered by aggregates, `LIMIT`/`OFFSET`
#guard groupedSpider "SELECT age FROM singer GROUP BY age ORDER BY count(*) DESC LIMIT 1"
#guard groupedSpider "SELECT Age, count(*) FROM Singer WHERE age > 20 GROUP BY Age ORDER BY COUNT(*)"
#guard groupedSpider ("SELECT T1.name FROM singer AS T1 JOIN song AS T2 ON T1.singer_id = " ++
  "T2.singer_id GROUP BY T1.name ORDER BY count(*) DESC, max(T2.title) LIMIT 3 OFFSET 1")
-- 3b-4: bare columns read on the first row, `HAVING` with `ORDER BY`, `LIMIT` alone
#guard groupedSpider "SELECT name, count(*) FROM singer GROUP BY age"
#guard groupedSpider ("SELECT T2.title FROM singer AS T1 JOIN song AS T2 ON T1.singer_id = " ++
  "T2.singer_id GROUP BY T1.singer_id ORDER BY count(*) DESC LIMIT 1")
#guard groupedSpider ("SELECT T1.name, T1.age FROM singer AS T1 JOIN song AS T2 ON " ++
  "T1.singer_id = T2.singer_id GROUP BY T1.singer_id HAVING count(*) >= 2")
#guard groupedSpider "SELECT age FROM singer GROUP BY age HAVING count(*) > 1 ORDER BY count(*)"
#guard groupedSpider "SELECT age FROM singer GROUP BY age LIMIT 2"
-- 3b-5: a bare column next to one `MIN`/`MAX` reads the row where its argument is extreme
#guard groupedSpider "SELECT name, max(age) FROM singer GROUP BY singer_id"
#guard groupedSpider "SELECT Name, Singer_ID, min(Age) FROM singer GROUP BY Singer_ID"
#guard groupedSpider "SELECT name FROM singer GROUP BY age HAVING max(singer_id) > 1 ORDER BY max(singer_id)"
-- 3b-6: ordered by a key column, selected or not, mixed with aggregates
#guard groupedSpider "SELECT age, count(*) FROM singer GROUP BY age ORDER BY age"
#guard groupedSpider "SELECT count(*) FROM singer GROUP BY age ORDER BY age DESC LIMIT 2"
#guard groupedSpider "SELECT age FROM singer GROUP BY age ORDER BY count(*), age"
-- 4: `BETWEEN` in `HAVING`, over an aggregate or a key
#guard groupedSpider "SELECT age FROM singer GROUP BY age HAVING count(*) BETWEEN 1 AND 2"
#guard groupedSpider "SELECT age, count(*) FROM singer GROUP BY age HAVING age BETWEEN 20 AND 30"
#guard !groupedSpider "SELECT age FROM singer GROUP BY age HAVING avg(singer_id) BETWEEN 1 AND 2"
-- 3c: `AVG` items, grouped or not (related up to rounding)
#guard groupedSpider "SELECT age, avg(singer_id) FROM singer GROUP BY age"
#guard groupedSpider "SELECT age, avg(singer_id) FROM singer GROUP BY age ORDER BY count(*) DESC LIMIT 1"
-- Outside: a sort key column captured by another item's name or not a key, `AVG` in `ORDER BY`
-- or `HAVING`, a `HAVING`
-- column that is no key; a bare column next to two `MIN`/`MAX` calls, or to one with DISTINCT
#guard !groupedSpider "SELECT count(*) AS age FROM singer GROUP BY age ORDER BY age"
#guard !groupedSpider "SELECT age FROM singer GROUP BY age ORDER BY name"
-- (the key is matched as written: `ORDER BY Age` after `GROUP BY age` stays outside)
#guard !groupedSpider "SELECT count(*) FROM singer GROUP BY age ORDER BY Age"
#guard !groupedSpider "SELECT age FROM singer GROUP BY age ORDER BY avg(singer_id)"
#guard groupedSpider "SELECT age FROM singer GROUP BY age HAVING avg(singer_id) > 1"
#guard groupedSpider ("SELECT age, avg(singer_id) FROM singer GROUP BY age " ++
  "HAVING count(*) > 1 AND avg(singer_id) <= 3 ORDER BY age")
#guard !groupedSpider "SELECT age FROM singer GROUP BY age HAVING avg(singer_id) > min(singer_id)"
#guard !groupedSpider "SELECT age FROM singer GROUP BY age HAVING 1 < avg(singer_id)"
#guard !groupedSpider "SELECT age FROM singer GROUP BY age HAVING name = 'x'"
#guard !groupedSpider "SELECT name, max(age), min(age) FROM singer GROUP BY singer_id"
#guard !groupedSpider "SELECT name, max(DISTINCT age) FROM singer GROUP BY singer_id"
#guard !groupedSpider "SELECT name, max(age) FROM singer GROUP BY age ORDER BY min(singer_id)"

/-- Spider-shaped aggregate queries with bare columns and no `GROUP BY` (roadmap step 3b-6) have
    the shape of `elabStmt_correct_aggBare` and elaborate under the folding schema. -/
def aggBareSpider (sql : String) : Bool :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok stmt => aggBareShape stmt && (elabStmt singerSchema stmt).toBool
  | .error _ => false

-- 3b-6: the extreme row, or the first row, of the whole input
#guard aggBareSpider "select max(age), name from singer"
#guard aggBareSpider "SELECT min(Singer_ID), Name FROM Singer WHERE age > 20"
#guard aggBareSpider "SELECT count(*), name FROM singer"
-- 3c: `AVG` items without `GROUP BY`, not with `DISTINCT`
#guard aggBareSpider "SELECT avg(age), max(age), min(age) FROM singer"
#guard !aggBareSpider "SELECT avg(DISTINCT age) FROM singer"
-- Outside: no aggregate at all, two `MIN`/`MAX`, a `GROUP BY` (`groupedShape` instead), `LIMIT`
#guard !aggBareSpider "SELECT name FROM singer"
#guard !aggBareSpider "SELECT max(age), min(age), name FROM singer"
#guard !aggBareSpider "SELECT max(age), name FROM singer GROUP BY singer_id"
#guard !aggBareSpider "SELECT max(age), name FROM singer LIMIT 1"
#guard featuresSqlite "select max(age), name from singer" == []
#guard featuresSqlite "SELECT max(age), min(age), name FROM singer" == ["aggregate/GROUP BY"]

/-- `BareOk`'s third case (step 3b-5) is satisfiable by a statement that elaborates: a bare
    `name` next to the one `max(age)`, parsed in the sqlite dialect (`bareRow`). -/
def extremeMode : SqlEquiv.MinMaxMode := { mixed := .typeClass, bools := .asInt, bareRow := true }
def extremeItems : List SqlEquiv.SelectItem :=
  [.exprItem (.col ⟨none, "name"⟩) none,
   .exprItem (.agg (.max extremeMode) (some (.col ⟨none, "age"⟩)) false) none]

example : SqlBridge.CorrectGrouped.BareOk singerSchema extremeItems
    [.col ⟨none, "singer_id"⟩] none [] :=
  .inr (.inr ⟨rfl, true, extremeMode, .col ⟨none, "age"⟩, rfl, by decide, by decide⟩)

#guard SqlEquiv.parse "SELECT name, max(age) FROM singer GROUP BY singer_id" (dialect := .sqlite) ==
  .ok (.query (.simple (.mk false extremeItems (some (.table ⟨"singer", none⟩)) none
    [.col ⟨none, "singer_id"⟩] none [] none none)))
#guard (elabStmt singerSchema (groupedStmt extremeItems (.table ⟨"singer", none⟩) none
  [.col ⟨none, "singer_id"⟩] none [] none none)).toBool

/-- `OrderKeyOk`'s key-column case (step 3b-6) is satisfiable: `SELECT age … GROUP BY age ORDER BY
    age`, where the one item named like the key is the key column. -/
example : SqlBridge.CorrectGrouped.OrderKeyOk [.exprItem (.col ⟨none, "age"⟩) none]
    [.col ⟨none, "age"⟩] (.col ⟨none, "age"⟩) :=
  .inr ⟨_, rfl, by simp, fun it hit _ => by simp at hit; subst hit; rfl⟩

/-- Without `GROUP BY` (step 3b-6) too: `SELECT name, max(age) FROM singer` satisfies `BareOk` and
    elaborates. -/
example : SqlBridge.CorrectGrouped.BareOk singerSchema extremeItems [] none [] :=
  .inr (.inr ⟨rfl, true, extremeMode, .col ⟨none, "age"⟩, rfl, by decide, by decide⟩)
#guard (elabStmt singerSchema (groupedStmt extremeItems (.table ⟨"singer", none⟩) none
  [] none [] none none)).toBool

/-- `AvgRel`'s rounding case (step 3c) holds where `SqlEquiv` rounds: `AVG` of 1, 1, 2 is the
    typed 4/3 and `SqlEquiv`'s `1.3333333333333333` (registry row 7). -/
example : SqlBridge.CorrectAvg.AvgRel (some (.decimal (4 / 3)))
    (SqlEquiv.Value.mkDecimal 13333333333333333 16) :=
  .inr ⟨4 / 3, 16, rfl, le_refl _, by
    rw [SqlBridge.CorrectAvg.roundHalfAway, if_pos (by norm_num)]
    congr 1
    rw [eq_comm, Int.floor_eq_iff]; norm_num⟩

/-- Spider-shaped plain `SELECT DISTINCT` queries (roadmap step 5) have the shape of
    `elabStmt_correct_distinct` and elaborate under the folding schema. -/
def distinctSpider (sql : String) : Bool :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok stmt => distinctShape stmt && (elabStmt singerSchema stmt).toBool
  | .error _ => false

#guard distinctSpider "SELECT DISTINCT age FROM singer WHERE age > 20"
#guard distinctSpider ("SELECT DISTINCT T1.name FROM singer AS T1 JOIN song AS T2 ON " ++
  "T1.singer_id = T2.singer_id WHERE T1.age BETWEEN 20 AND 30")
#guard !distinctSpider "SELECT DISTINCT age FROM singer LIMIT 1"
#guard !distinctSpider "SELECT DISTINCT age FROM singer ORDER BY age"
#guard !distinctSpider "SELECT DISTINCT count(*) FROM singer"

/-- Spider-shaped set operations have the shape of `elabStmt_correct_setOp` and elaborate under
    the folding schema. -/
def setOpSpider (sql : String) : Bool :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok stmt => setOpShape stmt && (elabStmt singerSchema stmt).toBool
  | .error _ => false

#guard setOpSpider ("SELECT name FROM singer WHERE age > 40 INTERSECT " ++
  "SELECT name FROM singer WHERE age < 30")
#guard setOpSpider ("SELECT name FROM singer EXCEPT SELECT T1.name FROM singer AS T1 " ++
  "JOIN song AS T2 ON T1.singer_id = T2.singer_id")
#guard setOpSpider "SELECT name FROM singer UNION ALL SELECT name FROM singer WHERE age > 20"
-- a chain, and DISTINCT, aggregate and grouped branches (a bare column next to the key)
#guard setOpSpider ("SELECT name FROM singer UNION SELECT title FROM song EXCEPT " ++
  "SELECT name FROM singer WHERE age > 20")
#guard setOpSpider "SELECT DISTINCT name FROM singer INTERSECT SELECT name FROM singer"
#guard setOpSpider "SELECT count(*) FROM singer UNION SELECT max(age) FROM singer"
#guard setOpSpider ("SELECT singer_id, name FROM singer GROUP BY singer_id HAVING count(*) >= 1 " ++
  "INTERSECT SELECT singer_id, name FROM singer GROUP BY singer_id HAVING count(*) > 3")
-- outside: a trailing ORDER BY or LIMIT (the kept rows can differ, T18), an AVG branch (related
-- only up to rounding), a bare column without GROUP BY, a single SELECT
#guard !setOpSpider "SELECT name FROM singer UNION SELECT name FROM singer ORDER BY 1"
#guard !setOpSpider "SELECT name FROM singer UNION SELECT name FROM singer LIMIT 1"
#guard !setOpSpider "SELECT avg(age) FROM singer UNION SELECT avg(age) FROM singer"
#guard !setOpSpider ("SELECT name, avg(age) FROM singer GROUP BY name UNION " ++
  "SELECT name, age FROM singer")
#guard !setOpSpider "SELECT name, max(age) FROM singer UNION SELECT name, age FROM singer"
#guard !setOpSpider "SELECT name FROM singer"
-- the coverage report agrees on each, and names the branch that keeps a query outside
#guard featuresSqlite "SELECT name FROM singer UNION SELECT name FROM singer" == []
#guard featuresSqlite "SELECT name FROM singer UNION SELECT name FROM singer ORDER BY 1" ==
  [SqlBridge.Coverage.orderCompound]
#guard featuresSqlite "SELECT avg(age) FROM singer UNION SELECT avg(age) FROM singer" ==
  [SqlBridge.Coverage.setOpBranch]
#guard featuresSqlite "SELECT name, max(age) FROM singer UNION SELECT name, age FROM singer" ==
  [SqlBridge.Coverage.setOpBranch]
#guard featuresSqlite "SELECT name FROM singer UNION SELECT name FROM singer WHERE age + 1 = 2" ==
  [SqlBridge.Coverage.arithmetic]
#guard featuresSqlite "SELECT name FROM singer UNION SELECT name FROM singer WHERE name LIKE 'A%'" == []
-- `LIKE` is in the expression fragment, in either case mode (`Translates.like`): in `WHERE`,
-- as an item, under `NOT`; not in `HAVING`
#guard featuresSqlite "SELECT name FROM singer WHERE name LIKE '%a%'" == []
#guard features "SELECT name FROM users WHERE name LIKE '%a%' AND NOT (department LIKE 'S_les')" == []
#guard featuresSqlite "SELECT name LIKE 'A%' AS a FROM singer ORDER BY a" == []
#guard featuresSqlite "SELECT count(*) FROM singer WHERE name LIKE 'A%'" == []
#guard featuresSqlite "SELECT name FROM singer GROUP BY name HAVING name LIKE 'A%'" != []
-- branch shapes on which the report and the theorem's leaves could drift apart: a grouped
-- branch with an AVG item, a bare column next to COUNT without GROUP BY, DISTINCT over an
-- aggregate, a nested set operation with a bad branch (`featuresSqlite` says "disagrees" if so)
#guard featuresSqlite ("SELECT name, avg(age) FROM singer GROUP BY name UNION " ++
  "SELECT name, age FROM singer") == [SqlBridge.Coverage.setOpBranch]
#guard featuresSqlite "SELECT name, count(*) FROM singer UNION SELECT name, age FROM singer" ==
  [SqlBridge.Coverage.setOpBranch]
#guard featuresSqlite "SELECT DISTINCT name, max(age) FROM singer UNION SELECT name, age FROM singer"
  != []
#guard featuresSqlite ("SELECT name FROM singer UNION SELECT name FROM singer EXCEPT " ++
  "SELECT avg(age) FROM singer") == [SqlBridge.Coverage.setOpBranch]
#guard featuresSqlite ("SELECT name, count(*) FROM singer GROUP BY name INTERSECT " ++
  "SELECT name, count(*) FROM singer GROUP BY name HAVING count(*) > 1") == []
#guard featuresSqlite "SELECT count(*) FROM singer UNION SELECT count(DISTINCT name) FROM singer" == []

/-- `elabStmt_correct_setOp`'s hypothesis is satisfiable: a plain branch and a `DISTINCT` branch
    under `INTERSECT` form a `SetOpTree` of `Leaf`s, and the statement elaborates. -/
def setOpExample : SqlEquiv.Query :=
  .compound
    (.simple (.mk false [.exprItem (.col ⟨none, "name"⟩) none]
      (some (.table ⟨"singer", none⟩)) none [] none [] none none))
    .intersect
    (.simple (.mk true [.exprItem (.col ⟨none, "name"⟩) none]
      (some (.table ⟨"singer", none⟩)) none [] none [] none none))

example : SqlBridge.CorrectSetOp.SetOpTree (SqlBridge.CorrectSetOp.Leaf singerSchema)
    setOpExample :=
  .node _ (.leaf (.plain rfl rfl (by simp))) (.leaf (.distinct rfl rfl (by simp)))

#guard SqlEquiv.parse "SELECT name FROM singer INTERSECT SELECT DISTINCT name FROM singer"
  (dialect := .sqlite) == .ok (.query setOpExample)
#guard (elabStmt singerSchema (.query setOpExample)).toBool

/-- Spider-shaped `WHERE e [NOT] IN (SELECT …)` queries (step 6b) have the shape of
    `elabStmt_correct_inSub` and elaborate under the folding schema. -/
def inSubSpider (sql : String) : Bool :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok stmt => inSubShape stmt && (elabStmt singerSchema stmt).toBool
  | .error _ => false

#guard inSubSpider "SELECT name FROM singer WHERE singer_id NOT IN (SELECT singer_id FROM song)"
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id IN (SELECT T1.singer_id FROM " ++
  "singer AS T1 JOIN song AS T2 ON T1.singer_id = T2.singer_id WHERE T1.age > 20)")
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN (SELECT singer_id FROM song) " ++
  "ORDER BY name LIMIT 2")
-- outside `inSubShape`: an aggregate or DISTINCT outer query (their own shapes), and a body
-- that is not a `BodyOk` statement (DISTINCT, an aggregate body with LIMIT)
#guard inSubSpider ("SELECT name FROM singer WHERE age > 20 AND singer_id NOT IN " ++
  "(SELECT singer_id FROM song)")
-- step 6c: the node on either side of `AND`, over a body of aggregates, and scalar subqueries
-- on the right of a comparison (Spider's `WHERE age > (SELECT avg(age) …)` is next: `AVG`)
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song) AND age > 20")
#guard inSubSpider "SELECT name FROM singer WHERE singer_id NOT IN (SELECT max(singer_id) FROM song)"
#guard inSubSpider "SELECT name FROM singer WHERE age = (SELECT max(age) FROM singer)"
#guard inSubSpider ("SELECT name FROM singer WHERE age > 20 AND " ++
  "age < (SELECT max(age) FROM singer WHERE age < 50) ORDER BY name")
#guard inSubSpider ("SELECT T1.name FROM singer AS T1 JOIN song AS T2 ON T1.singer_id = T2.singer_id " ++
  "WHERE T1.age = (SELECT min(age) FROM singer) AND T2.title = 'x'")
#guard inSubSpider "SELECT name FROM singer WHERE age >= (SELECT age FROM singer WHERE name = 'a')"
-- outside: the node on the left of the comparison or under arithmetic, two nodes, an `AVG`,
-- `GROUP BY` or `LIMIT` body, and OR
#guard !inSubSpider "SELECT name FROM singer WHERE (SELECT max(age) FROM singer) = age"
#guard !inSubSpider "SELECT name FROM singer WHERE age = (SELECT max(age) FROM singer) - 1"
#guard !inSubSpider ("SELECT name FROM singer WHERE age > (SELECT min(age) FROM singer) AND " ++
  "age < (SELECT max(age) FROM singer)")
-- an `AVG` body: compared with a column or an integer literal (`AvgWhere`; the theorem also
-- takes the size bound `AvgBound`)
#guard inSubSpider "SELECT name FROM singer WHERE age > (SELECT avg(age) FROM singer)"
#guard inSubSpider ("SELECT name FROM singer WHERE name = 'a' AND " ++
  "30 <= (SELECT avg(age) FROM singer WHERE age > 20)")
#guard !inSubSpider "SELECT name FROM singer WHERE age + 1 > (SELECT avg(age) FROM singer)"
#guard !inSubSpider "SELECT name FROM singer WHERE 1.5 > (SELECT avg(age) FROM singer)"
#guard !inSubSpider "SELECT name FROM singer WHERE age > (SELECT avg(DISTINCT age) FROM singer)"
#guard !inSubSpider "SELECT name FROM singer WHERE age IN (SELECT avg(age) FROM singer)"
-- #411: a body that picks a row with `ORDER BY … LIMIT 1`: plain (the key need not be
-- selected) or grouped (ordered by an aggregate), as in Spider's car_1 and dog_kennels
#guard inSubSpider ("SELECT name FROM singer WHERE age = " ++
  "(SELECT age FROM singer ORDER BY age LIMIT 1)")
#guard inSubSpider ("SELECT name FROM singer WHERE age > " ++
  "(SELECT age FROM singer ORDER BY singer_id DESC LIMIT 1)")
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id = " ++
  "(SELECT singer_id FROM song GROUP BY singer_id ORDER BY count(*) ASC LIMIT 1)")
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id IN " ++
  "(SELECT singer_id FROM song ORDER BY title LIMIT 2 OFFSET 1)")
-- outside: a sort key that is an expression, an aggregate body with `LIMIT`, a grouped body
-- sorted by an `AVG`
#guard !inSubSpider ("SELECT name FROM singer WHERE age = " ++
  "(SELECT age FROM singer ORDER BY age + 1 LIMIT 1)")
#guard !inSubSpider ("SELECT name FROM singer WHERE age = " ++
  "(SELECT max(age) FROM singer LIMIT 1)")
#guard !inSubSpider ("SELECT name FROM singer WHERE singer_id = " ++
  "(SELECT singer_id FROM song GROUP BY singer_id ORDER BY avg(singer_id) LIMIT 1)")
#guard !inSubSpider ("SELECT name FROM singer WHERE age > 20 OR singer_id NOT IN " ++
  "(SELECT singer_id FROM song)")
#guard !inSubSpider "SELECT count(*) FROM singer WHERE singer_id NOT IN (SELECT singer_id FROM song)"
#guard !inSubSpider ("SELECT name, count(*) FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song)")
#guard !inSubSpider ("SELECT DISTINCT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song)")
#guard !inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT DISTINCT singer_id FROM song)")
-- a set-operation body under `IN` (#410, `SubBodyOk`), as in Spider's flight_2 query; the
-- membership does not depend on the order of the body's rows
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song UNION SELECT age FROM singer)")
#guard inSubSpider ("SELECT name FROM singer WHERE age > 20 AND singer_id IN " ++
  "(SELECT singer_id FROM song WHERE title = 'x' INTERSECT SELECT singer_id FROM singer " ++
  "EXCEPT SELECT max(age) FROM singer)")
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id IN " ++
  "(SELECT singer_id FROM song UNION ALL SELECT singer_id FROM song GROUP BY singer_id)")
-- outside: a branch that is not a body (DISTINCT, an `AVG` item, a non-key column), and a
-- set operation as a scalar subquery (its value is the first row, whose order is not related)
#guard !inSubSpider ("SELECT name FROM singer WHERE singer_id IN " ++
  "(SELECT singer_id FROM song UNION SELECT DISTINCT age FROM singer)")
#guard !inSubSpider ("SELECT name FROM singer WHERE age IN " ++
  "(SELECT age FROM singer UNION SELECT avg(age) FROM singer)")
#guard !inSubSpider ("SELECT name FROM singer WHERE singer_id IN " ++
  "(SELECT singer_id FROM song UNION SELECT singer_id FROM song GROUP BY title)")
#guard !inSubSpider ("SELECT name FROM singer WHERE age = " ++
  "(SELECT max(age) FROM singer UNION SELECT min(age) FROM singer)")
-- a grouped body (#409, `BodyOk.grouped`): item columns all keys, an optional `HAVING`
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song GROUP BY singer_id)")
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song GROUP BY singer_id HAVING count(*) > 1)")
#guard inSubSpider ("SELECT name FROM singer WHERE age > 20 AND singer_id IN " ++
  "(SELECT singer_id FROM song WHERE title = 'x' GROUP BY singer_id HAVING max(title) >= 'a')")
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id IN " ++
  "(SELECT count(*) FROM song GROUP BY singer_id)")
-- with `ORDER BY` or `LIMIT` too, since #411
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song GROUP BY singer_id ORDER BY count(*))")
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song GROUP BY singer_id LIMIT 1)")
-- outside: a bare (non-key) column, an `AVG` item, an `AVG` comparison in `HAVING`, or
-- `HAVING` without `GROUP BY`
#guard !inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song GROUP BY title)")
#guard !inSubSpider ("SELECT name FROM singer WHERE age IN " ++
  "(SELECT avg(singer_id) FROM song GROUP BY title)")
#guard !inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song GROUP BY singer_id HAVING avg(singer_id) > 1)")
#guard !inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT max(singer_id) FROM song HAVING count(*) > 1)")
-- a plain body with `LIMIT` (#411)
#guard inSubSpider ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song LIMIT 1)")
-- a correlated subquery has the shape but does not elaborate
#guard !inSubSpider ("SELECT name FROM singer WHERE singer_id IN " ++
  "(SELECT singer_id FROM song WHERE title = name)")
-- the coverage report agrees on each (`featuresSqlite` says "disagrees" otherwise)
#guard featuresSqlite "SELECT name FROM singer WHERE singer_id NOT IN (SELECT singer_id FROM song)" == []
#guard featuresSqlite ("SELECT name FROM singer WHERE age > 20 AND singer_id NOT IN " ++
  "(SELECT singer_id FROM song)") == []
#guard featuresSqlite ("SELECT DISTINCT name FROM singer WHERE age > 20 AND singer_id NOT IN " ++
  "(SELECT singer_id FROM song)") == []
#guard featuresSqlite ("SELECT count(*) FROM singer WHERE age > 20 AND singer_id IN " ++
  "(SELECT singer_id FROM song)") == []
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song) AND age > 20") == []
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song GROUP BY singer_id HAVING count(*) > 1)") == []
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song UNION SELECT age FROM singer)") == []
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id IN " ++
  "(SELECT singer_id FROM song UNION SELECT DISTINCT age FROM singer)") ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT name FROM singer WHERE age = " ++
  "(SELECT max(age) FROM singer UNION SELECT min(age) FROM singer)") ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id IN " ++
  "(SELECT count(*) FROM song GROUP BY singer_id)") == []
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song GROUP BY title)") == [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song GROUP BY singer_id HAVING avg(singer_id) > 1)") ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song GROUP BY singer_id ORDER BY count(*))") == []
#guard featuresSqlite ("SELECT count(*) FROM singer WHERE age > " ++
  "(SELECT age FROM singer ORDER BY singer_id DESC LIMIT 1)") == []
#guard featuresSqlite ("SELECT name FROM singer WHERE age = " ++
  "(SELECT age FROM singer ORDER BY age + 1 LIMIT 1)") != []
#guard featuresSqlite ("SELECT name FROM singer WHERE age = " ++
  "(SELECT max(age) FROM singer LIMIT 1)") != []
#guard featuresSqlite ("SELECT name FROM singer WHERE age > 20 OR singer_id NOT IN " ++
  "(SELECT singer_id FROM song)") == [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT DISTINCT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song) LIMIT 1") != []
#guard featuresSqlite ("SELECT name FROM singer WHERE age + 1 = 2 AND singer_id NOT IN " ++
  "(SELECT singer_id FROM song)") == [SqlBridge.Coverage.arithmetic]
#guard featuresSqlite ("SELECT name FROM singer WHERE name LIKE 'A%' AND singer_id NOT IN " ++
  "(SELECT singer_id FROM song)") == []
-- under aggregates without GROUP BY (`elabStmt_correct_agg_inSub`), also next to an AVG or a
-- bare column (`elabStmt_correct_aggBare_inSub`), and with GROUP BY
-- (`elabStmt_correct_grouped_inSub`): inside
#guard featuresSqlite ("SELECT count(*) FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song)") == []
#guard featuresSqlite ("SELECT min(age), count(DISTINCT name) FROM singer WHERE singer_id IN " ++
  "(SELECT singer_id FROM song WHERE title = 'x')") == []
#guard featuresSqlite ("SELECT avg(age) FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song)") == []
#guard featuresSqlite ("SELECT name, count(*) FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song)") == []
#guard featuresSqlite ("SELECT name, count(*) FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song) GROUP BY name") == []
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT DISTINCT singer_id FROM song)") == [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT max(singer_id) FROM song)") == []
-- scalar subqueries (step 6c): on the right of a comparison, a body of plain items or of
-- aggregates other than `AVG`; under `DISTINCT` and aggregates as the `IN` clauses are
#guard featuresSqlite "SELECT name FROM singer WHERE age = (SELECT max(age) FROM singer)" == []
#guard featuresSqlite ("SELECT DISTINCT name FROM singer WHERE age > 20 AND " ++
  "age < (SELECT max(age) FROM singer)") == []
#guard featuresSqlite "SELECT count(*) FROM singer WHERE age > (SELECT min(age) FROM singer)" == []
#guard featuresSqlite ("SELECT name FROM singer WHERE age > (SELECT avg(age) FROM singer)") == []
#guard featuresSqlite ("SELECT count(*), name FROM singer WHERE age > (SELECT avg(age) FROM singer) " ++
  "GROUP BY name") == []
#guard featuresSqlite ("SELECT DISTINCT name FROM singer WHERE age < (SELECT avg(age) FROM singer)") == []
#guard featuresSqlite ("SELECT name FROM singer WHERE 1.5 > (SELECT avg(age) FROM singer)") ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT name FROM singer WHERE age IN (SELECT avg(age) FROM singer)") ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT name FROM singer WHERE age > (SELECT avg(age) FROM singer LIMIT 1)") != []
#guard featuresSqlite ("SELECT name FROM singer WHERE (SELECT max(age) FROM singer) = age") ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT name FROM singer WHERE age = (SELECT max(age) FROM singer) " ++
  "GROUP BY name") == []
#guard featuresSqlite ("SELECT name FROM singer WHERE age = (SELECT max(age) FROM singer) " ++
  "GROUP BY name HAVING max(age + 1) > 2") != []
#guard featuresSqlite ("SELECT name FROM singer WHERE age + 1 = 2 AND " ++
  "age = (SELECT max(age) FROM singer)") == [SqlBridge.Coverage.arithmetic]
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id NOT IN " ++
  "(SELECT singer_id FROM song WHERE singer_id + 1 = 2)") == [SqlBridge.Coverage.arithmetic]
-- (parenthesised: the parser reads `a + 1 NOT IN (…)` as `a + (1 NOT IN (…))`, #400)
#guard featuresSqlite ("SELECT name FROM singer WHERE (singer_id + 1) NOT IN " ++
  "(SELECT singer_id FROM song)") == [SqlBridge.Coverage.arithmetic]

/-! ### A derived table under `COUNT(*)` (#412, `elabStmt_correct_countDerived`) -/

/-- The statement has the theorem's shape and elaborates under the Spider-style schema. -/
def countDerivedSpider (sql : String) : Bool :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok stmt => countDerivedShape stmt && (elabStmt singerSchema stmt).toBool
  | .error _ => false

-- inside: Spider's world_1 query (an anonymous derived table over `INTERSECT`), an aliased one,
-- a plain, an aggregate and a grouped body, several `COUNT(*)` items
#guard countDerivedSpider ("SELECT count(*) FROM (SELECT T1.name FROM singer AS T1 JOIN song AS T2 " ++
  "ON T1.singer_id = T2.singer_id WHERE T2.title = 'x' INTERSECT SELECT T1.name FROM singer AS T1 " ++
  "JOIN song AS T2 ON T1.singer_id = T2.singer_id WHERE T2.title = 'y')")
#guard countDerivedSpider "SELECT count(*) FROM (SELECT name FROM singer) AS t"
#guard countDerivedSpider "SELECT COUNT(*) AS n, count(*) FROM (SELECT age FROM singer WHERE age > 20)"
#guard countDerivedSpider "SELECT count(*) FROM (SELECT max(age) FROM singer)"
#guard countDerivedSpider "SELECT count(*) FROM (SELECT singer_id FROM song GROUP BY singer_id)"
#guard countDerivedSpider ("SELECT count(*) FROM (SELECT singer_id FROM song UNION ALL " ++
  "SELECT age FROM singer EXCEPT SELECT singer_id FROM singer)")
#guard countDerivedSpider "SELECT count(*) FROM (SELECT name FROM singer ORDER BY age LIMIT 2)"
-- outside: an item other than `COUNT(*)`, a `WHERE`, a derived table under a join, a body
-- outside `SubBodyOk` (`DISTINCT`, an `AVG` item), `GROUP BY` outside, nested derived tables
#guard !countDerivedSpider "SELECT count(name) FROM (SELECT name FROM singer)"
#guard !countDerivedSpider "SELECT max(age) FROM (SELECT age FROM singer)"
#guard !countDerivedSpider "SELECT count(*) FROM (SELECT age FROM singer) WHERE age > 1"
#guard !countDerivedSpider "SELECT count(*) FROM (SELECT age FROM singer) AS t JOIN song AS s ON t.age = s.singer_id"
#guard !countDerivedSpider "SELECT count(*) FROM (SELECT DISTINCT age FROM singer)"
#guard !countDerivedSpider "SELECT count(*) FROM (SELECT avg(age) FROM singer)"
#guard !countDerivedSpider "SELECT count(*) FROM (SELECT age FROM singer) GROUP BY age"
#guard !countDerivedSpider "SELECT count(*) FROM (SELECT count(*) FROM (SELECT age FROM singer))"
#guard !countDerivedSpider "SELECT name FROM (SELECT name FROM singer)"
-- the coverage report agrees on each
#guard featuresSqlite ("SELECT count(*) FROM (SELECT name FROM singer INTERSECT " ++
  "SELECT title FROM song)") == []
#guard featuresSqlite "SELECT count(*) FROM (SELECT name FROM singer) AS t" == []
#guard featuresSqlite "SELECT count(*) FROM (SELECT singer_id FROM song GROUP BY singer_id)" == []
#guard featuresSqlite "SELECT count(*) FROM (SELECT age + 1 FROM singer)" ==
  [SqlBridge.Coverage.arithmetic]
#guard featuresSqlite "SELECT count(name) FROM (SELECT name FROM singer)" ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite "SELECT count(*) FROM (SELECT age FROM singer) WHERE age > 1" ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite "SELECT count(*) FROM (SELECT DISTINCT age FROM singer)" ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite "SELECT count(*) FROM (SELECT avg(age) FROM singer)" ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite "SELECT count(*) FROM (SELECT count(*) FROM (SELECT age FROM singer))" ==
  [SqlBridge.Coverage.subquery]
#guard featuresSqlite "SELECT name FROM (SELECT name FROM singer)" ==
  [SqlBridge.Coverage.subquery]
-- only at the top of a statement: not as a subquery body or a set-operation branch
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id IN " ++
  "(SELECT count(*) FROM (SELECT age FROM singer))") == [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT count(*) FROM (SELECT age FROM singer) " ++
  "UNION SELECT age FROM singer") == [SqlBridge.Coverage.subquery]
-- nor a body or branch with a subquery in its `WHERE` (`BodyOk` and `Leaf` take fragment
-- `WHERE`s; the report used to count these inside)
#guard featuresSqlite ("SELECT count(*) FROM (SELECT name FROM singer WHERE singer_id IN " ++
  "(SELECT singer_id FROM song))") == [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT count(*) FROM (SELECT name FROM singer WHERE age > " ++
  "(SELECT min(age) FROM singer))") == [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT name FROM singer WHERE age IN (SELECT name FROM singer WHERE " ++
  "singer_id IN (SELECT singer_id FROM song))") == [SqlBridge.Coverage.subquery]
#guard featuresSqlite ("SELECT name FROM singer WHERE singer_id IN (SELECT singer_id FROM song) " ++
  "UNION SELECT name FROM singer") == [SqlBridge.Coverage.subquery]

end SqlCoreTest.CorrectExamples
