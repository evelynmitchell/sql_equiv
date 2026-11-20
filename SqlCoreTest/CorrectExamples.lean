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
import SqlBridge.Coverage
import SqlBridge.Spider
import SqlCoreTest.BridgeDiffTest

namespace SqlCoreTest.CorrectExamples
open SqlBridge SqlBridge.Correct SqlCoreTest.BridgeDiff
open SqlBridge.CorrectOrder (itemsNamed outName)
open SqlBridge.CorrectJoin (fromFragment joinStmt)
open SqlBridge.CorrectAgg (aggItems aggStmt itemExpr)
open SqlBridge.CorrectGroup (groupItems groupStmt havingFragment colRefs)
open SqlBridge.CorrectGrouped (groupedItems groupedStmt isMinMax)
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

/-- The shape of `elabStmt_correct_join` (roadmap steps 1 and 2, #352): fragment items, `FROM`
    (tables under inner and cross joins), `WHERE`; `ORDER BY` keys that are column references;
    named items when there is an `ORDER BY`. -/
def stmtShape : SqlEquiv.Stmt → Bool
  | stmt@(.query (.simple (.mk false items (some f) wh [] none orderBy lim off))) =>
    itemsFragment items && fromFragment f && wh.all isFragment &&
      orderBy.all (fun o => match o.expr with | .col _ => true | _ => false) &&
      (orderBy.isEmpty || itemsNamed items) && stmt == joinStmt items f wh orderBy lim off
  | _ => false

/-- The shape of `elabStmt_correct_agg` (roadmap step 3a): aggregates only, no `GROUP BY`. -/
def aggShape : SqlEquiv.Stmt → Bool
  | stmt@(.query (.simple (.mk false items (some f) wh [] none [] none none))) =>
    aggItems items && !items.isEmpty && fromFragment f && wh.all isFragment &&
      stmt == aggStmt items f wh
  | _ => false

/-- The shape of `elabStmt_correct_grouped` (roadmap steps 3b-1 to 3b-5): column keys, items
    aggregates or columns, an optional `HAVING` in `havingFragment`, `ORDER BY` aggregates, an
    optional `LIMIT`/`OFFSET`; with sort keys, no output name dotted or starting with
    `__group_orderkey_` (ignoring case); with a bare column (an item column not grouped), no
    `MIN`/`MAX` anywhere, or exactly one, not DISTINCT, in a mode that picks a row (`BareOk`). -/
def groupedShape : SqlEquiv.Stmt → Bool
  | stmt@(.query (.simple (.mk false items (some f) wh groupBy having orderBy lim off))) =>
    groupedItems items && !groupBy.isEmpty &&
      groupBy.all (fun | .col _ => true | _ => false) && fromFragment f && wh.all isFragment &&
      having.all (havingFragment groupBy) && orderBy.all (fun o => aggFragment o.expr) &&
      (orderBy.isEmpty || items.all (fun it => decide ('.' ∉ (outName it).toList) &&
        !"__group_orderkey_".toList.isPrefixOf (outName it).toLower.toList)) &&
      ((colRefs items).all (fun c => groupBy.contains (.col c)) ||
        (items.all (fun it => (SqlEquiv.minMaxCalls (itemExpr it)).isEmpty) &&
          having.all (fun h => (SqlEquiv.minMaxCalls h).isEmpty) &&
          orderBy.all (fun o => (SqlEquiv.minMaxCalls o.expr).isEmpty)) ||
        (match SqlEquiv.selectMinMaxCalls items having with
         | [(w, m, some arg, false)] =>
           m.bareRow && ((items.map itemExpr).filter aggFragment ++ aggsOfOpt having ++
             orderBy.map SqlEquiv.OrderByItem.expr).eraseDups.filter isMinMax ==
               [.agg (if w then .max m else .min m) (some arg) false]
         | _ => false)) &&
      stmt == groupedStmt items f wh groupBy having orderBy lim off
  | _ => false

/-- `SqlBridge.Coverage.outsideFragment` (the Spider coverage report, #352) finds no feature
    outside the fragment exactly when the statement has the theorem's shape, and its copy of
    `itemsNamed` agrees with the theorem's. -/
def coverageAgrees (sql : String) : Bool :=
  match SqlEquiv.parse sql with
  | .ok stmt =>
    (SqlBridge.Coverage.outsideFragment stmt).isEmpty ==
      (stmtShape stmt || aggShape stmt || groupedShape stmt) &&
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
  "SELECT name FROM users UNION SELECT product FROM orders ORDER BY 1 LIMIT 3" ].all coverageAgrees

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
#guard features "SELECT AVG(age) FROM users" == ["AVG", "aggregate/GROUP BY"]
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
    if fs.isEmpty == (stmtShape s || aggShape s || groupedShape s) then fs else ["disagrees"]
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
-- Outside: a key column as sort key, `AVG`, a `HAVING` column that is no key; a bare column next
-- to two `MIN`/`MAX` calls, or to one with DISTINCT
#guard !groupedSpider "SELECT age FROM singer GROUP BY age ORDER BY age"
#guard !groupedSpider "SELECT age FROM singer GROUP BY age ORDER BY avg(singer_id)"
#guard !groupedSpider "SELECT age FROM singer GROUP BY age HAVING name = 'x'"
#guard !groupedSpider "SELECT name, max(age), min(age) FROM singer GROUP BY singer_id"
#guard !groupedSpider "SELECT name, max(DISTINCT age) FROM singer GROUP BY singer_id"
#guard !groupedSpider "SELECT name, max(age) FROM singer GROUP BY age ORDER BY min(singer_id)"

end SqlCoreTest.CorrectExamples
