/-
  Elaborator correctness (#309): the theorem `SqlBridge.Correct.elabStmt_correct` is not vacuous on
  the bridge test schema. Its hypotheses about names hold (`WellNamed`), and parsed queries of the
  corpus are in the fragment and elaborate.
-/
import SqlBridge.Correct
import SqlBridge.CorrectOrder
import SqlBridge.Coverage
import SqlBridge.Spider
import SqlCoreTest.BridgeDiffTest

namespace SqlCoreTest.CorrectExamples
open SqlBridge SqlBridge.Correct SqlCoreTest.BridgeDiff
open SqlBridge.CorrectOrder (orderedStmt itemsNamed)

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

-- Outside the fragment: arithmetic, `*`, `DISTINCT`, joins.
#guard !inFragment "SELECT age + 1 FROM users"
#guard !inFragment "SELECT * FROM users"
#guard !inFragment "SELECT DISTINCT name FROM users"
#guard !inFragment "SELECT u.name FROM users u JOIN orders o ON u.id = o.user_id"

/-- The shape of `elabStmt_correct_ordered` (roadmap step 1, #352): fragment items and `WHERE`,
    `ORDER BY` keys that are column references, named items when there is an `ORDER BY`. -/
def orderedShape : SqlEquiv.Stmt → Bool
  | stmt@(.query (.simple (.mk false items (some (.table ⟨name, al⟩)) wh [] none orderBy lim off))) =>
    itemsFragment items && wh.all isFragment &&
      orderBy.all (fun o => match o.expr with | .col _ => true | _ => false) &&
      (orderBy.isEmpty || itemsNamed items) && stmt == orderedStmt items name al wh orderBy lim off
  | _ => false

/-- `SqlBridge.Coverage.outsideFragment` (the Spider coverage report, #352) finds no feature
    outside the fragment exactly when the statement has the theorem's shape, and its copy of
    `itemsNamed` agrees with the theorem's. -/
def coverageAgrees (sql : String) : Bool :=
  match SqlEquiv.parse sql with
  | .ok stmt =>
    (SqlBridge.Coverage.outsideFragment stmt).isEmpty == orderedShape stmt &&
      match stmt with
      | .query (.simple s) => SqlBridge.Coverage.itemsNamed s.items == itemsNamed s.items
      | _ => true
  | .error _ => false

#guard [ "SELECT name, age FROM users", "SELECT name FROM users WHERE age > 25",
  "SELECT name FROM users WHERE NOT (age < 30) OR department = 'Sales'",
  "SELECT u.name FROM users u WHERE u.age = 30", "SELECT name, age >= 30, NULL FROM users WHERE TRUE",
  "SELECT age + 1 FROM users", "SELECT * FROM users", "SELECT DISTINCT name FROM users",
  "SELECT u.name FROM users u JOIN orders o ON u.id = o.user_id",
  "SELECT name FROM users ORDER BY age LIMIT 2", "SELECT name FROM users LIMIT 2 OFFSET 1",
  "SELECT name AS n, age FROM users WHERE age > 1 ORDER BY n DESC, age NULLS FIRST",
  "SELECT name FROM users ORDER BY age + 1", "SELECT age > 30 FROM users ORDER BY age",
  "SELECT age > 30 FROM users LIMIT 1", "SELECT COUNT(*) FROM users",
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

/-! ### A Spider-shaped schema (#351)

Spider's schemas (`SqlBridge.Spider.schemaOf`) store names lowercased and fold references with
`String.toLower`, as sqlite's names are case-insensitive. The theorem's hypotheses hold for them:
the fold keeps names equal ignoring case, the names are well formed, and a database that answers
every spelling of a table name alike relates (here an empty one, to show `DbRel` is satisfiable
under folding; `SqlEquiv` looks a table up by the name as written, registry row 20). -/

open SqlBridge.Spider in
def singerSchema : NamedSchema :=
  { schemaOf #[⟨"singer", #[("singer_id", .int), ("name", .text), ("age", .int)]⟩] with
    config := SqlEquiv.Dialect.sqlite.config }

example : ∀ s, (singerSchema.fold s).toLower = s.toLower := string_toLower_toLower

example : WellNamed singerSchema := by
  constructor <;> (simp only [singerSchema, SqlBridge.Spider.schemaOf]; decide +kernel)

example : DbRel singerSchema (fun _ => []) (fun _ => []) := fun _ _ _ => .nil

/-- With an `ORDER BY`, `elabStmt_correct_ordered` also asks the fold to identify exactly the
    names equal ignoring case; `String.toLower` does. -/
example : ∀ x y, singerSchema.fold x = singerSchema.fold y ↔ x.toLower = y.toLower :=
  fun _ _ => Iff.rfl

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

/-- Spider-shaped queries with `ORDER BY` / `LIMIT` / `OFFSET` (roadmap step 1) have the shape
    of `elabStmt_correct_ordered` and elaborate under the folding schema. -/
def orderedSpider (sql : String) : Bool :=
  match SqlEquiv.parse sql (dialect := .sqlite) with
  | .ok stmt => orderedShape stmt && (elabStmt singerSchema stmt).toBool
  | .error _ => false

#guard orderedSpider "SELECT Name FROM Singer ORDER BY Age DESC LIMIT 1"
#guard orderedSpider "SELECT T1.name FROM SINGER AS T1 WHERE T1.age > 20 ORDER BY t1.AGE, T1.Name"
#guard orderedSpider "SELECT name AS n FROM singer ORDER BY n LIMIT 3 OFFSET 1"
#guard orderedSpider "SELECT name, age FROM singer LIMIT 2"
#guard !orderedSpider "SELECT name FROM singer ORDER BY age + 1"

end SqlCoreTest.CorrectExamples
