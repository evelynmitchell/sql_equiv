/-
  Elaborator correctness (#309): the theorem `SqlBridge.Correct.elabStmt_correct` is not vacuous on
  the bridge test schema. Its hypotheses about names hold (`WellNamed`), and parsed queries of the
  corpus are in the fragment and elaborate.
-/
import SqlBridge.Correct
import SqlBridge.Coverage
import SqlBridge.Spider
import SqlCoreTest.BridgeDiffTest

namespace SqlCoreTest.CorrectExamples
open SqlBridge SqlBridge.Correct SqlCoreTest.BridgeDiff

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

/-- `SqlBridge.Coverage.outsideFragment` (the Spider coverage report, #352) finds no feature
    outside the fragment exactly when the statement has the theorem's shape. -/
def coverageAgrees (sql : String) : Bool :=
  match SqlEquiv.parse sql with
  | .ok stmt@(.query (.simple (.mk false items (some (.table ⟨name, al⟩)) wh [] none [] none none))) =>
    let shape := itemsFragment items && wh.all isFragment && stmt == fragmentStmt items name al wh
    let none' := (SqlBridge.Coverage.outsideFragment stmt).isEmpty
    none' == shape
  | .ok stmt => SqlBridge.Coverage.outsideFragment stmt != []
  | .error _ => false

#guard [ "SELECT name, age FROM users", "SELECT name FROM users WHERE age > 25",
  "SELECT name FROM users WHERE NOT (age < 30) OR department = 'Sales'",
  "SELECT u.name FROM users u WHERE u.age = 30", "SELECT name, age >= 30, NULL FROM users WHERE TRUE",
  "SELECT age + 1 FROM users", "SELECT * FROM users", "SELECT DISTINCT name FROM users",
  "SELECT u.name FROM users u JOIN orders o ON u.id = o.user_id",
  "SELECT name FROM users ORDER BY age LIMIT 2", "SELECT COUNT(*) FROM users",
  "SELECT department FROM users GROUP BY department", "SELECT name FROM users WHERE age IS NULL",
  "SELECT name FROM users WHERE age IN (1, 2)", "SELECT name FROM users WHERE age BETWEEN 1 AND 2",
  "SELECT name FROM users WHERE name LIKE 'a%'", "SELECT 1",
  "SELECT name FROM users WHERE id IN (SELECT user_id FROM orders)",
  "SELECT name FROM users UNION SELECT product FROM orders" ].all coverageAgrees
#guard SqlBridge.Coverage.outsideFragment
  (match SqlEquiv.parse "SELECT name FROM users ORDER BY age LIMIT 2" with
   | .ok s => s | .error _ => .query (.simple default)) == ["ORDER BY/LIMIT"]

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

end SqlCoreTest.CorrectExamples
