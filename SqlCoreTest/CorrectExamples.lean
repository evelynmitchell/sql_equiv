/-
  Elaborator correctness (#309): the theorem `SqlBridge.Correct.elabStmt_correct` is not vacuous on
  the bridge test schema. Its hypotheses about names hold (`WellNamed`), and parsed queries of the
  corpus are in the fragment and elaborate.
-/
import SqlBridge.Correct
import SqlCoreTest.BridgeDiffTest

namespace SqlCoreTest.CorrectExamples
open SqlBridge SqlBridge.Correct SqlCoreTest.BridgeDiff

/-- The test schema's column names have no dots and are distinct ignoring case. -/
example : WellNamed named :=
  ⟨fun T => by cases T <;> decide, fun T => by cases T <;> decide +kernel⟩

example : named.fold = id := rfl

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

end SqlCoreTest.CorrectExamples
