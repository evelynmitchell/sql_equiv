/-
  Typed core phase 2 (#291): the transcription of `SemanticsTest.testDb` in
  `SqlCoreTest.SchemaExamples` has exactly the original rows.

  Each typed row is turned back into `SqlEquiv`'s name–value form with the
  schema's column names, and compared with the original table. Typed NULLs
  (`.null (some τ)`) are compared as untyped: the type now lives in the schema.
-/
import SqlCoreTest.SchemaExamples
import SqlCoreTest.ScalarDiffTest
import Test.SemanticsTest

namespace SqlCoreTest.SchemaDiff
open SqlCore SqlCoreTest.SchemaExamples

def eraseNullType : SqlEquiv.Value → SqlEquiv.Value
  | .null _ => .null none
  | v => v

def toOldRow {n : ℕ} (cols : Fin n → Column) (r : Row n) : SqlEquiv.Row :=
  (List.finRange n).map fun j =>
    ((cols j).name, (SqlCoreTest.ScalarDiff.datumToOld (r j)).getD (.null none))

def tables : List T := [.users, .orders, .products, .items, .singer, .museum]

/-- Tables whose transcription differs from the original, with a message. -/
def mismatches : List String :=
  tables.filterMap fun t =>
    let new := (db t).map (toOldRow (schema.columns t))
    let old := (SemanticsTest.testDb (tableName t)).map (·.map fun (k, v) => (k, eraseNullType v))
    if new == old then none else some s!"{tableName t}: {repr new} vs {repr old}"

end SqlCoreTest.SchemaDiff
