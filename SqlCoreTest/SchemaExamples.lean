/-
  Typed core phase 2 (#291): rows, column resolution and schemas.

  * Kernel-checked examples of `resolveColumn`, including ambiguity and exact
    (case-sensitive) names (decision 7).
  * "Done when" of #291: the `SqlEquiv` test database `SemanticsTest.testDb`
    written as a `DbSchema` and an instance, with conformance proved by
    `decide`. `SqlCoreTest.SchemaDiffTest` checks at run time that this
    transcription has the same rows as the original.
-/
import SqlCore

namespace SqlCoreTest.SchemaExamples
open SqlCore

/-! ### Column resolution -/

/-- The columns of `users u JOIN orders o`, trimmed. -/
def joinCols : Fin 4 → Column :=
  ![⟨some "u", "id", .int⟩, ⟨some "u", "name", .text⟩,
    ⟨some "o", "id", .int⟩, ⟨some "o", "user_id", .int⟩]

example : resolveColumn joinCols none "name" = .ok 1 := by decide
example : resolveColumn joinCols (some "o") "id" = .ok 2 := by decide
-- `id` is in both tables: ambiguous unqualified (SqlEquiv takes the first match)
example : resolveColumn joinCols none "id" = .error .ambiguousColumn := by decide
example : resolveColumn joinCols (some "x") "id" = .error .unknownColumn := by decide
-- exact names: case is the parser's job (SqlEquiv matches case-insensitively)
example : resolveColumn joinCols none "NAME" = .error .unknownColumn := by decide

/-! ### Rows -/

example : Row.Conforms ![.int, .text] ![some (.int 1), none] := by decide
example : ¬ Row.Conforms ![.int, .text] ![some (.text "1"), none] := by decide
example : Row.Conforms (Fin.append ![SqlType.int] ![SqlType.bool])
    (Fin.append ![some (.int 1)] ![some (.bool true)]) := by decide

/-! ### `SemanticsTest.testDb` in the new types -/

/-- The tables of `SemanticsTest.testDb`. -/
inductive T where
  | users | orders | products | items | singer | museum
  deriving DecidableEq, Repr

-- `deriving Fintype` fails at this Mathlib pin (its generated proof has a
-- `Multiset` coercion mismatch), so the instance is written out.
instance : Fintype T :=
  Fintype.ofList [.users, .orders, .products, .items, .singer, .museum] (by intro x; cases x <;> decide)

/-- Unqualified-free column declarations: each column is qualified by its table. -/
def cols (q : String) (cs : List (String × SqlType)) : Fin cs.length → Column :=
  fun i => ⟨some q, cs[i].1, cs[i].2⟩

def decls : T → List (String × SqlType)
  | .users => [("id", .int), ("name", .text), ("age", .int), ("department", .text)]
  | .orders => [("id", .int), ("user_id", .int), ("amount", .int), ("product", .text)]
  | .products => [("id", .int), ("name", .text), ("price", .int)]
  | .items => [("id", .int), ("name", .text), ("price", .decimal)]
  | .singer => [("Singer_ID", .int), ("Name", .text), ("Country", .text), ("Age", .int)]
  | .museum => [("name", .text), ("staff", .int)]

def tableName : T → String
  | .users => "users" | .orders => "orders" | .products => "products"
  | .items => "items" | .singer => "singer" | .museum => "museum"

def schema : DbSchema where
  Table := T
  arity t := (decls t).length
  columns t := cols (tableName t) (decls t)

instance : Fintype schema.Table := inferInstanceAs (Fintype T)

private def i (z : Int) : Datum := some (.int z)
private def s (x : String) : Datum := some (.text x)
private def d (q : ℚ) : Datum := some (.decimal q)

def db : Database schema
  | .users => [![i 1, s "Alice", i 30, s "Engineering"], ![i 2, s "Bob", i 25, s "Sales"],
      ![i 3, s "Carol", i 35, s "Engineering"], ![i 4, s "Dave", i 28, s "Marketing"],
      ![i 5, s "Eve", i 22, s "Sales"]]
  | .orders => [![i 1, i 1, i 100, s "Widget"], ![i 2, i 1, i 200, s "Gadget"],
      ![i 3, i 2, i 150, s "Widget"], ![i 4, i 3, i 300, s "Gizmo"]]
  | .products => [![i 1, s "Widget", i 50], ![i 2, s "Gadget", i 100], ![i 3, s "Gizmo", i 150]]
  | .items => [![i 1, s "Bolt", d (5/2)], ![i 2, s "Nut", d (5/4)], ![i 3, s "Washer", d 3],
      ![i 4, s "Shim", none]]
  | .singer => [![i 1, s "Joe", s "France", i 52], ![i 2, s "Tribal King", s "France", i 25],
      ![i 3, s "Rose White", s "UK", i 18]]
  | .museum => [![s "m1", i 9], ![s "m2", i 17], ![s "m3", none], ![s "m4", i 25],
      ![s "m5", i 41], ![s "m6", none]]

/-- The instance conforms to its schema (every cell has its declared type). -/
theorem db_conforms : db.Conforms := by decide

/-- A schema with an empty table still has columns; the empty instance conforms. -/
example : (Database.Conforms (S := schema) fun _ => []) := Database.conforms_empty

/-- A wrong-typed cell breaks conformance. -/
example : ¬ (Database.Conforms (S := schema) fun t =>
    match t with
    | .museum => [![s "m1", s "nine"]]
    | _ => []) := by decide

-- Resolution against a schema's table
example : resolveColumn (schema.columns .singer) none "Age" = .ok ⟨3, by decide⟩ := by decide
example : resolveColumn (schema.columns .singer) none "age" = .error .unknownColumn := by decide

end SqlCoreTest.SchemaExamples
