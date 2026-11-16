/-
  Typed core phase 4 (#293): checked examples of queries.

  The first part is the worked examples of cslib-frontier's
  `CslibFrontierTests/Languages/SQL/Query.lean` (pinned `e78796a1`, by Evelyn
  Mitchell and Samuel Schlesinger), up to its equivalence section (phase 5):
  bag semantics, three-valued `WHERE`, joins with duplicate and `NULL` keys,
  strict errors, typing and safety. Results are compared through
  `Except.toOption` by `decide`, since rows are functions.

  The second part is ours: decimals in queries, and queries over the typed
  `SemanticsTest.testDb` of phase 2 (#293's "done when").
-/
import SqlCoreTest.SchemaExamples

namespace SqlCoreTest.QueryExamples

open SqlCore SqlCore.Query
open SqlCore.Expr (col lit unary binary inList)

namespace Frontier

/-- The tables of the test schema. -/
inductive T where
  | emp
  | dept
  | empty
  deriving DecidableEq

instance : Fintype T where
  elems := {.emp, .dept, .empty}
  complete t := by cases t <;> decide

/-- `emp(name text, dept int)`, `dept(id int, title text)` and `empty(x int, y text)`. -/
abbrev S : DbSchema where
  Table := T
  arity _ := 2
  columns
    | .emp => ![⟨some "emp", "name", .text⟩, ⟨some "emp", "dept", .int⟩]
    | .dept => ![⟨some "dept", "id", .int⟩, ⟨some "dept", "title", .text⟩]
    | .empty => ![⟨some "empty", "x", .int⟩, ⟨some "empty", "y", .text⟩]

/-- The integer literal `z`. -/
abbrev int {n : ℕ} (z : ℤ) : Expr n := lit (.int z)

/-- An instance: `ann` occurs twice in `emp`, `cy` has no department, department `1` occurs twice
in `dept` and one department has a `NULL` id; `empty` has no rows. -/
abbrev D : Database S
  | T.emp => [![some (.text "ann"), some (.int 1)], ![some (.text "bob"), some (.int 1)],
      ![some (.text "cy"), none], ![some (.text "ann"), some (.int 1)]]
  | T.dept => [![some (.int 1), some (.text "eng")], ![some (.int 1), some (.text "ops")],
      ![some (.int 2), some (.text "law")], ![none, some (.text "tmp")]]
  | T.empty => []

abbrev emp : Query S 2 := table T.emp
abbrev dept : Query S 2 := table T.dept
abbrev empty : Query S 2 := table T.empty

theorem hD : D.Conforms := by decide

-- An instance with an integer in a text column does not conform.
example : ¬Database.Conforms (S := S) fun
    | T.emp => [![some (.int 0), none]]
    | _ => [] := by
  decide

/-! ### Bags: duplicates are kept, except by `DISTINCT` -/

-- `SELECT dept FROM emp` keeps one row per employee, duplicates and `NULL` included.
example : ((project ![col 1] emp).eval D).toOption =
    some [![some (.int 1)], ![some (.int 1)], ![none], ![some (.int 1)]] := by
  decide

-- `UNION ALL` keeps the duplicates of both sides.
example : ((unionAll (project ![col 1] emp) (project ![col 0] dept)).eval D).toOption =
    some [![some (.int 1)], ![some (.int 1)], ![none], ![some (.int 1)],
      ![some (.int 1)], ![some (.int 1)], ![some (.int 2)], ![none]] := by
  decide

-- `DISTINCT` keeps one copy of each row; the two `NULL` rows are duplicates of each other.
example : ((distinct (unionAll (project ![col 1] emp) (project ![col 0] dept))).eval D).toOption =
    some [![some (.int 1)], ![some (.int 2)], ![none]] := by
  decide

/-! ### `WHERE` keeps only `TRUE` rows -/

-- `WHERE dept NOT IN (2)` drops `cy`, whose `NULL` department makes the predicate `unknown`.
example : ((select (unary .not (inList (col 1) [some (.int 2)])) emp).eval D).toOption =
    some [![some (.text "ann"), some (.int 1)], ![some (.text "bob"), some (.int 1)],
      ![some (.text "ann"), some (.int 1)]] := by
  decide

-- `WHERE dept NOT IN (2, NULL)` keeps nothing: with a `NULL` in the list, `NOT IN` is never
-- `TRUE`.
example : ((select (unary .not (inList (col 1) [some (.int 2), none])) emp).eval D).toOption =
    some [] := by
  decide

/-! ### Schemas do not depend on data -/

-- The empty table has its declared columns, and every query over it is typed from the schema.
example : empty.typeOf = some ![.int, .text] := by decide
example : (empty.eval D).toOption = some [] := by decide
example : (project ![col 1, col 0] empty).typeOf = some ![.text, .int] := by decide

/-! ### Joins -/

/-- `emp JOIN dept ON emp.dept = dept.id`. -/
abbrev empDept : Query S 4 := join (binary (.cmp .eq) (col 1) (col 2)) emp dept

-- Each employee of department `1` meets both rows with id `1`, so the duplicate `ann` row gives
-- two more; `cy`'s `NULL` key and the `NULL` id match nothing.
example : (empDept.eval D).toOption = some
    [![some (.text "ann"), some (.int 1), some (.int 1), some (.text "eng")],
     ![some (.text "ann"), some (.int 1), some (.int 1), some (.text "ops")],
     ![some (.text "bob"), some (.int 1), some (.int 1), some (.text "eng")],
     ![some (.text "bob"), some (.int 1), some (.int 1), some (.text "ops")],
     ![some (.text "ann"), some (.int 1), some (.int 1), some (.text "eng")],
     ![some (.text "ann"), some (.int 1), some (.int 1), some (.text "ops")]] := by
  decide

-- The cross join is `ON TRUE`: all 4 × 4 pairs.
example : ((join (lit (.bool true)) emp dept).eval D).toOption.map List.length = some 16 := by
  decide

example : empDept.typeOf = some ![SqlType.text, .int, .int, .text] := by decide

/-! ### Errors are strict -/

/-- `SELECT dept / 0 FROM t`. -/
abbrev divZero (t : Query S 2) : Query S 1 := project ![binary (.arith .div) (col 1) (int 0)] t

-- The first row divides by zero, so the whole query fails …
example : (divZero emp).eval D = .error .divisionByZero := rfl
-- … while the same query on an empty table evaluates nothing and succeeds.
example : ((divZero empty).eval D).toOption = some [] := by decide

-- An ill-typed predicate fails on a nonempty input: `name` is text, not boolean.
example : (select (col 0) emp).typeOf = none := by decide
example : (select (col 0) emp).eval D = .error .typeMismatch := rfl

/-! ### Typing and safety -/

-- Type soundness: a well-typed query never raises a type error on a conforming instance, and its
-- rows have its types.
example (D' : Database S) (hD' : D'.Conforms) : empDept.eval D' ≠ .error .typeMismatch :=
  eval_ne_typeMismatch hD' (Γ := ![.text, .int, .int, .text]) (by decide)
example (D' : Database S) (hD' : D'.Conforms) {rs : List (Row 4)} (h : empDept.eval D' = .ok rs) :
    ∀ r ∈ rs, r 1 = none ∨ ∃ z, r 1 = some (.int z) := fun r hr => by
  have hr := conforms_of_eval_eq_ok hD' (Γ := ![.text, .int, .int, .text]) (by decide) h r hr 1
  rcases hd : r 1 with _ | v
  · exact .inl rfl
  · rw [hd] at hr
    obtain ⟨z, rfl⟩ := Value.type_eq_int_iff.mp hr
    exact .inr ⟨z, rfl⟩

-- Safety is decidable and syntactic: division by a nonzero literal is safe, by zero it is not.
example : (project ![binary (.arith .div) (col 1) (int 2)] emp).IsSafe := by decide
example : ¬(divZero emp).IsSafe := by decide
example : ¬(divZero empty).IsSafe := by decide

-- A safe query succeeds on every conforming instance.
example (D' : Database S) (hD' : D'.Conforms) : ∃ rs, (empDept.eval D').toOption = some rs := by
  obtain ⟨rs, h⟩ := IsSafe.exists_eval_eq_ok (q := empDept) (by decide) hD'
  exact ⟨rs, by rw [h]; rfl⟩

end Frontier

/-! ### Decimals in queries -/

namespace Decimal
open Frontier

/-- `emp.dept * 1.5`: an integer column promoted to decimal. -/
abbrev scaled : Query S 1 := project ![binary (.arith .mul) (col 1) (lit (.decimal (3/2)))] emp

example : scaled.typeOf = some ![.decimal] := by decide
example : (scaled.eval D).toOption =
    some [![some (.decimal (3/2))], ![some (.decimal (3/2))], ![none], ![some (.decimal (3/2))]] := by
  decide +kernel

-- `WHERE dept = 1.0` matches the integer `1` (promotion), and drops the `NULL` department.
example : ((select (binary (.cmp .eq) (col 1) (lit (.decimal 1))) emp).eval D).toOption.map List.length =
    some 3 := by
  decide +kernel

-- Decimal division is ill-typed, so a query using it is not safe.
example : (project ![binary (.arith .div) (lit (.decimal 1)) (col 1)] emp).typeOf = none := by decide

end Decimal

/-! ### Queries over the typed `SemanticsTest.testDb` (phase 2) -/

namespace TestDb
open SqlCoreTest.SchemaExamples

abbrev users : Query schema 4 := table (S := schema) T.users
abbrev orders : Query schema 4 := table (S := schema) T.orders
abbrev items : Query schema 3 := table (S := schema) T.items

-- `SELECT name FROM users WHERE age > 25`
example : ((project ![col 1] (select (binary (.cmp .gt) (col 2) (lit (.int 25))) users)).eval db).toOption =
    some [![some (.text "Alice")], ![some (.text "Carol")], ![some (.text "Dave")]] := by
  decide

-- `SELECT u.name, o.product FROM users u JOIN orders o ON u.id = o.user_id`
example : ((project ![col 1, col 7] (join (binary (.cmp .eq) (col 0) (col 5)) users orders)).eval db).toOption =
    some [![some (.text "Alice"), some (.text "Widget")], ![some (.text "Alice"), some (.text "Gadget")],
      ![some (.text "Bob"), some (.text "Widget")], ![some (.text "Carol"), some (.text "Gizmo")]] := by
  decide

-- `SELECT DISTINCT department FROM users`
example : ((distinct (project ![col 3] users)).eval db).toOption =
    some [![some (.text "Engineering")], ![some (.text "Marketing")], ![some (.text "Sales")]] := by
  decide

-- `SELECT name FROM items WHERE price > 2`: decimal prices against an integer; NULL is dropped.
example : ((project ![col 1] (select (binary (.cmp .gt) (col 2) (lit (.int 2))) items)).eval db).toOption =
    some [![some (.text "Bolt")], ![some (.text "Washer")]] := by
  decide +kernel

-- The join is safe, so it succeeds on every conforming instance of the schema.
example (D : Database schema) (hD : D.Conforms) :
    ∃ rs, (join (binary (.cmp .eq) (col 0) (col 5)) users orders).eval D = .ok rs :=
  IsSafe.exists_eval_eq_ok (by unfold IsSafe; decide) hD

end TestDb

end SqlCoreTest.QueryExamples
