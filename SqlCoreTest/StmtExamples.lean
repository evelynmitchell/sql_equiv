/-
  Typed core phase 9.7 (#465): INSERT, UPDATE, DELETE (`SqlCore.Stmt`), checked by `decide` on a
  schema `p(a int, b int)` with rows (1, 2) and (3, 4).
-/
import SqlCoreTest.QueryExamples

namespace SqlCoreTest.StmtExamples

open SqlCore SqlCore.Query
open SqlCore.Expr (col lit)

/-- One table. -/
inductive T where
  | p
  deriving DecidableEq

instance : Fintype T where
  elems := {.p}
  complete t := by cases t; decide

/-- `p(a int, b int)`. -/
abbrev S : DbSchema where
  Table := T
  arity _ := 2
  columns _ := ![⟨some "p", "a", .int⟩, ⟨some "p", "b", .int⟩]

abbrev int {n : ℕ} (z : ℤ) : Expr n := lit (.int z)

abbrev D : Database S
  | T.p => [![some (.int 1), some (.int 2)], ![some (.int 3), some (.int 4)]]

theorem hD : D.Conforms := by decide

/-- The rows of `p` after the statement, or `none` on an error. -/
def after (s : Stmt S) : Option (List (List Datum)) :=
  (s.exec D).toOption.map fun D' => (D' T.p).map fun r => [r 0, r 1]

/-- The error of the statement, if any. -/
def errorOf (s : Stmt S) : Option EvalError :=
  match s.exec D with
  | .error e => some e
  | .ok _ => none

abbrev a : Expr 2 := col 0
abbrev b : Expr 2 := col 1

-- `UPDATE p SET a = b, b = a`: every SET reads the old row, so the columns swap (sqlite, DuckDB,
-- Postgres; `SqlEquiv` gives (2, 2), each SET seeing the earlier ones)
example : after (.update T.p ![b, a] (lit (.bool true))) =
    some [[some (.int 2), some (.int 1)], [some (.int 4), some (.int 3)]] := by decide +kernel

-- `UPDATE p SET a = a + 10 WHERE a = 1`: only the matching row changes
example : after (.update T.p ![.binary (.arith .add) a (int 10), b]
    (.binary (.cmp .eq) a (int 1))) =
    some [[some (.int 11), some (.int 2)], [some (.int 3), some (.int 4)]] := by decide +kernel

-- the assignments are not evaluated on rows the WHERE rejects: `SET a = a / 0 WHERE a = 5`
example : after (.update T.p ![.binary (.arith .div) a (int 0), b]
    (.binary (.cmp .eq) a (int 5))) =
    some [[some (.int 1), some (.int 2)], [some (.int 3), some (.int 4)]] := by decide +kernel

-- … and an error on a matching row fails the statement
example : errorOf (.update T.p ![.binary (.arith .div) a (int 0), b]
    (.binary (.cmp .eq) a (int 1))) = some .divisionByZero := by decide +kernel

-- `DELETE FROM p WHERE a = 1`
example : after (.delete T.p (.binary (.cmp .eq) a (int 1))) =
    some [[some (.int 3), some (.int 4)]] := by decide +kernel

-- a `NULL` predicate keeps the row, as `WHERE` does
example : after (.delete T.p (.binary (.cmp .eq) a (.null .int))) =
    some [[some (.int 1), some (.int 2)], [some (.int 3), some (.int 4)]] := by decide +kernel

-- the DELETE predicate is evaluated on every row
example : errorOf (.delete T.p (.binary (.cmp .eq) (.binary (.arith .div) a (int 0)) (int 1))) =
    some .divisionByZero := by decide +kernel

-- `INSERT INTO p VALUES (5, 6)`: a projection over the one-row source
example : after (.insert T.p (.project ![int 5, int 6] .one)) =
    some [[some (.int 1), some (.int 2)], [some (.int 3), some (.int 4)],
      [some (.int 5), some (.int 6)]] := by decide +kernel

-- `INSERT INTO p SELECT b, a FROM p`: the query reads the old instance
example : after (.insert T.p (.project ![b, a] (table T.p))) =
    some [[some (.int 1), some (.int 2)], [some (.int 3), some (.int 4)],
      [some (.int 2), some (.int 1)], [some (.int 4), some (.int 3)]] := by decide +kernel

-- typing: an assignment must have its column's type, and the predicate must be boolean
example : (Stmt.update (S := S) T.p ![b, a] (lit (.bool true))).WellTyped := by decide
example : ¬ (Stmt.update (S := S) T.p ![lit (.text "x"), a] (lit (.bool true))).WellTyped := by
  decide
example : ¬ (Stmt.delete (S := S) T.p a).WellTyped := by decide
example : (Stmt.insert T.p (.project ![int 5, int 6] (.one : Query S 0))).WellTyped := by decide

end SqlCoreTest.StmtExamples
