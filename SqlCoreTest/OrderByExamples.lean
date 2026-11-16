/-
  Typed core phase 8b: ORDER BY, LIMIT and OFFSET, checked by `decide` on the
  frontier test schema (`emp(name text, dept int)`: `ann 1`, `bob 1`,
  `cy NULL`, `ann 1`). The expected rows are what Postgres 16 and DuckDB
  return, except where a tie leaves their order unspecified; the core sorts
  stably, so tied rows keep their input order.
-/
import SqlCoreTest.QueryExamples

namespace SqlCoreTest.OrderByExamples

open SqlCore SqlCore.Query SqlCoreTest.QueryExamples.Frontier
open SqlCore.Expr (col lit unary binary)

/-- An ascending key, `NULL`s last (the Postgres default for `ASC`). -/
abbrev asc (e : Expr n) : SortKey n := ⟨e, false, false⟩
/-- A descending key, `NULL`s first (the Postgres default for `DESC`). -/
abbrev desc (e : Expr n) : SortKey n := ⟨e, true, true⟩

/-- `SELECT name FROM emp ORDER BY name`. -/
example : ((project ![col 0] (orderBy ![asc (col 0)] emp)).eval D).toOption = some
    [![some (.text "ann")], ![some (.text "ann")], ![some (.text "bob")], ![some (.text "cy")]] := by
  decide +kernel

-- `ORDER BY dept DESC`: the NULL first, then the ties in input order (ann, bob, ann).
example : ((orderBy ![desc (col 1)] emp).eval D).toOption = some
    [![some (.text "cy"), none], ![some (.text "ann"), some (.int 1)],
     ![some (.text "bob"), some (.int 1)], ![some (.text "ann"), some (.int 1)]] := by
  decide +kernel

-- `ORDER BY dept, name DESC`: the second key breaks the tie; the NULL sorts last.
example : ((orderBy ![asc (col 1), ⟨col 0, true, false⟩] emp).eval D).toOption = some
    [![some (.text "bob"), some (.int 1)], ![some (.text "ann"), some (.int 1)],
     ![some (.text "ann"), some (.int 1)], ![some (.text "cy"), none]] := by
  decide +kernel

-- `NULLS FIRST` on an ascending key.
example : ((project ![col 0] (orderBy ![⟨col 1, false, true⟩, asc (col 0)] emp)).eval D).toOption =
    some [![some (.text "cy")], ![some (.text "ann")], ![some (.text "ann")],
      ![some (.text "bob")]] := by
  decide +kernel

-- `ORDER BY name LIMIT 2 OFFSET 1`.
example : ((project ![col 0] (limit (some 2) 1 (orderBy ![asc (col 0)] emp))).eval D).toOption =
    some [![some (.text "ann")], ![some (.text "bob")]] := by
  decide +kernel

-- `OFFSET` past the end is empty; `LIMIT 0` is empty; no `LIMIT` keeps the rest.
example : ((limit none 9 emp).eval D).toOption = some [] := by decide
example : ((limit (some 0) 0 emp).eval D).toOption = some [] := by decide
example : ((project ![col 0] (limit none 3 emp)).eval D).toOption = some [![some (.text "ann")]] := by
  decide

-- A key may be any expression of the input, not only a column: `ORDER BY -dept`.
example : ((project ![col 0] (orderBy ![asc (unary .neg (col 1)), asc (col 0)] emp)).eval D).toOption =
    some [![some (.text "ann")], ![some (.text "ann")], ![some (.text "bob")],
      ![some (.text "cy")]] := by
  decide +kernel

-- Typing: ORDER BY keeps the input's type, and an ill-typed key makes the query ill-typed.
example : (orderBy ![asc (col 0)] emp).typeOf = some ![.text, .int] := by decide
example : (orderBy ![asc (unary .neg (col 0))] emp).typeOf = none := by decide

-- Strict errors: a failing key fails the query.
example : ((orderBy ![asc (binary (.arith .div) (col 1) (lit (.int 0)))] emp).eval D) =
    .error .divisionByZero := by decide

-- Soundness: a safe ORDER BY / LIMIT query succeeds on every conforming instance.
example (D' : Database S) (hD' : D'.Conforms) :
    ∃ rs, (limit (some 2) 1 (orderBy ![asc (col 0)] emp)).eval D' = .ok rs :=
  IsSafe.exists_eval_eq_ok (by decide) hD'

-- Congruence: ORDER BY is a congruence at every level, LIMIT at the ordered level.
example {q q' : Query S 2} (h : Equiv .bag q q') :
    Equiv .bag (orderBy ![asc (col 0)] q) (orderBy ![asc (col 0)] q') := Equiv.orderBy _ h

-- The checker sees through simplification below an ORDER BY.
example : Equiv .ordered (orderBy ![asc (col 0)] (select (lit (.bool true)) emp))
    (orderBy ![asc (col 0)] emp) := by sql_query_equiv

/-! ### `SELECT DISTINCT … ORDER BY` an unselected key (registry row 5, `firstRow`)

`SELECT DISTINCT id FROM dept ORDER BY title DESC`, as the bridge elaborates it in the sqlite and
duckdb dialects: group by `id`, take the title of each group's first row, sort, keep `id`. The
first titles are eng (1), law (2) and tmp (NULL), so the order is NULL, 2, 1; MAX would give ops
for 1 and the order NULL, 1, 2. -/
example : ((project ![col 0] (orderBy ![desc (col 1)]
    (aggregate ![col 0] ![.first (col 1)] dept))).eval D).toOption =
    some [![none], ![some (.int 2)], ![some (.int 1)]] := by
  decide +kernel

-- `first` takes each group's first row, and keeps its NULL: with the NULL department sorted first,
-- the first department is NULL, not the first non-null one (DuckDB's `first`, not `any_value`).
example : ((aggregate ![col 0] ![.first (col 1)] emp).eval D).toOption = some
    [![some (.text "ann"), some (.int 1)], ![some (.text "bob"), some (.int 1)],
     ![some (.text "cy"), none]] := by decide
example : ((aggregate (g := 0) ![] ![.first (col 1)] (orderBy ![⟨col 1, false, true⟩] emp)).eval
    D).toOption = some [![none]] := by decide +kernel
example : (aggregate (g := 0) ![] ![.first (col 1)] emp).typeOf = some ![.int] := by decide

end SqlCoreTest.OrderByExamples
