/-
  Typed core phase 9.6 (#464): `WITH RECURSIVE` (`Query.recurse`), checked by `decide`. Each
  example mirrors a query that DuckDB and Postgres were run on (25 Nov 2026): the step is evaluated
  on the previous round's new rows only (the working table), `UNION` removes duplicates against
  every row so far, and the iteration stops when a round adds none.
-/
import SqlCoreTest.QueryExamples

namespace SqlCoreTest.RecurseExamples

open SqlCore SqlCore.Query SqlCoreTest.QueryExamples.Frontier
open SqlCore.Expr (col lit)

abbrev n0 : Expr 1 := col 0

/-- One integer row: `SELECT z`. -/
abbrev row1 (z : ℤ) : Query S 1 := project ![int z] one

/-- The working row as the step's source (`FROM r`). -/
abbrev r : Query S 1 := outer ![.int]

/-- The result's single column, or the error. -/
def result (q : Query S 1) : Except EvalError (List Datum) :=
  (q.eval D).map (·.map (· 0))

-- `WITH RECURSIVE c AS (SELECT 1 AS n UNION ALL SELECT n + 1 FROM c WHERE n < 3) SELECT n FROM c`
-- gives 1, 2, 3 (both engines)
example : result (recurse false 100 (row1 1)
    (project ![.binary (.arith .add) n0 (int 1)] (select (.binary (.cmp .lt) n0 (int 3)) r))) =
    .ok [some (.int 1), some (.int 2), some (.int 3)] := by decide +kernel

-- `… (SELECT 1 AS n UNION SELECT (n % 3) + 1 FROM r) …`: a cycle; `UNION` stops it at 1, 2, 3
example : result (recurse true 100 (row1 1)
    (project ![.binary (.arith .add) (.binary (.arith .mod) n0 (int 3)) (int 1)] r)) =
    .ok [some (.int 1), some (.int 2), some (.int 3)] := by decide +kernel

-- the same cycle with `UNION ALL` never stops: the round limit is an error (the engines run on)
example : result (recurse false 5 (row1 1)
    (project ![.binary (.arith .add) (.binary (.arith .mod) n0 (int 3)) (int 1)] r)) =
    .error .recursionLimit := by decide +kernel

-- `UNION` removes duplicates of the base rows too: base 1, 1, 2 gives 1, 2
example : result (recurse true 100 (unionAll (unionAll (row1 1) (row1 1)) (row1 2))
    (select (.binary (.cmp .gt) n0 (int 5)) r)) =
    .ok [some (.int 1), some (.int 2)] := by decide +kernel

-- `UNION ALL` keeps them, and each copy recurses: base 1, 1 with `n + 1 WHERE n < 2` gives
-- 1, 1, 2, 2
example : result (recurse false 100 (unionAll (row1 1) (row1 1))
    (project ![.binary (.arith .add) n0 (int 1)] (select (.binary (.cmp .lt) n0 (int 2)) r))) =
    .ok [some (.int 1), some (.int 1), some (.int 2), some (.int 2)] := by decide +kernel

-- an error in a round fails the query (Postgres: division by zero at n = 3)
example : result (recurse false 100 (row1 1)
    (project ![.binary (.arith .add) n0 (int 1)]
      (select (.binary (.cmp .gt) (.binary (.arith .div) (int 10) (.binary (.arith .sub) (int 3) n0))
        (int 0)) r))) =
    .error .divisionByZero := by decide +kernel

-- the step joins the working row with a table: departments reachable from 1 through `dept`
-- (each `dept` row `(id, title)` read as an edge `id → id + 1` while `id < 2`)
example : result (recurse true 100 (row1 1)
    (project ![.binary (.arith .add) (col 1) (int 1)]
      (join (.binary (.cmp .eq) (col 0) (col 1))
        r (select (.binary (.cmp .lt) (col 0) (int 2)) (project ![col 0] dept))))) =
    .ok [some (.int 1), some (.int 2)] := by decide +kernel

-- typing: the step must keep the base's types, read through `outer`
example : (recurse (S := S) false 10 (row1 1) (project ![n0] r)).typeOf = some ![.int] := by
  decide
example : (recurse (S := S) false 10 (row1 1) (project ![lit (.text "x")] r)).typeOf = none := by
  decide

end SqlCoreTest.RecurseExamples
