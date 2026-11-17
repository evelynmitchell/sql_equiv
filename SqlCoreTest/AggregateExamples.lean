/-
  Typed core phase 8a (#313) and 8d (AVG): GROUP BY and aggregates, checked by `decide` on
  the frontier test schema (`emp(name text, dept int)`, with a duplicate `ann`
  row and a `NULL` department; `empty` has no rows). The expected rows are
  what Postgres 16 and DuckDB return for the same data.
-/
import SqlCoreTest.QueryExamples

namespace SqlCoreTest.AggregateExamples

open SqlCore SqlCore.Query SqlCoreTest.QueryExamples.Frontier
open SqlCore.Expr (col lit unary binary)

/-- `SELECT dept, COUNT(*), COUNT(name), COUNT(DISTINCT name) FROM emp GROUP BY dept`. -/
abbrev byDept : Query S 4 :=
  aggregate ![col 1] ![.countStar, .call .count false (col 0), .call .count true (col 0)] emp

-- Groups in order of first appearance; the NULL department is a group of its own.
example : (byDept.eval D).toOption = some
    [![some (.int 1), some (.int 3), some (.int 3), some (.int 2)],
     ![none, some (.int 1), some (.int 1), some (.int 1)]] := by decide

example : byDept.typeOf = some ![.int, .int, .int, .int] := by decide

-- No GROUP BY: one row, even over an empty table; COUNT is 0 and SUM/MIN/MAX are NULL.
example : ((aggregate (g := 0) ![] ![.countStar, .call .sum false (col 0), .call .max false (col 1)]
    empty).eval D).toOption = some [![some (.int 0), none, none]] := by decide

-- With GROUP BY, an empty input has no groups.
example : ((aggregate ![col 0] ![.countStar] empty).eval D).toOption = some [] := by decide

-- SUM, MIN, MAX ignore NULL; SUM DISTINCT counts each value once.
/-- `SELECT SUM(dept), SUM(DISTINCT dept), MIN(name), MAX(name) FROM emp`. -/
abbrev totals : Query S 4 :=
  aggregate (g := 0) ![] ![.call .sum false (col 1), .call .sum true (col 1),
    .call .min false (col 0), .call .max false (col 0)] emp
example : (totals.eval D).toOption =
    some [![some (.int 3), some (.int 1), some (.text "ann"), some (.text "cy")]] := by decide
example : totals.typeOf = some ![.int, .int, .text, .text] := by decide

-- HAVING is a WHERE over the aggregate: departments with more than one employee.
example : ((select (binary (.cmp .gt) (col 1) (lit (.int 1))) (aggregate ![col 1] ![.countStar] emp)).eval
    D).toOption = some [![some (.int 1), some (.int 3)]] := by decide

-- AVG is exact (phase 8d, registry T10): the departments 1, 1, NULL, 1 average to 1, as a decimal;
-- over `dept` ids 1, 1, 2, NULL the mean is 4/3, where engines round.
example : ((aggregate (g := 0) ![] ![.call .avg false (col 1)] emp).eval D).toOption =
    some [![some (.decimal 1)]] := by decide +kernel
example : ((aggregate (g := 0) ![] ![.call .avg false (col 0)] dept).eval D).toOption =
    some [![some (.decimal (4/3))]] := by decide +kernel
-- AVG DISTINCT averages 1 and 2; over no rows AVG is NULL.
example : ((aggregate (g := 0) ![] ![.call .avg true (col 0)] dept).eval D).toOption =
    some [![some (.decimal (3/2))]] := by decide +kernel
example : ((aggregate (g := 0) ![] ![.call .avg false (col 0)] empty).eval D).toOption =
    some [![none]] := by decide +kernel
-- AVG is a decimal over integers and decimals, and ill-typed over text.
example : (aggregate (g := 0) ![] ![.call .avg false (col 1)] emp).typeOf = some ![.decimal] := by
  decide
example : (aggregate (g := 0) ![] ![.call .avg false (col 0)] emp).typeOf = none := by decide

-- Typing: SUM over text and MAX over booleans are ill-typed (registry row 14).
example : (aggregate (g := 0) ![] ![.call .sum false (col 0)] emp).typeOf = none := by decide
example : (aggregate (g := 0) ![] ![.call .max false (lit (.bool true))] emp).typeOf = none := by
  decide

-- Strict errors: a failing aggregate argument fails the query, on a nonempty group.
example : ((aggregate (g := 0) ![] ![.call .sum false (binary (.arith .div) (col 1) (lit (.int 0)))]
    emp).eval D) = .error .divisionByZero := by decide
-- … and soundness: a safe aggregate query succeeds on every conforming instance.
example (D' : Database S) (hD' : D'.Conforms) : ∃ rs, byDept.eval D' = .ok rs :=
  IsSafe.exists_eval_eq_ok (by decide) hD'

end SqlCoreTest.AggregateExamples
