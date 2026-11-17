/-
  Typed core phase 8f (#329): uncorrelated subqueries, attached as a column
  (`Query.attach`), checked by `decide` on the frontier test schema
  (`emp(name text, dept int)`: ann 1, bob 1, cy NULL, ann 1;
  `dept(id int, title text)`: 1 eng, 1 ops, 2 law, NULL tmp).
-/
import SqlCoreTest.QueryExamples

namespace SqlCoreTest.SubqueryExamples

open SqlCore SqlCore.Query SqlCoreTest.QueryExamples.Frontier
open SqlCore.Expr (col lit unary binary)

/-- `SELECT id FROM dept`. -/
abbrev deptIds : Query S 1 := project ![col 0] dept

-- `dept IN (SELECT id FROM dept)`: TRUE for department 1, NULL for the NULL department.
example : ((attach (.inSub false (col 1)) deptIds emp).eval D).toOption = some
    [![some (.text "ann"), some (.int 1), some (.bool true)],
     ![some (.text "bob"), some (.int 1), some (.bool true)],
     ![some (.text "cy"), none, none],
     ![some (.text "ann"), some (.int 1), some (.bool true)]] := by decide

-- `NOT IN` a list holding a NULL is never TRUE: `1 NOT IN (2, NULL)` is NULL, so no row passes.
example : ((select (col 2) (attach (.inSub true (lit (.int 1)))
    (project ![col 0] (select (binary .or (unary .not (binary (.cmp .eq) (col 0) (lit (.int 1))))
      (unary .isNull (col 0))) dept))
    emp)).eval D).toOption = some [] := by decide
-- … while without the NULL, `1 NOT IN (2)` is TRUE on every row.
example : ((select (col 2) (attach (.inSub true (lit (.int 1)))
    (project ![col 0] (select (unary .not (binary (.cmp .eq) (col 0) (lit (.int 1)))) dept))
    emp)).eval D).toOption.map List.length = some 4 := by decide

-- A scalar subquery: `(SELECT MAX(id) FROM dept)` is 2 on every row.
example : ((attach (.scalar false) (aggregate (g := 0) ![] ![.call .max false (col 0)] dept)
    (project ![col 0] emp)).eval D).toOption.map (·.map (· 1)) =
    some [some (.int 2), some (.int 2), some (.int 2), some (.int 2)] := by decide +kernel

-- No rows: NULL. Several rows: an error, or the first row in the sqlite dialect (registry T17).
example : ((attach (.scalar false) (project ![col 0] empty) (project ![col 0] emp)).eval
    D).toOption.map (·.map (· 1)) = some [none, none, none, none] := by decide
example : (attach (.scalar false) deptIds emp).eval D = .error .cardinality := by decide
example : ((attach (.scalar true) deptIds (project ![col 0] emp)).eval D).toOption.map
    (·.map (· 1)) = some [some (.int 1), some (.int 1), some (.int 1), some (.int 1)] := by decide

-- The subquery is evaluated even when the outer query has no rows: a strict multi-row error.
example : (attach (.scalar false) deptIds empty).eval D = .error .cardinality := by decide

-- Typing: a scalar column has the subquery's type; IN needs comparable types and is boolean.
example : (attach (.scalar false) deptIds emp).typeOf = some ![.text, .int, .int] := by decide
example : (attach (.inSub false (col 1)) deptIds emp).typeOf = some ![.text, .int, .bool] := by
  decide
example : (attach (.inSub false (col 0)) deptIds emp).typeOf = none := by decide

-- Safety: an error-mode scalar subquery is never safe (its row count is not known statically);
-- IN and a first-row scalar subquery are.
example : ¬ (attach (.scalar false) deptIds emp).IsSafe := by decide
example : (attach (.scalar true) deptIds emp).IsSafe := by decide
example (D' : Database S) (hD' : D'.Conforms) :
    ∃ rs, (attach (.inSub true (col 1)) deptIds emp).eval D' = .ok rs :=
  IsSafe.exists_eval_eq_ok (by decide) hD'

end SqlCoreTest.SubqueryExamples
