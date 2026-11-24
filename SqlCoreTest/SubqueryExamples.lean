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

/-! ### Correlated bodies (phase 9.4b, #462, decision D6) -/

/-- The departments of the outer `emp` row: `dept` joined behind the outer row (`emp.dept` is
column 1, `dept.id` column 2). -/
abbrev myDepts : Query S 4 :=
  select (binary (.cmp .eq) (col 1) (col 2)) (join (lit (.bool true)) (outer (S.ctx .emp)) dept)

-- `SELECT *, (SELECT COUNT(*) FROM dept WHERE dept.id = emp.dept) FROM emp`: the body runs once
-- per outer row; the NULL department matches nothing.
example : ((lateral (aggregate (g := 0) ![] ![.countStar] myDepts) emp).eval D).toOption.map
    (·.map (· 2)) = some [some (.int 2), some (.int 2), some (.int 0), some (.int 2)] := by
  decide +kernel

-- `LIMIT` applies per outer row: the first title of each employee's department.
example : ((lateral (limit (some 1) 0 (project ![col 3] myDepts)) emp).eval D).toOption.map
    (·.map (· 2)) = some [some (.text "eng"), some (.text "eng"), some (.text "eng")] := by
  decide +kernel

-- Well-typed, so it never fails on a conforming instance; a free `outer` is ill-typed.
example : (lateral (aggregate (g := 0) ![] ![.countStar] myDepts) emp).typeOf =
    some ![.text, .int, .int] := by decide
example : (outer (S := S) (S.ctx .emp)).typeOf = none := by decide

-- A body that reads no outer row is a cross join (`Query.lateral_closed`).
example : Equiv .ordered (lateral deptIds emp) (join (lit (.bool true)) emp deptIds) :=
  lateral_closed (by decide) (by decide) emp

end SqlCoreTest.SubqueryExamples
