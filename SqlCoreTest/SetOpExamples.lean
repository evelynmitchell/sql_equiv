/-
  Typed core phase 8c (#322): INTERSECT, EXCEPT and LIKE, checked by `decide`
  on the frontier test schema (`emp(name text, dept int)`: departments 1, 1,
  NULL, 1; `dept(id int, title text)`: ids 1, 1, 2, NULL). Set operations
  treat NULLs in the same places as equal and keep one copy of each row, as
  the standard, Postgres, DuckDB and sqlite do.
-/
import SqlCoreTest.QueryExamples

namespace SqlCoreTest.SetOpExamples

open SqlCore SqlCore.Query SqlCoreTest.QueryExamples.Frontier
open SqlCore.Expr (col lit unary binary)

/-- `SELECT dept FROM emp`. -/
abbrev empDepts : Query S 1 := project ![col 1] emp
/-- `SELECT id FROM dept`. -/
abbrev deptIds : Query S 1 := project ![col 0] dept

-- `INTERSECT`: 1 and NULL occur on both sides, once each in the result.
example : ((intersect empDepts deptIds).eval D).toOption = some [![none], ![some (.int 1)]] := by
  decide
-- `EXCEPT`: only department 2 has no employee.
example : ((difference deptIds empDepts).eval D).toOption = some [![some (.int 2)]] := by decide
-- … and every employee's department has an entry.
example : ((difference empDepts deptIds).eval D).toOption = some [] := by decide

-- Typing: both sides must have the same column types.
example : (intersect empDepts deptIds).typeOf = some ![.int] := by decide
example : (intersect (project ![col 0] emp) deptIds).typeOf = none := by decide

-- Soundness: a safe set operation succeeds on every conforming instance.
example (D' : Database S) (hD' : D'.Conforms) : ∃ rs, (difference deptIds empDepts).eval D' = .ok rs :=
  IsSafe.exists_eval_eq_ok (by decide) hD'

-- Congruence at every level, including the set level.
example {q q' : Query S 1} (h : Equiv .set q q') :
    Equiv .set (intersect q deptIds) (intersect q' deptIds) := Query.Equiv.intersect h (Query.Equiv.refl _)

/-! ### `LIKE` -/

/-- `x LIKE p`, case-sensitive (`ci = false`) or sqlite's ASCII case-insensitive rule. -/
abbrev like (ci : Bool) (x p : String) : Except EvalError Datum :=
  evalBinOp (.like ci) (some (.text x)) (some (.text p))

example : like false "ann" "a%" = .ok (some (.bool true)) := by decide
example : like false "ann" "A%" = .ok (some (.bool false)) := by decide
example : like true "ann" "A%" = .ok (some (.bool true)) := by decide
-- `_` is exactly one character; `%` may be empty, also inside the pattern.
example : like false "bob" "_ob" = .ok (some (.bool true)) := by decide
example : like false "ob" "_ob" = .ok (some (.bool false)) := by decide
example : like false "ab" "a%%b" = .ok (some (.bool true)) := by decide
example : like false "" "%" = .ok (some (.bool true)) := by decide
-- The sqlite rule folds ASCII letters only.
example : like true "É" "é" = .ok (some (.bool false)) := by decide
-- NULL on either side is NULL; a non-text operand is a type error.
example : evalBinOp (.like false) none (some (.text "%")) = .ok none := by decide
example : evalBinOp (.like false) (some (.int 1)) (some (.text "%")) = .error .typeMismatch := by
  decide

/-- `SELECT name FROM emp WHERE name LIKE 'a%'`. -/
example : ((project ![col 0] (select (binary (.like false) (col 0) (lit (.text "a%"))) emp)).eval
    D).toOption = some [![some (.text "ann")], ![some (.text "ann")]] := by decide

end SqlCoreTest.SetOpExamples
