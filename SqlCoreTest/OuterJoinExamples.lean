/-
  Typed core phase 9.3 (#461): outer joins (`Query.outerJoin`), checked by `decide` on the frontier
  test schema: `emp(name, dept)` = ann 1, bob 1, cy NULL, ann 1; `dept(id, title)` = 1 eng, 1 ops,
  2 law, NULL tmp; `empty` has no rows. A `NULL` key matches nothing, as in every engine.
-/
import SqlCoreTest.QueryExamples

namespace SqlCoreTest.OuterJoinExamples

open SqlCore SqlCore.Query SqlCoreTest.QueryExamples.Frontier
open SqlCore.Expr (col lit)

/-- `emp.dept = dept.id` over the joined row. -/
abbrev onDept : Expr 4 := .binary (.cmp .eq) (col 1) (col 2)

/-- The number of result rows, or the error. -/
def count {n : ℕ} (q : Query S n) : Except EvalError ℕ := (q.eval D).map List.length

-- inner join: the 6 matching pairs (ann and bob each with eng and ops)
example : count (join onDept emp dept) = .ok 6 := by decide +kernel
-- LEFT: the 6 pairs and cy, whose NULL department matches nothing, padded with NULL
example : count (outerJoin .left onDept emp dept) = .ok 7 := by decide +kernel
-- RIGHT: the 6 pairs and the departments no employee has (law, and tmp with a NULL id)
example : count (outerJoin .right onDept emp dept) = .ok 8 := by decide +kernel
-- FULL: both
example : count (outerJoin .full onDept emp dept) = .ok 9 := by decide +kernel

-- cy's padded row: its name, then NULL for both `dept` columns
example : ((outerJoin .left onDept emp dept).eval D).map
    (fun rs => (rs.filter fun r => r 0 = some (.text "cy")).map fun r => [r 0, r 1, r 2, r 3]) =
    .ok [[some (.text "cy"), none, none, none]] := by decide +kernel

-- against an empty side: LEFT keeps every left row (`outerRows_left_nil`), RIGHT has none, and
-- FULL with an empty left side keeps every right row
example : count (outerJoin .left onDept emp empty) = .ok 4 := by decide +kernel
example : count (outerJoin .right onDept emp empty) = .ok 0 := by decide +kernel
example : count (outerJoin .full onDept empty dept) = .ok 4 := by decide +kernel

-- typing: the same rule as an inner join; a non-boolean condition is ill-typed
example : (outerJoin (S := S) .left onDept emp dept).typeOf =
    some ![.text, .int, .int, .text] := by decide
example : (outerJoin (S := S) .left (col 0) emp dept).typeOf = none := by decide

end SqlCoreTest.OuterJoinExamples
