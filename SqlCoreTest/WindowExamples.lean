/-
  Typed core phase 9.5 (#463): window functions (`Query.window`), checked by `decide` on the
  frontier test schema (`emp(name text, dept int)`: ann 1, bob 1, cy NULL, ann 1).
-/
import SqlCoreTest.QueryExamples

namespace SqlCoreTest.WindowExamples

open SqlCore SqlCore.Query SqlCoreTest.QueryExamples.Frontier
open SqlCore.Expr (col lit)

/-- `ORDER BY name`. -/
abbrev byName : SortKey 2 := ⟨col 0, false, false⟩

/-- The window column of each row. -/
def winCol (c : WinCall 2) : Option (List Datum) :=
  ((window c emp).eval D).toOption.map (·.map (· 2))

-- `ROW_NUMBER() OVER (PARTITION BY dept ORDER BY name)`: ties (the two anns) in input order;
-- the NULL department is a partition of its own
example : winCol ⟨[col 1], [byName], .rowNumber⟩ =
    some [some (.int 1), some (.int 3), some (.int 1), some (.int 2)] := by decide +kernel

-- `RANK()` gives tied rows one rank and skips; `DENSE_RANK()` does not skip
example : winCol ⟨[col 1], [byName], .rank⟩ =
    some [some (.int 1), some (.int 3), some (.int 1), some (.int 1)] := by decide +kernel
example : winCol ⟨[col 1], [byName], .denseRank⟩ =
    some [some (.int 1), some (.int 2), some (.int 1), some (.int 1)] := by decide +kernel

-- `COUNT(*) OVER (PARTITION BY dept)`: the whole partition without `ORDER BY`
example : winCol ⟨[col 1], [], .agg .countStar⟩ =
    some [some (.int 3), some (.int 3), some (.int 1), some (.int 3)] := by decide +kernel

-- `SUM(dept) OVER (ORDER BY name)`: a running sum that includes the row's peers
example : winCol ⟨[], [byName], .agg (.call .sum false (col 1))⟩ =
    some [some (.int 2), some (.int 3), some (.int 3), some (.int 2)] := by decide +kernel

-- `ROW_NUMBER() OVER ()`: input order
example : winCol ⟨[], [], .rowNumber⟩ =
    some [some (.int 1), some (.int 2), some (.int 3), some (.int 4)] := by decide +kernel

-- typed: the window column is an integer; `SUM` over text is ill-typed
example : (window ⟨[col 1], [byName], .rank⟩ emp).typeOf = some ![.text, .int, .int] := by
  decide
example : (window ⟨[], [], .agg (.call .sum false (col 0))⟩ emp).typeOf = none := by decide

end SqlCoreTest.WindowExamples
