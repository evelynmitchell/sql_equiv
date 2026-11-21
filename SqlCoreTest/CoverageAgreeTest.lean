/-
  The Spider coverage report against the theorems' own shapes (#352). `SqlBridge.Coverage`
  counts the Spider queries inside the elaborator-correctness fragment by a feature list of its
  own; `SqlCoreTest.CorrectExamples` defines the fragment from the theorems' hypotheses
  (`stmtShape`, `aggShape`, `aggBareShape`, `groupedShape`, `distinctShape`, `setOpShape`, `inSubShape`). This
  test runs both over every query
  of `benchmarks/spider/dev_queries.jsonl`, parsed in the sqlite dialect as the report does, and
  fails on any disagreement: a report that counts a query no theorem covers (as a first draft of
  step 3b-5 did), or misses one.
-/
import SqlCoreTest.CorrectExamples

namespace SqlCoreTest.CoverageAgree
open Lean SqlCoreTest.CorrectExamples

def queriesPath : System.FilePath := "benchmarks/spider/dev_queries.jsonl"

/-- Fewer parsed queries than this means the corpus was not really read (a vacuous pass). -/
def minParsed : Nat := 500

/-- (parsed, in the fragment, disagreements); `none` when the Spider file is missing. -/
def run : IO (Option (Nat × Nat × List String)) := do
  unless ← queriesPath.pathExists do return none
  let lines := (← IO.FS.readFile queriesPath).splitOn "\n" |>.filter (· ≠ "")
  let mut n := 0
  let mut inside := 0
  let mut bad : List String := []
  for l in lines do
    let some j := (Json.parse l).toOption | continue
    let some q := (j.getObjValAs? String "query").toOption | continue
    match SqlEquiv.parse q (dialect := .sqlite) with
    | .ok s =>
      n := n + 1
      let cov := (SqlBridge.Coverage.outsideFragment s).isEmpty
      let shp := anyShape s
      if shp then inside := inside + 1
      if cov != shp then
        bad := s!"report says {if cov then "inside" else "outside"}, the theorems' shape says {if shp then "inside" else "outside"}: {q}" :: bad
    | .error _ => pure ()
  return some (n, inside, bad.reverse)

end SqlCoreTest.CoverageAgree
