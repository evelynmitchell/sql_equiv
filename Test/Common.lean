/-
  Common test infrastructure shared across test modules
-/
import SqlEquiv

namespace Test

open SqlEquiv

/-- Test result type -/
inductive TestResult where
  | pass : String → TestResult
  | fail : String → String → TestResult  -- name, error message
  deriving Repr

def TestResult.isPass : TestResult → Bool
  | .pass _ => true
  | .fail _ _ => false

def TestResult.name : TestResult → String
  | .pass n => n
  | .fail n _ => n

/-- Run a list of tests and print results -/
def runTests (suiteName : String) (tests : List TestResult) : IO (Nat × Nat) := do
  IO.println s!"═══════════════════════════════════"
  IO.println suiteName
  IO.println s!"═══════════════════════════════════"

  let mut passed := 0
  let mut failed := 0

  for result in tests do
    match result with
    | .pass name =>
      IO.println s!"✓ {name}"
      passed := passed + 1
    | .fail name msg =>
      IO.println s!"✗ {name}"
      IO.println s!"  {msg}"
      failed := failed + 1

  IO.println "───────────────────────────────────"
  IO.println s!"Passed: {passed}, Failed: {failed}"

  if failed > 0 then
    IO.println "TESTS FAILED"
  else
    IO.println "ALL TESTS PASSED"

  return (passed, failed)

end Test
