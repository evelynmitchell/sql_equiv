/-
  Common test infrastructure shared across test modules
-/
import SqlEquiv

namespace Test

open SqlEquiv

-- ============================================================================
-- Expression Helpers
-- ============================================================================

/-- Create a simple (unqualified) column reference -/
def col (name : String) : Expr := .col ⟨none, name⟩

/-- Create a qualified column reference -/
def qcol (table : String) (name : String) : Expr := .col ⟨some table, name⟩

/-- Create an integer literal -/
def intLit (n : Int) : Expr := .lit (.int n)

/-- Create a boolean literal -/
def boolLit (b : Bool) : Expr := .lit (.bool b)

/-- Create a string literal -/
def strLit (s : String) : Expr := .lit (.string s)

/-- Create a null literal -/
def nullLit : Expr := .lit (.null none)

-- ============================================================================
-- FromClause Helpers
-- ============================================================================

/-- Create a simple table FROM clause -/
def table (name : String) : FromClause := .table ⟨name, none⟩

/-- Create a table with alias -/
def tableAs (name : String) (alias : String) : FromClause := .table ⟨name, some alias⟩

/-- Create an inner join -/
def innerJoin (left : FromClause) (right : FromClause) (on_ : Option Expr) : FromClause :=
  .join left .inner right on_

/-- Create a left join -/
def leftJoin (left : FromClause) (right : FromClause) (on_ : Option Expr) : FromClause :=
  .join left .left right on_

/-- Create a right join -/
def rightJoin (left : FromClause) (right : FromClause) (on_ : Option Expr) : FromClause :=
  .join left .right right on_

/-- Create a cross join -/
def crossJoin (left : FromClause) (right : FromClause) : FromClause :=
  .join left .cross right none

/-- Create a full outer join -/
def fullJoin (left : FromClause) (right : FromClause) (on_ : Option Expr) : FromClause :=
  .join left .full right on_

-- ============================================================================
-- Test Infrastructure
-- ============================================================================

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

-- ============================================================================
-- Row Normalization Helpers (for join tests with column reordering)
-- ============================================================================

/-- Sort row columns by key name for order-independent comparison -/
def normalizeRow (r : Row) : Row := r.mergeSort (fun a b => a.1 < b.1)

/-- Produce a string key from a normalized row for sorting rows -/
def rowKey (r : Row) : String :=
  (normalizeRow r).foldl (fun acc (k, v) => acc ++ k ++ "=" ++ v.toSql ++ ",") ""

end Test
