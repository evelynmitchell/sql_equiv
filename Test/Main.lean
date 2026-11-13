/-
  Test Runner: Runs all test suites
-/
import Test.ParserTest
import Test.SemanticsTest
import Test.EquivTest
import Test.PropertyTest
import Test.AxiomCoverageTest
import Test.TrustBaseTest
import Test.RewriterTest

def main : IO UInt32 := do
  IO.println "╔═══════════════════════════════════╗"
  IO.println "║     SQL Equiv Test Suite          ║"
  IO.println "╚═══════════════════════════════════╝\n"

  let mut totalFailed : Nat := 0

  let (_, failed) ← ParserTest.runParserTests
  totalFailed := totalFailed + failed
  IO.println ""

  let (_, failed) ← SemanticsTest.runSemanticsTests
  totalFailed := totalFailed + failed
  IO.println ""

  let (_, failed) ← EquivTest.runEquivTests
  totalFailed := totalFailed + failed
  IO.println ""

  let (_, failed) ← PropertyTest.runPropertyTests
  totalFailed := totalFailed + failed
  IO.println ""

  let (_, failed) ← AxiomCoverageTest.runAxiomCoverageTests
  totalFailed := totalFailed + failed
  IO.println ""

  let (_, failed) ← RewriterTest.runRewriterTests
  totalFailed := totalFailed + failed
  IO.println ""

  IO.println "═══════════════════════════════════"
  if totalFailed > 0 then
    IO.println s!"FAILED: {totalFailed} test(s) failed across all suites"
    return 1
  else
    IO.println "All test suites completed — all tests passed!"
    return 0
