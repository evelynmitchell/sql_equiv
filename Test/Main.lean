/-
  Test Runner: Runs all test suites
-/
import Test.ParserTest
import Test.SemanticsTest
import Test.EquivTest
import Test.PropertyTest
import Test.OptimizerTest
import Test.ExprNormalizationTest
import Test.JoinReorderingTest
import Test.PredicatePushdownTest

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════╗"
  IO.println "║     SQL Equiv Test Suite          ║"
  IO.println "╚═══════════════════════════════════╝\n"

  let _ ← ParserTest.runParserTests
  IO.println ""

  let _ ← SemanticsTest.runSemanticsTests
  IO.println ""

  EquivTest.runEquivTests
  IO.println ""

  let _ ← PropertyTest.runPropertyTests
  IO.println ""

  let _ ← OptimizerTest.runOptimizerTests
  IO.println ""

  let _ ← ExprNormalizationTest.runExprNormalizationTests
  IO.println ""

  let _ ← JoinReorderingTest.runJoinReorderingTests
  IO.println ""

  let _ ← PredicatePushdownTest.runPredicatePushdownTests
  IO.println ""

  IO.println "═══════════════════════════════════"
  IO.println "All test suites completed!"
