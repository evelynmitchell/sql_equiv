/-
  Test runner for the typed core (#287). Compile-time checks:
  `SqlCoreTest.TrustBaseTest`, `SqlCoreTest.ScalarExamples`. Runtime:
  the differential test `SqlCoreTest.ScalarDiffTest` against `SqlEquiv`.
-/
import SqlCoreTest.TrustBaseTest
import SqlCoreTest.ScalarExamples
import SqlCoreTest.ScalarDiffTest

def main : IO UInt32 := do
  IO.println "SqlCore tests: compile-time checks passed (trust base, runtime overrides, scalar examples)"
  let (n, documented, bad) := SqlCoreTest.ScalarDiff.run
  IO.println s!"Scalar differential vs SqlEquiv: {n} cases, {documented} documented differences, {bad.length} unexpected"
  for line in bad do
    IO.println s!"  UNEXPECTED: {line}"
  if bad.isEmpty && documented > 0 then return 0 else return 1
