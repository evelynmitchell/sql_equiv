/-
  Test runner for the typed core (#287). Compile-time checks:
  `SqlCoreTest.TrustBaseTest`, `SqlCoreTest.ScalarExamples`,
  `SqlCoreTest.SchemaExamples`. Runtime: the differential test
  `SqlCoreTest.ScalarDiffTest` against `SqlEquiv`, and
  `SqlCoreTest.SchemaDiffTest` (the typed test database matches the original).
-/
import SqlCoreTest.TrustBaseTest
import SqlCoreTest.ScalarExamples
import SqlCoreTest.ScalarDiffTest
import SqlCoreTest.SchemaExamples
import SqlCoreTest.SchemaDiffTest

def main : IO UInt32 := do
  IO.println "SqlCore tests: compile-time checks passed (trust base, runtime overrides, scalar and schema examples)"
  let (n, documented, bad) := SqlCoreTest.ScalarDiff.run
  IO.println s!"Scalar differential vs SqlEquiv: {n} cases, {documented} documented differences, {bad.length} unexpected"
  for line in bad do
    IO.println s!"  UNEXPECTED: {line}"
  let schemaBad := SqlCoreTest.SchemaDiff.mismatches
  IO.println s!"Schema transcription of SemanticsTest.testDb: {SqlCoreTest.SchemaDiff.tables.length} tables, {schemaBad.length} mismatched"
  for line in schemaBad do
    IO.println s!"  MISMATCH: {line}"
  if bad.isEmpty && documented > 0 && schemaBad.isEmpty then return 0 else return 1
