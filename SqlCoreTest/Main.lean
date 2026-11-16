/-
  Test runner for the typed core (#287). Compile-time checks:
  `SqlCoreTest.TrustBaseTest`, `SqlCoreTest.ScalarExamples`,
  `SqlCoreTest.SchemaExamples`, `SqlCoreTest.ExprExamples`. Runtime: the
  differential tests `SqlCoreTest.ScalarDiffTest` and `SqlCoreTest.ExprDiffTest`
  against `SqlEquiv`, and `SqlCoreTest.SchemaDiffTest` (the typed test
  database matches the original).
-/
import SqlCoreTest.TrustBaseTest
import SqlCoreTest.ScalarExamples
import SqlCoreTest.ScalarDiffTest
import SqlCoreTest.SchemaExamples
import SqlCoreTest.SchemaDiffTest
import SqlCoreTest.ExprExamples
import SqlCoreTest.ExprDiffTest
import SqlCoreTest.QueryExamples
import SqlCoreTest.LawExamples
import SqlCoreTest.BridgeDiffTest

def main : IO UInt32 := do
  IO.println "SqlCore tests: compile-time checks passed (trust base, runtime overrides, scalar, schema, expression and query examples)"
  let (n, documented, bad) := SqlCoreTest.ScalarDiff.run
  IO.println s!"Scalar differential vs SqlEquiv: {n} cases, {documented} documented differences, {bad.length} unexpected"
  for line in bad do
    IO.println s!"  UNEXPECTED: {line}"
  let schemaBad := SqlCoreTest.SchemaDiff.mismatches
  IO.println s!"Schema transcription of SemanticsTest.testDb: {SqlCoreTest.SchemaDiff.tables.length} tables, {schemaBad.length} mismatched"
  for line in schemaBad do
    IO.println s!"  MISMATCH: {line}"
  let (en, edoc, ebad) := SqlCoreTest.ExprDiff.run
  IO.println s!"Expression differential vs SqlEquiv: {en} cases, {edoc} documented differences, {ebad.length} unexpected"
  for line in ebad.take 20 do
    IO.println s!"  UNEXPECTED: {line}"
  let (bn, bfails) := SqlCoreTest.BridgeDiff.run
  IO.println s!"Parsed SQL through SqlBridge vs SqlEquiv: {bn} queries, {bfails.length} failures"
  for line in bfails do
    IO.println s!"  FAIL: {line}"
  if bad.isEmpty && documented > 0 && schemaBad.isEmpty && ebad.isEmpty && en > 0 && bfails.isEmpty then
    return 0
  else return 1
