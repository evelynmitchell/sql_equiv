/-
  Test runner for the typed core (#287). Compile-time checks:
  `SqlCoreTest.TrustBaseTest`, `SqlCoreTest.ScalarExamples`,
  `SqlCoreTest.SchemaExamples`, `SqlCoreTest.ExprExamples`. Runtime: the
  differential tests `SqlCoreTest.ScalarDiffTest` and `SqlCoreTest.ExprDiffTest`
  against `SqlEquiv`, and `SqlCoreTest.SchemaDiffTest` (the typed test
  database matches the original), `SqlCoreTest.BridgeDiffTest` (parsed SQL vs
  `SqlEquiv`) and `SqlCoreTest.DuckdbDiffTest` (parsed SQL vs DuckDB) and `SqlCoreTest.SqliteDiffTest`
  (bare columns vs sqlite). `SqlCoreTest.CorrectExamples`: the hypotheses of the elaborator
  correctness theorem (#309) hold on the bridge test schema. `SqlCoreTest.CoverageAgreeTest`: the
  Spider coverage report agrees with the theorems' shapes on every Spider query.
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
import SqlCoreTest.AggregateExamples
import SqlCoreTest.OrderByExamples
import SqlCoreTest.SetOpExamples
import SqlCoreTest.SubqueryExamples
import SqlCoreTest.SimplifyExamples
import SqlCoreTest.BridgeDiffTest
import SqlCoreTest.DuckdbDiffTest
import SqlCoreTest.PostgresDiffTest
import SqlCoreTest.SqliteDiffTest
import SqlCoreTest.CorrectExamples
import SqlCoreTest.CoverageAgreeTest

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
  -- In CI (`CI` is set) a missing engine is a failure, not a skip: a skipped harness is quiet.
  let inCI := (← IO.getEnv "CI").isSome
  let skipped (what : String) : List String := if inCI then [s!"{what} harness skipped in CI"] else []
  let duckFails ← match ← SqlCoreTest.DuckdbDiff.run with
    | none =>
      IO.println "Parsed SQL through SqlBridge vs DuckDB: SKIPPED (no duckdb binary; CI installs it)"
      pure (skipped "DuckDB")
    | some (dn, ddoc, dfails) =>
      IO.println s!"Parsed SQL through SqlBridge vs DuckDB: {dn} queries, {ddoc} documented differences, {dfails.length} failures"
      for line in dfails do
        IO.println s!"  FAIL: {line}"
      pure dfails
  let pgFails ← match ← SqlCoreTest.PostgresDiff.run with
    | none =>
      IO.println "Parsed SQL through SqlBridge vs Postgres: SKIPPED (no reachable Postgres; CI starts it)"
      pure (skipped "Postgres")
    | some (pn, pdoc, pfails) =>
      IO.println s!"Parsed SQL through SqlBridge vs Postgres: {pn} queries, {pdoc} documented differences, {pfails.length} failures"
      for line in pfails do
        IO.println s!"  FAIL: {line}"
      pure pfails
  let sqliteFails ← match ← SqlCoreTest.SqliteDiff.run with
    | none =>
      IO.println "Bare columns through SqlBridge vs sqlite: SKIPPED (no sqlite3 binary)"
      pure (skipped "sqlite")
    | some (sn, sfails) =>
      IO.println s!"Bare columns through SqlBridge vs sqlite: {sn} queries, {sfails.length} failures"
      for line in sfails do
        IO.println s!"  FAIL: {line}"
      pure sfails
  let covOk ← match ← SqlCoreTest.CoverageAgree.run with
    | none =>
      IO.println "Spider coverage report vs theorem shapes: SKIPPED (no benchmarks/spider/dev_queries.jsonl; run from the repo root)"
      pure true
    | some (cn, inside, cbad) =>
      IO.println s!"Spider coverage report vs theorem shapes: {cn} queries, {inside} with the fragment's shape, {cbad.length} disagreements"
      for line in cbad.take 20 do
        IO.println s!"  DISAGREE: {line}"
      if cn < SqlCoreTest.CoverageAgree.minParsed then
        IO.println s!"  FAIL: only {cn} queries parsed (expected at least {SqlCoreTest.CoverageAgree.minParsed})"
      pure (cbad.isEmpty && cn ≥ SqlCoreTest.CoverageAgree.minParsed)
  if bad.isEmpty && documented > 0 && schemaBad.isEmpty && ebad.isEmpty && en > 0 && bfails.isEmpty &&
      duckFails.isEmpty && pgFails.isEmpty && sqliteFails.isEmpty && covOk then
    return 0
  else return 1
