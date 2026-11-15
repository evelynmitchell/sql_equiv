/-
  Test runner for the typed core (#287). Phase 0: the checks are compile-time
  (`SqlCoreTest.TrustBaseTest`); later phases add runtime suites here.
-/
import SqlCoreTest.TrustBaseTest

def main : IO UInt32 := do
  IO.println "SqlCore tests: compile-time checks passed (trust base, runtime overrides)"
  return 0
