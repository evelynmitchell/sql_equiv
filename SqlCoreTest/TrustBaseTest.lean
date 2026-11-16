/-
  Trust-base guard for the typed core (#287): the `SqlCore` namespace must use
  only Lean's standard axioms (no `sorry`, no `native_decide`, no project
  axioms) and contain no hand-written runtime overrides. Same commands as
  `Test/TrustBaseTest.lean` (shared in `Test/TrustBaseCommands.lean`).
-/
import SqlCore
import SqlBridge.Elab
import Test.TrustBaseCommands

#assert_trust_base SqlCore

#assert_no_runtime_overrides SqlCore

-- The bridge from parsed SQL (#295): the elaborator (definitions; the theorems are generated).
#assert_trust_base SqlBridge
#assert_no_runtime_overrides SqlBridge
