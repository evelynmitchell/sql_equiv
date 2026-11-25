/-
  Trust-base guard for the typed core (#287): the `SqlCore` namespace must use
  only Lean's standard axioms (no `sorry`, no `native_decide`, no project
  axioms) and contain no hand-written runtime overrides. Same commands as
  `Test/TrustBaseTest.lean` (shared in `Test/TrustBaseCommands.lean`).
-/
import SqlCore
import SqlBridge.Elab
import SqlBridge.Inline
import SqlBridge.Correct
import SqlBridge.CorrectLike
import SqlBridge.CorrectOrder
import SqlBridge.CorrectJoin
import SqlBridge.CorrectAgg
import SqlBridge.CorrectGroup
import SqlBridge.CorrectGroupOrder
import SqlBridge.CorrectGrouped
import SqlBridge.CorrectExtreme
import SqlBridge.CorrectAvg
import SqlBridge.CorrectAggBare
import SqlBridge.CorrectDistinct
import SqlBridge.CorrectSetOp
import SqlBridge.CorrectSub
import SqlBridge.CorrectDerived
import SqlBridge.Coverage
import SqlBridge.Spider
import SqlBridge.SpiderEval
import SqlBridge.Cli
import Test.TrustBaseCommands

#assert_trust_base SqlCore

#assert_no_runtime_overrides SqlCore

-- The bridge from parsed SQL (#295): the elaborator, and its correctness theorem for
-- `SELECT … FROM t WHERE p` (#309, `SqlBridge.Correct`), with `ORDER BY` / `LIMIT` / `OFFSET`
-- (#352 step 1, `SqlBridge.CorrectOrder`), joins (step 2, `SqlBridge.CorrectJoin`) and aggregates
-- without `GROUP BY` (step 3a, `SqlBridge.CorrectAgg`) and `GROUP BY` (step 3b-1,
-- `SqlBridge.CorrectGroup`), and the later steps. Every `SqlBridge/Correct*.lean` file must be
-- imported here, or its theorems are not checked: `tools/check_trust_base_imports.py` (in CI)
-- fails when one is missing.
#assert_trust_base SqlBridge
#assert_no_runtime_overrides SqlBridge
