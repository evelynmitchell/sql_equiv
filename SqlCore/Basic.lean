/-
  Phase 0 scaffold for `SqlCore` (#289).

  The only content is a check that the Mathlib pieces the typed core is built
  on are available: `Fin` tuples (rows will be `Fin n → Datum`, #291) and
  `Fin.append` (joined rows). Phase 1 (#290) replaces this file's role with
  `SqlCore/Value.lean`.
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation

namespace SqlCore

/-- Mathlib's tuple notation and `Fin.append` work as the typed rows will use
    them: appending a 1-column row to a 2-column row gives a 3-column row. -/
theorem fin_append_smoke :
    Fin.append ![(1 : ℕ)] ![2, 3] (2 : Fin 3) = 3 := by decide

end SqlCore
