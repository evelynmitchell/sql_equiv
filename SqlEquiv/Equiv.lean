/-
  SQL Equivalence Definitions and Proofs — Re-export Hub
  All submodules are imported here so that `import SqlEquiv.Equiv` still works.

  **Over the reference oracle (decisions D3, D7, #466).** This works over `SqlEquiv`'s untyped
  evaluator, now a labelled reference oracle; its theorems are laws about that oracle. The
  project's rewriter and checker are the typed core's (`SqlCore.Expr.simplify`,
  `SqlCore.Query.checkEquiv`).
-/
import SqlEquiv.Equiv.Defs
import SqlEquiv.Equiv.ValueLemmas
import SqlEquiv.Equiv.ExprAxioms
import SqlEquiv.Equiv.Decidable
import SqlEquiv.Equiv.Comparison
import SqlEquiv.Equiv.SetBagLemmas
import SqlEquiv.Equiv.StatementAxioms
import SqlEquiv.Equiv.StatementChecker
