/-
  Typed core phase 3 (#292): kernel-checked examples of expressions, typing
  and safety, and the soundness theorem applied to the typed test database.
-/
import SqlCoreTest.SchemaExamples

namespace SqlCoreTest.ExprExamples
open SqlCore SqlCore.Expr SqlCoreTest.SchemaExamples

/-- `users`: id, name, age, department. -/
abbrev Γu : Fin 4 → SqlType := ![.int, .text, .int, .text]
private def id' : Expr 4 := .col 0
private def age : Expr 4 := .col 2
private def dept : Expr 4 := .col 3
private def int (z : Int) : Expr 4 := .lit (.int z)
private def dec (q : ℚ) : Expr 4 := .lit (.decimal q)

private def alice : Row 4 := ![some (.int 1), some (.text "Alice"), some (.int 30), some (.text "Engineering")]
private def nobody : Row 4 := ![some (.int 9), none, none, none]

-- Evaluation
example : (Expr.binary (.cmp .gt) age (int 25)).eval alice = .ok (some (.bool true)) := by decide
example : (Expr.binary (.cmp .gt) age (int 25)).eval nobody = .ok none := by decide
example : (Expr.inList dept [some (.text "Sales"), none]).eval alice = .ok none := by decide
example : (Expr.caseWhen (.binary (.cmp .gt) age (int 25)) (.lit (.text "old")) (.lit (.text "young"))).eval
    nobody = .ok (some (.text "young")) := by decide
-- CASE evaluates only the branch it takes: the ELSE branch would divide by zero
example : (Expr.caseWhen (.lit (.bool true)) (int 1) (.binary (.arith .div) (int 1) (int 0))).eval
    alice = .ok (some (.int 1)) := by decide

-- Typing with promotion: `age + 0.5` is decimal, `age = 30.0` is boolean, `1.0 / 2` is ill-typed
example : (Expr.binary (.arith .add) age (dec (1/2))).typeOf Γu = some .decimal := by decide
example : (Expr.binary (.cmp .eq) age (dec 30)).typeOf Γu = some .bool := by decide
example : (Expr.binary (.arith .div) (dec 1) (int 2)).typeOf Γu = none := by decide
example : (Expr.binary (.arith .mod) (dec 1) (int 2)).typeOf Γu = some .decimal := by decide
example : (Expr.binary (.cmp .eq) age dept).typeOf Γu = none := by decide
example : (Expr.inList age [some (.decimal 30), none]).typeOf Γu = some .bool := by decide
example : (Expr.inList age [some (.text "30")]).typeOf Γu = none := by decide
-- CASE branches must have one type
example : (Expr.caseWhen (.lit (.bool true)) age dept).typeOf Γu = none := by decide

-- Safety: division only by a nonzero numeric literal
example : (Expr.binary (.arith .div) age (int 2)).IsSafe Γu := by decide
example : ¬ (Expr.binary (.arith .div) age (int 0)).IsSafe Γu := by decide
example : ¬ (Expr.binary (.arith .div) age id').IsSafe Γu := by decide
example : (Expr.binary (.arith .mod) age (dec (1/2))).IsSafe Γu := by decide +kernel
example : (Expr.binary .and (.binary (.cmp .gt) age (int 25)) (.unary .isNotNull dept)).IsSafePredicate Γu := by
  decide

-- Lowering: an expression over `users ⋈ orders` that reads only the left side
example : (Expr.binary (.cmp .eq) (.col 0) (.col 2) : Expr (4 + 4)).lowerLeft =
    some (Expr.binary (.cmp .eq) (.col 0) (.col 2)) := by decide
example : (Expr.binary (.cmp .eq) (.col 0) (.col 5) : Expr (4 + 4)).lowerLeft = none := by decide

private def pred : Expr 4 := .binary .and (.binary (.cmp .gt) age (int 25)) (.unary .isNotNull dept)

/-- Soundness on the typed test database: a safe predicate never fails on a row of `users`. -/
example (r : Row 4) (hr : r ∈ db .users) : ∃ t, pred.evalTruth r = .ok t := by
  -- `IsSafePredicate`'s instance is stated for one `n`; unfold it so that `decide` sees
  -- `schema.arity .users` and `4` as the same arity.
  have hs : IsSafePredicate (schema.ctx .users) pred := by unfold IsSafePredicate; decide
  exact hs.exists_evalTruth_eq_ok (db_conforms .users r hr)

-- Preconditions (`SqlEquiv/Equiv/Defs.lean` counterparts)
example : dept.IsSafeText Γu := by decide
example : ¬ age.IsText Γu := by decide
example : (Expr.lit (.bool true) : Expr 4).IsTwoValued Γu := isTwoValued_lit_bool Γu true

end SqlCoreTest.ExprExamples
