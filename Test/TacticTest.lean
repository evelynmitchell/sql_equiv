/-
  #278 step 2: `sql_equiv!` is kernel-checked.

  Compile-time checks. The goals below need `sql_equiv!`'s normalization
  branch (commutativity at several depths, which the plain rewrite list does
  not reach). Before #278 that branch could not fire (its `have` could not
  fill `syntacticEquiv _ _`) and used `native_decide`; now it is
  `refine syntacticEquiv_implies_equiv ?_; decide +kernel`.

  `#guard_msgs` pins the axioms of a theorem proved by the tactic: it must not
  gain `Lean.ofReduceBool` / `Lean.trustCompiler`.
-/
import SqlEquiv

namespace TacticTest
open SqlEquiv

private def a : Expr := .col ⟨none, "a"⟩
private def b : Expr := .col ⟨some "t", "b"⟩
private def c : Expr := .lit (.string "x")

theorem nested_comm :
    Expr.binOp .and (.binOp .or a (.binOp .add c b)) b ≃ₑ
      Expr.binOp .and b (.binOp .or (.binOp .add b c) a) := by
  sql_equiv!

theorem mul_under_not :
    Expr.unaryOp .not (.binOp .mul (.binOp .add a b) c) ≃ₑ
      Expr.unaryOp .not (.binOp .mul c (.binOp .add b a)) := by
  sql_equiv!

/-- info: 'TacticTest.nested_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nested_comm

/-- info: 'TacticTest.mul_under_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mul_under_not

-- `syntacticEquiv` itself, both directions, in the kernel
example : syntacticEquiv (.binOp .or a b) (.binOp .or b a) = true := by decide +kernel
example : syntacticEquiv (.binOp .or a b) (.binOp .and b a) = false := by decide +kernel
example : syntacticEquiv (.binOp .sub a b) (.binOp .sub b a) = false := by decide +kernel

-- #278 step 3: the aggregate / window detectors are total, so the
-- `hNoAgg`-style hypotheses of statement theorems are decided directly.
example : selectHasAggregate [.exprItem (.col ⟨some "t", "c"⟩) none] = false := by decide
example : selectHasAggregate [.exprItem (.func "f" [.countStar]) none] = true := by decide
example : selectHasWindowFn [.exprItem (.lit (.int 1)) none] = false := by decide
example : selectHasWindowFn
    [.exprItem (.case [(a, .windowFn .rank none (.mk [] []))] none) none] = true := by decide

end TacticTest
