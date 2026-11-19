/-
  #278 step 1: `DecidableEq` on the AST is total and kernel-reducible.

  These are compile-time checks: each `example` is decided by `decide`, which
  evaluates the generated deciders (`tools/gen_ast_deceq.py`) inside Lean's
  type checker. If the deciders became partial, opaque or `unsafe` again,
  `decide` could not reduce them and this file would fail to build.
  Both directions are covered (equal, and unequal with the same or a
  different constructor), for each mutual type and the nested
  `List` / `Option` / pair fields.
-/
import SqlEquiv

namespace AstDecEqTest
open SqlEquiv

private def x : Expr := .col ⟨none, "x"⟩
private def one : Expr := .lit (.int 1)
private def sel (w : Option Expr) : SelectStmt :=
  .mk false [.exprItem x none] (some (.table ⟨"t", none⟩)) w [] none [] none none

-- Same constructor, equal / unequal fields
example : Expr.binOp .add one x = Expr.binOp .add one x := by decide
example : Expr.binOp .add one x ≠ Expr.binOp .sub one x := by decide
example : Expr.binOp .add one x ≠ Expr.binOp .add x one := by decide

-- Different constructors
example : one ≠ Expr.countStar := by decide
example : Expr.countStar ≠ Expr.subquery (.simple (sel none)) := by decide

-- Nested fields: List Expr, Option Expr, List (Expr × Expr)
example : Expr.func "f" [one, x] = Expr.func "f" [one, x] := by decide
example : Expr.func "f" [one, x] ≠ Expr.func "f" [one] := by decide
example : Expr.agg (.sum .error) (some x) false ≠ Expr.agg (.sum .error) none false := by decide
example : Expr.«case» [(x, one)] none ≠ Expr.«case» [(one, one)] none := by decide
example : Expr.«case» [(x, one)] (some x) = Expr.«case» [(x, one)] (some x) := by decide

-- Through subqueries, SELECT, FROM, window specs and queries
example : Expr.exists false (.simple (sel (some x))) ≠ Expr.exists false (.simple (sel none)) := by
  decide
example : Expr.windowFn .rowNumber none (.mk [x] [.mk x .asc .last]) =
    Expr.windowFn .rowNumber none (.mk [x] [.mk x .asc .last]) := by decide
example : Query.compound (.simple (sel none)) .union (.simple (sel none)) ≠
    Query.simple (sel none) := by decide
example : Query.withCTE [.mk "c" (.simple (sel none)) false] (.simple (sel none)) ≠
    Query.withCTE [.mk "c" (.simple (sel none)) true] (.simple (sel none)) := by decide

-- `BEq` is the lawful one derived from `DecidableEq`
example : LawfulBEq Expr := inferInstance
example : LawfulBEq Query := inferInstance
example : LawfulBEq Stmt := inferInstance

end AstDecEqTest
