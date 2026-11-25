/-
  Certified statement-level equivalence checkers (#213, #278 step 4).

  **Over the reference oracle (decisions D3, D7, #466).** This works over `SqlEquiv`'s untyped
  evaluator, now a labelled reference oracle; its theorems are laws about that oracle. The
  project's rewriter and checker are the typed core's (`SqlCore.Expr.simplify`,
  `SqlCore.Query.checkEquiv`).

  `checkSelectEquiv` and `checkQueryEquiv` return a proof of `≃ₛ` / `≃ᵩ`, or
  `unknown`. They are sound by construction (every `proved` result carries a
  kernel-checked proof) and deliberately incomplete:

  - syntactically equal statements (via the generated `DecidableEq`);
  - SELECTs equal except for their WHERE clauses, when `checkEquivFull` proves
    the two predicates `≃ₑ` (lifted by `select_where_congr`, #238);
  - queries built from such SELECTs with the same set operations, when the left
    branches name their columns alike (congruence through `evalQuery_simple` /
    `evalQuery_compound`; the names matter since #340).

  This replaces the note in `Decidable.lean` that statement checkers were
  blocked on the `partial def` statement deciders.
-/
import SqlEquiv.Equiv.Decidable
import SqlEquiv.Equiv.StatementAxioms

namespace SqlEquiv

/-- Result of a statement-level check: a proof of `P`, or unknown. -/
inductive StmtCheckResult (P : Prop) where
  | proved : P → StmtCheckResult P
  | unknown : StmtCheckResult P

/-- Whether the check produced a proof. -/
def StmtCheckResult.isProved {P : Prop} : StmtCheckResult P → Bool
  | .proved _ => true
  | .unknown => false

/-- Certified SELECT equivalence check. `proved` carries `s1 ≃ₛ s2`. -/
def checkSelectEquiv (s1 s2 : SelectStmt) : StmtCheckResult (s1 ≃ₛ s2) :=
  if h : s1 = s2 then
    .proved (h ▸ select_equiv_refl s1)
  else
    match s1, s2 with
    | .mk d i f (some p) g hv o l off, .mk d' i' f' (some q) g' hv' o' l' off' =>
      if hrest : d = d' ∧ i = i' ∧ f = f' ∧ g = g' ∧ hv = hv' ∧ o = o' ∧ l = l' ∧ off = off' then
        match checkEquivFull p q with
        | .equiv hpq => .proved (by
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hrest
            exact select_where_congr hpq d i f g hv o l off)
        | _ => .unknown
      else .unknown
    | _, _ => .unknown

/-- Certified query equivalence check. `proved` carries `q1 ≃ᵩ q2`. -/
def checkQueryEquiv (q1 q2 : Query) : StmtCheckResult (q1 ≃ᵩ q2) :=
  if h : q1 = q2 then
    .proved (h ▸ query_equiv_refl q1)
  else
    match q1, q2 with
    | .simple s1, .simple s2 =>
      match checkSelectEquiv s1 s2 with
      | .proved hs => .proved (fun db => by
          rw [evalQuery_simple, evalQuery_simple]; exact hs db)
      | .unknown => .unknown
    | .compound l1 op1 r1, .compound l2 op2 r2 =>
      -- Equal results are not enough for the left branches: a set operation names its
      -- columns by its left branch's SELECT list (#340), and two empty results can come
      -- from lists with different names.
      if hop : op1 = op2 ∧ l1.outputNames? = l2.outputNames? then
        match checkQueryEquiv l1 l2, checkQueryEquiv r1 r2 with
        | .proved hl, .proved hr => .proved (fun db => by
            obtain ⟨rfl, hn⟩ := hop
            rw [evalQuery_compound, evalQuery_compound, hl db, hr db, hn])
        | _, _ => .unknown
      else .unknown
    | _, _ => .unknown

-- Compile-time smoke tests, one per reachable branch (kernel-checked).
section SmokeTests
private def cx : Expr := .col ⟨none, "x"⟩
private def cy : Expr := .col ⟨none, "y"⟩
private def i (n : Int) : Expr := .lit (.int n)
private def sel (w : Option Expr) : SelectStmt :=
  .mk false [.exprItem cx none] (some (.table ⟨"t", none⟩)) w [] none [] none none
-- x = 1 AND x > 0, and the same with the conjuncts swapped
private def wAnd1 : Expr := .binOp .and (.binOp .eq cx (i 1)) (.binOp .gt cx (i 0))
private def wAnd2 : Expr := .binOp .and (.binOp .gt cx (i 0)) (.binOp .eq cx (i 1))
-- ground: 1 + 1 = 2
private def wGround : Expr := .binOp .eq (.binOp .add (i 1) (i 1)) (i 2)
private def q (w : Option Expr) (op : SetOp) : Query := .compound (.simple (sel w)) op (.simple (sel none))

-- syntactic
example : (checkSelectEquiv (sel none) (sel none)).isProved = true := by decide +kernel
-- WHERE congruence via normalization
example : (checkSelectEquiv (sel (some wAnd1)) (sel (some wAnd2))).isProved = true := by
  decide +kernel
-- WHERE congruence via the ground semantic branch of checkEquivFull
example : (checkSelectEquiv (sel (some wGround)) (sel (some (.lit (.bool true))))).isProved =
    true := by decide +kernel
-- unknown: different WHERE predicates
example : (checkSelectEquiv (sel (some (.binOp .eq cx (i 1)))) (sel (some (.binOp .eq cx (i 2))))).isProved =
    false := by decide +kernel
-- unknown: WHERE vs no WHERE
example : (checkSelectEquiv (sel (some (.lit (.bool true)))) (sel none)).isProved = false := by
  decide +kernel
-- query: SELECT lifting and compound congruence
example : (checkQueryEquiv (q (some (.binOp .or cx cy)) .union) (q (some (.binOp .or cy cx)) .union)).isProved =
    true := by decide +kernel
-- query: different set operation is unknown
example : (checkQueryEquiv (q none .union) (q none .unionAll)).isProved = false := by decide +kernel
end SmokeTests

end SqlEquiv
