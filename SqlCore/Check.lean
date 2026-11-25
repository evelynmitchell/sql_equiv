/-
Copyright (c) 2026 Evelyn Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell
-/
module

public import SqlCore.Simplify
public import SqlCore.Canon
public import Mathlib.Data.Fintype.Basic

/-!
# Certified equivalence checkers (typed core phase 7, #296)

`Expr.checkEquiv Γ e₁ e₂` and `Query.checkEquiv q₁ q₂` either return a proof of equivalence or
`unknown`. They are sound by construction, since every `proved` result carries a kernel-checked
proof, and deliberately incomplete: two inputs are proved equivalent when the canonical forms
(`Expr.canon`, `Query.canon`) of their simplifications (`Expr.simplify`, `Query.simplify`) are
syntactically equal, and the certificates of both steps transfer the equality back to the inputs.

The tactics `sql_expr_equiv` and `sql_query_equiv` close goals `Expr.Equiv Γ e₁ e₂` and
`Query.Equiv ℓ q₁ q₂` by running the checker in the kernel (`decide +kernel`, no `native_decide`).

`Query` has no derived `DecidableEq`: its `table` constructor is indexed by the table's arity,
which defeats the deriving handler. `Query.beq` compares two queries of possibly different
arities, and `Query.eq_of_beq` makes the comparison sound.

These are the counterparts of `SqlEquiv`'s `checkSelectEquiv` and `checkQueryEquiv`
(`SqlEquiv/Equiv/StatementChecker.lean`).
-/

@[expose] public section

namespace SqlCore

/-- The result of a certified check: a proof of `P`, or no verdict. -/
inductive Check (P : Prop) : Type where
  | proved (h : P)
  | unknown

/-- Whether the check produced a proof. -/
def Check.isProved {P : Prop} : Check P → Bool
  | .proved _ => true
  | .unknown => false

theorem Check.of_isProved {P : Prop} {c : Check P} (h : c.isProved) : P := by
  cases c with
  | proved h' => exact h'
  | unknown => simp [Check.isProved] at h

namespace Expr

variable {n : ℕ}

/-- Simplification, then the canonical form. -/
def normalize (Γ : Fin n → SqlType) (e : Expr n) : Expr n := (e.simplify Γ).canon

theorem equiv_normalize (Γ : Fin n → SqlType) (e : Expr n) : Equiv Γ e (e.normalize Γ) :=
  (equiv_simplify Γ e).trans (sequiv_canon _ Γ)

/-- Certified expression equivalence: equal normal forms prove `Equiv Γ e₁ e₂`. -/
def checkEquiv (Γ : Fin n → SqlType) (e₁ e₂ : Expr n) : Check (Equiv Γ e₁ e₂) :=
  if h : e₁.normalize Γ = e₂.normalize Γ then
    .proved ((equiv_normalize Γ e₁).trans (h ▸ (equiv_normalize Γ e₂).symm))
  else .unknown

end Expr

namespace Query

variable {S : DbSchema} [DecidableEq S.Table]

/-- Structural comparison of two queries of possibly different arities. Every pair of
constructors is listed, so that Lean can generate the equation lemmas. -/
def beq : {n m : ℕ} → Query S n → Query S m → Bool
  | _, _, table t, q' =>
    match q' with
    | table t' => decide (t = t')
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, select (n := n) p q, q' =>
    match q' with
    | table _ => false
    | select (n := m) p' q' => if h : n = m then decide (h ▸ p = p') && beq q q' else false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, project (n := n) (k := k) es q, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project (n := n') (k := k') es' q' =>
      if h : n = n' ∧ k = k' then decide ((fun i => h.1 ▸ es (h.2 ▸ i)) = es') && beq q q' else false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, join (n := n₁) (m := m₁) θ q₁ q₂, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join (n := n₁') (m := m₁') θ' q₁' q₂' =>
      if h : n₁ = n₁' ∧ m₁ = m₁' then
        decide ((h.1 ▸ h.2 ▸ θ : Expr (n₁' + m₁')) = θ') && beq q₁ q₁' && beq q₂ q₂'
      else false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, unionAll q₁ q₂, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll q₁' q₂' => beq q₁ q₁' && beq q₂ q₂'
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, distinct q, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct q' => beq q q'
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, aggregate (n := n) (g := g) (a := a) keys aggs q, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate (n := n') (g := g') (a := a') keys' aggs' q' =>
      if h : n = n' ∧ g = g' ∧ a = a' then
        decide ((fun i => h.1 ▸ keys (h.2.1 ▸ i)) = keys') &&
          decide ((fun j => h.1 ▸ aggs (h.2.2 ▸ j)) = aggs') && beq q q'
      else false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, orderBy (n := n) (k := k) keys q, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy (n := n') (k := k') keys' q' =>
      if h : n = n' ∧ k = k' then
        decide ((fun i => h.1 ▸ keys (h.2 ▸ i)) = keys') && beq q q'
      else false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, limit c o q, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit c' o' q' => decide (c = c') && decide (o = o') && beq q q'
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, intersect q₁ q₂, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect q₁' q₂' => beq q₁ q₁' && beq q₂ q₂'
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, difference q₁ q₂, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference q₁' q₂' => beq q₁ q₁' && beq q₂ q₂'
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, attach (n := n) kind sub q, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach (n := n') kind' sub' q' =>
      if h : n = n' then decide (h ▸ kind = kind') && beq sub sub' && beq q q' else false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, one, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => true
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, outer (n := n) Γ, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer (n := n') Γ' => if h : n = n' then decide (h ▸ Γ = Γ') else false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, lateral (n := n) (k := k) body q, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral (n := n') (k := k') body' q' => beq body body' && beq q q'
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, window (n := n) c q, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window (n := n') c' q' => if h : n = n' then decide (h ▸ c = c') && beq q q' else false
    | recurse _ _ _ _ => false
    | outerJoin _ _ _ _ => false
  | _, _, recurse d k b st, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse d' k' b' st' => decide (d = d') && decide (k = k') && beq b b' && beq st st'
    | outerJoin _ _ _ _ => false
  | _, _, outerJoin (n := n) (m := m) k θ q₁ q₂, q' =>
    match q' with
    | table _ => false
    | select _ _ => false
    | project _ _ => false
    | join _ _ _ => false
    | unionAll _ _ => false
    | distinct _ => false
    | aggregate _ _ _ => false
    | orderBy _ _ => false
    | limit _ _ _ => false
    | intersect _ _ => false
    | difference _ _ => false
    | attach _ _ _ => false
    | one => false
    | outer _ => false
    | lateral _ _ => false
    | window _ _ => false
    | recurse _ _ _ _ => false
    | outerJoin (n := n') (m := m') k' θ' q₁' q₂' =>
      if h : n = n' ∧ m = m' then
        decide (k = k') && decide (h.1 ▸ h.2 ▸ θ = θ') && beq q₁ q₁' && beq q₂ q₂'
      else false

/-- `beq` is sound: equal results mean equal arities and equal queries. -/
theorem eq_of_beq {n m : ℕ} {q : Query S n} {q' : Query S m} (h : beq q q' = true) :
    ∃ h : n = m, h ▸ q = q' := by
  induction q generalizing m with
  | table t =>
    cases q' <;> simp only [beq, decide_eq_true_eq, reduceCtorEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | select p q ih =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    rename_i p' q'
    split_ifs at h with hn
    subst hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hq⟩ := h
    obtain ⟨hn', e⟩ := ih hq
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | project es q ih =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    split_ifs at h with hn
    obtain ⟨rfl, rfl⟩ := hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hq⟩ := h
    obtain ⟨hn', e⟩ := ih hq
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | join θ q₁ q₂ ih₁ ih₂ =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    split_ifs at h with hn
    obtain ⟨rfl, rfl⟩ := hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, h₁⟩, h₂⟩ := h
    obtain ⟨hn', e⟩ := ih₁ h₁
    cases hn'
    subst e
    obtain ⟨hn', e⟩ := ih₂ h₂
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | unionAll q₁ q₂ ih₁ ih₂ =>
    cases q' <;> simp only [beq, reduceCtorEq, Bool.and_eq_true] at h
    obtain ⟨hn', e⟩ := ih₁ h.1
    cases hn'
    subst e
    obtain ⟨hn', e⟩ := ih₂ h.2
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | distinct q ih =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    obtain ⟨hn', e⟩ := ih h
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | aggregate keys aggs q ih =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    split_ifs at h with hn
    obtain ⟨rfl, rfl, rfl⟩ := hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, hq⟩ := h
    obtain ⟨hn', e⟩ := ih hq
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | orderBy keys q ih =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    split_ifs at h with hn
    obtain ⟨rfl, rfl⟩ := hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hq⟩ := h
    obtain ⟨hn', e⟩ := ih hq
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | limit c o q ih =>
    cases q' <;> simp only [beq, reduceCtorEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, hq⟩ := h
    obtain ⟨hn', e⟩ := ih hq
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | intersect q₁ q₂ ih₁ ih₂ =>
    cases q' <;> simp only [beq, reduceCtorEq, Bool.and_eq_true] at h
    obtain ⟨hn', e⟩ := ih₁ h.1
    cases hn'
    subst e
    obtain ⟨hn', e⟩ := ih₂ h.2
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | difference q₁ q₂ ih₁ ih₂ =>
    cases q' <;> simp only [beq, reduceCtorEq, Bool.and_eq_true] at h
    obtain ⟨hn', e⟩ := ih₁ h.1
    cases hn'
    subst e
    obtain ⟨hn', e⟩ := ih₂ h.2
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | attach kind sub q ihs ihq =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    split_ifs at h with hn
    subst hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hs⟩, hq⟩ := h
    obtain ⟨hn', e⟩ := ihs hs
    cases hn'
    subst e
    obtain ⟨hn', e⟩ := ihq hq
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | one =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    exact ⟨rfl, rfl⟩
  | outer Γ =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    split_ifs at h with hn
    subst hn
    simp only [decide_eq_true_eq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | window c q ih =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    split_ifs at h with hn
    subst hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hq⟩ := h
    obtain ⟨hn', e⟩ := ih hq
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩
  | outerJoin k θ q₁ q₂ ih₁ ih₂ =>
    cases q' <;> simp only [beq, reduceCtorEq] at h
    split_ifs at h with hn
    obtain ⟨rfl, rfl⟩ := hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, h₁⟩, h₂⟩ := h
    obtain ⟨_, e₁⟩ := ih₁ h₁
    obtain ⟨_, e₂⟩ := ih₂ h₂
    subst e₁ e₂
    exact ⟨rfl, rfl⟩
  | recurse d k b st ihb ihs =>
    cases q' <;> simp only [beq, reduceCtorEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hb⟩, hs⟩ := h
    obtain ⟨hn', eb⟩ := ihb hb
    cases hn'
    subst eb
    obtain ⟨_, es⟩ := ihs hs
    subst es
    exact ⟨rfl, rfl⟩
  | lateral body q ihb ihq =>
    cases q' <;> simp only [beq, reduceCtorEq, Bool.and_eq_true] at h
    obtain ⟨hn', e⟩ := ihb h.1
    cases hn'
    subst e
    obtain ⟨hn', e⟩ := ihq h.2
    cases hn'
    subst e
    exact ⟨rfl, rfl⟩

theorem eq_of_beq_self {n : ℕ} {q q' : Query S n} (h : beq q q' = true) : q = q' := by
  obtain ⟨_, h⟩ := eq_of_beq h
  exact h

/-- Simplification, then the canonical form of every expression. -/
def normalize {n : ℕ} (q : Query S n) : Query S n := q.simplify.canon

omit [DecidableEq S.Table] in
theorem equiv_normalize {n : ℕ} (q : Query S n) : Equiv .ordered q q.normalize :=
  (equiv_simplify q).trans (equiv_canon _)

/-- Certified query equivalence: equal normal forms prove `Equiv .ordered q₁ q₂`, hence
equivalence at every level. -/
def checkEquiv {n : ℕ} (q₁ q₂ : Query S n) : Check (Equiv .ordered q₁ q₂) :=
  if h : beq q₁.normalize q₂.normalize = true then
    .proved ((equiv_normalize q₁).trans ((eq_of_beq_self h) ▸ (equiv_normalize q₂).symm))
  else .unknown

/-- A successful check proves equivalence at any level. -/
theorem equiv_of_check {n : ℕ} {ℓ : EquivLevel} {q₁ q₂ : Query S n}
    (h : (checkEquiv q₁ q₂).isProved = true) : Equiv ℓ q₁ q₂ :=
  (Check.of_isProved h).of_ordered

end Query

theorem Expr.equiv_of_check {n : ℕ} {Γ : Fin n → SqlType} {e₁ e₂ : Expr n}
    (h : (Expr.checkEquiv Γ e₁ e₂).isProved = true) : Expr.Equiv Γ e₁ e₂ :=
  Check.of_isProved h

/-- Close `Expr.Equiv Γ e₁ e₂` by running `Expr.checkEquiv` in the kernel. -/
macro "sql_expr_equiv" : tactic =>
  `(tactic| exact SqlCore.Expr.equiv_of_check (by decide +kernel))

/-- Close `Query.Equiv ℓ q₁ q₂` by running `Query.checkEquiv` in the kernel. -/
macro "sql_query_equiv" : tactic =>
  `(tactic| exact SqlCore.Query.equiv_of_check (by decide +kernel))

end SqlCore
