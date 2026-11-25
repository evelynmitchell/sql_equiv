/-
Copyright (c) 2026 Evelyn Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell
-/
module

public import SqlCore.Simplify

/-!
# Canonical forms modulo associativity and commutativity (typed core phase 7, #296)

`Expr.canon` puts an expression in a canonical form. It flattens chains of `AND` and of `OR`,
sorts the operands, and rebuilds the chain right-associated. It sorts the two operands of `=`,
`<>`, `+` and `*`, and turns `>` and `>=` into `<` and `<=` with the operands swapped. So
`b AND a` and `a AND b`, `x > 1` and `1 < x`, and `(a OR b) OR c` and `c OR (b OR a)` get the same
canonical form.

Every step is a law that holds with no side condition, under strict errors too: associativity
and commutativity of `AND`/`OR` (`Expr.Equiv.and_assoc`, `binary_comm`), and the comparison
swap (`evalBinOp_cmp_swap`). So the certificate is a *strong* equivalence, `Expr.SEquiv`:
equivalent in every typing context, which amounts to agreement on every row
(`Expr.SEquiv.toOption_eval`). Strong equivalence lifts into queries with no typing hypothesis
(`Query.equiv_canon`).

The order used for sorting (`Expr.cmp`) only decides which canonical form is chosen. Soundness
does not depend on it, since every reordering is justified by a law.

This is the counterpart of the normaliser in `SqlEquiv`'s decision procedure
(`SqlEquiv/Equiv/Decidable.lean`, `normalizeExpr`).
-/

@[expose] public section

namespace SqlCore

/-! ### Every row conforms to its own typing context -/

namespace Row

/-- The typing context read off a row: each cell's type, `int` for `NULL`. -/
def ctxOf {n : ℕ} (r : Row n) : Fin n → SqlType := fun i => ((r i).map Value.type).getD .int

theorem conforms_ctxOf {n : ℕ} (r : Row n) : r.Conforms r.ctxOf := fun i => by
  unfold ctxOf
  rcases r i with _ | v <;> simp

end Row

namespace Expr

variable {n : ℕ}

/-! ### Strong equivalence -/

/-- Equivalence in every typing context. -/
def SEquiv (e₁ e₂ : Expr n) : Prop := ∀ Γ : Fin n → SqlType, Equiv Γ e₁ e₂

namespace SEquiv

theorem refl (e : Expr n) : SEquiv e e := fun _ => Equiv.refl e
theorem symm {e₁ e₂ : Expr n} (h : SEquiv e₁ e₂) : SEquiv e₂ e₁ := fun Γ => (h Γ).symm
theorem trans {e₁ e₂ e₃ : Expr n} (h₁ : SEquiv e₁ e₂) (h₂ : SEquiv e₂ e₃) : SEquiv e₁ e₃ :=
  fun Γ => (h₁ Γ).trans (h₂ Γ)

/-- A strong equivalence is agreement on every row. -/
theorem toOption_eval {e₁ e₂ : Expr n} (h : SEquiv e₁ e₂) (r : Row n) :
    (e₁.eval r).toOption = (e₂.eval r).toOption :=
  h r.ctxOf r r.conforms_ctxOf

theorem toOption_evalTruth {e₁ e₂ : Expr n} (h : SEquiv e₁ e₂) (r : Row n) :
    (e₁.evalTruth r).toOption = (e₂.evalTruth r).toOption :=
  (h r.ctxOf).evalTruth r.conforms_ctxOf

theorem unary (op : UnOp) {e e' : Expr n} (h : SEquiv e e') :
    SEquiv (Expr.unary op e) (Expr.unary op e') := fun Γ => (h Γ).unary op

theorem binary (op : BinOp) {a a' b b' : Expr n} (ha : SEquiv a a') (hb : SEquiv b b') :
    SEquiv (Expr.binary op a b) (Expr.binary op a' b') := fun Γ => (ha Γ).binary op (hb Γ)

theorem inList {e e' : Expr n} (h : SEquiv e e') (vs : List Datum) :
    SEquiv (Expr.inList e vs) (Expr.inList e' vs) := fun Γ => (h Γ).inList vs

theorem caseWhen {c c' a a' b b' : Expr n} (hc : SEquiv c c') (ha : SEquiv a a')
    (hb : SEquiv b b') : SEquiv (Expr.caseWhen c a b) (Expr.caseWhen c' a' b') :=
  fun Γ => (hc Γ).caseWhen (ha Γ) (hb Γ)

end SEquiv

/-! ### A total order on expressions, for sorting -/

def SqlType.rank : SqlType → ℕ
  | .int => 0 | .text => 1 | .bool => 2 | .decimal => 3

def UnOp.rank : UnOp → ℕ
  | .not => 0 | .neg => 1 | .isNull => 2 | .isNotNull => 3 | .round _ => 4 | .lower => 5
  | .upper => 6 | .length => 7 | .toDecimal => 8

/-- The parameter of a unary operator (`ROUND`'s places), to order operators of one rank. -/
def UnOp.param : UnOp → ℤ
  | .round d => d
  | _ => 0

def BinOp.rank : BinOp → ℕ
  | .arith .add => 0 | .arith .sub => 1 | .arith .mul => 2 | .arith .div => 3
  | .arith .mod => 4 | .cmp .eq => 5 | .cmp .ne => 6 | .cmp .lt => 7 | .cmp .le => 8
  | .cmp .gt => 9 | .cmp .ge => 10 | .and => 11 | .or => 12 | .concat => 13
  | .like false => 14 | .like true => 15

def cmpValue : Value → Value → Ordering
  | .int a, .int b => compare a b
  | .text a, .text b => compare a b
  | .bool a, .bool b => compare a b
  | .decimal a, .decimal b => compare a b
  | a, b => compare (SqlType.rank a.type) (SqlType.rank b.type)

def cmpDatum : Datum → Datum → Ordering
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some a, some b => cmpValue a b

def cmpDatums : List Datum → List Datum → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (cmpDatum a b).then (cmpDatums as bs)

def tag : Expr n → ℕ
  | lit _ => 0 | null _ => 1 | col _ => 2 | unary _ _ => 3 | binary _ _ _ => 4
  | inList _ _ => 5 | caseWhen _ _ _ => 6

/-- A structural order on expressions: constructor, then fields. -/
def cmp : Expr n → Expr n → Ordering
  | lit a, lit b => cmpValue a b
  | null σ, null τ => compare (SqlType.rank σ) (SqlType.rank τ)
  | col i, col j => compare i j
  | unary o a, unary p b =>
    ((compare (UnOp.rank o) (UnOp.rank p)).then (compare (UnOp.param o) (UnOp.param p))).then
      (cmp a b)
  | binary o a₁ a₂, binary p b₁ b₂ =>
    (compare (BinOp.rank o) (BinOp.rank p)).then ((cmp a₁ b₁).then (cmp a₂ b₂))
  | inList a vs, inList b ws => (cmp a b).then (cmpDatums vs ws)
  | caseWhen a₁ a₂ a₃, caseWhen b₁ b₂ b₃ => (cmp a₁ b₁).then ((cmp a₂ b₂).then (cmp a₃ b₃))
  | a, b => compare (tag a) (tag b)

/-- Sorting order: `a` goes before `b` unless it compares greater. -/
def le (a b : Expr n) : Bool := cmp a b != .gt

/-! ### Chains of an associative and commutative operator -/

/-- The operands of a chain of `op`, left to right. -/
def flat (op : BinOp) : Expr n → List (Expr n)
  | binary o a b => if o = op then flat op a ++ flat op b else [binary o a b]
  | e => [e]

/-- A right-associated chain of `op` over a nonempty list. -/
def chain (op : BinOp) : List (Expr n) → Expr n
  | [] => lit (.bool true)
  | [a] => a
  | a :: b :: l => binary op a (chain op (b :: l))

theorem flat_ne_nil (op : BinOp) (e : Expr n) : flat op e ≠ [] := by
  cases e with
  | binary o a b =>
    unfold flat
    split_ifs
    · simp [flat_ne_nil op a]
    · simp
  | _ => simp [flat]

theorem chain_cons {op : BinOp} (a : Expr n) {l : List (Expr n)} (h : l ≠ []) :
    chain op (a :: l) = binary op a (chain op l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons b l => rfl

section Chain

variable {op : BinOp}
  (hassoc : ∀ a b c : Expr n, SEquiv (binary op (binary op a b) c) (binary op a (binary op b c)))
  (hcomm : ∀ a b : Expr n, SEquiv (binary op a b) (binary op b a))
include hassoc

theorem chain_append {l₁ l₂ : List (Expr n)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    SEquiv (chain op (l₁ ++ l₂)) (binary op (chain op l₁) (chain op l₂)) := by
  induction l₁ with
  | nil => exact absurd rfl h₁
  | cons a l ih =>
    by_cases hl : l = []
    · subst hl
      rw [List.singleton_append, chain_cons a h₂]
      exact .refl _
    · rw [List.cons_append, chain_cons a (by simp [hl]), chain_cons a hl]
      exact ((SEquiv.refl a).binary op (ih hl)).trans (hassoc _ _ _).symm

theorem chain_flat (e : Expr n) : SEquiv (chain op (flat op e)) e := by
  induction e with
  | binary o a b iha ihb =>
    unfold flat
    split_ifs with ho
    · subst ho
      exact (chain_append hassoc (flat_ne_nil _ a) (flat_ne_nil _ b)).trans (iha.binary _ ihb)
    · exact .refl _
  | _ => exact .refl _

include hcomm

theorem chain_perm {l₁ l₂ : List (Expr n)} (p : l₁.Perm l₂) (h : l₁ ≠ []) :
    SEquiv (chain op l₁) (chain op l₂) := by
  induction p with
  | nil => exact absurd rfl h
  | cons x p ih =>
    rename_i l l'
    by_cases hl : l = []
    · subst hl
      rw [List.Perm.nil_eq p]
      exact .refl _
    · have hl' : l' ≠ [] := fun h' => hl (List.Perm.eq_nil (h' ▸ p))
      rw [chain_cons x hl, chain_cons x hl']
      exact (SEquiv.refl x).binary op (ih hl)
  | swap x y l =>
    by_cases hl : l = []
    · subst hl
      exact hcomm y x
    · rw [chain_cons y (by simp), chain_cons x hl, chain_cons x (by simp), chain_cons y hl]
      exact (hassoc _ _ _).symm.trans (((hcomm y x).binary op (.refl _)).trans (hassoc _ _ _))
  | trans p₁ p₂ ih₁ ih₂ =>
    exact (ih₁ h).trans (ih₂ fun h' => h (List.Perm.eq_nil (h' ▸ p₁.symm).symm))

end Chain

/-- Insert into a sorted list. Insertion sort is structurally recursive, so the kernel evaluates
it (`List.mergeSort` is well-founded recursion, which `decide +kernel` does not unfold). -/
def insertSorted (a : Expr n) : List (Expr n) → List (Expr n)
  | [] => [a]
  | b :: l => if le a b then a :: b :: l else b :: insertSorted a l

def isort : List (Expr n) → List (Expr n)
  | [] => []
  | a :: l => insertSorted a (isort l)

theorem perm_insertSorted (a : Expr n) (l : List (Expr n)) : (insertSorted a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b l ih =>
    unfold insertSorted
    split_ifs
    · exact .refl _
    · exact ((ih.cons b).trans (.swap a b l))

theorem perm_isort (l : List (Expr n)) : (isort l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a l ih => exact (perm_insertSorted a _).trans (ih.cons a)

/-- Sort the chain of `op` rooted at `e`. -/
def sortChain (op : BinOp) (e : Expr n) : Expr n :=
  chain op (isort (flat op e))

theorem sequiv_sortChain {op : BinOp}
    (hassoc : ∀ a b c : Expr n, SEquiv (binary op (binary op a b) c) (binary op a (binary op b c)))
    (hcomm : ∀ a b : Expr n, SEquiv (binary op a b) (binary op b a)) (e : Expr n) :
    SEquiv e (sortChain op e) :=
  (chain_flat hassoc e).symm.trans
    (chain_perm hassoc hcomm (perm_isort _).symm (flat_ne_nil op e))

theorem and_assoc' (a b c : Expr n) :
    SEquiv (binary .and (binary .and a b) c) (binary .and a (binary .and b c)) :=
  fun _ => Equiv.and_assoc a b c

theorem or_assoc' (a b c : Expr n) :
    SEquiv (binary .or (binary .or a b) c) (binary .or a (binary .or b c)) :=
  fun _ => Equiv.or_assoc a b c

theorem comm_of {op : BinOp} (h : ∀ x y : Datum, evalBinOp op x y = evalBinOp op y x)
    (a b : Expr n) : SEquiv (binary op a b) (binary op b a) :=
  fun _ => Equiv.binary_comm (fun x y => by rw [h]) a b

/-! ### The canonical form -/

/-- One canonicalising step at a binary node whose operands are already canonical. -/
def canonBinary (op : BinOp) (a b : Expr n) : Expr n :=
  match op with
  | .and => sortChain .and (binary .and a b)
  | .or => sortChain .or (binary .or a b)
  | .cmp .eq => if cmp a b == .gt then binary (.cmp .eq) b a else binary (.cmp .eq) a b
  | .cmp .ne => if cmp a b == .gt then binary (.cmp .ne) b a else binary (.cmp .ne) a b
  | .cmp .gt => binary (.cmp .lt) b a
  | .cmp .ge => binary (.cmp .le) b a
  | .arith .add => if cmp a b == .gt then binary (.arith .add) b a else binary (.arith .add) a b
  | .arith .mul => if cmp a b == .gt then binary (.arith .mul) b a else binary (.arith .mul) a b
  | op => binary op a b

/-- The canonical form of an expression, bottom up. -/
def canon : Expr n → Expr n
  | unary op e => unary op e.canon
  | binary op a b => canonBinary op a.canon b.canon
  | inList e vs => inList e.canon vs
  | caseWhen c a b => caseWhen c.canon a.canon b.canon
  | e => e

private theorem cmp_swap_sequiv (op : CmpOp) (a b : Expr n) :
    SEquiv (binary (.cmp op) a b) (binary (.cmp op.swap) b a) :=
  fun _ r _ => by
    simp only [eval_binary]
    rcases a.eval r with ea | da <;> rcases b.eval r with eb | db <;>
      simp [evalBinOp_cmp_swap]

theorem sequiv_canonBinary (op : BinOp) (a b : Expr n) :
    SEquiv (binary op a b) (canonBinary op a b) := by
  unfold canonBinary
  split
  · exact sequiv_sortChain and_assoc' (comm_of evalBinOp_and_comm) _
  · exact sequiv_sortChain or_assoc' (comm_of evalBinOp_or_comm) _
  · split
    · exact cmp_swap_sequiv .eq a b
    · exact .refl _
  · split
    · exact cmp_swap_sequiv .ne a b
    · exact .refl _
  · exact cmp_swap_sequiv .gt a b
  · exact cmp_swap_sequiv .ge a b
  · split
    · exact comm_of evalBinOp_add_comm a b
    · exact .refl _
  · split
    · exact comm_of evalBinOp_mul_comm a b
    · exact .refl _
  · exact .refl _

/-- An expression is strongly equivalent to its canonical form. -/
theorem sequiv_canon (e : Expr n) : SEquiv e e.canon := by
  induction e with
  | unary op e ih => exact ih.unary op
  | binary op a b iha ihb => exact (iha.binary op ihb).trans (sequiv_canonBinary op _ _)
  | inList e vs ih => exact ih.inList vs
  | caseWhen c a b ihc iha ihb => exact ihc.caseWhen iha ihb
  | _ => exact .refl _

end Expr

/-! ### Queries -/

namespace Query

variable {S : DbSchema} {n m k : ℕ} {ℓ : EquivLevel}

/-- Every expression of the query in canonical form. -/
def canon : {n : ℕ} → Query S n → Query S n
  | _, table t => table t
  | _, select p q => select p.canon q.canon
  | _, project es q => project (fun i => (es i).canon) q.canon
  | _, join θ q₁ q₂ => join θ.canon q₁.canon q₂.canon
  | _, unionAll q₁ q₂ => unionAll q₁.canon q₂.canon
  | _, distinct q => distinct q.canon
  | _, aggregate keys aggs q => aggregate keys aggs q.canon
  | _, orderBy keys q => orderBy keys q.canon
  | _, limit c o q => limit c o q.canon
  | _, intersect q₁ q₂ => intersect q₁.canon q₂.canon
  | _, difference q₁ q₂ => difference q₁.canon q₂.canon
  | _, attach kind sub q => attach kind sub.canon q.canon
  | _, one => one
  | _, outer Γ => outer Γ
  | _, lateral body q => lateral body q.canon
  | _, window c q => window c q.canon

theorem select_sexpr {p p' : Expr n} (hp : p.SEquiv p') (q : Query S n) :
    Equiv ℓ (select p q) (select p' q) := fun D _ => by
  simp only [eval_select]
  rcases q.eval D with e | rs
  · exact .none
  · exact (EquivLevel.Rel.refl ℓ rs).filterRows fun r _ => hp.toOption_evalTruth r

theorem project_sexpr {es es' : Fin k → Expr n} (h : ∀ i, (es i).SEquiv (es' i)) (q : Query S n) :
    Equiv ℓ (project es q) (project es' q) := fun D _ => by
  simp only [eval_project]
  rcases q.eval D with e | rs
  · exact .none
  · exact (EquivLevel.Rel.refl ℓ rs).mapM_evalRow fun r _ =>
      Expr.toOption_evalRow_congr fun i => (h i).toOption_eval r

theorem join_sexpr {θ θ' : Expr (n + m)} (h : θ.SEquiv θ') (q₁ : Query S n) (q₂ : Query S m) :
    Equiv ℓ (join θ q₁ q₂) (join θ' q₁ q₂) := fun D _ => by
  simp only [eval_join]
  rcases q₁.eval D with e | rs
  · exact .none
  · rcases q₂.eval D with e | ss
    · exact .none
    · exact (EquivLevel.Rel.refl ℓ _).filterRows fun r _ => h.toOption_evalTruth r

/-- A query is ordered-equivalent to its canonical form. -/
theorem equiv_canon (q : Query S n) : Equiv .ordered q q.canon := by
  induction q with
  | table t => exact .refl _
  | select p q ih => exact (ih.select p).trans (select_sexpr (Expr.sequiv_canon p) _)
  | project es q ih =>
    exact (ih.project es).trans (project_sexpr (fun i => Expr.sequiv_canon (es i)) _)
  | join θ q₁ q₂ ih₁ ih₂ => exact (ih₁.join θ ih₂).trans (join_sexpr (Expr.sequiv_canon θ) _ _)
  | unionAll q₁ q₂ ih₁ ih₂ => exact ih₁.unionAll ih₂
  | distinct q ih => exact ih.distinct
  | aggregate keys aggs q ih => exact Equiv.aggregate keys aggs ih
  | orderBy keys q ih => exact Equiv.orderBy keys ih
  | limit c o q ih => exact Equiv.limit c o ih
  | intersect q₁ q₂ ih₁ ih₂ => exact Equiv.intersect ih₁ ih₂
  | difference q₁ q₂ ih₁ ih₂ => exact Equiv.difference ih₁ ih₂
  | attach kind sub q ihs ihq => exact Equiv.attach kind ihs ihq
  | one => exact .refl _
  | outer Γ => exact .refl _
  | lateral body q _ ihq => exact Equiv.lateral body ihq
  | window c q ih => exact Equiv.window c ih

end Query

end SqlCore
