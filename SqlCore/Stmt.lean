/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module

public import SqlCore.Query

/-!
# SQL statements that change an instance: INSERT, UPDATE, DELETE

`Stmt S` is a data-modifying statement over the schema `S` (phase 9.7, #465). `Stmt.exec D s` runs
it on the instance `D` and returns the new instance, or the first error; the statement is atomic,
so an error leaves no partial change (the caller keeps `D`).

* `insert t q`: the rows of `q`, evaluated on the old instance, are appended to table `t`. The
  elaborator builds `q` from `VALUES` (a `UNION ALL` of one-row projections) or from a `SELECT`,
  with the columns of an explicit column list placed by position and the others `NULL`.
* `update t set w`: on each row of `t` where `w` is `TRUE`, column `i` becomes `set i`, every
  `set i` evaluated on the **old** row, as the engines do (`UPDATE t SET a = b, b = a` swaps). A
  column the statement does not assign has `set i = col i`. `set` is not evaluated on the other
  rows, so an error there cannot occur.
* `delete t w`: the rows of `t` where `w` is `TRUE` are removed; `w` is evaluated on every row.

Engines follow the same rules. `SqlEquiv`'s evaluator does not (each `SET` sees the earlier ones,
and `INSERT` without a column list makes up column names); the engines are the oracle (#458 D4).

Type soundness (`Stmt.exec_spec`): on a conforming instance, a well-typed statement returns a
conforming instance, or fails with a runtime error (`EvalError.IsRuntime`).
-/

@[expose] public section

namespace SqlCore

/-- A data-modifying statement over the schema `S`. -/
inductive Stmt (S : DbSchema) where
  /-- `INSERT INTO t …`: append the rows of a query of the table's arity. -/
  | insert (t : S.Table) (q : Query S (S.arity t))
  /-- `UPDATE t SET … WHERE w`: the new value of every column, read on the old row. -/
  | update (t : S.Table) (set : Fin (S.arity t) → Expr (S.arity t)) (w : Expr (S.arity t))
  /-- `DELETE FROM t WHERE w`. -/
  | delete (t : S.Table) (w : Expr (S.arity t))

namespace Stmt

variable {S : DbSchema}

/-- The statement is well-typed for its table: an inserted query has the table's types, each
assignment the type of its column, and a `WHERE` predicate is boolean. -/
def WellTyped : Stmt S → Prop
  | insert t q => q.typeOf = some (S.ctx t)
  | update t set w => (∀ i, (set i).typeOf (S.ctx t) = some (S.ctx t i)) ∧
      w.typeOf (S.ctx t) = some .bool
  | delete t w => w.typeOf (S.ctx t) = some .bool

instance : DecidablePred (WellTyped (S := S)) := fun s => by
  cases s <;> unfold WellTyped <;> infer_instance

variable [DecidableEq S.Table]

/-- Run the statement on `D`: the new instance, or the first error. -/
def exec (D : Database S) : Stmt S → Except EvalError (Database S)
  | insert t q => do
    let rs ← q.eval D
    return Function.update D t (D t ++ rs)
  | update t set w => do
    let rs ← (D t).mapM fun r => do
      if (← w.evalTruth r).isTrue then Expr.evalRow set r else pure r
    return Function.update D t rs
  | delete t w => do
    let rs ← (D t).filterMapM fun r => do
      return if (← w.evalTruth r).isTrue then none else some r
    return Function.update D t rs

/-- Replacing one table of a conforming instance by rows of the table's types gives a conforming
instance. -/
theorem conforms_update {D : Database S} (hD : D.Conforms) {t : S.Table}
    {rs : List (Row (S.arity t))} (hrs : ∀ r ∈ rs, r.Conforms (S.ctx t)) :
    Database.Conforms (Function.update D t rs) := by
  intro t' r hr
  by_cases h : t' = t
  · subst h
    rw [Function.update_self] at hr
    exact hrs r hr
  · rw [Function.update_of_ne h] at hr
    exact hD t' r hr

/-- Type soundness for statements: on a conforming instance, a well-typed statement returns a
conforming instance, or fails with a runtime error (division by zero, or a scalar subquery with
several rows). It never raises `typeMismatch`. -/
theorem exec_spec {D : Database S} (hD : D.Conforms) {s : Stmt S} (hs : s.WellTyped) :
    Except.Spec (s.exec D) Database.Conforms EvalError.IsRuntime := by
  cases s with
  | insert t q =>
    simp only [exec]
    refine ((Query.eval_spec hD hs).mono (fun _ h => h) fun e he => he.1).bind
      fun rs _ hrs => ?_
    refine conforms_update hD fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact hD t r hr
    · exact hrs r hr
  | update t set w =>
    obtain ⟨hset, hw⟩ := hs
    simp only [exec]
    refine (Except.Spec.mapM (R := fun _ r' => r'.Conforms (S.ctx t))
      (E := EvalError.IsRuntime) fun r hr => ?_).bind fun rs _ hrs => ?_
    · refine ((Expr.evalTruth_spec (hD t r hr) hw).mono (fun _ h => h)
        fun e he => Or.inl he.1).bind fun tr _ _ => ?_
      split
      · exact (Expr.evalRow_spec (hD t r hr) hset).mono (fun _ h => h) fun e he => Or.inl he.1
      · exact hD t r hr
    · exact conforms_update hD fun r' hr' => (hrs r' hr').elim fun _ ⟨_, h⟩ => h
  | delete t w =>
    simp only [exec]
    refine (Except.Spec.filterMapM (R := fun r r' => r' = r) (E := EvalError.IsRuntime)
      fun r hr => ?_).bind fun rs _ hrs => ?_
    · refine ((Expr.evalTruth_spec (hD t r hr) hs).mono (fun _ h => h)
        fun e he => Or.inl he.1).bind fun tr _ _ => ?_
      split <;> simp
    · refine conforms_update hD fun r' hr' => ?_
      obtain ⟨r, hr, h⟩ := hrs r' hr'
      rw [h]
      exact hD t r hr

/-- A successful well-typed statement on a conforming instance gives a conforming instance. -/
theorem exec_conforms {D D' : Database S} (hD : D.Conforms) {s : Stmt S} (hs : s.WellTyped)
    (h : s.exec D = .ok D') : D'.Conforms :=
  (exec_spec hD hs).of_eq_ok h

end Stmt

end SqlCore
