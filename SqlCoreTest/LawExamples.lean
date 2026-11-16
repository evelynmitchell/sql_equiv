/-
  Typed core phase 5 (#294): checked uses of the equivalence and the laws.

  * `Queries`: cslib-frontier's `CslibFrontierTests/Languages/SQL/QueryLaws.lean`
    (pinned `e78796a1`, by Evelyn Mitchell and Samuel Schlesinger). Each query
    law is applied with its side conditions discharged by `decide`, and for
    each side condition there is a concrete instance on which the law fails
    without it.
  * `Exprs`: the same project's `CslibFrontierTests/Languages/SQL/Expr.lean`.
  * `ExprSideConditions`: ours. For each expression law with a side
    condition, a conforming row on which the law fails without it.
-/
import SqlCoreTest.QueryExamples

namespace SqlCoreTest.LawExamples

namespace Queries

open SqlCore SqlCore.Query SqlCoreTest.QueryExamples.Frontier
open SqlCore.Expr (col lit unary binary)

/-- A query that succeeds on an instance and one that fails there are not equivalent, at any
level. -/
theorem not_equiv_of_toOption {n : ℕ} {ℓ : EquivLevel} {q₁ q₂ : Query S n} {rs : List (Row n)}
    (h₁ : (q₁.eval D).toOption = some rs) (h₂ : (q₂.eval D).toOption = none) :
    ¬Equiv ℓ q₁ q₂ := fun h => by
  have h' := h D hD
  rw [h₁, h₂] at h'
  exact Option.not_rel_some_none h'

/-- `dept / 0 = 1`: well-typed but unsafe, and failing on every employee with a department. -/
abbrev divZeroEq : Expr 2 := binary (.cmp .eq) (binary (.arith .div) (col 1) (int 0)) (int 1)

/-- The typing contexts of `emp` and `dept`. -/
abbrev Γemp : Fin 2 → SqlType := S.ctx T.emp
abbrev Γdept : Fin 2 → SqlType := S.ctx T.dept

example : ¬divZeroEq.IsSafePredicate Γemp := by decide

/-! ### Selections -/

-- `WHERE dept = 1` then `WHERE name = 'ann'` is one `WHERE dept = 1 AND name = 'ann'`.
example : Equiv .ordered (select isAnn (select isOne emp)) (select (binary .and isOne isAnn) emp) :=
  select_select rfl (by decide) isOne

-- Without safety of the outer predicate: the inner `WHERE FALSE` keeps nothing, so the left side
-- never evaluates `dept / 0`, while the conjunction evaluates it on every row.
example : ¬Equiv .set (select divZeroEq (select (lit (.bool false)) emp))
    (select (binary .and (lit (.bool false)) divZeroEq) emp) :=
  not_equiv_of_toOption (rs := []) (by decide) (by decide)

example : Equiv .ordered (select isAnn (select isOne emp)) (select isOne (select isAnn emp)) :=
  select_comm rfl (by decide) (by decide)

-- Without safety of the inner predicate: `WHERE dept / 0 = 1` fails on `emp`, while after the
-- exchange `WHERE FALSE` leaves it no row to fail on.
example : ¬Equiv .set (select (lit (.bool false)) (select divZeroEq emp))
    (select divZeroEq (select (lit (.bool false)) emp)) := by
  refine fun h => not_equiv_of_toOption (rs := []) (ℓ := .set) ?_ ?_ h.symm <;> decide

-- Without safety of the outer predicate: the same two queries, exchanged.
example : ¬Equiv .set (select divZeroEq (select (lit (.bool false)) emp))
    (select (lit (.bool false)) (select divZeroEq emp)) :=
  not_equiv_of_toOption (rs := []) (by decide) (by decide)

/-- `SELECT dept, dept + 1 FROM emp`. -/
abbrev deptSucc : Fin 2 → Expr 2 := ![col 1, binary (.arith .add) (col 1) (int 1)]

-- `SELECT * FROM (SELECT dept, dept + 1 FROM emp) WHERE col 1 > 1` filters `emp` by
-- `dept + 1 > 1`, the predicate with the projection substituted.
example : Equiv .ordered (select (binary (.cmp .gt) (col 1) (int 1)) (project deptSucc emp))
    (project deptSucc (select (binary (.cmp .gt) (binary (.arith .add) (col 1) (int 1)) (int 1))
      emp)) :=
  select_project (es := deptSucc) rfl (by decide) _

-- Without safety of the projection: the left side evaluates `dept / 0` on every row, the right
-- side only on the rows that `WHERE FALSE` keeps.
example : ¬Equiv .set (select (lit (.bool false)) (project ![divZeroEq] emp))
    (project ![divZeroEq] (select ((lit (.bool false)).subst ![divZeroEq]) emp)) := by
  refine fun h => not_equiv_of_toOption (rs := []) (ℓ := .set) ?_ ?_ h.symm <;> decide

-- Pushing `name = 'ann'` into the left input of `emp JOIN dept ON emp.dept = dept.id`, and
-- `id = 1` into the right input.
example : Equiv .ordered (select (isAnn.rename (Fin.castAdd 2)) empDept)
    (join (binary (.cmp .eq) (col 1) (col 2)) (select isAnn emp) dept) :=
  select_join_left (Γ := Γemp) (Δ := Γdept) rfl rfl (by decide) (by decide)

/-- `id = 1` over `dept`. -/
abbrev idOne : Expr 2 := binary (.cmp .eq) (col 0) (int 1)

example : Equiv .ordered (select (idOne.rename (Fin.natAdd 2)) empDept)
    (join (binary (.cmp .eq) (col 1) (col 2)) emp (select idOne dept)) :=
  select_join_right (Γ := Γemp) (Δ := Γdept) rfl rfl (by decide) (by decide)

/-- `id / 0 = 1` over `dept`: unsafe, and failing on every department. -/
abbrev idDivZeroEq : Expr 2 := binary (.cmp .eq) (binary (.arith .div) (col 0) (int 0)) (int 1)

-- Without safety of the pushed predicate: joined with the empty table, the left side evaluates
-- nothing, while the pushed `WHERE` evaluates `dept / 0` on every employee.
example : ¬Equiv .set (select (divZeroEq.rename (Fin.castAdd 2))
      (join (binary (.cmp .eq) (col 1) (col 2)) emp empty))
    (join (binary (.cmp .eq) (col 1) (col 2)) (select divZeroEq emp) empty) :=
  not_equiv_of_toOption (rs := []) (by decide) (by decide)

-- The same for the right input: joined with the empty table on the left by `ON x = id`, a safe
-- predicate, the left side evaluates nothing, while the pushed `WHERE` evaluates `id / 0` on every
-- department.
example : (binary (.cmp .eq) (col 0) (col 2) : Expr 4).IsSafePredicate
    (Fin.append (S.ctx T.empty) Γdept) := by decide
example : ¬Equiv .set (select (idDivZeroEq.rename (Fin.natAdd 2))
      (join (binary (.cmp .eq) (col 0) (col 2)) empty dept))
    (join (binary (.cmp .eq) (col 0) (col 2)) empty (select idDivZeroEq dept)) :=
  not_equiv_of_toOption (rs := []) (by decide) (by decide)

-- Without safety of the join predicate: pushing `WHERE FALSE` into the left input leaves no pair
-- for `ON dept / 0 = 1` to fail on.
example : ¬Equiv .set (select ((lit (.bool false)).rename (Fin.castAdd 2))
      (join (divZeroEq.rename (Fin.castAdd 2)) emp dept))
    (join (divZeroEq.rename (Fin.castAdd 2)) (select (lit (.bool false)) emp) dept) := by
  refine fun h => not_equiv_of_toOption (rs := []) (ℓ := .set) ?_ ?_ h.symm <;> decide

-- The same for the right input: pushing `WHERE FALSE` into `dept` leaves no pair for
-- `ON dept / 0 = 1` to fail on.
example : ¬Equiv .set (select ((lit (.bool false)).rename (Fin.natAdd 2))
      (join (divZeroEq.rename (Fin.castAdd 2)) emp dept))
    (join (divZeroEq.rename (Fin.castAdd 2)) emp (select (lit (.bool false)) dept)) := by
  refine fun h => not_equiv_of_toOption (rs := []) (ℓ := .set) ?_ ?_ h.symm <;> decide

-- A `WHERE` over a cross join is the inner join.
example : Equiv .ordered
    (select (binary (.cmp .eq) (col 1) (col 2)) (join (lit (.bool true)) emp dept)) empDept :=
  select_join_true _ _ _

/-! ### Projections -/

-- `SELECT 2 * c0 FROM (SELECT dept, name FROM emp)` is `SELECT 2 * dept FROM emp`.
example : Equiv .ordered
    (project ![binary (.arith .mul) (col 0) (int 2)] (project ![col 1, col 0] emp))
    (project ![binary (.arith .mul) (col 1) (int 2)] emp) := by
  have h := project_project (q := emp) (g := ![col 1, col 0]) rfl (by decide)
    ![binary (.arith .mul) (col 0) (int 2)]
  have hf : (fun j => (![binary (.arith .mul) (col 0) (int 2)] j).subst ![col 1, col 0]) =
      (![binary (.arith .mul) (col 1) (int 2)] : Fin 1 → Expr 2) := by
    decide
  rwa [hf] at h

-- Without safety of the inner projection: the outer projection does not use it, so the fused
-- projection never evaluates `dept / 0`.
example : ¬Equiv .set (project ![int 1] (project ![divZeroEq] emp))
    (project (fun j => (![int 1] j).subst ![divZeroEq]) emp) := by
  refine fun h => not_equiv_of_toOption (ℓ := .set)
    (rs := [![some (.int 1)], ![some (.int 1)], ![some (.int 1)], ![some (.int 1)]]) ?_ ?_ h.symm
  <;> decide

example : Equiv .ordered (project Expr.col emp) emp := project_col emp

/-! ### `UNION ALL` -/

example : Equiv .ordered (select isOne (unionAll emp noDept))
    (unionAll (select isOne emp) (select isOne noDept)) :=
  select_unionAll _ _ _

example : Equiv .ordered (project ![col 0] (unionAll emp noDept))
    (unionAll (project ![col 0] emp) (project ![col 0] noDept)) :=
  project_unionAll _ _ _

example :
    Equiv .ordered (unionAll (unionAll emp noDept) emp) (unionAll emp (unionAll noDept emp)) :=
  unionAll_assoc _ _ _

-- Commutativity holds for bags; `SqlCoreTest.QueryExamples` checks that it fails for lists.
example : Equiv .bag (unionAll emp noDept) (unionAll noDept emp) := unionAll_comm _ _

/-! ### Joins -/

/-- `dept JOIN emp ON dept.id = emp.dept`, with the columns put back in the order of `empDept`. -/
abbrev deptEmp : Query S 4 :=
  project (fun i => col (finAddFlip (m := 2) (n := 2) i))
    (join ((binary (.cmp .eq) (col 1) (col 2)).rename (finAddFlip (m := 2) (n := 2))) dept emp)

example : Equiv .bag empDept deptEmp := join_comm _ _ _

-- The join predicate after the exchange compares the same columns.
example : ((binary (.cmp .eq) (col 1) (col 2) : Expr 4).rename (finAddFlip (m := 2) (n := 2))) =
    binary (.cmp .eq) (col 3) (col 0) := by
  decide

-- The pairs come in another order, so the two joins are not equal as lists.
example : ¬Equiv .ordered empDept deptEmp := by
  rw [equiv_ordered_iff]
  intro h
  exact absurd (h D hD) (by decide)

/-! ### `DISTINCT` -/

example :
    Equiv .ordered (distinct (distinct (project ![col 1] emp))) (distinct (project ![col 1] emp)) :=
  distinct_distinct _

example : Equiv .ordered (distinct (unionAll noDept noDept)) (distinct noDept) :=
  distinct_unionAll_self _

-- `WHERE` commutes with `DISTINCT` over a query with repeated rows, with no condition: an unsafe
-- predicate such as `dept / 0 = 1` fails on both sides alike.
example : Equiv .ordered (select isOne (distinct (unionAll emp emp)))
    (distinct (select isOne (unionAll emp emp))) :=
  select_distinct _ _

example : ((select divZeroEq (distinct emp)).eval D).toOption = none ∧
    ((distinct (select divZeroEq emp)).eval D).toOption = none := by
  decide

/-! ### Congruence in the expression arguments -/

/-- `AND` has the same observations in either order. -/
theorem and_comm_toOption (a b : Datum) :
    (evalBinOp .and a b).toOption = (evalBinOp .and b a).toOption := by
  rw [evalBinOp_and_comm]

-- Commuting an `AND` inside a `SELECT` list: the input's typing hypothesis is `rfl` for a table
-- and `decide` for a derived table.
example : Equiv .bag (project ![binary .and isOne isAnn] emp)
    (project ![binary .and isAnn isOne] emp) :=
  Equiv.project_expr (Γ := Γemp) rfl
    (Fin.forall_fin_one.mpr (Expr.Equiv.binary_comm and_comm_toOption _ _))

example : Equiv .ordered (project ![binary .and isOne isAnn] (select isOne emp))
    (project ![binary .and isAnn isOne] (select isOne emp)) :=
  Equiv.project_expr (Γ := Γemp) (by decide)
    (Fin.forall_fin_one.mpr (Expr.Equiv.binary_comm and_comm_toOption _ _))

-- Commuting an `AND` in a join predicate, in the joined typing context.
example : Equiv .set (join (binary .and (binary (.cmp .eq) (col 1) (col 2)) (isAnn.rename
      (Fin.castAdd 2))) emp dept)
    (join (binary .and (isAnn.rename (Fin.castAdd 2)) (binary (.cmp .eq) (col 1) (col 2)))
      emp dept) :=
  Equiv.join_expr (Γ := Γemp) (Δ := Γdept) rfl rfl (Expr.Equiv.binary_comm and_comm_toOption _ _)

-- Levels form a linear order, so `Query.Equiv.mono` composes with order lemmas.
example (q₁ q₂ : Query S 2) (h : Equiv .bag q₁ q₂) : Equiv .bag q₁ q₂ := h.mono le_rfl
example (q₁ q₂ : Query S 2) (h : Equiv .ordered q₁ q₂) : Equiv .set q₁ q₂ :=
  h.mono (le_trans (EquivLevel.ordered_le .bag) (by decide))

end Queries

namespace Exprs

open SqlCore SqlCore.Expr

abbrev int {n : ℕ} (z : ℤ) : Expr n := lit (.int z)

/-- The typing context `(int, int, text)`. -/
abbrev Γ : Fin 3 → SqlType := ![.int, .int, .text]

/-- The row `(1, NULL, 'x')`. -/
abbrev r : Row 3 := ![some (.int 1), none, some (.text "x")]

/-! ### Rows -/

example : r.Conforms Γ := by decide
example : ¬Row.Conforms Γ ![some (.text "1"), none, none] := by decide
example : r ≠ ![some (.int 1), none, none] := by decide
-- Rows computed by reindexing compare by `decide` too.
example : r ∘ Fin.rev = ![some (.text "x"), none, some (.int 1)] := by decide

/-! ### Evaluation -/

-- Column references read the row by position.
example : (col 0).eval r = .ok (some (.int 1)) := rfl
example : (binary (.arith .add) (col 0) (int 2)).eval r = .ok (some (.int 3)) := rfl

-- `NULL` propagates through `=`, so `x = x` is not `TRUE` when `x` is `NULL`: a rewriter may not
-- replace it by `TRUE` without knowing that `x` is non-null.
example : (binary (.cmp .eq) (col 1) (col 1)).evalTruth r = .ok .unknown := rfl
example : (unary .isNull (col 1)).evalTruth r = .ok .true := rfl
example : (binary .or (binary (.cmp .eq) (col 1) (int 1)) (unary .isNull (col 1))).evalTruth r =
    .ok .true := rfl
example : (inList (col 0) [some (.int 2), none]).evalTruth r = .ok .unknown := rfl

-- Errors: an ill-typed operand, a division by zero, and a non-boolean predicate.
example : (binary (.arith .add) (col 0) (col 2)).eval r = .error .typeMismatch := rfl
example : (binary (.arith .div) (col 0) (int 0)).eval r = .error .divisionByZero := rfl
example : (col 0).evalTruth r = .error .typeMismatch := rfl

-- Evaluation is strict: the left error is reported even though the right one comes later.
example : (binary (.cmp .lt) (binary (.arith .div) (col 0) (int 0)) (col 2)).eval r =
    .error .divisionByZero := rfl

-- `CASE` evaluates only the branch it takes: the error in the other branch is not raised.
example : (caseWhen (lit (.bool true)) (int 1) (binary (.arith .div) (col 0) (int 0))).eval r =
    .ok (some (.int 1)) := rfl
-- An `unknown` condition takes the `ELSE` branch.
example : (caseWhen (binary (.cmp .eq) (col 1) (int 1)) (binary (.arith .div) (col 0) (int 0))
    (int 2)).eval r = .ok (some (.int 2)) := rfl

/-! ### Renaming and substitution -/

-- A predicate on the left input of a join, moved onto the joined row.
example (s : Row 2) :
    ((binary (.cmp .gt) (col 0) (int 0)).rename (Fin.castAdd 2)).evalTruth (Fin.append r s) =
      .ok .true := by
  simp only [evalTruth, eval_rename_castAdd]
  rfl

-- A predicate on the output of `SELECT col 0 + 1, col 2` is a predicate on the input row.
example : ((binary (.cmp .eq) (col 0) (int 2)).subst
    ![binary (.arith .add) (col 0) (int 1), col 2]).evalTruth r = .ok .true := rfl

/-! ### Typing and safety -/

example : (binary (.arith .add) (col 0) (col 1)).typeOf Γ = some .int := rfl
example : (binary (.arith .add) (col 0) (col 2)).typeOf Γ = none := rfl
example : (caseWhen (unary .isNull (col 1)) (null .int) (col 0)).typeOf Γ = some .int := rfl
example : (inList (col 2) [some (.int 1)]).typeOf Γ = none := rfl

-- Type soundness: an `int`-typed expression never raises a type error on a conforming row.
example (s : Row 3) (hs : s.Conforms Γ) :
    (binary (.arith .add) (col 0) (col 1)).eval s ≠ .error .typeMismatch :=
  eval_ne_typeMismatch hs rfl

-- Division by a nonzero literal is safe; by a column it is not, even if the column is never zero.
example : (binary (.arith .div) (col 0) (int 2)).IsSafe Γ := by decide
example : ¬(binary (.arith .div) (col 0) (col 1)).IsSafe Γ := by decide
example : ¬(binary (.arith .div) (col 0) (int 0)).IsSafe Γ := by decide

-- A safe predicate selects or drops every conforming row without failing.
example (s : Row 3) (hs : s.Conforms Γ) :
    ∃ t, (binary (.cmp .le) (binary (.arith .mod) (col 0) (int 3)) (col 1)).evalTruth s = .ok t :=
  IsSafePredicate.exists_evalTruth_eq_ok (by decide) hs

/-! ### Equivalence -/

-- `NOT (a < b)` and `a >= b` are equivalent in any context.
example (a b : Expr 3) :
    Equiv Γ (unary .not (binary (.cmp .lt) a b)) (binary (.cmp .ge) a b) := by
  refine Equiv.of_eval_eq fun s _ => ?_
  simp only [eval_unary, eval_binary]
  rcases a.eval s with _ | x
  · rfl
  rcases b.eval s with _ | y
  · rfl
  exact (evalBinOp_cmp_negate .lt x y).symm

-- `a AND b` and `b AND a` may raise different first errors, but they are equivalent: equivalence
-- observes only success and result. Equivalences chain by `calc`.
example (a b c : Expr 3) :
    Equiv Γ (binary .and (binary .and a b) c) (binary .and c (binary .and b a)) :=
  have hand : ∀ x y, (evalBinOp .and x y).toOption = (evalBinOp .and y x).toOption :=
    fun x y => by rw [evalBinOp_and_comm]
  calc Equiv Γ (binary .and (binary .and a b) c) (binary .and (binary .and b a) c) :=
        (Equiv.binary_comm hand a b).binary .and (Expr.Equiv.refl c)
    Equiv Γ _ (binary .and c (binary .and b a)) := Equiv.binary_comm hand _ _

-- A safe predicate on the left input of a join stays safe on the joined row.
example : ((binary (.cmp .gt) (col 0) (int 0)).rename (Fin.castAdd 2)).IsSafePredicate
    (Fin.append Γ ![.bool, .text]) :=
  IsSafePredicate.rename _ (by decide)

/-- `x IS NULL OR x IS NOT NULL` for the column `x = col 0`. -/
abbrev nullOrNotNull : Expr 1 := binary .or (unary .isNull (col 0)) (unary .isNotNull (col 0))

-- `TRUE` and `x IS NULL OR x IS NOT NULL` are equivalent …
example : Equiv ![.int] (lit (.bool true)) nullOrNotNull := by
  refine Equiv.of_eval_eq fun s _ => ?_
  cases h : s 0 <;> simp [eval_binary, eval_unary, h, evalUnOp, evalBinOp, Datum.toTruth,
    Truth.toDatum]

-- … but substituting `1 / 0` for `x` breaks the equivalence: `Equiv.subst` needs `divSafe`.
example : (((lit (.bool true)).subst ![binary (.arith .div) (int 1) (int 0)]).eval
      (Fin.elim0 : Row 0)).toOption = some (some (.bool true)) ∧
    ((nullOrNotNull.subst ![binary (.arith .div) (int 1) (int 0)]).eval
      (Fin.elim0 : Row 0)).toOption = none := by
  decide

/-! ### Name resolution -/

/-- The columns `t.a : int`, `t.b : int`, `u.a : text`. -/
abbrev cols : Fin 3 → Column :=
  ![⟨some "t", "a", .int⟩, ⟨some "t", "b", .int⟩, ⟨some "u", "a", .text⟩]

example : resolveColumn cols none "b" = .ok 1 := rfl
example : resolveColumn cols (some "u") "a" = .ok 2 := rfl
example : resolveColumn cols none "a" = .error .ambiguousColumn := rfl
example : resolveColumn cols none "c" = .error .unknownColumn := rfl
example : resolveColumn cols (some "u") "b" = .error .unknownColumn := rfl

-- A resolved reference has the requested name and qualifier, and an ambiguous one has two
-- different matching columns.
example {i : Fin 3} (h : resolveColumn cols (some "t") "a" = .ok i) :
    (cols i).name = "a" ∧ (cols i).qualifier = some "t" :=
  Column.matches_some.mp (Column.Matches.of_resolveColumn_eq_ok h)
example : ∃ i j, i ≠ j ∧ (cols i).Matches none "a" ∧ (cols j).Matches none "a" :=
  resolveColumn_eq_ambiguousColumn_iff.mp rfl

end Exprs

/-! ### Expression laws without their side conditions -/

namespace ExprSideConditions

open SqlCore SqlCore.Expr

/-- Two expressions are not equivalent when some conforming row tells them apart. -/
theorem not_equiv_of_row {n : ℕ} {Γ : Fin n → SqlType} {e₁ e₂ : Expr n} (r : Row n)
    (hr : r.Conforms Γ) (h : (e₁.eval r).toOption ≠ (e₂.eval r).toOption) :
    ¬ Expr.Equiv Γ e₁ e₂ := fun h' => h (h' r hr)

/-- `(c0, c1) : (int, text)`, and the row `(5, 'a')`. -/
abbrev Γ : Fin 2 → SqlType := ![.int, .text]
abbrev r : Row 2 := ![some (.int 5), some (.text "a")]
abbrev c0 : Expr 2 := col 0
abbrev c1 : Expr 2 := col 1
abbrev tt : Expr 2 := lit (.bool true)
abbrev ff : Expr 2 := lit (.bool false)
/-- `c0 / 0 = 1`: boolean-typed but not safe. -/
abbrev unsafeP : Expr 2 := binary (.cmp .eq) (binary (.arith .div) c0 (lit (.int 0))) (lit (.int 1))

example : r.Conforms Γ := by decide
example : unsafeP.typeOf Γ = some .bool := by decide
example : ¬ unsafeP.IsSafePredicate Γ := by decide

-- `not_not` needs a boolean operand: `NOT NOT 5` fails, `5` does not.
example : ¬ Expr.Equiv Γ (unary .not (unary .not c0)) c0 := not_equiv_of_row r (by decide) (by decide)
-- `neg_neg` needs a numeric operand.
example : ¬ Expr.Equiv Γ (unary .neg (unary .neg c1)) c1 := not_equiv_of_row r (by decide) (by decide)
-- `and_true`, `true_and`, `or_false`, `false_or` need a boolean operand.
example : ¬ Expr.Equiv Γ (binary .and c1 tt) c1 := not_equiv_of_row r (by decide) (by decide)
example : ¬ Expr.Equiv Γ (binary .and tt c1) c1 := not_equiv_of_row r (by decide) (by decide)
example : ¬ Expr.Equiv Γ (binary .or c1 ff) c1 := not_equiv_of_row r (by decide) (by decide)
example : ¬ Expr.Equiv Γ (binary .or ff c1) c1 := not_equiv_of_row r (by decide) (by decide)
-- `and_false`, `false_and`, `or_true`, `true_or` need a safe predicate; boolean typing
-- is not enough, since the strict evaluation of `c0 / 0` fails.
example : ¬ Expr.Equiv Γ (binary .and unsafeP ff) ff := not_equiv_of_row r (by decide) (by decide)
example : ¬ Expr.Equiv Γ (binary .and ff unsafeP) ff := not_equiv_of_row r (by decide) (by decide)
example : ¬ Expr.Equiv Γ (binary .or unsafeP tt) tt := not_equiv_of_row r (by decide) (by decide)
example : ¬ Expr.Equiv Γ (binary .or tt unsafeP) tt := not_equiv_of_row r (by decide) (by decide)
-- `add_zero`, `zero_add`, `sub_zero`, `mul_one`, `one_mul` need a numeric operand.
example : ¬ Expr.Equiv Γ (binary (.arith .add) c1 (lit (.int 0))) c1 :=
  not_equiv_of_row r (by decide) (by decide)
example : ¬ Expr.Equiv Γ (binary (.arith .add) (lit (.int 0)) c1) c1 :=
  not_equiv_of_row r (by decide) (by decide)
example : ¬ Expr.Equiv Γ (binary (.arith .sub) c1 (lit (.int 0))) c1 :=
  not_equiv_of_row r (by decide) (by decide)
example : ¬ Expr.Equiv Γ (binary (.arith .mul) c1 (lit (.int 1))) c1 :=
  not_equiv_of_row r (by decide) (by decide)
example : ¬ Expr.Equiv Γ (binary (.arith .mul) (lit (.int 1)) c1) c1 :=
  not_equiv_of_row r (by decide) (by decide)
-- `inList_nil` needs a safe probe: `(c0 / 0) IN ()` fails, `FALSE` does not.
example : ¬ Expr.Equiv Γ (Expr.inList (binary (.arith .div) c0 (lit (.int 0))) []) ff :=
  not_equiv_of_row r (by decide) (by decide)

-- With the side conditions the laws hold; the arithmetic ones also for decimals.
example : Expr.Equiv Γ (binary .and unsafeP tt) unsafeP := Expr.Equiv.and_true (by decide)
example : Expr.Equiv ![SqlType.decimal] (binary (.arith .add) (col 0) (lit (.int 0))) (col 0) :=
  Expr.Equiv.add_zero (τ := .decimal) rfl (by decide)

end ExprSideConditions

end SqlCoreTest.LawExamples
