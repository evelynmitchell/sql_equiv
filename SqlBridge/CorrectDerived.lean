/-
  Elaborator correctness for a derived table in `FROM` (#412, part of #352).

  `SELECT COUNT(*), … FROM (sq) [AS al]`, where the body `sq` is a subquery body of
  `SqlBridge.CorrectSub.SubBodyOk`: a plain, aggregate or grouped statement, or a tree of
  `UNION [ALL]`, `INTERSECT` and `EXCEPT` over such statements.

  * Order. A set-operation body's rows are related only up to their order
    (`CorrectSetOp.PermRel`, registry T18), so the derived table's rows are too. `COUNT(*)` reads
    only how many rows there are, which a permutation keeps, so the outer statement's one row is
    related exactly (`List.Forall₂ OutRel`), with no permutation.
  * Names. `SqlEquiv` requalifies the body's rows by the alias (`requalifyRow`, #257; the parser
    names an anonymous derived table `sub`), and the elaborator requalifies its columns by the
    folded alias. `COUNT(*)` reads no column, so the outer statement here does not depend on how
    the two name the derived table's columns. Relating column references into a derived table
    would need the keys of `SqlEquiv`'s output rows, which the statement theorems do not state
    (they relate values by position, `OutRel`); that is left to a follow-up.
  * Fuel. The outer `SELECT` elaborates its `FROM` subquery with fuel 15, which `subBody_ctx`
    takes as `14 + 1`.
-/
import SqlBridge.CorrectSub

namespace SqlBridge.CorrectDerived
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectSub

/-- Every item is `COUNT(*)`, with or without an alias. -/
def countItems : List SqlEquiv.SelectItem → Bool
  | [] => true
  | .exprItem .countStar _ :: rest => countItems rest
  | _ :: _ => false

theorem aggItems_of_countItems : ∀ {items : List SqlEquiv.SelectItem}, countItems items = true →
    aggItems items = true
  | [], _ => rfl
  | .exprItem .countStar _ :: rest, h => by
    simp only [countItems] at h
    simp [aggItems, aggFragment, aggItems_of_countItems h]
  | .exprItem (.lit _) _ :: _, h | .exprItem (.col _) _ :: _, h
  | .exprItem (.binOp _ _ _) _ :: _, h | .exprItem (.unaryOp _ _) _ :: _, h
  | .exprItem (.func _ _) _ :: _, h | .exprItem (.agg _ _ _) _ :: _, h
  | .exprItem (.case _ _) _ :: _, h | .exprItem (.inList _ _ _) _ :: _, h
  | .exprItem (.between _ _ _) _ :: _, h | .exprItem (.inSubquery _ _ _) _ :: _, h
  | .exprItem (.exists _ _) _ :: _, h | .exprItem (.subquery _) _ :: _, h
  | .exprItem (.windowFn _ _ _) _ :: _, h | .star _ :: _, h => by simp [countItems] at h

theorem countItems_mem : ∀ {items : List SqlEquiv.SelectItem}, countItems items = true →
    ∀ it ∈ items, itemExpr it = .countStar
  | [], _, _, h => by cases h
  | .exprItem .countStar _ :: rest, h, it, hit => by
    simp only [countItems] at h
    rcases List.mem_cons.mp hit with rfl | hit
    · rfl
    · exact countItems_mem h it hit
  | .exprItem (.lit _) _ :: _, h, _, _ | .exprItem (.col _) _ :: _, h, _, _
  | .exprItem (.binOp _ _ _) _ :: _, h, _, _ | .exprItem (.unaryOp _ _) _ :: _, h, _, _
  | .exprItem (.func _ _) _ :: _, h, _, _ | .exprItem (.agg _ _ _) _ :: _, h, _, _
  | .exprItem (.case _ _) _ :: _, h, _, _ | .exprItem (.inList _ _ _) _ :: _, h, _, _
  | .exprItem (.between _ _ _) _ :: _, h, _, _ | .exprItem (.inSubquery _ _ _) _ :: _, h, _, _
  | .exprItem (.exists _ _) _ :: _, h, _, _ | .exprItem (.subquery _) _ :: _, h, _, _
  | .exprItem (.windowFn _ _ _) _ :: _, h, _, _ | .star _ :: _, h, _, _ => by
    simp [countItems] at h

/-- A derived table elaborates to its body's query, with the body's columns requalified. -/
theorem elabFrom_subquery_ok (N : NamedSchema) (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S))
    {sq : SqlEquiv.SubQuery} {al : String} {n : ℕ} {qf : Query N.S n} {cf : Fin n → Column}
    (h : elabFrom N sub (.subquery sq al) = .ok ⟨n, qf, cf⟩) :
    ∃ cols, sub sq = .ok ⟨n, qf, cols⟩ := by
  simp only [elabFrom] at h
  obtain ⟨⟨m, q, cols⟩, hs, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Elaborated.mk.injEq] at h
  obtain ⟨rfl, h1, -⟩ := h
  cases h1
  exact ⟨cols, hs⟩

/-- **Elaborator correctness for `COUNT(*)` over a derived table (#412).** For
    `SELECT COUNT(*), … FROM (sq) [AS al]` whose body `sq` is a subquery body of `SubBodyOk` (a
    plain, aggregate or grouped statement, or set operations over such statements): when the
    statement elaborates, the typed query evaluates to one row, related exactly to `SqlEquiv`'s
    one row. The body's rows are related only up to order (a set operation's are, registry T18);
    `COUNT(*)` does not see the order. Hypotheses as `elabStmt_correct_agg`'s. -/
theorem elabStmt_correct_countDerived (N : NamedSchema)
    (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {sq : SqlEquiv.SubQuery} {al : String}
    (hci : countItems items = true) (hne : items ≠ []) (hb : SubBodyOk sq)
    {e : Elaborated N.S} (h : elabStmt N (aggStmt items (.subquery sq al) none) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (aggStmt items (.subquery sq al) none)).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  have hai := aggItems_of_countItems hci
  obtain ⟨hty, n, qf, cf, hf, q₀, hq₀, a, aggs, keys, its, haggs, hits, rfl⟩ :=
    elab_agg_shape N hai hne h
  simp only [elabWhere, pure, Except.pure, Except.ok.injEq] at hq₀
  subst hq₀
  obtain ⟨cols, hsub⟩ := elabFrom_subquery_ok N _ hf
  simp only at hty hnb ⊢
  -- typing
  obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
  obtain ⟨Γa, hΓa, -⟩ := Query.typeOf_project_eq_some.mp hΔ
  obtain ⟨Γ₀, Δk, Δa, hq₀ty, -, has, -⟩ := Query.typeOf_aggregate_eq_some hΓa
  obtain ⟨-, -, hnbq₀⟩ := hnb
  -- the body: safe, and related up to order to `SqlEquiv`'s rows for it
  obtain ⟨-, ss, hss, hperm⟩ := subBody_ctx N hfold hfoldCI hwn hfix hD hrel hb
    (fu := 14) hsub (by simp [hq₀ty]) hnbq₀
  obtain ⟨ss', hp, hfa⟩ := hperm []
  have hlen : ss.length = (SqlEquiv.evalSubQueryWithContext db [] sq).length :=
    hp.length_eq.trans hfa.length_eq
  -- the aggregates over the body's rows
  have hRconf := Query.conforms_of_eval_eq_ok hD hq₀ty hss
  obtain ⟨A, hA⟩ : ∃ A, AggCall.evalAll aggs ss = .ok A := by
    rcases AggCall.evalAll_ok_or_divisionByZero hRconf has with ⟨A, hA, -⟩ | ⟨-, j, hj⟩
    · exact ⟨A, hA⟩
    · obtain ⟨x, hx, hel⟩ := haggs j
      rw [agg_divSafe cf N.fold x hx hel] at hj; cases hj
  have hk : ∀ r : Row n, Expr.evalRow keys r = .ok (fun _ => none) := fun r =>
    Expr.evalRow_eq_ok_iff.mpr (fun i => i.elim0)
  set row0 : Row (0 + a) := Fin.append (fun _ => none : Row 0) A with hrow0
  have hagg : (Query.aggregate keys aggs qf).eval D = .ok [row0] := by
    rw [Query.eval_aggregate, hss]
    simp only [bind, Except.bind]
    rw [mapM_ok_map (g := fun r => ((fun _ => none : Row 0), r)) (fun r _ => by simp [hk, pure, Except.pure])]
    simp only [Row.groups, ↓reduceIte, List.map_map]
    have : ((Prod.snd ∘ fun r : Row n => ((fun _ => none : Row 0), r)) : Row n → Row n) = id := rfl
    simp [this, List.mapM_cons, hA, pure, Except.pure, hrow0]
  have hcol : ∀ i : Fin its.length, ∃ j : Fin a,
      elabAgg cf N.fold (itemExpr (items[i.1]'(by have := hits.length_eq; omega))) = .ok (aggs j) ∧
      (its[i.1]).1 = .col (Fin.natAdd 0 j) := fun i =>
    (List.forall₂_iff_get.mp hits).2 i.1 _ i.2
  have hex : ∀ i : Fin its.length, ∃ d, ((its[i.1]).1).eval row0 = .ok d := fun i => by
    obtain ⟨j, -, hj⟩ := hcol i
    rw [hj]; exact ⟨_, rfl⟩
  set r : Row its.length := fun i => (hex i).choose with hr
  have hrow : Expr.evalRow (fun i : Fin its.length => (its[i.1]).1) row0 = .ok r :=
    Expr.evalRow_eq_ok_iff.mpr fun i => (hex i).choose_spec
  refine ⟨[r], by rw [Query.eval_project, hagg]; simp [hrow, pure, Except.pure, bind, Except.bind],
    _, rfl, ?_⟩
  -- `SqlEquiv`'s side: one row, each item the number of the derived table's rows
  simp only [SqlEquiv.evalQuery]
  rw [SqlEquiv.evalSelect_eq_evalSelectCore, evalSelectCore_agg _ _ _ _ _ _ _ _ _ _ _ _ _
    (selectHasAggregate_aggItems hai hne)]
  refine .cons ?_ .nil
  unfold OutRel
  rw [items_vals db _ _ hai]
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [hits.length_eq], fun i h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
  have hi : i < its.length := by simpa using h1
  have hi' : i < items.length := by simpa using h2
  obtain ⟨j, hel, hj⟩ := hcol ⟨i, hi⟩
  have hcs := countItems_mem hci _ (List.getElem_mem hi')
  simp only [hcs, elabAgg, pure, Except.pure, Except.ok.injEq] at hel
  have hri : r ⟨i, hi⟩ = A j := by
    have e1 := (hex ⟨i, hi⟩).choose_spec
    have e2 : ((its[i]).1).eval row0 = .ok (A j) := by
      rw [hj]
      show Except.ok (row0 (Fin.natAdd 0 j)) = _
      rw [hrow0, Fin.append_right]
    exact Except.ok.inj (e1.symm.trans e2)
  have hAj := evalAll_get hA j
  rw [← hel] at hAj
  simp only [AggCall.eval, Except.ok.injEq] at hAj
  simp only [hri, ← hAj, hcs, SqlEquiv.evalExprWithAggParam, Option.getD_some,
    SqlEquiv.evalFrom_subquery, List.length_map, hlen]
  exact .int _

end SqlBridge.CorrectDerived
