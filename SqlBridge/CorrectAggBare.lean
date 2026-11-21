/-
  Elaborator correctness for aggregates without `GROUP BY` next to bare columns (#352, roadmap
  step 3b-6): `SELECT … FROM f [WHERE p]`, items aggregates of step 3a or bare columns (registry
  T9, sqlite), at least one aggregate. The elaborator builds the same query as for a grouped one,
  with no keys (`elab_grouped_shape` with `groupBy = []`): one aggregate row over every input row,
  even none. `SqlEquiv` reads the bare columns on its sample row (`bareSampleRow`), `[]` when the
  input is empty. A bare column is `AggCall.first` with no `MIN`/`MAX` and `AggCall.atExtreme` next
  to the one call (`BareOk`); over no rows both are `NULL`, as a column of the empty row is.
-/
import SqlBridge.CorrectGrouped

namespace SqlBridge.CorrectAggBare
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGroup SqlBridge.CorrectGroupOrder SqlBridge.CorrectGrouped

/-- A column read on the empty row (the sample row of no rows) is `NULL`. -/
theorem col_on_empty (db : SqlEquiv.Database) (U : SqlEquiv.Table) (c : SqlEquiv.ColumnRef) :
    (SqlEquiv.evalExprWithAggParam ee db U [] (.col c)).getD (.null none) = .null none := by
  rcases c with ⟨_ | t, col⟩ <;>
    simp [SqlEquiv.evalExprWithAggParam, ee, SqlEquiv.evalExprWithDb_col, SqlEquiv.Row.getQualified,
      SqlEquiv.Row.lookupCI]

/-- An aggregate item makes `SqlEquiv` take its aggregate path. -/
theorem selectHasAggregate_of_agg {items : List SqlEquiv.SelectItem}
    (hgi : groupedItems items = true) (hai : ∃ it ∈ items, itemAggFragment (itemExpr it) = true) :
    SqlEquiv.selectHasAggregate items = true := by
  obtain ⟨it, hit, hag⟩ := hai
  obtain ⟨x, al, rfl, -⟩ := groupedItems_mem hgi it hit
  simp only [SqlEquiv.selectHasAggregate, List.any_eq_true]
  refine ⟨_, hit, ?_⟩
  simp only [itemExpr] at hag
  cases x <;> simp_all [itemAggFragment, aggFragment, CorrectAvg.avgFragment, SqlEquiv.hasAggregate]

/-- `first` and `atExtreme` over no rows are `NULL`. -/
theorem bare_eval_nil {n : ℕ} {c : AggCall n} (hc : (∃ e, c = .first e) ∨ ∃ p k e, c = .atExtreme p k e)
    {d : Datum} (h : c.eval [] = .ok d) : d = none := by
  rcases hc with ⟨e, rfl⟩ | ⟨p, k, e, rfl⟩ <;>
    simp [AggCall.eval, bestAt, pure, Except.pure, bind, Except.bind] at h <;> exact h.symm

set_option maxHeartbeats 8000000 in
/-- **Elaborator correctness for aggregates without `GROUP BY`, with bare columns (#352, roadmap
    step 3b-6).** For `SELECT … FROM f [WHERE p]`, every item an aggregate of step 3a or a column,
    at least one an aggregate, the bare columns as `BareOk` allows (no `MIN`/`MAX`, or exactly
    one): when the statement elaborates, the typed query's one row relates to `SqlEquiv`'s, an
    `AVG` item (step 3c) up to `SqlEquiv`'s rounding (`OutRelI`). The typed query is safe, and
    the rows relate under every outer row too (the statement as a subquery body). -/
theorem elabStmt_correct_aggBare_ctx (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (hgi : groupedItems items = true) (hai : ∃ it ∈ items, itemAggFragment (itemExpr it) = true)
    (hff : fromFragment fr = true)
    (hwo : ∀ {n : ℕ} (qf q₀ : Query N.S n) (cf : Fin n → Column),
      elabFrom N (fun sq => elabSubQuery N 15 sq) fr = .ok ⟨n, qf, cf⟩ →
      elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf wh = .ok q₀ →
      WhereOk cf N.fold db D wh qf q₀)
    (hbf : BareOk N items [] none [])
    {e : Elaborated N.S} (h : elabStmt N (groupedStmt items fr wh [] none [] none none) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    e.q.IsSafe ∧ ∃ rs, e.q.eval D = .ok rs ∧
      (∃ out, (SqlEquiv.evalStmt db (groupedStmt items fr wh [] none [] none none)).2 = some out ∧
        List.Forall₂ (OutRelI items) rs out) ∧
      ∀ ctx, List.Forall₂ (OutRelI items) rs (SqlEquiv.evalSelectWithContext db ctx
        (.mk false items (some fr) wh [] none [] none none)) := by
  obtain ⟨hty, n, qf, cf, hf, q₀, hq₀, keyList, a, aggs, its, sk, mk, hk, hmk, haggs, hits, hsk,
    qh, hqh, rfl⟩ := elab_grouped_shape N hfoldCI hgi (.inr hai) (by simp) (by simp) (by simp) hbf h
  have hwo' := hwo qf q₀ cf hf hq₀
  simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hk
  subst hk
  cases hsk
  rcases hqh with ⟨-, rfl⟩ | ⟨hv, p, out, hhs, -⟩
  swap; · cases hhs
  simp only [limitWrap, List.length_nil, ↓reduceIte] at hty hnb ⊢
  -- a bare column's aggregate: `first` with no `MIN`/`MAX`, or `atExtreme` at the one
  have hmkC : ∀ c e', c ∈ colRefs items → elabExpr cf N.fold noHook (.col c) = .ok e' →
      ((∀ e, mk e = .first e) ∧ SqlEquiv.selectMinMaxCalls items none = []) ∨
        ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
          mode.bareRow = true ∧
          SqlEquiv.selectMinMaxCalls items none = [(wantMax, mode, some arg, false)] ∧
          isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
          ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e := by
    intro c e' hc he'
    obtain ⟨it, hit, hite⟩ := exists_item_of_colRefs hc
    exact hmk ⟨it, hit, c, e', hite, he', List.not_mem_nil⟩
  obtain ⟨hnames, hfrom⟩ := from_rel N hfold hfoldCI hwn hfix hD hrel _ fr hff hf
  simp only at hnames hfrom hty hnb ⊢
  -- typing
  obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
  obtain ⟨Γa, hΓa, -⟩ := Query.typeOf_project_eq_some.mp hΔ
  obtain ⟨Γ₀, Δk, Δa, hq₀ty, -, has, -⟩ := Query.typeOf_aggregate_eq_some hΓa
  obtain ⟨-, hnbA, hnbq₀⟩ := hnb
  have hnbAgg := (hnbA Γ₀ hq₀ty).2
  have hsrc : qf.typeOf = some Γ₀ := hwo'.src _ hq₀ty
  have hnbsrc : QNoBoolOrder qf := hwo'.nb hnbq₀
  obtain ⟨hdivf, Rf, hRf, hrelf⟩ := hfrom hsrc hnbsrc
  have hrows : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) Rf
      (SqlEquiv.evalFrom db fr) := hrelf.imp fun r u h =>
    ⟨rowRel_of_keyed N.fold hfold hfoldCI (fun j => (hnames j).1) (fun j => (hnames j).2) h.1, h.2⟩
  have hdivq₀ : q₀.divSafe = true := hwo'.div _ hq₀ty hnbq₀ hdivf
  obtain ⟨R, hR⟩ := Query.IsSafe.exists_eval_eq_ok (q := q₀) ⟨by simp [hq₀ty], hdivq₀⟩ hD
  have hRU₀ : ∃ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U :=
    ⟨_, hwo'.rel hq₀ty hnbq₀ hRf hR hrows⟩
  have hRconf : ∀ r ∈ R, r.Conforms Γ₀ := fun r hr => by
    obtain ⟨U, hU⟩ := hRU₀
    obtain ⟨u, -, h⟩ := forall₂_mem_left hU hr; exact h.2
  -- every aggregate is safe
  have hda : ∀ j, (aggs j).divSafe = true := fun j => by
    rcases haggs j with ⟨x, hx, hel⟩ | ⟨c, e', hc, he', -, hj⟩
    · exact itemAgg_divSafe cf N.fold x hx hel
    · obtain ⟨idx, rfl⟩ := elab_col_is_col cf N.fold c he'
      rcases hmkC c _ hc he' with ⟨hfst, -⟩ | ⟨w, m, arg, k', -, -, hfrag, hk', hat⟩
      · rw [hj, hfst]; rfl
      · rw [hj, hat]
        simp only [AggCall.divSafe, Bool.and_eq_true]
        exact ⟨Translates.divSafe _ _ (translates_of_elab cf N.fold arg hfrag hk'), rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, AggCall.evalAll aggs R = .ok A := by
    rcases AggCall.evalAll_ok_or_divisionByZero hRconf has with ⟨A, hA, -⟩ | ⟨-, j, hj⟩
    · exact ⟨A, hA⟩
    · rw [hda j] at hj; cases hj
  -- the typed query: one aggregate row, projected
  set row0 : Row (0 + a) := Fin.append (fun _ => none : Row 0) A with hrow0
  have hagg : ∀ keys : Fin 0 → Expr n, (Query.aggregate keys aggs q₀).eval D = .ok [row0] := by
    intro keys
    have hk : ∀ r : Row n, Expr.evalRow keys r = .ok (fun _ => none) := fun r =>
      Expr.evalRow_eq_ok_iff.mpr (fun i => i.elim0)
    rw [Query.eval_aggregate, hR]
    simp only [bind, Except.bind]
    rw [mapM_ok_map (g := fun r => ((fun _ => none : Row 0), r))
      (fun r _ => by simp [hk, pure, Except.pure])]
    simp only [Row.groups, ↓reduceIte, List.map_map]
    have : ((Prod.snd ∘ fun r : Row n => ((fun _ => none : Row 0), r)) : Row n → Row n) = id := rfl
    simp [this, List.mapM_cons, hA, pure, Except.pure, hrow0]
  -- each output column is an aggregate's column: an item aggregate, or a bare column's
  have hcol : ∀ i : Fin its.length, ∃ j : Fin a, (its[i.1]).1 = .col (Fin.natAdd _ j) ∧
      ((elabAgg cf N.fold (itemExpr (items[i.1]'(by have := hits.length_eq; omega))) = .ok (aggs j)) ∨
        ∃ c e', itemExpr (items[i.1]'(by have := hits.length_eq; omega)) = .col c ∧
          elabExpr cf N.fold noHook (.col c) = .ok e' ∧ aggs j = mk e') := fun i => by
    rcases (List.forall₂_iff_get.mp hits).2 i.1 (by have := hits.length_eq; omega) i.2 with
      ⟨j, hel, hj⟩ | ⟨c, i', -⟩ | ⟨c, j, e', hc, hel, -, hjf, hj⟩
    · exact ⟨j, hj, .inl hel⟩
    · exact i'.elim0
    · exact ⟨j, hj, .inr ⟨c, e', hc, hel, hjf⟩⟩
  have hex : ∀ i : Fin its.length, ∃ d, ((its[i.1]).1).eval row0 = .ok d := fun i => by
    obtain ⟨j, hj, -⟩ := hcol i
    rw [hj]; exact ⟨_, rfl⟩
  set r : Row its.length := fun i => (hex i).choose with hr
  have hrow : Expr.evalRow (fun i : Fin its.length => (its[i.1]).1) row0 = .ok r :=
    Expr.evalRow_eq_ok_iff.mpr fun i => (hex i).choose_spec
  have hitems : ∀ it ∈ items, ∃ e al, it = .exprItem e al := fun it hit => by
    obtain ⟨e, al, h, -⟩ := groupedItems_mem hgi it hit; exact ⟨e, al, h⟩
  -- each item's value, over any related input rows, on their sample row
  have final : ∀ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U →
      List.Forall₂ (fun (x : SqlEquiv.SelectItem × Datum) v => ItemRel x.1 x.2 v)
        (items.zip (List.ofFn r)) (items.map fun it =>
        (SqlEquiv.evalExprWithAggParam ee db U
          ((SqlEquiv.bareSampleRow (fun r e => SqlEquiv.evalExprWithDb db r e)
            (SqlEquiv.selectMinMaxCalls items none) U).getD []) (itemExpr it)).getD (.null none)) := by
    intro U hRU
    apply List.forall₂_iff_get.mpr
    refine ⟨by simp [hits.length_eq], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_zip, List.getElem_ofFn, List.getElem_map]
    have hi : i < its.length := by simp at h1; omega
    have hi' : i < items.length := by simpa using h2
    obtain ⟨j, hj, hcase⟩ := hcol ⟨i, hi⟩
    have hri : r ⟨i, hi⟩ = A j := by
      have h1 := (hex ⟨i, hi⟩).choose_spec
      have h2 : ((its[i]).1).eval row0 = .ok (A j) := by
        rw [hj]
        show Except.ok (row0 (Fin.natAdd _ j)) = _
        rw [hrow0, Fin.append_right]
      exact Except.ok.inj (h1.symm.trans h2)
    simp only [hri]
    rcases hcase with hel | ⟨c, e', hc, hel, hjf⟩
    · -- an aggregate
      obtain ⟨x, al, hx, hcase'⟩ := groupedItems_mem hgi _ (List.getElem_mem hi')
      have hfr' : itemAggFragment (itemExpr items[i]) = true := by
        rw [hx]; simp only [itemExpr]
        rcases hcase' with h | ⟨c, rfl⟩
        · exact h
        · rw [hx] at hel; simp [itemExpr, elabAgg, throw, throwThe, MonadExceptOf.throw] at hel
      simp only [itemAggFragment, Bool.or_eq_true] at hfr'
      rcases hfr' with hfr | hfr
      · rw [ItemRel, if_neg (by simp [avgFragment_false_of_agg hfr])]
        obtain ⟨v, hv, hvr⟩ := agg_rel cf N.fold db hRU _ _ hfr hel (hnbAgg j) (has j)
          (evalAll_get hA j)
        rw [hv]; exact hvr
      · rw [ItemRel, if_pos hfr]
        obtain ⟨v, hv, hvr⟩ := CorrectAvg.avg_rel cf N.fold db hRU _ _ hfr hel (hnbAgg j) (has j)
          (evalAll_get hA j)
        rw [hv]; exact hvr
    · -- a bare column
      have hcr : c ∈ colRefs items := by
        obtain ⟨x, al, hx, -⟩ := groupedItems_mem hgi _ (List.getElem_mem hi')
        rw [hx] at hc; simp only [itemExpr] at hc; subst hc
        exact colRefs_of_mem (List.getElem_mem hi') hx
      have htr := translates_of_elab cf N.fold (.col c) rfl hel
      have hnbe : NoBoolOrder Γ₀ e' := by
        obtain ⟨idx, rfl⟩ := elab_col_is_col cf N.fold c hel; trivial
      have hfe := evalAll_get hA j
      rw [hjf] at hfe
      rw [ItemRel, hc, if_neg (by simp [CorrectAvg.avgFragment])]
      rcases hmkC c e' hcr hel with ⟨hfst, hcalls⟩ |
        ⟨wantMax, mode, arg, k', hm, hcalls, hfrag, hk', hat⟩
      · -- no `MIN`/`MAX`: `first`, on the first row
        rw [hfst] at hfe
        rw [hcalls, bareSampleRow_nil_calls]
        rcases hRU with _ | ⟨hrow₀, -⟩
        · rw [bare_eval_nil (.inl ⟨_, rfl⟩) hfe]
          exact ⟨_, col_on_empty db _ c⟩
        · simp only [List.head?_cons, Option.getD_some]
          obtain ⟨v, hv, hvr⟩ := Translates.eval_rel cf N.fold db hrow₀.1 hrow₀.2 htr hnbe
            (first_eval hfe)
          simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
          exact hvr
      · -- one `MIN`/`MAX`: `atExtreme`, on the row where its argument is extreme
        rw [hat] at hfe
        rw [hcalls]
        rcases hRU with _ | ⟨hrow₀, hrest⟩
        · rw [bare_eval_nil (.inr ⟨_, _, _, rfl⟩) hfe]
          rw [(SqlEquiv.bareSampleRow_eq_none_iff _ _ _).mpr rfl, Option.getD_none]
          exact ⟨_, col_on_empty db _ c⟩
        · have hRU : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) _ _ :=
            List.Forall₂.cons hrow₀ hrest
          have hagj := hnbAgg j
          rw [hjf, hat] at hagj
          obtain ⟨hnbk, -⟩ := hagj
          obtain ⟨τ, hkty, hτ⟩ : ∃ τ, k'.typeOf Γ₀ = some τ ∧ τ ≠ .bool := by
            have hty' := has j
            rw [hjf, hat] at hty'
            simp only [AggCall.typeOf] at hty'
            split at hty'
            all_goals first
              | (rename_i hk; exact ⟨_, hk, by simp⟩)
              | cases hty'
          obtain ⟨s', hs', v, hv, hvr⟩ := CorrectExtreme.atExtreme_rel cf N.fold db hτ hm
            (translates_of_elab cf N.fold arg hfrag hk') hnbk hkty htr hnbe hRU (by simp) hfe
          rw [hs', Option.getD_some]
          simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
          exact hvr
  have hsafe : (Query.project (fun i : Fin its.length => (its[i]).1)
      (Query.aggregate (fun i : Fin 0 => i.elim0) aggs q₀)).IsSafe := by
    refine ⟨hty, ?_⟩
    have h1 : ∀ i : Fin its.length, ((its[i]).1).divSafe = true := fun i => by
      obtain ⟨j, hj, -⟩ := hcol i
      show ((its[i.1]).1).divSafe = true
      rw [hj]; rfl
    simp only [Query.divSafe, hda, hdivq₀, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun i => h1 i, fun i => i.elim0, fun _ => trivial⟩
  refine ⟨hsafe, [r], by rw [Query.eval_project, hagg _]; simp [hrow, pure, Except.pure, bind, Except.bind],
    ⟨_, rfl, ?_⟩, fun ctx => ?_⟩
  rotate_left
  · -- under an outer row (a subquery body)
    rw [SqlEquiv.evalSelectWithContext_eq_evalSelectCore, evalSelectCore_agg_ctx _ _ _ _ _ _ _ _ _
      _ _ _ _ _ (selectHasAggregate_of_agg hgi hai)]
    refine .cons ⟨hits.length_eq, ?_⟩ .nil
    rw [items_vals_group db _ _ hitems]
    apply final
    refine hwo'.rel hq₀ty hnbq₀ hRf hR ?_
    rw [List.forall₂_map_right_iff]
    exact hrows.imp fun r u h => ⟨rowRel_append ctx h.1, h.2⟩
  -- `SqlEquiv`'s side: one row of the items' values, on its sample row
  simp only [SqlEquiv.evalQuery]
  rw [SqlEquiv.evalSelect_eq_evalSelectCore, evalSelectCore_agg _ _ _ _ _ _ _ _ _ _ _ _ _
    (selectHasAggregate_of_agg hgi hai)]
  refine .cons ⟨hits.length_eq, ?_⟩ .nil
  rw [items_vals_group db _ _ hitems]
  apply final
  exact hwo'.rel hq₀ty hnbq₀ hRf hR hrows

/-- `elabStmt_correct_aggBare_ctx` as a statement theorem. -/
theorem elabStmt_correct_aggBare_w (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (hgi : groupedItems items = true) (hai : ∃ it ∈ items, itemAggFragment (itemExpr it) = true)
    (hff : fromFragment fr = true)
    (hwo : ∀ {n : ℕ} (qf q₀ : Query N.S n) (cf : Fin n → Column),
      elabFrom N (fun sq => elabSubQuery N 15 sq) fr = .ok ⟨n, qf, cf⟩ →
      elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf wh = .ok q₀ →
      WhereOk cf N.fold db D wh qf q₀)
    (hbf : BareOk N items [] none [])
    {e : Elaborated N.S} (h : elabStmt N (groupedStmt items fr wh [] none [] none none) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupedStmt items fr wh [] none [] none none)).2 = some out ∧
        List.Forall₂ (OutRelI items) rs out := by
  obtain ⟨-, rs, hrs, hout, -⟩ := elabStmt_correct_aggBare_ctx N hfold hfoldCI hwn hfix hD hrel
    hgi hai hff hwo hbf h hnb
  exact ⟨rs, hrs, hout⟩

/-- `elabStmt_correct_aggBare_w` with a `WHERE` in the expression fragment. -/
theorem elabStmt_correct_aggBare (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (hgi : groupedItems items = true) (hai : ∃ it ∈ items, itemAggFragment (itemExpr it) = true)
    (hff : fromFragment fr = true) (hw : ∀ w ∈ wh, isFragment w = true)
    (hbf : BareOk N items [] none [])
    {e : Elaborated N.S} (h : elabStmt N (groupedStmt items fr wh [] none [] none none) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupedStmt items fr wh [] none [] none none)).2 = some out ∧
        List.Forall₂ (OutRelI items) rs out :=
  elabStmt_correct_aggBare_w N hfold hfoldCI hwn hfix hD hrel hgi hai hff
    (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq) hbf h hnb

end SqlBridge.CorrectAggBare
