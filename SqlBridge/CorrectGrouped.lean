/-
  Elaborator correctness for grouped queries (#352, roadmap steps 3b-4, 3b-5): one statement for
  `SELECT … FROM f [WHERE p] GROUP BY c₁, … [HAVING h] [ORDER BY a₁, …] [LIMIT n] [OFFSET m]`,
  items aggregates of step 3a, key columns, or bare columns (registry T9), read on the group's
  first row or, next to one `MIN`/`MAX`, on the row where its argument is extreme.

  * `evalSelectCore_grouped_full`: `SqlEquiv`'s grouped path in closed form, `HAVING` and the
    per-group sort keys included.
  * `elab_grouped_shape`: the elaborator's query. A bare column becomes the aggregate
    `AggCall.first` when no `MIN`/`MAX` is written, so both evaluators read the group's first row,
    and `AggCall.atExtreme` next to exactly one (not DISTINCT, in a mode that picks the row), which
    `SqlBridge.CorrectExtreme.atExtreme_rel` relates to `SqlEquiv`'s `bareSampleRow` (`BareOk`).
    Item columns resolve in the `FROM` scope (the elaborator checks it).
-/
import SqlBridge.CorrectGroupOrder
import SqlBridge.CorrectExtreme

namespace SqlBridge.CorrectGrouped
open SqlEquiv SqlBridge.CorrectGroup

/-- `SqlEquiv`'s grouped path in closed form: an optional `HAVING`, any `ORDER BY` (rewritten onto
    the per-group key rows), `LIMIT`/`OFFSET`. A group whose `HAVING` is not `TRUE` on its sample
    row gives neither a row nor a key row. -/
theorem evalSelectCore_grouped_full (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool) (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause) (wh : Option Expr) (groupBy : List Expr)
    (having : Option Expr) (orderBy : List OrderByItem) (lim off : Option Nat)
    (hg : groupBy ≠ []) :
    ∃ (F F' : List (List (Option Value) × Table) → Row → List (List (Option Value) × Table))
      (Φ Ψ : List (Option Value) × Table → Option Row),
      (∀ gs u, (gs.map Prod.fst).Nodup →
        F gs u = insU (groupBy.map fun e => (exprEval db u e).map Value.setKey) u gs) ∧
      (∀ gs u, (gs.map Prod.fst).Nodup →
        F' gs u = insU (groupBy.map fun e => (exprEval db u e).map Value.setKey) u gs) ∧
      (∀ key rows s, bareSampleRow (exprEval db) (selectMinMaxCalls items having) rows = some s →
        Φ (key, rows) = if (having.all fun c => exprWithAggEval db rows s c == some (Value.bool true))
          then some (items.flatMap (selectItemWithAggEval db rows s)) else none) ∧
      (∀ key rows s, bareSampleRow (exprEval db) (selectMinMaxCalls items having) rows = some s →
        Ψ (key, rows) = if (having.all fun c => exprWithAggEval db rows s c == some (Value.bool true))
          then some (groupOrderKeyRow db exprWithAggEval orderBy rows s
            (items.flatMap (selectItemWithAggEval db rows s))) else none) ∧
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
        (SelectStmt.mk false items (some from_) wh groupBy having orderBy lim off) =
      applyOrderByLimitOffsetAligned compareEval db (groupOrderByItems orderBy) lim off true
        (((match wh with
          | some c => (fromEval db from_).filter fun row => exprEval db row c == some (Value.bool true)
          | none => fromEval db from_).foldl F' []).filterMap Ψ)
        (((match wh with
          | some c => (fromEval db from_).filter fun row => exprEval db row c == some (Value.bool true)
          | none => fromEval db from_).foldl F []).filterMap Φ) := by
  have hne : groupBy.isEmpty = false := by cases groupBy <;> simp_all
  refine ⟨?F, ?F', ?Φ, ?Ψ, ?h1, ?h1', ?h2, ?h2', ?h3⟩
  case h3 =>
    rw [evalSelectCore_eq_afterFilter]
    cases wh <;> simp [evalSelectAfterFilter, evalSelectProjectDistinct, evalSelectGroupOrderKeys,
      hne] <;> rfl
  case h1 =>
    intro gs u h
    split
    · rename_i x hx; exact addStep_found _ u gs h hx
    · rename_i hx; exact addStep_new _ u gs hx
  case h1' =>
    intro gs u h
    split
    · rename_i x hx; exact addStep_found _ u gs h hx
    · rename_i hx; exact addStep_new _ u gs hx
  case h2 =>
    intro key rows s h
    cases having <;> simp [h]
  case h2' =>
    intro key rows s h
    cases having <;> simp [h]

end SqlBridge.CorrectGrouped

namespace SqlBridge.CorrectGrouped
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGroup SqlBridge.CorrectGroupOrder

/-- Items of step 3b-4: aggregates of step 3a and columns (keys or bare). -/
def groupedItems : List SqlEquiv.SelectItem → Bool
  | [] => true
  | .exprItem e _ :: rest =>
    (aggFragment e || match e with | .col _ => true | _ => false) && groupedItems rest
  | _ :: _ => false

/-- The statements of step 3b-4. -/
def groupedStmt (items : List SqlEquiv.SelectItem) (f : SqlEquiv.FromClause)
    (wh : Option SqlEquiv.Expr) (groupBy : List SqlEquiv.Expr) (having : Option SqlEquiv.Expr)
    (orderBy : List SqlEquiv.OrderByItem) (lim off : Option ℕ) : SqlEquiv.Stmt :=
  .query (.simple (.mk false items (some f) wh groupBy having orderBy lim off))

/-- The `MIN`/`MAX` aggregates. -/
def isMinMax : SqlEquiv.Expr → Bool
  | .agg (.min _) _ _ | .agg (.max _) _ _ => true
  | _ => false

/-- Where bare columns read (registry T9): every item column is a key; or the dialect takes bare
    columns and no `MIN`/`MAX` is written anywhere (the group's first row); or it takes them and
    one `MIN`/`MAX`, not `DISTINCT`, is written, as `SqlEquiv` and the elaborator both count it (the
    row where its argument is extreme). (Every item column resolves in the `FROM` scope: the
    elaborator checks it, #384.) -/
def BareOk (N : NamedSchema) (items : List SqlEquiv.SelectItem)
    (groupBy : List SqlEquiv.Expr) (having : Option SqlEquiv.Expr)
    (orderBy : List SqlEquiv.OrderByItem) : Prop :=
  (∀ c ∈ colRefs items, SqlEquiv.Expr.col c ∈ groupBy) ∨
  (N.config.bareColumns = .sqlite ∧ (∀ it ∈ items, SqlEquiv.minMaxCalls (itemExpr it) = []) ∧
    (∀ h ∈ having, SqlEquiv.minMaxCalls h = []) ∧ ∀ o ∈ orderBy, SqlEquiv.minMaxCalls o.expr = []) ∨
  (N.config.bareColumns = .sqlite ∧ ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode)
    (arg : SqlEquiv.Expr), mode.bareRow = true ∧
    SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
    (((items.map itemExpr).filter aggFragment ++ aggsOfOpt having ++
      orderBy.map SqlEquiv.OrderByItem.expr).eraseDups.filter isMinMax) =
      [.agg (if wantMax then .max mode else .min mode) (some arg) false])

section
variable {f : SqlEquiv.SelectItem → Option SqlEquiv.Expr} (hf : ∀ e al, f (.exprItem e al) = some e)
include hf

theorem aggsOfList_groupedItems : ∀ items, groupedItems items = true →
    aggsOfList (items.filterMap f) = (items.map itemExpr).filter aggFragment
  | [], _ => by simp [aggsOfList]
  | .exprItem e al :: rest, h => by
    simp only [groupedItems, Bool.and_eq_true, Bool.or_eq_true] at h
    have he : aggFragment e = true ∨ ∃ c, e = .col c := by
      rcases h.1 with h1 | h1
      · exact .inl h1
      · cases e <;> simp_all
    simp only [List.filterMap_cons, hf, aggsOfList, aggsOf_groupItem e he,
      aggsOfList_groupedItems rest h.2, List.map_cons, itemExpr, List.filter_cons]
    split <;> simp
  | .star _ :: _, h => by simp [groupedItems] at h

theorem colsOutsideAggsList_groupedItems : ∀ items, groupedItems items = true →
    colsOutsideAggsList (items.filterMap f) = colRefs items
  | [], _ => by simp [colsOutsideAggsList, colRefs]
  | .exprItem e al :: rest, h => by
    simp only [groupedItems, Bool.and_eq_true, Bool.or_eq_true] at h
    have ih := colsOutsideAggsList_groupedItems rest h.2
    rcases h.1 with h1 | h1
    · cases e <;> simp_all [colsOutsideAggsList, colsOutsideAggs, colRefs, aggFragment]
    · cases e <;> simp_all [colsOutsideAggsList, colsOutsideAggs, colRefs]
  | .star _ :: _, h => by simp [groupedItems] at h

end

theorem mapM_eq_map {α β ε : Type _} {f : α → Except ε β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = .ok (g x)) → l.mapM f = .ok (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self, mapM_eq_map (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

/-- No `MIN`/`MAX` call in an expression: none among its aggregates. -/
theorem minMaxCalls_of_aggsOf_having {groupBy : List SqlEquiv.Expr} : ∀ (h : SqlEquiv.Expr),
    havingFragment groupBy h = true → SqlEquiv.minMaxCalls h = [] →
      ∀ x ∈ aggsOf h, SqlEquiv.minMaxCalls x = []
  | .lit _, _, _, x, hx | .col _, _, _, x, hx => by simp [aggsOf] at hx
  | .binOp op p q, hf, hm, x, hx => by
    simp only [havingFragment, Bool.and_eq_true] at hf
    simp only [SqlEquiv.minMaxCalls, List.append_eq_nil_iff] at hm
    simp only [aggsOf, List.mem_append] at hx
    rcases hx with hx | hx
    · exact minMaxCalls_of_aggsOf_having p hf.1.2 hm.1 x hx
    · exact minMaxCalls_of_aggsOf_having q hf.2 hm.2 x hx
  | .unaryOp op p, hf, hm, x, hx => by
    cases op <;> simp only [havingFragment] at hf
    · exact minMaxCalls_of_aggsOf_having p hf (by simpa [SqlEquiv.minMaxCalls] using hm) x
        (by simpa [aggsOf] using hx)
    all_goals simp [aggFragment] at hf
  | .countStar, _, hm, x, hx => by simp [aggsOf] at hx; subst hx; exact hm
  | .agg fn a d, _, hm, x, hx => by simp [aggsOf] at hx; subst hx; exact hm
  | .func _ _, hf, _, _, _ | .case _ _, hf, _, _, _ | .inList _ _ _, hf, _, _, _
  | .between _ _ _, hf, _, _, _ | .inSubquery _ _ _, hf, _, _, _ | .exists _ _, hf, _, _, _
  | .subquery _, hf, _, _, _ | .windowFn _ _ _, hf, _, _, _ => by
    simp [havingFragment, aggFragment] at hf

/-- No `MIN`/`MAX` call: the elaborator's filter for `MIN`/`MAX` aggregates is empty. -/
theorem filter_nil_of_noMinMax {l : List SqlEquiv.Expr} (hl : ∀ x ∈ l, SqlEquiv.minMaxCalls x = [])
    {p : SqlEquiv.Expr → Bool} (hp : ∀ x, SqlEquiv.minMaxCalls x = [] → p x = false) :
    l.filter p = [] :=
  List.filter_eq_nil_iff.mpr fun x hx => by simp [hp x (hl x hx)]

theorem groupedItems_mem : ∀ {items : List SqlEquiv.SelectItem},
    groupedItems items = true → ∀ it ∈ items, ∃ e al, it = .exprItem e al ∧
      (aggFragment e = true ∨ ∃ c, e = .col c)
  | [], _, _, h => by simp at h
  | .exprItem e al :: rest, h, it, hit => by
    simp only [groupedItems, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases List.mem_cons.mp hit with rfl | hit
    · refine ⟨e, al, rfl, ?_⟩
      rcases h.1 with h1 | h1
      · exact .inl h1
      · cases e <;> simp_all
    · exact groupedItems_mem h.2 it hit
  | .star _ :: _, h, _, _ => by simp [groupedItems] at h

/-- `ColumnRef`'s derived `BEq` compares fields. -/
instance : LawfulBEq SqlEquiv.ColumnRef where
  eq_of_beq {a b} h := by
    obtain ⟨t, c⟩ := a; obtain ⟨t', c'⟩ := b
    change (t == t' && c == c') = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]
  rfl {a} := by
    obtain ⟨t, c⟩ := a
    change (t == t && c == c) = true
    simp

theorem colRefs_of_mem {items : List SqlEquiv.SelectItem} {it : SqlEquiv.SelectItem} (hit : it ∈ items)
    {c : SqlEquiv.ColumnRef} {al : Option String} (h : it = .exprItem (.col c) al) : c ∈ colRefs items := by
  induction items with
  | nil => simp at hit
  | cons x rest ih =>
    rcases List.mem_cons.mp hit with rfl | hit
    · subst h; simp [colRefs]
    · have := ih hit
      cases x with
      | exprItem e al' => cases e <;> simp [colRefs, this]
      | star t => simpa [colRefs] using this

theorem exists_item_of_colRefs {c : SqlEquiv.ColumnRef} :
    ∀ {items : List SqlEquiv.SelectItem}, c ∈ colRefs items →
      ∃ it ∈ items, itemExpr it = .col c
  | [], h => by simp [colRefs] at h
  | .exprItem e al :: rest, h => by
    cases e
    case col c' =>
      simp only [colRefs, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨it, hit, he⟩ := exists_item_of_colRefs h
        exact ⟨it, List.mem_cons_of_mem _ hit, he⟩
    all_goals
      obtain ⟨it, hit, he⟩ := exists_item_of_colRefs (by simpa [colRefs] using h)
      exact ⟨it, List.mem_cons_of_mem _ hit, he⟩
  | .star _ :: rest, h => by
    obtain ⟨it, hit, he⟩ := exists_item_of_colRefs (by simpa [colRefs] using h)
    exact ⟨it, List.mem_cons_of_mem _ hit, he⟩

/-- `findIdx?` in `X ++ Y`: an element of `X` is found where it is in `X`. -/
theorem findIdx_append_left {α : Type _} {X Y : List α} {p : α → Bool} {j : ℕ}
    (h : X.findIdx? p = some j) : (X ++ Y).findIdx? p = some j := by
  rw [List.findIdx?_append, h]; rfl

theorem findIdx_append_right {α : Type _} {X Y : List α} {p : α → Bool} {j : ℕ}
    (hX : X.findIdx? p = none) (h : Y.findIdx? p = some j) :
    (X ++ Y).findIdx? p = some (j + X.length) := by
  rw [List.findIdx?_append, hX, h]; rfl

/-- With no `MIN`/`MAX` call, the sample row is the group's first row. -/
theorem bareSampleRow_nil_calls (argEval : SqlEquiv.Row → SqlEquiv.Expr → Option SqlEquiv.Value)
    (rows : SqlEquiv.Table) : SqlEquiv.bareSampleRow argEval [] rows = rows.head? := rfl

theorem selectMinMaxCalls_nil {items : List SqlEquiv.SelectItem} {having : Option SqlEquiv.Expr}
    (hi : ∀ it ∈ items, ∃ e al, it = .exprItem e al ∧ SqlEquiv.minMaxCalls e = [])
    (hh : ∀ h ∈ having, SqlEquiv.minMaxCalls h = []) :
    SqlEquiv.selectMinMaxCalls items having = [] := by
  have h2 : SqlEquiv.minMaxCalls.minMaxCallsOpt having = [] := by
    cases having with
    | none => rfl
    | some h => exact hh h rfl
  unfold SqlEquiv.selectMinMaxCalls
  rw [List.flatMap_eq_nil_iff.mpr ?h1, h2]
  · rfl
  case h1 =>
    intro it hit
    obtain ⟨e, al, rfl, he⟩ := hi it hit
    exact he

/-- `AggCall.first` reads its expression on the group's first row. -/
theorem first_eval {m : ℕ} {e : Expr m} {r₀ : Row m} {rs : List (Row m)} {d : Datum}
    (h : (AggCall.first e).eval (r₀ :: rs) = .ok d) : e.eval r₀ = .ok d := by
  simp only [AggCall.eval, List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
  rcases h0 : e.eval r₀ with _ | d₀
  · simp [h0] at h
  rcases h1 : rs.mapM e.eval with _ | ds
  · simp [h0, h1] at h
  simp only [h0, h1, Except.ok.injEq, List.head?_cons, Option.getD_some] at h
  rw [h]

/-- A relation through `mapM`: each output relates to the image of its partner. -/
theorem forall₂_mapM_rel {α β γ δ ε : Type _} {P : α → β → Prop} {f : α → Except ε γ}
    {Q : γ → δ → Prop} {g : β → δ} (hq : ∀ a b, P a b → ∀ c, f a = .ok c → Q c (g b)) :
    ∀ {as : List α} {bs : List β} {cs : List γ}, List.Forall₂ P as bs → as.mapM f = .ok cs →
      List.Forall₂ Q cs (bs.map g)
  | _, _, cs, .nil, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | a :: as, b :: bs, cs, .cons hab hs, h => by
    rw [List.mapM_cons] at h
    rcases hd : f a with _ | c
    · simp [hd, bind, Except.bind] at h
    rcases hr : as.mapM f with _ | cs'
    · simp [hd, hr, bind, Except.bind] at h
    simp only [hd, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .cons (hq a b hab c hd) (forall₂_mapM_rel hq hs hr)

theorem filter_isMinMax {p : SqlEquiv.Expr → Bool} (hp : ∀ x, p x = isMinMax x)
    (l : List SqlEquiv.Expr) : l.filter p = l.filter isMinMax :=
  List.filter_congr fun x _ => hp x

set_option maxHeartbeats 4000000 in
theorem elab_grouped_shape (N : NamedSchema) {items : List SqlEquiv.SelectItem}
    {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} {groupBy : List SqlEquiv.Expr}
    {having : Option SqlEquiv.Expr} {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hgi : groupedItems items = true) (hgb : groupBy ≠ [])
    (hob : ∀ o ∈ orderBy, aggFragment o.expr = true)
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hhv : ∀ h ∈ having, havingFragment groupBy h = true)
    (hbf : BareOk N items groupBy having orderBy)
    (hw : ∀ w ∈ wh, isFragment w = true) {e : Elaborated N.S}
    (h : elabStmt N (groupedStmt items fr wh groupBy having orderBy lim off) = .ok e) :
    e.q.typeOf.isSome ∧ ∃ sub n, ∃ qf : Query N.S n, ∃ cf, elabFrom N sub fr = .ok ⟨n, qf, cf⟩ ∧
      ∃ q₀ : Query N.S n,
        ((wh = none ∧ q₀ = qf) ∨ ∃ w p, wh = some w ∧
          elabExpr cf N.fold noHook w = .ok p ∧ q₀ = .select p qf) ∧
      ∃ (keyList : List (Expr n)) (a : ℕ) (aggs : Fin a → AggCall n)
        (its : List (Expr (keyList.length + a) × Column)) (sk : List (SortKey (keyList.length + a)))
        (mk : Expr n → AggCall n),
        groupBy.mapM (elabExpr cf N.fold noHook) = .ok keyList ∧
        -- with a bare column: `first` and no `MIN`/`MAX` call, or `atExtreme` at the one call
        ((∃ it ∈ items, ∃ c e', itemExpr it = .col c ∧ elabExpr cf N.fold noHook (.col c) = .ok e' ∧
            e' ∉ keyList) →
          ((∀ e, mk e = .first e) ∧ SqlEquiv.selectMinMaxCalls items having = []) ∨
          ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
            mode.bareRow = true ∧
            SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
            isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
            ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e) ∧
        (∀ j, (∃ x, aggFragment x = true ∧ elabAgg cf N.fold x = .ok (aggs j)) ∨
          ∃ c e', c ∈ colRefs items ∧ elabExpr cf N.fold noHook (.col c) = .ok e' ∧ e' ∉ keyList ∧
            aggs j = mk e') ∧
        List.Forall₂ (fun it x =>
          (∃ j : Fin a, elabAgg cf N.fold (itemExpr it) = .ok (aggs j) ∧
            x.1 = .col (Fin.natAdd _ j)) ∨
          (∃ c, ∃ i : Fin keyList.length, itemExpr it = .col c ∧
            elabExpr cf N.fold noHook (.col c) = .ok keyList[i] ∧ x.1 = .col (Fin.castAdd a i)) ∨
          (∃ c, ∃ j : Fin a, ∃ e', itemExpr it = .col c ∧ elabExpr cf N.fold noHook (.col c) = .ok e' ∧
            e' ∉ keyList ∧ aggs j = mk e' ∧ x.1 = .col (Fin.natAdd _ j)))
          items its ∧
        List.Forall₂ (fun o k => ∃ j : Fin a, elabAgg cf N.fold o.expr = .ok (aggs j) ∧
          k.e = .col (Fin.natAdd _ j) ∧ k.desc = (o.dir == .desc) ∧
          k.nullsFirst = (o.nulls == .first)) orderBy sk ∧
        ∃ qh : Query N.S (keyList.length + a),
          ((having = none ∧ qh = .aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀) ∨
            ∃ hv p out, having = some hv ∧
              TranslatesH cf out N.fold (fun i : Fin keyList.length => keyList[i]) aggs hv p ∧
              qh = .select p (.aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀)) ∧
        e = ⟨its.length, limitWrap lim off
          (if sk.length = 0 then .project (fun i => (its[i]).1) qh
           else .project (fun i => (its[i]).1) (.orderBy (fun i : Fin sk.length => sk[i]) qh)),
          fun i => (its[i]).2⟩ := by
  simp only [groupedStmt, elabStmt, elabQuery, bind, Except.bind] at h
  rcases hraw : elabQueryRaw N (.simple (.mk false items (some fr) wh groupBy having orderBy lim off))
    with _ | e₀
  · simp [hraw] at h
  simp only [hraw] at h
  split at h
  swap
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hty
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨hty, ?_⟩
  simp only [elabQueryRaw, elabSelect] at hraw
  rw [elabSelectF] at hraw
  obtain ⟨⟨n, qf, cf⟩, hf, hraw'⟩ := bind_ok hraw
  clear hraw
  rename' hraw' => hraw
  dsimp only at hraw
  have hgbe : groupBy.isEmpty = false := by
    cases groupBy with
    | nil => exact absurd rfl hgb
    | cons _ _ => rfl
  cases wh
  case' none =>
    simp only [pure, Except.pure, bind, Except.bind] at hraw
    refine ⟨_, n, qf, cf, hf, qf, .inl ⟨rfl, rfl⟩, ?_⟩
  case' some w =>
    simp only [subsOf_frag w (hw w rfl), List.foldl_nil, List.isEmpty_nil, ↓reduceIte] at hraw
    rcases hp : elabExpr cf N.fold noHook w with _ | p
    · simp [hp, bind, Except.bind] at hraw
    simp only [hp, bind, Except.bind, pure, Except.pure] at hraw
    refine ⟨_, n, qf, cf, hf, .select p qf, .inr ⟨w, p, rfl, hp, rfl⟩, ?_⟩
  all_goals
    rw [aggsOfList_groupedItems ?hf items hgi, colsOutsideAggsList_groupedItems ?hf2 items hgi,
      aggsOfList_orderBy ?hf3 orderBy hob, colsOutsideAggsList_orderBy ?hf4 orderBy hob] at hraw
    case hf => intros; rfl
    case hf2 => intros; rfl
    case hf3 => intro o; cases o; rfl
    case hf4 => intro o; cases o; rfl
    simp only [hgbe, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hraw
    split at hraw
    · cases hraw
    rename_i keyList hk
    split at hraw
    · cases hraw
    rename_i colsE hcolsE
    split at hraw
    · cases hraw
    rename_i aggList hv
    generalize hB : List.filterMap _
      (if (N.config.bareColumns == SqlEquiv.BareColumns.sqlite) = true then _ else []) = B at hraw
    have hK := mapM_forall₂ hk
    have hV := mapM_forall₂ hv
    have hkey : ∀ c, SqlEquiv.Expr.col c ∈ groupBy → ∃ e', elabExpr cf N.fold noHook (.col c) = .ok e' ∧
        e' ∈ keyList := fun c hc => by
      obtain ⟨e', he', h⟩ := forall₂_mem_left hK hc
      exact ⟨e', h, he'⟩
    -- every item column resolves in the `FROM` scope: the elaborator checks it (#384)
    have hres' : ∀ c ∈ colRefs items, ∃ e', elabExpr cf N.fold noHook (.col c) = .ok e' := by
      intro c hc
      obtain ⟨e', -, he'⟩ := forall₂_mem_left (mapM_forall₂ hcolsE) (List.mem_append_left _ hc)
      exact ⟨e', he'⟩
    -- the bare columns: item columns that are no key
    have hBmem : ∀ p ∈ B, elabExpr cf N.fold noHook (.col p.1) = .ok p.2 ∧ p.2 ∉ keyList ∧
        p.1 ∈ colRefs items := by
      intro p hp
      rw [← hB, List.mem_filterMap] at hp
      obtain ⟨c, hcm, hc⟩ := hp
      split at hc
      · rename_i e' he'
        split at hc
        · cases hc
        · cases hc; rename_i hn
          refine ⟨he', by simpa using hn, ?_⟩
          -- a `HAVING` column is a key, so a bare column is an item column
          split at hcm
          · rcases List.mem_append.mp (mem_of_mem_eraseDups' _ le_rfl hcm) with hcm | hcm
            · exact hcm
            · exfalso
              cases having with
              | none => simp [colsOutsideAggsOpt] at hcm
              | some hv' =>
                obtain ⟨e'', he'', hmem⟩ := hkey c (having_cols hv' (hhv hv' rfl) c hcm)
                rw [he'] at he''; cases he''; simp at hn; exact hn hmem
          · simp at hcm
      · cases hc
    -- no bare column; or no MIN/MAX (the first row); or one MIN/MAX (the extreme row)
    have hBX : B = [] ∨ ((∀ x ∈ ((items.map itemExpr).filter aggFragment ++ aggsOfOpt having ++
        orderBy.map SqlEquiv.OrderByItem.expr).eraseDups, SqlEquiv.minMaxCalls x = []) ∧
        SqlEquiv.selectMinMaxCalls items having = []) ∨
        ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr), mode.bareRow = true ∧
          SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
          (((items.map itemExpr).filter aggFragment ++ aggsOfOpt having ++
        orderBy.map SqlEquiv.OrderByItem.expr).eraseDups).filter isMinMax =
            [.agg (if wantMax then .max mode else .min mode) (some arg) false] := by
      rcases hbf with hall | ⟨-, hmi, hmh, hmo⟩ | ⟨-, w, m, a', hm, hcalls, hext⟩
      · left
        rw [← hB, List.filterMap_eq_nil_iff]
        intro c hc
        have hcg : SqlEquiv.Expr.col c ∈ groupBy := by
          split at hc
          · rcases List.mem_append.mp (mem_of_mem_eraseDups' _ le_rfl hc) with hc | hc
            · exact hall c hc
            · cases having with
              | none => simp [colsOutsideAggsOpt] at hc
              | some hv' => exact having_cols hv' (hhv hv' rfl) c hc
          · simp at hc
        obtain ⟨e', he', hmem⟩ := hkey c hcg
        simp [he', hmem]
      · have hc0 : SqlEquiv.selectMinMaxCalls items having = [] := by
          refine selectMinMaxCalls_nil (fun it hit => ?_) hmh
          obtain ⟨e, al, rfl, -⟩ := groupedItems_mem hgi it hit
          exact ⟨e, al, rfl, hmi _ hit⟩
        refine .inr (.inl ⟨fun x hx => ?_, hc0⟩)
        rcases List.mem_append.mp (List.mem_eraseDups.mp hx) with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨hx, -⟩ := List.mem_filter.mp hx
            obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hx
            exact hmi it hit
          · cases having with
            | none => simp [aggsOfOpt] at hx
            | some hv' => exact minMaxCalls_of_aggsOf_having hv' (hhv hv' rfl) (hmh hv' rfl) x hx
        · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
          exact hmo o ho
      · exact .inr (.inr ⟨w, m, a', hm, hcalls, hext⟩)
    split at hraw
    case' isTrue hBne =>
      rcases hBX.resolve_left (by intro h0; simp [h0] at hBne) with ⟨hX, hcalls⟩ |
        ⟨wantMax, mode, arg, hm, hcalls, hext⟩
      case' inl =>
        rw [filter_nil_of_noMinMax hX ?hp] at hraw
        case hp =>
          intro x hx
          cases x
          case agg fn _ _ => cases fn <;> first | rfl | simp [SqlEquiv.minMaxCalls] at hx
          all_goals rfl
        simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, List.length_nil,
          show ¬ ((0 : ℕ) > 1) by omega] at hraw
        rw [mapM_eq_map (l := B) (g := fun x => AggCall.first x.2) (fun _ _ => rfl)] at hraw
        obtain ⟨mk, hmk⟩ : ∃ mk : Expr n → AggCall n, (AggCall.first : Expr n → AggCall n) = mk := ⟨_, rfl⟩
        rw [hmk] at hraw
        have hmkS : ((∀ e, mk e = .first e) ∧ (B = [] ∨ SqlEquiv.selectMinMaxCalls items having = [])) ∨
            ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
              mode.bareRow = true ∧
              SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
              isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
              ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e :=
          .inl ⟨fun e => by rw [← hmk], .inr hcalls⟩
      case' inr =>
        -- the one `MIN`/`MAX`: its argument is a fragment, and elaborates
        have hmemx : SqlEquiv.Expr.agg (if wantMax then .max mode else .min mode) (some arg) false ∈
            ((items.map itemExpr).filter aggFragment ++ aggsOfOpt having ++
        orderBy.map SqlEquiv.OrderByItem.expr).eraseDups := by
          have : SqlEquiv.Expr.agg (if wantMax then .max mode else .min mode) (some arg) false ∈
              (((items.map itemExpr).filter aggFragment ++ aggsOfOpt having ++
        orderBy.map SqlEquiv.OrderByItem.expr).eraseDups).filter isMinMax := by rw [hext]; simp
          exact (List.mem_filter.mp this).1
        have hfrag : isFragment arg = true := by
          have hx : aggFragment (.agg (if wantMax then .max mode else .min mode) (some arg) false) := by
            rcases List.mem_append.mp (List.mem_eraseDups.mp hmemx) with hx | hx
            · rcases List.mem_append.mp hx with hx | hx
              · exact (List.mem_filter.mp hx).2
              · cases having with
                | none => simp [aggsOfOpt] at hx
                | some hv' => exact having_aggs hv' (hhv hv' rfl) _ hx
            · obtain ⟨o, ho, ho'⟩ := List.mem_map.mp hx; rw [← ho']; exact hob o ho
          cases wantMax <;> simpa [aggFragment] using hx
        rw [filter_isMinMax (fun x => by
          cases x
          case agg fn _ _ => cases fn <;> rfl
          all_goals rfl) _, hext] at hraw
        rcases hk' : elabExpr cf N.fold noHook arg with err | k'
        · exfalso
          obtain ⟨p₀, B', rfl⟩ : ∃ p₀ B', B = p₀ :: B' := by
            cases B with
            | nil => simp at hBne
            | cons p₀ B' => exact ⟨p₀, B', rfl⟩
          cases wantMax <;> simp [hk', List.mapM_cons, bind, Except.bind] at hraw
        cases wantMax
        case' false =>
          simp only [Bool.false_eq_true, ↓reduceIte, List.any_cons, List.any_nil, Bool.or_false,
            List.length_singleton, gt_iff_lt, lt_self_iff_false, hk'] at hraw
          rw [mapM_eq_map (l := B) (g := fun x => AggCall.atExtreme .lt k' x.2) (fun _ _ => rfl)] at hraw
          obtain ⟨mk, hmk⟩ : ∃ mk : Expr n → AggCall n, AggCall.atExtreme Ordering.lt k' = mk := ⟨_, rfl⟩
          rw [hmk] at hraw
          have hmkS : ((∀ e, mk e = .first e) ∧
              (B = [] ∨ SqlEquiv.selectMinMaxCalls items having = [])) ∨
              ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
                mode.bareRow = true ∧
                SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
                isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
                ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e :=
            .inr ⟨false, mode, arg, k', hm, hcalls, hfrag, hk', fun e => by rw [← hmk]; rfl⟩
        case' true =>
          simp only [↓reduceIte, eq_self_iff_true, Bool.false_eq_true, List.any_cons, List.any_nil,
            Bool.or_false,
            List.length_singleton, gt_iff_lt, lt_self_iff_false, hk'] at hraw
          rw [mapM_eq_map (l := B) (g := fun x => AggCall.atExtreme .gt k' x.2) (fun _ _ => rfl)] at hraw
          obtain ⟨mk, hmk⟩ : ∃ mk : Expr n → AggCall n, AggCall.atExtreme Ordering.gt k' = mk := ⟨_, rfl⟩
          rw [hmk] at hraw
          have hmkS : ((∀ e, mk e = .first e) ∧
              (B = [] ∨ SqlEquiv.selectMinMaxCalls items having = [])) ∨
              ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
                mode.bareRow = true ∧
                SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
                isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
                ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e :=
            .inr ⟨true, mode, arg, k', hm, hcalls, hfrag, hk', fun e => by rw [← hmk]; rfl⟩
    case' isFalse hBe =>
      have hB0 : B = [] := by simpa using hBe
      rw [mapM_eq_map (l := B) (g := fun x => AggCall.first x.2) (by simp [hB0])] at hraw
      obtain ⟨mk, hmk⟩ : ∃ mk : Expr n → AggCall n, (AggCall.first : Expr n → AggCall n) = mk := ⟨_, rfl⟩
      rw [hmk] at hraw
      have hmkS : ((∀ e, mk e = .first e) ∧ (B = [] ∨ SqlEquiv.selectMinMaxCalls items having = [])) ∨
          ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
            mode.bareRow = true ∧
            SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
            isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
            ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e :=
        .inl ⟨fun e => by rw [← hmk], .inl hB0⟩
    all_goals
      simp only at hraw
      split at hraw
      · cases hraw
      rename_i out hout
      -- the aggregates' list `X`: aggregates of the items, of `HAVING` and of `ORDER BY`
      have hXf' : ∀ x ∈ ((items.map itemExpr).filter aggFragment ++ aggsOfOpt having ++
          orderBy.map SqlEquiv.OrderByItem.expr).eraseDups, aggFragment x = true := by
        intro x hx
        rcases List.mem_append.mp (List.mem_eraseDups.mp hx) with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact (List.mem_filter.mp hx).2
          · cases having with
            | none => simp [aggsOfOpt] at hx
            | some hv' => exact having_aggs hv' (hhv hv' rfl) x hx
        · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx; exact hob o ho
      have hXi : ∀ it ∈ items, aggFragment (itemExpr it) = true →
          itemExpr it ∈ ((items.map itemExpr).filter aggFragment ++ aggsOfOpt having ++
            orderBy.map SqlEquiv.OrderByItem.expr).eraseDups := fun it hit hfr =>
        List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_left _
          (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_, hit, rfl⟩, hfr⟩)))
      have hXh : ∀ hv ∈ having, ∀ x ∈ aggsOf hv,
          x ∈ ((items.map itemExpr).filter aggFragment ++ aggsOfOpt having ++
            orderBy.map SqlEquiv.OrderByItem.expr).eraseDups := by
        intro hv hhv' x hx
        cases hhv'
        exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_right _ hx))
      have hXo : ∀ o ∈ orderBy, o.expr ∈ ((items.map itemExpr).filter aggFragment ++
          aggsOfOpt having ++ orderBy.map SqlEquiv.OrderByItem.expr).eraseDups := fun o ho =>
        List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩))
      generalize ((items.map itemExpr).filter aggFragment ++ aggsOfOpt having ++
        orderBy.map SqlEquiv.OrderByItem.expr).eraseDups = X at hXf' hXi hXh hXo hV hraw hout
      clear hv hBX
      have hlenX : X.length = aggList.length := hV.length_eq
      -- the hook's list: `X`, then the bare columns
      have hXf : ∀ x ∈ X ++ B.map (fun x => SqlEquiv.Expr.col x.1),
          aggFragment x = true ∨ ∃ c, x = .col c ∧ SqlEquiv.Expr.col c ∉ groupBy := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact .inl (hXf' x hx)
        · obtain ⟨⟨c, e'⟩, hcB, rfl⟩ := List.mem_map.mp hx
          refine .inr ⟨c, rfl, fun hcg => ?_⟩
          obtain ⟨e'', he'', hmem⟩ := hkey c hcg
          obtain ⟨he', hn, -⟩ := hBmem _ hcB
          rw [he''] at he'; cases he'; exact hn hmem
      have hfindX : ∀ x ∈ X, ∃ j, (X ++ B.map (fun x => SqlEquiv.Expr.col x.1)).findIdx? (· == x) =
          some j ∧ ∃ hj : j < X.length, X[j] = x := by
        intro x hx
        obtain ⟨j, hj⟩ : ∃ j, X.findIdx? (· == x) = some j :=
          Option.isSome_iff_exists.mp (by
            rw [List.findIdx?_isSome, List.any_eq_true]; exact ⟨x, hx, by simp⟩)
        obtain ⟨hjl, hje, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
        exact ⟨j, findIdx_append_left hj, hjl, by simpa using hje⟩
      have hagg : ∀ j (hj : j < X.length), ∃ hja : j < (aggList ++ B.map (fun x => mk x.2)).length,
          elabAgg cf N.fold X[j] = .ok ((aggList ++ B.map (fun x => mk x.2))[j]) := by
        intro j hj
        have hjv : j < aggList.length := hlenX ▸ hj
        refine ⟨by simp; omega, ?_⟩
        rw [List.getElem_append_left hjv]
        have := (List.forall₂_iff_get.mp hV).2 j hj hjv
        simpa using this
      have hkc : ∀ i : Fin keyList.length, ∃ idx, keyList[i] = .col idx := by
        intro i
        have h1 := (List.forall₂_iff_get.mp hK).2 i.1 (by have := hK.length_eq; omega) i.2
        simp only [List.get_eq_getElem] at h1
        obtain ⟨c, hc⟩ := hgc _ (List.getElem_mem (by have := hK.length_eq; omega : i.1 < groupBy.length))
        rw [hc] at h1
        exact elab_col_is_col cf N.fold c h1
      -- a non-key item column is a bare column
      have hbareB : ∀ c e', c ∈ colRefs items → elabExpr cf N.fold noHook (.col c) = .ok e' →
          e' ∉ keyList → (c, e') ∈ B := by
        intro c e' hc he' hkm
        rw [← hB, List.mem_filterMap]
        refine ⟨c, ?_, by simp [he', hkm]⟩
        rcases hbf with hall | ⟨hsq, -⟩ | ⟨hsq, -⟩
        · obtain ⟨e'', he'', hm⟩ := hkey c (hall c hc)
          rw [he'] at he''; cases he''; exact absurd hm hkm
        all_goals
          simp only [hsq]
          exact List.mem_eraseDups.mpr (List.mem_append_left _ hc)
      rcases having with _ | hv
      case' some =>
        simp only at hraw
        split at hraw
        · cases hraw
        rename_i p hp
        have hp' : elabExpr out N.fold (aggHook (a := (aggList ++ B.map (fun x => mk x.2)).length)
            cf N.fold (fun i : Fin keyList.length => keyList[i])
            (X ++ B.map (fun x => SqlEquiv.Expr.col x.1))) hv = .ok p := by
          split at hp
          · simp only [Except.ok.injEq] at hp; subst hp; assumption
          · split at hp <;> simp [throw, throwThe, MonadExceptOf.throw] at hp
          · simp [throw, throwThe, MonadExceptOf.throw] at hp
      all_goals
        try simp only at hraw
        split at hraw
        · cases hraw
        rename_i its hits
        obtain ⟨keys', hk', rfl⟩ := finishSelect_nondistinct N.fold _ orderBy lim off hraw
        refine ⟨keyList, _, fun j => (aggList ++ B.map (fun x => mk x.2))[j], its, keys', mk, hk,
          ?gMk, ?gAggs, ?gItems, ?gKeys, ?gQh⟩
        case gMk =>
          rintro ⟨it, hit, c, e', hc, he', hkn⟩
          have hcr : c ∈ colRefs items := by
            obtain ⟨x, al, hx, -⟩ := groupedItems_mem hgi _ hit
            rw [hx] at hc; simp only [itemExpr] at hc; subst hc
            exact colRefs_of_mem hit hx
          rcases hmkS with ⟨hf, hB0 | hcalls⟩ | hat
          · have := hbareB c e' hcr he' hkn; rw [hB0] at this; simp at this
          · exact .inl ⟨hf, hcalls⟩
          · exact .inr hat
        case gAggs =>
          intro ⟨j, hj⟩
          by_cases hjv : j < aggList.length
          · left
            obtain ⟨_, hel⟩ := hagg j (hlenX ▸ hjv)
            exact ⟨_, hXf' _ (List.getElem_mem _), hel⟩
          · right
            have hjB : j - aggList.length < B.length := by simp at hj; omega
            refine ⟨B[j - aggList.length].1, B[j - aggList.length].2,
              (hBmem _ (List.getElem_mem hjB)).2.2, (hBmem _ (List.getElem_mem hjB)).1,
              (hBmem _ (List.getElem_mem hjB)).2.1, ?_⟩
            show (aggList ++ B.map (fun x => mk x.2))[j] = _
            rw [List.getElem_append_right (by omega)]
            simp
        case gKeys =>
          refine forall₂_imp_mem (mapM_forall₂ hk') fun o ho k hok => ?_
          obtain ⟨oe, dir, nulls⟩ := o
          have hfr : aggFragment oe = true := hob _ ho
          obtain ⟨j, hj, hjl, hje⟩ := hfindX oe (hXo _ ho)
          obtain ⟨hja, hel⟩ := hagg j hjl
          unfold elabOrderKey at hok
          cases oe
          all_goals try simp [aggFragment] at hfr
          all_goals
            simp only [bind, Except.bind] at hok
            rw [elab_of_hook _ _ _ (hook_agg _ _ _ _ hj hja)] at hok
            simp only [pure, Except.pure, Except.ok.injEq] at hok
            subst hok
            exact ⟨⟨j, hja⟩, hje ▸ hel, rfl, rfl, rfl⟩
        case gItems =>
          refine forall₂_imp_mem (mapM_forall₂ hits) fun it hit x hx => ?_
          obtain ⟨e, al, rfl, hcase⟩ := groupedItems_mem hgi _ hit
          dsimp only at hx
          rcases hcase with hfr | ⟨c, rfl⟩
          · -- an aggregate: its column among the aggregates
            obtain ⟨j, hj, hjl, hje⟩ := hfindX e (hXi _ hit hfr)
            obtain ⟨hja, hel⟩ := hagg j hjl
            rw [elab_of_hook _ _ _ (hook_agg _ _ _ _ hj hja)] at hx
            simp only at hx
            split at hx
            · simp only [Except.ok.injEq] at hx
              subst hx
              exact .inl ⟨⟨j, hja⟩, hje ▸ hel, rfl⟩
            · simp [throw, throwThe, MonadExceptOf.throw] at hx
          · have hc : c ∈ colRefs items := colRefs_of_mem hit rfl
            obtain ⟨e', he'⟩ := hres' c hc
            have hnX : ∀ y ∈ X, y ≠ .col c := fun y hy h => by
              have := hXf' y hy; rw [h] at this; simp [aggFragment] at this
            by_cases hkm : e' ∈ keyList
            · -- a key column: its column among the keys
              have hnone : (X ++ B.map (fun x => SqlEquiv.Expr.col x.1)).findIdx?
                  (· == SqlEquiv.Expr.col c) = none := by
                rw [List.findIdx?_eq_none_iff]
                intro y hy
                rcases List.mem_append.mp hy with hy | hy
                · simpa using hnX y hy
                · obtain ⟨⟨c', e''⟩, hcB, rfl⟩ := List.mem_map.mp hy
                  rw [beq_eq_false_iff_ne, ne_eq, SqlEquiv.Expr.col.injEq]
                  rintro rfl
                  obtain ⟨he'', hn, -⟩ := hBmem _ hcB
                  rw [he'] at he''; cases he''; exact hn hkm
              obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hkm
              obtain ⟨i₀, hi₀⟩ : ∃ i₀, (List.finRange keyList.length).find?
                  (fun k : Fin keyList.length => keyList[k] == keyList[i]'hi) = some i₀ :=
                Option.isSome_iff_exists.mp
                  ((List.find?_isSome (p := fun k : Fin keyList.length => keyList[k] == keyList[i]'hi)).mpr
                    ⟨⟨i, hi⟩, List.mem_finRange _, beq_self_eq_true (keyList[i]'hi)⟩)
              have hk₀ : keyList[i₀] = keyList[i]'hi := by
                simpa using List.find?_some hi₀
              rw [elab_key keyList out cf N.fold _ hnone he' hi₀] at hx
              simp only at hx
              split at hx
              · simp only [Except.ok.injEq] at hx
                subst hx
                exact .inr (.inl ⟨c, i₀, rfl, by rw [he', hk₀], rfl⟩)
              · simp [throw, throwThe, MonadExceptOf.throw] at hx
            · -- a bare column: its `first` aggregate
              have hcB : (c, e') ∈ B := hbareB c e' hc he' hkm
              obtain ⟨k, hk⟩ : ∃ k, (B.map (fun x => SqlEquiv.Expr.col x.1)).findIdx?
                  (· == SqlEquiv.Expr.col c) = some k :=
                Option.isSome_iff_exists.mp (by
                  rw [List.findIdx?_isSome, List.any_eq_true]
                  exact ⟨_, List.mem_map.mpr ⟨_, hcB, rfl⟩, by simp⟩)
              obtain ⟨hkl, hke, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
              have hkB : k < B.length := by simpa using hkl
              have hkc : B[k].1 = c := by simpa using hke
              have hnoneX : X.findIdx? (· == SqlEquiv.Expr.col c) = none := by
                rw [List.findIdx?_eq_none_iff]; intro y hy; simpa using hnX y hy
              have hja : k + X.length < (aggList ++ B.map (fun x => mk x.2)).length := by
                simp; omega
              rw [elab_of_hook _ _ _ (hook_agg _ _ _ _ (findIdx_append_right hnoneX hk) hja)] at hx
              simp only at hx
              split at hx
              · simp only [Except.ok.injEq] at hx
                subst hx
                have hBk := (hBmem _ (List.getElem_mem hkB)).1
                rw [hkc, he'] at hBk
                cases hBk
                refine .inr (.inr ⟨c, ⟨k + X.length, hja⟩, _, rfl, he', hkm, ?_, rfl⟩)
                show (aggList ++ B.map (fun x => mk x.2))[k + X.length] = _
                rw [List.getElem_append_right (by omega)]
                simp [hlenX]
              · simp [throw, throwThe, MonadExceptOf.throw] at hx
        case gQh =>
          first
            | exact ⟨_, .inl ⟨rfl, rfl⟩, rfl⟩
            | (refine ⟨_, .inr ⟨hv, p, out, rfl, ?_, rfl⟩, rfl⟩
               refine translatesH_of_elab cf N.fold keyList out _ _ groupBy hXf ?_ hkc hkey
                 hv (hhv hv rfl) (fun x hx => List.mem_append_left _ (hXh hv rfl x hx)) hp'
               intro j hj hfr
               have hjX : j < X.length := by
                 by_contra hn
                 rw [List.getElem_append_right (by omega)] at hfr
                 simp [aggFragment] at hfr
               obtain ⟨hja, hel⟩ := hagg j hjX
               refine ⟨hja, ?_⟩
               rw [List.getElem_append_left hjX]
               exact hel)

end SqlBridge.CorrectGrouped


namespace SqlBridge.CorrectGrouped
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGroup SqlBridge.CorrectGroupOrder

/-- The truth of a predicate on a row, `false` on an error. -/
def keepRow {m : ℕ} (p : Expr m) (r : Row m) : Bool :=
  match p.evalTruth r with
  | .ok t => t.isTrue
  | .error _ => false

/-- A predicate that filters the rows: each row's truth evaluates, and the rows kept are those
    whose truth is `TRUE`. -/
theorem filterRows_eq_filter {m : ℕ} (p : Expr m) : ∀ {as as' : List (Row m)},
    p.filterRows as = .ok as' →
      (∀ A ∈ as, ∃ t, p.evalTruth A = .ok t) ∧ as' = as.filter (keepRow p)
  | [], as', h => by
    simp only [Expr.filterRows, List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | A :: as, as', h => by
    obtain ⟨t, R'', hte, hrs, rfl⟩ := filterRows_cons_ok h
    obtain ⟨hall, rfl⟩ := filterRows_eq_filter p hrs
    refine ⟨fun B hB => ?_, ?_⟩
    · rcases List.mem_cons.mp hB with rfl | hB
      · exact ⟨t, hte⟩
      · exact hall B hB
    · simp only [List.filter_cons, keepRow, hte]

/-- Groups kept by both evaluators relate, and groups dropped by both give nothing: the typed rows
    kept relate, in order, to `SqlEquiv`'s rows zipped with their key rows. -/
theorem grouped_rel {X G : Type _} {Φ Ψ : G → Option SqlEquiv.Row}
    {PR : X → SqlEquiv.Row × SqlEquiv.Row → Prop} (keep : X → Bool) :
    ∀ {as : List X} {gs : List G}, List.Forall₂ (fun A g =>
        (keep A = true ∧ ∃ p k, Φ g = some p ∧ Ψ g = some k ∧ PR A (p, k)) ∨
        (keep A = false ∧ Φ g = none ∧ Ψ g = none)) as gs →
      List.Forall₂ PR (as.filter keep) ((gs.filterMap Φ).zip (gs.filterMap Ψ)) ∧
        ((gs.filterMap Φ).zip (gs.filterMap Ψ)).map Prod.fst = gs.filterMap Φ
  | _, _, .nil => ⟨.nil, rfl⟩
  | A :: _, _ :: _, .cons h hs => by
    obtain ⟨ih1, ih2⟩ := grouped_rel keep hs
    rcases h with ⟨hk, p, k, hp, hq, hpr⟩ | ⟨hk, hp, hq⟩
    · rw [List.filter_cons_of_pos hk, List.filterMap_cons_some hp, List.filterMap_cons_some hq,
        List.zip_cons_cons, List.map_cons, ih2]
      exact ⟨.cons hpr ih1, rfl⟩
    · rw [List.filter_cons_of_neg (by simp [hk]), List.filterMap_cons_none hp,
        List.filterMap_cons_none hq]
      exact ⟨ih1, ih2⟩

/-- `zip_rel` with the elements' memberships. -/
theorem zip_rel_mem {α β γ : Type _} {P : α → β → Prop} {Q : α → γ → Prop} {E : β → γ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ},
      (∀ a ∈ as, ∀ b ∈ bs, ∀ c, P a b → Q a c → E b c) →
      List.Forall₂ P as bs → List.Forall₂ Q as cs → List.Forall₂ E bs cs
  | _, _, _, _, .nil, .nil => .nil
  | _, _, _, h, .cons hp hps, .cons hq hqs =>
    .cons (h _ List.mem_cons_self _ List.mem_cons_self _ hp hq)
      (zip_rel_mem (fun a ha b hb c => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) c)
        hps hqs)

set_option maxHeartbeats 8000000 in
/-- **Elaborator correctness for grouped queries (#352, roadmap steps 3b-4, 3b-5).** For
    `SELECT … FROM f [WHERE p] GROUP BY c₁, … [HAVING h] [ORDER BY a₁, …] [LIMIT n] [OFFSET m]`,
    column keys, every item an aggregate of step 3a, a key column or a bare column, `h` in
    `havingFragment`, every sort key an aggregate: when the statement elaborates, the typed query's
    rows relate, in order, to `SqlEquiv`'s. Bare columns read the group's first row, or the row
    where the one `MIN`/`MAX` argument is extreme (`BareOk`), and with sort keys no output
    name captures `SqlEquiv`'s key columns (`hnm`). -/
theorem elabStmt_correct_grouped (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} {having : Option SqlEquiv.Expr}
    {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hgi : groupedItems items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hw : ∀ w ∈ wh, isFragment w = true) (hhv : ∀ h ∈ having, havingFragment groupBy h = true)
    (hob : ∀ o ∈ orderBy, aggFragment o.expr = true) (hbf : BareOk N items groupBy having orderBy)
    (hnm : orderBy ≠ [] → ∀ it ∈ items, '.' ∉ (outName it).toList ∧
      ∀ k, (outName it).toLower ≠ SqlEquiv.groupOrderKeyName k)
    {e : Elaborated N.S}
    (h : elabStmt N (groupedStmt items fr wh groupBy having orderBy lim off) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupedStmt items fr wh groupBy having orderBy lim off)).2 =
        some out ∧ List.Forall₂ OutRel rs out := by
  obtain ⟨hty, sub, n, qf, cf, hf, q₀, hq₀, keyList, a, aggs, its, sk, mk, hk, hmk, haggs, hits, hsk,
    qh, hqh, rfl⟩ := elab_grouped_shape N hgi hgb hob hgc hhv hbf hw h
  -- what a bare column's aggregate is: `first` with no `MIN`/`MAX`, or `atExtreme` at the one
  have hmkC : ∀ c e', c ∈ colRefs items → elabExpr cf N.fold noHook (.col c) = .ok e' →
      e' ∉ keyList → ((∀ e, mk e = .first e) ∧ SqlEquiv.selectMinMaxCalls items having = []) ∨
        ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
          mode.bareRow = true ∧
          SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
          isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
          ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e := by
    intro c e' hc he' hkn
    obtain ⟨it, hit, hite⟩ := exists_item_of_colRefs hc
    exact hmk ⟨it, hit, c, e', hite, he', hkn⟩
  have hlo : orderBy.length = sk.length := hsk.length_eq
  obtain ⟨hnames, hfrom⟩ := from_rel N hfold hfoldCI hwn hfix hD hrel sub fr hff hf
  simp only at hnames hfrom hty hnb ⊢
  rw [typeOf_limitWrap] at hty
  rw [qnb_limitWrap] at hnb
  -- the sort keys: each the column of an aggregate
  have hskget : ∀ i : Fin sk.length, ∃ j : Fin a,
      elabAgg cf N.fold (orderBy[i.1]'(by omega)).expr = .ok (aggs j) ∧
      (sk[i]).e = .col (Fin.natAdd _ j) ∧ (sk[i]).desc = ((orderBy[i.1]'(by omega)).dir == .desc) ∧
      (sk[i]).nullsFirst = ((orderBy[i.1]'(by omega)).nulls == .first) := by
    intro i
    have := (List.forall₂_iff_get.mp hsk).2 i.1 (by omega) i.2
    simpa using this
  choose kj hkj using hskget
  set aggQ : Query N.S (keyList.length + a) :=
    .aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀ with haggQ
  -- typing and the boolean side conditions, through the optional `ORDER BY`
  obtain ⟨Γa, hΓqh, hnbqh, hnbO⟩ : ∃ Γa, qh.typeOf = some Γa ∧ QNoBoolOrder qh ∧
      (sk.length ≠ 0 → ∀ i : Fin sk.length, (sk[i]).e.typeOf Γa ≠ some .bool) := by
    obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
    by_cases h0 : sk.length = 0
    · simp only [h0, ↓reduceIte] at hΔ hnb
      obtain ⟨Γa, hΓa, -⟩ := Query.typeOf_project_eq_some.mp hΔ
      exact ⟨Γa, hΓa, hnb.2, fun h => absurd h0 h⟩
    · simp only [h0, ↓reduceIte] at hΔ hnb
      obtain ⟨Γa, hΓo, -⟩ := Query.typeOf_project_eq_some.mp hΔ
      obtain ⟨hΓa, -⟩ := Query.typeOf_orderBy_eq_some hΓo
      exact ⟨Γa, hΓa, hnb.2.2, fun _ => hnb.2.1 Γa hΓa⟩
  -- the `HAVING` predicate, if any: which aggregate rows it keeps
  obtain ⟨P, hP, hΓa, hnbA, hnbP, hdivP⟩ : ∃ P : Option (Expr (keyList.length + a)),
      ((having = none ∧ P = none ∧ qh = aggQ) ∨ ∃ hv p out, having = some hv ∧ P = some p ∧
        TranslatesH cf out N.fold (fun i : Fin keyList.length => keyList[i]) aggs hv p ∧
        qh = .select p aggQ) ∧
      aggQ.typeOf = some Γa ∧ QNoBoolOrder aggQ ∧ (∀ p ∈ P, NoBoolOrder Γa p) ∧
      (∀ p ∈ P, p.divSafe = true) := by
    rcases hqh with ⟨hhn, rfl⟩ | ⟨hv, p, out, hhs, htrH, rfl⟩
    · exact ⟨none, .inl ⟨hhn, rfl, rfl⟩, hΓqh, hnbqh, by simp, by simp⟩
    · refine ⟨some p, .inr ⟨hv, p, out, hhs, rfl, htrH, rfl⟩,
        (Query.typeOf_select_eq_some.mp hΓqh).1, hnbqh.2, ?_, ?_⟩
      · intro p' hp'; cases hp'; exact hnbqh.1 Γa (Query.typeOf_select_eq_some.mp hΓqh).1
      · intro p' hp'; cases hp'
        exact TranslatesH.divSafe htrH
  obtain ⟨Γ₀, Δk, Δa, hq₀ty, hks, has, hΓeq⟩ := Query.typeOf_aggregate_eq_some hΓa
  obtain ⟨hnbA', hnbq₀⟩ := hnbA
  have hnbK := (hnbA' Γ₀ hq₀ty).1
  have hnbAgg := (hnbA' Γ₀ hq₀ty).2
  have hτb : sk.length ≠ 0 → ∀ i : Fin sk.length, Δa (kj i) ≠ .bool := by
    intro h0 i hb
    apply hnbO h0 i
    rw [(hkj i).2.1, ← hΓeq]
    simp [Expr.typeOf, hb]
  have hsrc : qf.typeOf = some Γ₀ := by
    rcases hq₀ with ⟨-, rfl⟩ | ⟨w, p, -, -, rfl⟩
    · exact hq₀ty
    · exact (Query.typeOf_select_eq_some.mp hq₀ty).1
  have hnbsrc : QNoBoolOrder qf := by
    rcases hq₀ with ⟨-, rfl⟩ | ⟨w, p, -, -, rfl⟩
    · exact hnbq₀
    · exact hnbq₀.2
  obtain ⟨hdivf, Rf, hRf, hrelf⟩ := hfrom hsrc hnbsrc
  have hrows : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) Rf
      (SqlEquiv.evalFrom db fr) := hrelf.imp fun r u h =>
    ⟨rowRel_of_keyed N.fold hfold hfoldCI (fun j => (hnames j).1) (fun j => (hnames j).2) h.1, h.2⟩
  have hdivq₀ : q₀.divSafe = true := by
    rcases hq₀ with ⟨-, rfl⟩ | ⟨w, p, hwp, hp, rfl⟩
    · exact hdivf
    · simp only [Query.divSafe, hdivf, Bool.and_true]
      exact Translates.divSafe _ _ (translates_of_elab _ _ w (hw w hwp) hp)
  obtain ⟨R, hR⟩ := Query.IsSafe.exists_eval_eq_ok (q := q₀) ⟨by simp [hq₀ty], hdivq₀⟩ hD
  -- the keys translate the `GROUP BY` columns
  have hK := mapM_forall₂ hk
  have hlen : groupBy.length = keyList.length := hK.length_eq
  have hkey : ∀ c, SqlEquiv.Expr.col c ∈ groupBy → ∃ e', elabExpr cf N.fold noHook (.col c) = .ok e' ∧
      e' ∈ keyList := fun c hc => by
    obtain ⟨e', he', h⟩ := forall₂_mem_left hK hc
    exact ⟨e', h, he'⟩
  have htk : ∀ i : Fin keyList.length, Translates cf N.fold (groupBy[i.1]'(by omega)) keyList[i] := by
    intro i
    have h1 := (List.forall₂_iff_get.mp hK).2 i.1 (by omega) i.2
    simp only [List.get_eq_getElem] at h1
    obtain ⟨c, hc⟩ := hgc _ (List.getElem_mem (by omega : i.1 < groupBy.length))
    rw [hc] at h1 ⊢
    exact translates_of_elab cf N.fold _ rfl h1
  have hdivK : ∀ i : Fin keyList.length, (keyList[i]).divSafe = true :=
    fun i => Translates.divSafe _ _ (htk i)
  -- every aggregate is safe: aggregates of step 3a, and `first` of a column
  have hda : ∀ j, (aggs j).divSafe = true := fun j => by
    rcases haggs j with ⟨x, hx, hel⟩ | ⟨c, e', hc, he', hkn, hj⟩
    · exact agg_divSafe cf N.fold x hx hel
    · obtain ⟨idx, rfl⟩ := elab_col_is_col cf N.fold c he'
      rcases hmkC c _ hc he' hkn with ⟨hfst, -⟩ | ⟨w, m, arg, k', -, -, hfrag, hk', hat⟩
      · rw [hj, hfst]; rfl
      · rw [hj, hat]
        simp only [AggCall.divSafe, Bool.and_eq_true]
        exact ⟨Translates.divSafe _ _ (translates_of_elab cf N.fold arg hfrag hk'), rfl⟩
  have hdivA : aggQ.divSafe = true := by
    simp only [haggQ, Query.divSafe, hda, hdivq₀, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun i => hdivK i, fun _ => trivial⟩
  -- the typed query evaluates
  have hsafe : (limitWrap lim off (if sk.length = 0 then .project (fun i : Fin its.length => (its[i]).1) qh
      else .project (fun i : Fin its.length => (its[i]).1)
        (.orderBy (fun i : Fin sk.length => sk[i]) qh))).IsSafe := by
    refine ⟨by rw [typeOf_limitWrap]; exact hty, ?_⟩
    rw [divSafe_limitWrap]
    have hcols : ∀ i : Fin its.length, ((its[i]).1).divSafe = true := by
      intro i
      rcases (List.forall₂_iff_get.mp hits).2 i.1 (by have := hits.length_eq; omega) i.2 with
        ⟨j, -, hj⟩ | ⟨c, i', -, -, hj⟩ | ⟨c, j, e', -, -, -, -, hj⟩ <;>
        (simp only [List.get_eq_getElem] at hj; show ((its[i.1]).1).divSafe = true; rw [hj]; rfl)
    have hqd : qh.divSafe = true := by
      rcases hP with ⟨-, rfl, rfl⟩ | ⟨hv, p, out, -, rfl, -, rfl⟩
      · exact hdivA
      · simp only [Query.divSafe, hdivA, Bool.and_true]; exact hdivP p rfl
    by_cases h0 : sk.length = 0
    · simp only [h0, ↓reduceIte, Query.divSafe, hqd, Bool.and_true, decide_eq_true_eq]
      exact fun i => hcols i
    · simp only [h0, ↓reduceIte, Query.divSafe, hqd, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨fun i => hcols i, fun i => by rw [(hkj i).2.1]; rfl⟩
  obtain ⟨rs, hrs⟩ := Query.IsSafe.exists_eval_eq_ok hsafe hD
  refine ⟨rs, hrs, _, rfl, ?_⟩
  -- the typed evaluation, step by step
  obtain ⟨base, hbase, rfl⟩ := eval_limitWrap D lim off _ hrs
  obtain ⟨rowsH, hH, hbase'⟩ : ∃ rowsH, qh.eval D = .ok rowsH ∧
      (if sk.length = 0 then rowsH.mapM (Expr.evalRow fun i : Fin its.length => (its[i]).1) = .ok base
       else ∃ keyedS, rowsH.mapM (fun r : Row (keyList.length + a) =>
          (do return (← Expr.evalRow (fun i : Fin sk.length => (sk[i]).e) r, r) :
            Except EvalError (Row sk.length × Row (keyList.length + a)))) = .ok keyedS ∧
        ((sortKeyed (fun i : Fin sk.length => sk[i]) keyedS).map Prod.snd).mapM
          (Expr.evalRow fun i : Fin its.length => (its[i]).1) = .ok base) := by
    by_cases h0 : sk.length = 0
    · simp only [h0, ↓reduceIte] at hbase ⊢
      rw [Query.eval_project] at hbase
      obtain ⟨rowsH, hH, hout⟩ := bind_ok hbase
      exact ⟨rowsH, hH, hout⟩
    · simp only [h0, ↓reduceIte] at hbase ⊢
      rw [Query.eval_project] at hbase
      obtain ⟨sorted, hsorted, hout⟩ := bind_ok hbase
      rw [Query.eval_orderBy] at hsorted
      obtain ⟨rowsH, hH, hsorted⟩ := bind_ok hsorted
      obtain ⟨keyedS, hkeyedS, hpure⟩ := bind_ok hsorted
      cases hpure
      exact ⟨rowsH, hH, keyedS, hkeyedS, hout⟩
  -- the aggregate's rows, filtered by `HAVING`
  let keep : Row (keyList.length + a) → Bool := fun A => P.all fun p => keepRow p A
  obtain ⟨rowsA, hA, rfl, hPt⟩ : ∃ rowsA, aggQ.eval D = .ok rowsA ∧ rowsH = rowsA.filter keep ∧
      ∀ A ∈ rowsA, ∀ p ∈ P, ∃ t, p.evalTruth A = .ok t := by
    rcases hP with ⟨-, rfl, rfl⟩ | ⟨hv, p, out, -, rfl, -, rfl⟩
    · exact ⟨rowsH, hH, by simp [keep], by simp⟩
    · rw [Query.eval_select] at hH
      obtain ⟨rowsA, hA, hfilt⟩ := bind_ok hH
      obtain ⟨hall, rfl⟩ := filterRows_eq_filter p hfilt
      exact ⟨rowsA, hA, by simp [keep], fun A hA p' hp' => by cases hp'; exact hall A hA⟩
  have hAeval := hA
  rw [haggQ, Query.eval_aggregate, hR] at hA
  obtain ⟨R', hR', hA⟩ := bind_ok hA
  cases hR'
  obtain ⟨keyed, hkeyed, hgrp⟩ := bind_ok hA
  have hg0 : keyList.length ≠ 0 := by
    intro h0; apply hgb; exact List.eq_nil_of_length_eq_zero (by omega)
  have hgroups : Row.groups keyed = Row.groupAux [] keyed := by simp [Row.groups, hg0]
  have hKeyed : List.Forall₂ (fun r p => ∃ k, Expr.evalRow (fun i : Fin keyList.length => keyList[i]) r
      = .ok k ∧ p = (k, r)) R keyed :=
    (mapM_forall₂ hkeyed).imp fun r p h => bind_pure_ok h
  have hitems : ∀ it ∈ items, ∃ e al, it = .exprItem e al := fun it hit => by
    obtain ⟨e, al, h, -⟩ := groupedItems_mem hgi it hit; exact ⟨e, al, h⟩
  -- `SqlEquiv`'s side
  simp only [SqlEquiv.evalQuery]
  rw [SqlEquiv.evalSelect_eq_evalSelectCore]
  obtain ⟨F, F', Φ, Ψ, hF, hF', hΦ, hΨ, heq⟩ :=
    evalSelectCore_grouped_full _ _ _ _ _ _ _ _ _ _ items fr wh groupBy having orderBy lim off hgb
  rw [heq, applyOrder_eq]
  apply limit_rel
  -- a typed aggregate row against `SqlEquiv`'s (projected row, key row)
  let PRA : Row (keyList.length + a) → SqlEquiv.Row × SqlEquiv.Row → Prop := fun A y =>
    (∀ o, Expr.evalRow (fun i : Fin its.length => (its[i]).1) A = .ok o → OutRel o y.1) ∧
    (∀ i : Fin sk.length, ∃ v, SqlEquiv.evalExprWithDb db (y.1 ++ y.2)
      ((SqlEquiv.groupOrderByItems orderBy)[i.1]'(by
        rw [length_groupOrderByItems]; omega)).expr = some v ∧
        DatumRel (A (Fin.natAdd _ (kj i))) v) ∧
    A.Conforms Γa
  have core : ∀ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U →
      List.Forall₂ PRA (rowsA.filter keep) (((U.foldl F []).filterMap Φ).zip
        ((U.foldl F' []).filterMap Ψ)) ∧
      (((U.foldl F []).filterMap Φ).zip ((U.foldl F' []).filterMap Ψ)).map Prod.fst =
        (U.foldl F []).filterMap Φ := by
    intro U hRU
    let kf : SqlEquiv.Row → List (Option SqlEquiv.Value) := fun u =>
      groupBy.map fun e => (SqlEquiv.evalExprWithDb db u e).map SqlEquiv.Value.setKey
    let E : Row keyList.length × Row n → SqlEquiv.Row → Prop := fun p u =>
      (RowRel cf N.fold p.2 u ∧ p.2.Conforms Γ₀) ∧
        Expr.evalRow (fun i : Fin keyList.length => keyList[i]) p.2 = .ok p.1 ∧ KRel Δk p.1 (kf u)
    have hE : List.Forall₂ E keyed U := by
      refine zip_rel (fun r pk u hpk hq => ?_) hKeyed hRU
      obtain ⟨k, hk, rfl⟩ := hpk
      refine ⟨hq, hk, ?_⟩
      have hval : ∀ i : Fin keyList.length, ∃ v,
          SqlEquiv.evalExprWithDb db u (groupBy[i.1]'(by omega)) = some v ∧
            TRel (Δk i) (k i) v := by
        intro i
        have hki : (keyList[i]).eval r = .ok (k i) := Expr.evalRow_eq_ok_iff.mp hk i
        obtain ⟨v, hv, hrel⟩ := Translates.eval_rel cf N.fold db hq.1 hq.2 (htk i) (hnbK i) hki
        exact ⟨v, hv, hrel, Expr.hasType_of_eval_eq_ok hq.2 (hks i) hki⟩
      choose w hw using hval
      refine ⟨w, ?_, fun i => (hw i).2⟩
      apply List.ext_getElem (by simp [kf, hlen])
      intro i h1 h2
      simp only [kf, List.getElem_map, List.getElem_ofFn]
      rw [(hw ⟨i, by simpa using h2⟩).1]; rfl
    have hgrel := groupAux_rel (E := E) (kf := kf) (KRel := KRel Δk) (fun _ _ _ h => h.2.2)
      (fun _ _ _ _ h₁ h₂ => krel_iff h₁ h₂) hE (acc := []) (acc' := []) .nil
    rw [foldl_insU kf F hF U [] List.nodup_nil, foldl_insU kf F' hF' U [] List.nodup_nil]
    have hsub : ∀ grp ∈ Row.groupAux [] keyed, grp ∈ Row.groups keyed := by
      rw [hgroups]; exact fun _ h => h
    have hGO : Row.GroupsOf keyed (Row.groups keyed) := by
      rw [hgroups]; exact Row.groupsOf_groupAux (fun _ h => by simp at h) (fun x hx => hx)
    have hP1 : List.Forall₂ (fun g A => (do return Fin.append g.1 (← AggCall.evalAll aggs g.2) :
        Except EvalError (Row (keyList.length + a))) = .ok A) (Row.groupAux [] keyed) rowsA := by
      rw [← hgroups]; exact mapM_forall₂ hgrp
    apply grouped_rel keep
    refine zip_rel_mem ?_ hP1 hgrel
    rintro ⟨k, rs'⟩ hgm A hAm ⟨key, us⟩ h1 ⟨hkk, hrs'⟩
    obtain ⟨hne, -⟩ := hGO _ (hsub _ hgm)
    simp only at hne hrs' hkk
    have hus : us ≠ [] := by
      rintro rfl; cases hrs'; exact hne rfl
    obtain ⟨s, hs⟩ : ∃ s, SqlEquiv.bareSampleRow (fun r e => SqlEquiv.evalExprWithDb db r e)
        (SqlEquiv.selectMinMaxCalls items having) us = some s :=
      Option.ne_none_iff_exists'.mp ((SqlEquiv.bareSampleRow_eq_none_iff _ _ _).not.mpr hus)
    have hsm := bareSampleRow_mem _ _ hs
    obtain ⟨Ag, hAe, rfl⟩ := bind_pure_ok h1
    have hrows' : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) rs' us :=
      hrs'.imp fun _ _ h => h.1
    obtain ⟨rs_, -, hE_⟩ := forall₂_mem_right hrs' hsm
    -- the aggregate row conforms
    have hrsc : ∀ r ∈ rs', r.Conforms Γ₀ := fun r hr => by
      obtain ⟨u, -, h⟩ := forall₂_mem_left hrows' hr; exact h.2
    have hAc : Row.Conforms Δa Ag := by
      rcases AggCall.evalAll_ok_or_divisionByZero hrsc has with ⟨A', hA', hc⟩ | ⟨hdz, -⟩
      · rw [hAe, Except.ok.injEq] at hA'; subst hA'; exact hc
      · rw [hAe] at hdz; cases hdz
    have hkc : Row.Conforms Δk k := fun i =>
      Expr.hasType_of_eval_eq_ok hE_.1.2 (hks i) (Expr.evalRow_eq_ok_iff.mp hE_.2.1 i)
    have hconf : Row.Conforms Γa (Fin.append k Ag : Row (keyList.length + a)) := by
      rw [← hΓeq]; exact Row.conforms_append_iff.mpr ⟨hkc, hAc⟩
    -- the `HAVING` decision agrees
    have hdec : keep (Fin.append k Ag) = having.all (fun c =>
        SqlEquiv.evalExprWithAggParam ee db us s c == some (.bool true)) := by
      rcases hP with ⟨hhn, hPn, -⟩ | ⟨hv, p, out, hhs, hPs, htrH, -⟩
      · simp [keep, hhn, hPn]
      · obtain ⟨t, ht⟩ := hPt _ hAm p (by simp [hPs])
        obtain ⟨d, hd, hdt⟩ : ∃ d, p.eval (Fin.append k Ag) = .ok d ∧ d.toTruth = .ok t := by
          unfold Expr.evalTruth at ht
          rcases he : p.eval (Fin.append k Ag) with _ | d
          · simp [he, bind, Except.bind] at ht
          · simp only [he, bind, Except.bind] at ht
            exact ⟨d, rfl, ht⟩
        obtain ⟨v, hv', hrel⟩ := TranslatesH.eval_rel cf out N.fold _ aggs db hrows' hAe hconf
          ⟨rs_, hE_.1.1, hE_.1.2, hE_.2.1⟩ hnbK hnbAgg (fun j => ⟨_, has j⟩) htrH
          (hnbP p (by simp [hPs])) hd
        simp only [keep, hPs, hhs, Option.all_some, keepRow, ht, hv']
        exact isTrue_iff_where hrel hdt
    rw [hΦ key us s hs, hΨ key us s hs, ← hdec]
    cases hkp : keep (Fin.append k Ag)
    · exact .inr ⟨rfl, by simp, by simp⟩
    simp only [↓reduceIte]
    refine .inl ⟨by simp, _, _, rfl, rfl, ?_, ?_, hconf⟩
    · -- the items
      intro r h2
      have hr := Expr.evalRow_eq_ok_iff.mp h2
      unfold OutRel
      rw [items_vals_group db us s hitems]
      apply List.forall₂_iff_get.mpr
      refine ⟨by simp [hits.length_eq], fun i h1' h2' => ?_⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
      have hi : i < its.length := by simpa using h1'
      have hi' : i < items.length := by simpa using h2'
      have hcase := (List.forall₂_iff_get.mp hits).2 i hi' hi
      simp only [List.get_eq_getElem] at hcase
      rcases hcase with ⟨j, hel, hj⟩ | ⟨c, i', hc, hel, hj⟩ | ⟨c, j, e', hc, hel, hkn, hjf, hj⟩
      · -- an aggregate
        have hri : r ⟨i, hi⟩ = Ag j := by
          have h3 := hr ⟨i, hi⟩
          have h4 : ((its[i]).1).eval (Fin.append k Ag) = .ok (Ag j) := by
            rw [hj]; show Except.ok _ = _; rw [Fin.append_right]
          exact Except.ok.inj (h3.symm.trans h4)
        obtain ⟨x, al, hx, hcase'⟩ := groupedItems_mem hgi _ (List.getElem_mem hi')
        have hfr : aggFragment (itemExpr items[i]) = true := by
          rw [hx]; simp only [itemExpr]
          rcases hcase' with h | ⟨c, rfl⟩
          · exact h
          · rw [hx] at hel; simp [itemExpr, elabAgg, throw, throwThe, MonadExceptOf.throw] at hel
        obtain ⟨v, hv, hvr⟩ := agg_rel cf N.fold db hrows' s _ hfr hel (hnbAgg j) (has j)
          (evalAll_get hAe j)
        rw [hri, hv]; exact hvr
      · -- a key column, read on the sample row
        have hri : r ⟨i, hi⟩ = k i' := by
          have h3 := hr ⟨i, hi⟩
          have h4 : ((its[i]).1).eval (Fin.append k Ag) = .ok (k i') := by
            rw [hj]; show Except.ok _ = _; rw [Fin.append_left]
          exact Except.ok.inj (h3.symm.trans h4)
        have hki : (keyList[i']).eval rs_ = .ok (k i') := Expr.evalRow_eq_ok_iff.mp hE_.2.1 i'
        have htr := translates_of_elab cf N.fold (.col c) rfl hel
        obtain ⟨v, hv, hvr⟩ := Translates.eval_rel cf N.fold db hE_.1.1 hE_.1.2 htr (hnbK i') hki
        rw [hri, hc]
        simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
        exact hvr
      · -- a bare column, read on the group's first row
        have hri : r ⟨i, hi⟩ = Ag j := by
          have h3 := hr ⟨i, hi⟩
          have h4 : ((its[i]).1).eval (Fin.append k Ag) = .ok (Ag j) := by
            rw [hj]; show Except.ok _ = _; rw [Fin.append_right]
          exact Except.ok.inj (h3.symm.trans h4)
        have hcr : c ∈ colRefs items := by
          obtain ⟨x, al, hx, -⟩ := groupedItems_mem hgi _ (List.getElem_mem hi')
          rw [hx] at hc; simp only [itemExpr] at hc; subst hc
          exact colRefs_of_mem (List.getElem_mem hi') hx
        have htr := translates_of_elab cf N.fold (.col c) rfl hel
        have hnbe : NoBoolOrder Γ₀ e' := by
          obtain ⟨idx, rfl⟩ := elab_col_is_col cf N.fold c hel; trivial
        have hfe := evalAll_get hAe j
        rw [hjf] at hfe
        rcases hmkC c e' hcr hel hkn with ⟨hfst, hcalls⟩ |
          ⟨wantMax, mode, arg, k', hm, hcalls, hfrag, hk', hat⟩
        · -- no `MIN`/`MAX`: `first`, on the group's first row
          rw [hfst] at hfe
          rw [hcalls, bareSampleRow_nil_calls] at hs
          obtain ⟨r₀, rs₁, rfl⟩ : ∃ r₀ rs₁, rs' = r₀ :: rs₁ := by
            cases rs' with
            | nil => cases hrows'; simp at hs
            | cons r₀ rs₁ => exact ⟨r₀, rs₁, rfl⟩
          obtain ⟨u₀, us₁, rfl⟩ : ∃ u₀ us₁, us = u₀ :: us₁ := by
            cases us with
            | nil => simp at hs
            | cons u₀ us₁ => exact ⟨u₀, us₁, rfl⟩
          simp only [List.head?_cons, Option.some.injEq] at hs
          subst hs
          have hrow₀ := (List.forall₂_cons.mp hrows').1
          have hd₀ := first_eval hfe
          obtain ⟨v, hv, hvr⟩ := Translates.eval_rel cf N.fold db hrow₀.1 hrow₀.2 htr hnbe hd₀
          rw [hri, hc]
          simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
          exact hvr
        · -- one `MIN`/`MAX`: `atExtreme`, on the row where its argument is extreme
          rw [hat] at hfe
          rw [hcalls] at hs
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
            (translates_of_elab cf N.fold arg hfrag hk') hnbk hkty htr hnbe hrows' hus hfe
          rw [hs'] at hs
          cases hs
          rw [hri, hc]
          simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
          exact hvr
    · -- the sort-key values, read back from the key row
      intro i
      have hob0 : orderBy ≠ [] := by
        intro h0
        have hi2 := i.2
        have : sk.length = 0 := by rw [← hlo, h0]; rfl
        omega
      let p := items.flatMap (SqlEquiv.evalSelectItemWithAggParam ee db us s)
      have hval : ∀ i' : Fin orderBy.length, ∃ v,
          SqlEquiv.evalExprWithAggParam ee db us (p ++ s) (orderBy[i']).expr = some v ∧
            DatumRel (Ag (kj ⟨i', by omega⟩)) v := fun i' =>
        agg_rel cf N.fold db hrows' (p ++ s) _ (hob _ (List.getElem_mem _)) (hkj ⟨i', by omega⟩).1
          (hnbAgg _) (has _) (evalAll_get hAe _)
      choose vs hvs using hval
      have hkr := groupOrderKeyRow_eq db _ orderBy us s p vs (fun i => (hvs i).1)
      have hfree : KeyNameFree p := by
        intro kv hkv
        obtain ⟨it, hit, hname⟩ := names_of_items db us s hitems kv hkv
        rw [hname]; exact hnm hob0 it hit
      refine ⟨vs ⟨i, by omega⟩, ?_, ?_⟩
      · rw [getElem_groupOrderByItems]
        show SqlEquiv.evalExprWithDb db (p ++ SqlEquiv.groupOrderKeyRow db _ orderBy us s p)
          (.col ⟨none, SqlEquiv.groupOrderKeyName i⟩) = _
        rw [SqlEquiv.evalExprWithDb_col, hkr]
        exact keyRow_lookup p hfree vs ⟨i, by omega⟩
      · show DatumRel (Fin.append k Ag (Fin.natAdd _ (kj i))) _
        rw [Fin.append_right]; exact (hvs ⟨i, by omega⟩).2
  suffices hfin : ∀ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U →
      List.Forall₂ OutRel base (if (SqlEquiv.groupOrderByItems orderBy).isEmpty then
        (U.foldl F []).filterMap Φ
      else ((((U.foldl F []).filterMap Φ).zip ((U.foldl F' []).filterMap Ψ)).mergeSort
        fun p₁ p₂ => SqlEquiv.compareByOrderItemsParam
          (fun db' r e => SqlEquiv.evalExprWithDb db' r e) db (p₁.1 ++ p₁.2) (p₂.1 ++ p₂.2)
          (SqlEquiv.groupOrderByItems orderBy)).map Prod.fst) by
    apply hfin
    rcases hq₀ with ⟨rfl, rfl⟩ | ⟨w, p, rfl, hp, rfl⟩
    · rw [hRf, Except.ok.injEq] at hR; subst hR; exact hrows
    · have hR' := hR
      simp only [Query.eval_select, hRf, bind, Except.bind] at hR'
      exact filter_rel _ _ db (translates_of_elab _ _ w (hw w rfl) hp) (hnbq₀.1 _ hsrc) hrows hR'
  intro U hRU
  obtain ⟨hPR, hfst⟩ := core U hRU
  by_cases h0 : sk.length = 0
  · have hob0 : orderBy = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hgob : (SqlEquiv.groupOrderByItems orderBy).isEmpty = true := by
      simp [hob0, SqlEquiv.groupOrderByItems]
    simp only [h0, ↓reduceIte] at hbase'
    simp only [hgob, ↓reduceIte]
    rw [← hfst]
    exact forall₂_mapM_rel (fun A y hpra c hc => hpra.1 c hc) hPR hbase'
  · have hgob : (SqlEquiv.groupOrderByItems orderBy).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff, ← List.length_pos_iff, length_groupOrderByItems]; omega
    simp only [h0, ↓reduceIte] at hbase'
    obtain ⟨keyedS, hkeyedS, hout⟩ := hbase'
    simp only [hgob, Bool.false_eq_true, ↓reduceIte]
    have hKS : List.Forall₂ (fun A x => ∃ kk, Expr.evalRow (fun i : Fin sk.length => (sk[i]).e) A =
        .ok kk ∧ x = (kk, A)) (rowsA.filter keep) keyedS :=
      (mapM_forall₂ hkeyedS).imp fun _ _ h => bind_pure_ok h
    let τ : Fin sk.length → SqlType := fun i => Δa (kj i)
    let PR : Row sk.length × Row (keyList.length + a) → SqlEquiv.Row × SqlEquiv.Row → Prop :=
      fun x y => PRA x.2 y ∧ ∀ i, x.1 i = x.2 (Fin.natAdd _ (kj i))
    have hPRz : List.Forall₂ PR keyedS (((U.foldl F []).filterMap Φ).zip
        ((U.foldl F' []).filterMap Ψ)) := zip_rel (fun A x y hx hpra => by
          obtain ⟨kk, hkk, rfl⟩ := hx
          refine ⟨hpra, fun i => ?_⟩
          have h3 := Expr.evalRow_eq_ok_iff.mp hkk i
          rw [(hkj i).2.1] at h3
          exact (Except.ok.inj h3).symm) hKS hPR
    obtain ⟨W, hW1, hW2, hW⟩ := sorted_gen (fun i : Fin sk.length => sk[i]) τ
      (fun p₁ p₂ => SqlEquiv.compareByOrderItemsParam
        (fun db' r e => SqlEquiv.evalExprWithDb db' r e) db (p₁.1 ++ p₁.2) (p₂.1 ++ p₂.2)
        (SqlEquiv.groupOrderByItems orderBy)) PR
      (fun x y hxy i => by
        show (x.1 i).HasType (Δa (kj i))
        have := hxy.1.2.2 (Fin.natAdd _ (kj i))
        simp only [← hΓeq, Fin.append_right] at this
        rw [hxy.2 i]; exact this)
      (fun x₁ y₁ x₂ y₂ h₁ h₂ => by
        apply compareBy_agree' _ db _ _ _ (by rw [length_groupOrderByItems]; exact hlo)
        intro i
        obtain ⟨v₁, hv₁, hr₁⟩ := h₁.1.2.1 i
        obtain ⟨v₂, hv₂, hr₂⟩ := h₂.1.2.1 i
        rw [hv₁, hv₂, h₁.2 i, h₂.2 i]
        refine cmpDatum_agree (sk[i]) _ ?_ ?_ hr₁ hr₂ ?_
        · rw [getElem_groupOrderByItems]; exact (hkj i).2.2.1
        · rw [getElem_groupOrderByItems]; exact (hkj i).2.2.2
        · rintro x y ⟨hx, -⟩
          have := h₁.1.2.2 (Fin.natAdd _ (kj i))
          simp only [← hΓeq, Fin.append_right] at this
          rw [hx] at this
          exact hτb h0 i (by simpa [Datum.HasType] using this.symm)) hPRz
    rw [hW1, List.map_map] at hout
    rw [hW2, List.map_map]
    exact mapM_rel_of (fun w hw d hd => (hW w hw).1.1 d hd) hout

end SqlBridge.CorrectGrouped

/-! ### Steps 3b-1 to 3b-3 as instances of the unified statement -/

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGrouped

theorem groupedItems_of_groupItems {groupBy : List SqlEquiv.Expr} :
    ∀ {items : List SqlEquiv.SelectItem}, groupItems groupBy items = true → groupedItems items = true
  | [], _ => rfl
  | .exprItem e al :: rest, h => by
    simp only [groupItems, groupedItems, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    refine ⟨?_, groupedItems_of_groupItems h.2⟩
    rcases h.1 with h1 | h1
    · exact .inl h1
    · right; cases e <;> simp_all
  | .star _ :: _, h => by simp [groupItems] at h

/-- **Elaborator correctness for `GROUP BY` (#352, roadmap step 3b-1).** For
    `SELECT … FROM f [WHERE p] GROUP BY c₁, …, cₘ`, with column keys and every item either a key
    column or an aggregate of step 3a, and `f` a `FROM` tree of step 2: when the statement
    elaborates, the typed query's groups relate, in order, to `SqlEquiv`'s. An instance of
    `elabStmt_correct_grouped`. -/
theorem elabStmt_correct_group (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} (hgi : groupItems groupBy items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hw : ∀ w ∈ wh, isFragment w = true)
    {e : Elaborated N.S} (h : elabStmt N (groupStmt items fr wh groupBy) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupStmt items fr wh groupBy)).2 = some out ∧
        List.Forall₂ OutRel rs out :=
  elabStmt_correct_grouped N hfold hfoldCI hwn hfix hD hrel (groupedItems_of_groupItems hgi) hgb hgc
    hff hw (by simp) (by simp) (.inl (colRefs_mem hgi)) (by simp) h hnb

/-- **Elaborator correctness for `GROUP BY … HAVING` (#352, roadmap step 3b-2).** As
    `elabStmt_correct_group`, with a `HAVING` predicate of literals, key columns, aggregates of
    step 3a, comparisons, `AND`, `OR` and `NOT` (`havingFragment`): the groups it keeps relate, in
    order. An instance of `elabStmt_correct_grouped`. -/
theorem elabStmt_correct_having (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} (hgi : groupItems groupBy items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hw : ∀ w ∈ wh, isFragment w = true) {hav : SqlEquiv.Expr}
    (hhv : havingFragment groupBy hav = true)
    {e : Elaborated N.S} (h : elabStmt N (groupStmt items fr wh groupBy (some hav)) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupStmt items fr wh groupBy (some hav))).2 = some out ∧
        List.Forall₂ OutRel rs out :=
  elabStmt_correct_grouped N hfold hfoldCI hwn hfix hD hrel (groupedItems_of_groupItems hgi) hgb hgc
    hff hw (fun h hh => by cases hh; exact hhv) (by simp) (.inl (colRefs_mem hgi)) (by simp) h hnb

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroupOrder
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGroup SqlBridge.CorrectGrouped

/-- **Elaborator correctness for `GROUP BY … ORDER BY` aggregates (#352, roadmap step 3b-3).** For
    `SELECT … FROM f [WHERE p] GROUP BY c₁, …, cₘ ORDER BY a₁, … [LIMIT n] [OFFSET m]`, the items
    and keys as in `elabStmt_correct_group`, every sort key an aggregate of step 3a, and no output
    name able to capture `SqlEquiv`'s sort-key columns: when the statement elaborates, the typed
    query's rows relate, in order, to `SqlEquiv`'s. An instance of `elabStmt_correct_grouped`. -/
theorem elabStmt_correct_group_ordered (N : NamedSchema)
    (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hgi : groupItems groupBy items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hw : ∀ w ∈ wh, isFragment w = true)
    (hob : ∀ o ∈ orderBy, aggFragment o.expr = true)
    (hnm : ∀ it ∈ items, '.' ∉ (outName it).toList ∧
      ∀ k, (outName it).toLower ≠ SqlEquiv.groupOrderKeyName k)
    {e : Elaborated N.S}
    (h : elabStmt N (groupOrderStmt items fr wh groupBy orderBy lim off) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupOrderStmt items fr wh groupBy orderBy lim off)).2 =
        some out ∧ List.Forall₂ OutRel rs out :=
  elabStmt_correct_grouped N hfold hfoldCI hwn hfix hD hrel (groupedItems_of_groupItems hgi) hgb hgc
    hff hw (by simp) hob (.inl (colRefs_mem hgi)) (fun _ => hnm) h hnb

end SqlBridge.CorrectGroupOrder
