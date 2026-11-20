import SqlBridge.CorrectAgg

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct

/-! ### Grouping: the typed `Row.groups` against `SqlEquiv`'s `addToGroups` -/

section Groups
variable {g n : ℕ} {β L : Type} [BEq L] [LawfulBEq L]

/-- `SqlEquiv`'s grouping step when group keys are distinct: add the row to the group of its key,
    or open a new group at the end. -/
def insU (key : L) (u : β) : List (L × List β) → List (L × List β)
  | [] => [(key, [u])]
  | (k, us) :: gs => if k == key then (k, us ++ [u]) :: gs else (k, us) :: insU key u gs

theorem insU_keys (key : L) (u : β) : ∀ gs : List (L × List β),
    (gs.map Prod.fst).Nodup → ((insU key u gs).map Prod.fst).Nodup ∧
      ∀ k, k ∈ (insU key u gs).map Prod.fst ↔ k = key ∨ k ∈ gs.map Prod.fst
  | [], _ => by simp [insU]
  | (k, us) :: gs, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨hk, hgs⟩ := h
    obtain ⟨ih1, ih2⟩ := insU_keys key u gs hgs
    by_cases hkk : k = key
    · subst hkk
      simp only [insU, beq_self_eq_true, ↓reduceIte, List.map_cons, List.nodup_cons, List.mem_cons]
      exact ⟨⟨hk, hgs⟩, fun k' => by tauto⟩
    · have : (k == key) = false := by simpa using hkk
      simp only [insU, this, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.nodup_cons,
        List.mem_cons]
      refine ⟨⟨fun hm => ?_, ih1⟩, fun k' => ?_⟩
      · rcases (ih2 k).mp hm with h | h
        · exact hkk h
        · exact hk h
      · rw [ih2]; tauto

variable (E : Row g × Row n → β → Prop) (kf : β → L) (KRel : Row g → L → Prop)

/-- Typed and untyped groups agree: related keys, and related rows in order. -/
def GRel (G : Row g × List (Row n)) (G' : L × List β) : Prop :=
  KRel G.1 G'.1 ∧ List.Forall₂ (fun r u => E (G.1, r) u) G.2 G'.2

variable {E kf KRel}
variable (hE : ∀ k r u, E (k, r) u → KRel k (kf u))
  (hK : ∀ k₁ l₁ k₂ l₂, KRel k₁ l₁ → KRel k₂ l₂ → (k₁ = k₂ ↔ l₁ = l₂))
include hE hK

theorem insert_rel {k : Row g} {r : Row n} {u : β} (hku : E (k, r) u) :
    ∀ {gs : List (Row g × List (Row n))} {gs' : List (L × List β)}, List.Forall₂ (GRel E KRel) gs gs' →
      List.Forall₂ (GRel E KRel) (Row.insertGroup k r gs) (insU (kf u) u gs')
  | _, _, .nil => .cons ⟨hE k r u hku, .cons hku .nil⟩ .nil
  | (k', rs) :: _, (key, us) :: _, .cons ⟨hkr, hrs⟩ hs => by
    have hiff := hK k' key k (kf u) hkr (hE k r u hku)
    by_cases hkk : k' = k
    · subst hkk
      have : (key == kf u) = true := by simpa using hiff.mp rfl
      simp only [Row.insertGroup, ↓reduceIte, insU, this]
      exact .cons ⟨hkr, List.rel_append hrs (.cons hku .nil)⟩ hs
    · have : (key == kf u) = false := by simpa using fun h => hkk (hiff.mpr h)
      simp only [Row.insertGroup, hkk, ↓reduceIte, insU, this, Bool.false_eq_true]
      exact .cons ⟨hkr, hrs⟩ (insert_rel hku hs)

theorem groupAux_rel : ∀ {l : List (Row g × Row n)} {U : List β}, List.Forall₂ E l U →
    ∀ {acc : List (Row g × List (Row n))} {acc' : List (L × List β)}, List.Forall₂ (GRel E KRel) acc acc' →
      List.Forall₂ (GRel E KRel) (Row.groupAux acc l) (U.foldl (fun gs u => insU (kf u) u gs) acc')
  | _, _, .nil, _, _, h => h
  | _ :: _, _ :: _, .cons hku hs, _, _, h => groupAux_rel hs (insert_rel hE hK hku h)

end Groups
end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup
open SqlEquiv

section Closed

theorem addStep_new {L : Type} [BEq L] [LawfulBEq L] {β : Type} (K : L) (u : β) :
    ∀ gs : List (L × List β), gs.find? (fun x => x.1 == K) = none → gs ++ [(K, [u])] = insU K u gs
  | [], _ => rfl
  | (k, us) :: gs, h => by
    simp only [List.find?_cons] at h
    split at h
    · cases h
    · rename_i hk
      simp only [List.cons_append, insU, hk, Bool.false_eq_true, ↓reduceIte, addStep_new K u gs h]

theorem addStep_found {L : Type} [BEq L] [LawfulBEq L] [DecidableEq L] {β : Type} (K : L) (u : β) :
    ∀ gs : List (L × List β), (gs.map Prod.fst).Nodup → ∀ {x}, gs.find? (fun x => x.1 == K) = some x →
      gs.map (fun x => if x.1 = K then (x.1, x.2 ++ [u]) else x) = insU K u gs
  | [], _, _, h => by simp at h
  | (k, us) :: gs, hnd, x, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases hk : k = K
    · subst hk
      simp only [List.map_cons, ↓reduceIte, insU, beq_self_eq_true, List.cons.injEq, _root_.true_and]
      calc _ = gs.map id := List.map_congr_left fun y hy => by
              have : y.1 ≠ k := fun e => hnd.1 (e ▸ List.mem_map_of_mem hy)
              simp [this]
        _ = gs := List.map_id gs
    · have hk' : (k == K) = false := by simpa using hk
      simp only [List.find?_cons, hk'] at h
      simp only [List.map_cons, hk, ↓reduceIte, insU, hk', Bool.false_eq_true,
        addStep_found K u gs hnd.2 h]

/-- `SqlEquiv`'s `GROUP BY` without `HAVING`, `ORDER BY`, `LIMIT`: the groups, built by a step
    that is `insU` on distinct keys, each projected on a sample row of the group. -/
theorem evalSelectCore_grouped (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool) (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause) (wh : Option Expr) (groupBy : List Expr)
    (hg : groupBy ≠ []) :
    ∃ (F : List (List (Option Value) × Table) → Row → List (List (Option Value) × Table))
      (Φ : List (Option Value) × Table → Option (List (String × Value))),
      (∀ gs u, (gs.map Prod.fst).Nodup →
        F gs u = insU (groupBy.map fun e => (exprEval db u e).map Value.setKey) u gs) ∧
      (∀ key rows s, bareSampleRow (exprEval db) (selectMinMaxCalls items none) rows = some s →
        Φ (key, rows) = some (items.flatMap (selectItemWithAggEval db rows s))) ∧
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
        (SelectStmt.mk false items (some from_) wh groupBy none [] none none) =
      ((match wh with
        | some c => (fromEval db from_).filter fun row => exprEval db row c == some (Value.bool true)
        | none => fromEval db from_).foldl F []).filterMap Φ := by
  have hne : groupBy.isEmpty = false := by cases groupBy <;> simp_all
  refine ⟨?F, ?Φ, ?h1, ?h2, ?h3⟩
  case h3 =>
    rw [evalSelectCore_eq_afterFilter]
    cases wh <;> simp [evalSelectAfterFilter, evalSelectProjectDistinct, hne] <;> rfl
  case h1 =>
    intro gs u h
    split
    · rename_i x hx
      exact addStep_found _ u gs h hx
    · rename_i hx
      exact addStep_new _ u gs hx
  case h2 =>
    intro key rows s h
    simp [h]

end Closed

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup

theorem foldl_insU {L β : Type} [BEq L] [LawfulBEq L] (kf : β → L)
    (F : List (L × List β) → β → List (L × List β))
    (hF : ∀ gs u, (gs.map Prod.fst).Nodup → F gs u = insU (kf u) u gs) :
    ∀ (U : List β) (acc : List (L × List β)), (acc.map Prod.fst).Nodup →
      U.foldl F acc = U.foldl (fun gs u => insU (kf u) u gs) acc
  | [], _, _ => rfl
  | u :: U, acc, h => by
    simp only [List.foldl_cons]
    rw [hF acc u h]
    exact foldl_insU kf F hF U _ (insU_keys _ u acc h).1

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg

/-! ### Elaboration of `SELECT … FROM f [WHERE p] GROUP BY c₁, …` -/

/-- Every item is an aggregate of step 3a, or a column that is one of the `GROUP BY` keys. -/
def groupItems (groupBy : List SqlEquiv.Expr) : List SqlEquiv.SelectItem → Bool
  | [] => true
  | .exprItem e _ :: rest =>
    (aggFragment e || match e with
      | .col c => decide (SqlEquiv.Expr.col c ∈ groupBy)
      | _ => false) && groupItems groupBy rest
  | _ :: _ => false

/-- The statements of step 3b-1. -/
def groupStmt (items : List SqlEquiv.SelectItem) (f : SqlEquiv.FromClause)
    (wh : Option SqlEquiv.Expr) (groupBy : List SqlEquiv.Expr) : SqlEquiv.Stmt :=
  .query (.simple (.mk false items (some f) wh groupBy none [] none none))

/-- The column references among the items. -/
def colRefs : List SqlEquiv.SelectItem → List SqlEquiv.ColumnRef
  | [] => []
  | .exprItem (.col c) _ :: rest => c :: colRefs rest
  | _ :: rest => colRefs rest

theorem groupItems_mem {groupBy : List SqlEquiv.Expr} : ∀ {items : List SqlEquiv.SelectItem},
    groupItems groupBy items = true → ∀ it ∈ items, ∃ e al, it = .exprItem e al ∧
      (aggFragment e = true ∨ ∃ c, e = .col c ∧ SqlEquiv.Expr.col c ∈ groupBy)
  | [], _, _, h => by simp at h
  | .exprItem e al :: rest, h, it, hit => by
    simp only [groupItems, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases List.mem_cons.mp hit with rfl | hit
    · refine ⟨e, al, rfl, ?_⟩
      rcases h.1 with h1 | h1
      · exact .inl h1
      · cases e <;> simp_all
    · exact groupItems_mem h.2 it hit
  | .star _ :: _, h, _, _ => by simp [groupItems] at h

theorem colRefs_mem {groupBy : List SqlEquiv.Expr} : ∀ {items : List SqlEquiv.SelectItem},
    groupItems groupBy items = true → ∀ c ∈ colRefs items, SqlEquiv.Expr.col c ∈ groupBy
  | [], _, _, h => by simp [colRefs] at h
  | .exprItem e al :: rest, h, c, hc => by
    simp only [groupItems, Bool.and_eq_true, Bool.or_eq_true] at h
    cases e
    case col c' =>
      simp only [colRefs, List.mem_cons] at hc
      rcases hc with rfl | hc
      · rcases h.1 with h1 | h1
        · simp [aggFragment] at h1
        · simpa using h1
      · exact colRefs_mem h.2 c hc
    all_goals exact colRefs_mem h.2 c (by simpa [colRefs] using hc)
  | .star _ :: _, h, _, _ => by simp [groupItems] at h

theorem aggsOf_groupItem (e : SqlEquiv.Expr) (h : aggFragment e = true ∨ ∃ c, e = .col c) :
    aggsOf e = (if aggFragment e then [e] else []) := by
  rcases h with h | ⟨c, rfl⟩
  · simp [aggsOf_aggFragment e h, h]
  · simp [aggsOf, aggFragment]

variable {f : SqlEquiv.SelectItem → Option SqlEquiv.Expr} (hf : ∀ e al, f (.exprItem e al) = some e)
include hf

theorem aggsOfList_groupItems {groupBy : List SqlEquiv.Expr} : ∀ items,
    groupItems groupBy items = true →
    aggsOfList (items.filterMap f) = (items.map itemExpr).filter aggFragment
  | [], _ => by simp [aggsOfList]
  | .exprItem e al :: rest, h => by
    simp only [groupItems, Bool.and_eq_true, Bool.or_eq_true] at h
    have he : aggFragment e = true ∨ ∃ c, e = .col c := by
      rcases h.1 with h1 | h1
      · exact .inl h1
      · cases e <;> simp_all
    simp only [List.filterMap_cons, hf, aggsOfList, aggsOf_groupItem e he,
      aggsOfList_groupItems rest h.2, List.map_cons, itemExpr, List.filter_cons]
    split <;> simp
  | .star _ :: _, h => by simp [groupItems] at h

theorem colsOutsideAggsList_groupItems {groupBy : List SqlEquiv.Expr} : ∀ items,
    groupItems groupBy items = true → colsOutsideAggsList (items.filterMap f) = colRefs items
  | [], _ => by simp [colsOutsideAggsList, colRefs]
  | .exprItem e al :: rest, h => by
    simp only [groupItems, Bool.and_eq_true, Bool.or_eq_true] at h
    have ih := colsOutsideAggsList_groupItems rest h.2
    rcases h.1 with h1 | h1
    · cases e <;> simp_all [colsOutsideAggsList, colsOutsideAggs, colRefs, aggFragment]
    · cases e <;> simp_all [colsOutsideAggsList, colsOutsideAggs, colRefs]
  | .star _ :: _, h => by simp [groupItems] at h

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg

theorem mem_of_mem_eraseDups' {α : Type} [BEq α] {a : α} :
    ∀ (n : ℕ) {l : List α}, l.length ≤ n → a ∈ l.eraseDups → a ∈ l
  | _, [], _, h => by simp at h
  | 0, _ :: _, hn, _ => by simp at hn
  | n + 1, b :: l, hn, h => by
    rw [List.eraseDups_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_of_mem_filter
        (mem_of_mem_eraseDups' n (le_trans (List.length_filter_le _ _) (by simpa using hn)) h))

theorem elab_of_hook {m : ℕ} (cols : Fin m → Column) (fold : String → String)
    (hook : SqlEquiv.Expr → Option (Expr m)) {e : SqlEquiv.Expr} {x : Expr m}
    (h : hook e = some x) : elabExpr cols fold hook e = .ok x := by
  unfold elabExpr; rw [h]; rfl

theorem hook_agg {n g a : ℕ} (cols : Fin n → Column) (fold : String → String) (keys : Fin g → Expr n)
    (X : List SqlEquiv.Expr) {e : SqlEquiv.Expr} {j : ℕ} (hj : X.findIdx? (· == e) = some j)
    (h : j < a) : aggHook (a := a) cols fold keys X e = some (.col (Fin.natAdd g ⟨j, h⟩)) := by
  simp [aggHook, hj, h]

theorem hook_key {n g a : ℕ} (cols : Fin n → Column) (fold : String → String) (keys : Fin g → Expr n)
    (X : List SqlEquiv.Expr) {e : SqlEquiv.Expr} {e' : Expr n} (hj : X.findIdx? (· == e) = none)
    (he : elabExpr cols fold noHook e = .ok e') {i : Fin g}
    (hi : (List.finRange g).find? (fun i => keys i == e') = some i) :
    aggHook (a := a) cols fold keys X e = some (.col (Fin.castAdd a i)) := by
  simp [aggHook, hj, he, hi]

theorem elab_key {n a : ℕ} (ks : List (Expr n)) (out : Fin (ks.length + a) → Column)
    (cols : Fin n → Column) (fold : String → String) (X : List SqlEquiv.Expr) {c : SqlEquiv.ColumnRef}
    {e' : Expr n} (hj : X.findIdx? (· == SqlEquiv.Expr.col c) = none)
    (he : elabExpr cols fold noHook (.col c) = .ok e') {i : Fin ks.length}
    (hi : (List.finRange ks.length).find? (fun k => ks[k] == e') = some i) :
    elabExpr out fold (aggHook (a := a) cols fold (fun i : Fin ks.length => ks[i]) X) (.col c) =
      .ok (.col (Fin.castAdd a i)) :=
  elab_of_hook _ _ _ (hook_key _ _ _ _ hj he hi)

set_option maxHeartbeats 1000000 in
theorem elab_group_shape (N : NamedSchema) {items : List SqlEquiv.SelectItem}
    {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} {groupBy : List SqlEquiv.Expr}
    (hgi : groupItems groupBy items = true) (hgb : groupBy ≠ [])
    (hw : ∀ w ∈ wh, isFragment w = true) {e : Elaborated N.S}
    (h : elabStmt N (groupStmt items fr wh groupBy) = .ok e) :
    e.q.typeOf.isSome ∧ ∃ sub n, ∃ qf : Query N.S n, ∃ cf, elabFrom N sub fr = .ok ⟨n, qf, cf⟩ ∧
      ∃ q₀ : Query N.S n,
        ((wh = none ∧ q₀ = qf) ∨ ∃ w p, wh = some w ∧
          elabExpr cf N.fold noHook w = .ok p ∧ q₀ = .select p qf) ∧
      ∃ (keyList : List (Expr n)) (a : ℕ) (aggs : Fin a → AggCall n)
        (its : List (Expr (keyList.length + a) × Column)),
        groupBy.mapM (elabExpr cf N.fold noHook) = .ok keyList ∧
        (∀ j, ∃ x, aggFragment x = true ∧ elabAgg cf N.fold x = .ok (aggs j)) ∧
        List.Forall₂ (fun it x =>
          (∃ j : Fin a, elabAgg cf N.fold (itemExpr it) = .ok (aggs j) ∧
            x.1 = .col (Fin.natAdd _ j)) ∨
          (∃ c, ∃ i : Fin keyList.length, itemExpr it = .col c ∧
            elabExpr cf N.fold noHook (.col c) = .ok keyList[i] ∧ x.1 = .col (Fin.castAdd a i)))
          items its ∧
        e = ⟨its.length, .project (fun i => (its[i]).1)
          (.aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀), fun i => (its[i]).2⟩ := by
  simp only [groupStmt, elabStmt, elabQuery, bind, Except.bind] at h
  rcases hraw : elabQueryRaw N (.simple (.mk false items (some fr) wh groupBy none [] none none))
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
    rw [aggsOfList_groupItems ?hf items hgi, colsOutsideAggsList_groupItems ?hf2 items hgi] at hraw
    case hf => intros; rfl
    case hf2 => intros; rfl
    simp only [List.map_nil, aggsOfList, aggsOfOpt, colsOutsideAggsOpt, colsOutsideAggsList,
      List.append_nil, hgbe, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      ] at hraw
    refine ⟨_, n, qf, cf, hf, qf, .inl ⟨rfl, rfl⟩, ?_⟩
  case' some w =>
    simp only [subsOf_frag w (hw w rfl), List.foldl_nil, List.isEmpty_nil, ↓reduceIte] at hraw
    rcases hp : elabExpr cf N.fold noHook w with _ | p
    · simp [hp, bind, Except.bind] at hraw
    simp only [hp, bind, Except.bind, pure, Except.pure] at hraw
    rw [aggsOfList_groupItems ?hf items hgi, colsOutsideAggsList_groupItems ?hf2 items hgi] at hraw
    case hf => intros; rfl
    case hf2 => intros; rfl
    simp only [List.map_nil, aggsOfList, aggsOfOpt, colsOutsideAggsOpt, colsOutsideAggsList,
      List.append_nil, hgbe, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      ] at hraw
    refine ⟨_, n, qf, cf, hf, .select p qf, .inr ⟨w, p, rfl, hp, rfl⟩, ?_⟩
  all_goals
    split at hraw
    · cases hraw
    rename_i keyList hk
    split at hraw
    · cases hraw
    rename_i aggList hv
    have hK := mapM_forall₂ hk
    have hV := mapM_forall₂ hv
    -- every item column is a key, so there are no bare columns
    have hkey : ∀ c, SqlEquiv.Expr.col c ∈ groupBy → ∃ e', elabExpr cf N.fold noHook (.col c) = .ok e' ∧
        e' ∈ keyList := fun c hc => by
      obtain ⟨e', he', h⟩ := forall₂_mem_left hK hc
      exact ⟨e', h, he'⟩
    rw [List.filterMap_eq_nil_iff.mpr ?hb] at hraw
    case hb =>
      intro c hc
      have hc' : c ∈ colRefs items := by
        split at hc
        · exact mem_of_mem_eraseDups' _ le_rfl hc
        · simp at hc
      obtain ⟨e', he', hmem⟩ := hkey c (colRefs_mem hgi c hc')
      simp [he', hmem]
    simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mapM_nil,
      pure, Except.pure, List.map_nil, List.append_nil] at hraw
    split at hraw
    · cases hraw
    rename_i out hout
    split at hraw
    · cases hraw
    rename_i its hits
    obtain ⟨keys', hk', rfl⟩ := finishSelect_nondistinct N.fold _ [] none none hraw
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hk'
    subst hk'
    refine ⟨keyList, _, fun j => aggList[j], its, hk, ?_, ?_, rfl⟩
    · intro ⟨j, hj⟩
      have hjv : j < aggList.length := by simpa using hj
      have hjl := hV.length_eq ▸ hjv
      have hx := (List.forall₂_iff_get.mp hV).2 j hjl hjv
      simp only [List.get_eq_getElem] at hx
      have hm := List.mem_eraseDups.mp (List.getElem_mem hjl)
      exact ⟨_, (List.mem_filter.mp hm).2, hx⟩
    · refine forall₂_imp_mem (mapM_forall₂ hits) fun it hit x hx => ?_
      obtain ⟨e, al, rfl, hcase⟩ := groupItems_mem hgi it hit
      dsimp only at hx
      rcases hcase with hfr | ⟨c, rfl, hc⟩
      · -- an aggregate: its column among the aggregates
        have hmem : e ∈ ((items.map itemExpr).filter aggFragment).eraseDups :=
          List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_, hit, rfl⟩, hfr⟩)
        obtain ⟨j, hj⟩ : ∃ j, ((items.map itemExpr).filter aggFragment).eraseDups.findIdx?
            (· == e) = some j :=
          Option.isSome_iff_exists.mp (by
            rw [List.findIdx?_isSome, List.any_eq_true]; exact ⟨e, hmem, by simp⟩)
        obtain ⟨hjl, hje, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
        simp only [beq_iff_eq] at hje
        have hjv : j < aggList.length := hV.length_eq ▸ hjl
        have hja : j < (aggList ++ []).length := by simpa using hjv
        rw [elab_of_hook _ _ _ (hook_agg _ _ _ _ hj hja)] at hx
        simp only at hx
        split at hx
        · simp only [Except.ok.injEq] at hx
          subst hx
          refine .inl ⟨⟨j, hja⟩, ?_, rfl⟩
          have := (List.forall₂_iff_get.mp hV).2 j hjl hjv
          simp only [List.get_eq_getElem, hje] at this
          simpa [itemExpr] using this
        · simp [throw, throwThe, MonadExceptOf.throw] at hx
      · -- a key column: its column among the keys
        have hnone : ((items.map itemExpr).filter aggFragment).eraseDups.findIdx?
            (· == SqlEquiv.Expr.col c) = none := by
          rw [List.findIdx?_eq_none_iff]
          intro y hy
          have := (List.mem_filter.mp (List.mem_eraseDups.mp hy)).2
          have hne : y ≠ .col c := by rintro rfl; simp [aggFragment] at this
          simpa using hne
        obtain ⟨e', he', hmem⟩ := hkey c hc
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
        obtain ⟨i₀, hi₀⟩ : ∃ i₀, (List.finRange keyList.length).find?
            (fun k : Fin keyList.length => keyList[k] == keyList[i]'hi) = some i₀ :=
          Option.isSome_iff_exists.mp
            ((List.find?_isSome (p := fun k : Fin keyList.length => keyList[k] == keyList[i]'hi)).mpr ⟨⟨i, hi⟩, List.mem_finRange _, beq_self_eq_true (keyList[i]'hi)⟩)
        have hk₀ : keyList[i₀] = keyList[i]'hi := by
          simpa using List.find?_some hi₀
        rw [elab_key keyList out cf N.fold _ hnone he' hi₀] at hx
        simp only at hx
        split at hx
        · simp only [Except.ok.injEq] at hx
          subst hx
          exact .inr ⟨c, i₀, rfl, by rw [he', hk₀], rfl⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at hx

end SqlBridge.CorrectGroup
