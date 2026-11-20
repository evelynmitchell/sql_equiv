/-
  Elaborator correctness for `GROUP BY` (#352, roadmap step 3b-1).

  `SELECT … FROM f [WHERE p] GROUP BY c₁, …, cₘ`, the keys column references, every item a key
  column or an aggregate of step 3a, `f` a `FROM` tree of step 2. The typed core groups keyed rows
  in order of first appearance (`Row.groups`); `SqlEquiv` groups the filtered rows by the set keys
  of the key values, also in order of first appearance, and projects each group on a sample row.

  * Grouping: with distinct keys, `SqlEquiv`'s grouping step is `insU` (`addStep_new`,
    `addStep_found`, `foldl_insU`), and on related rows whose keys correspond (`KRel`,
    `krel_iff`: equal typed keys exactly when equal set keys, by `trel_iff`) the two groupings
    relate group by group, in order (`groupAux_rel`).
  * The query: `SqlEquiv`'s grouped path in closed form (`evalSelectCore_grouped`), the
    elaborator's (`elab_group_shape`: no bare columns, as every item column is a key), and the
    statement (`elabStmt_correct_group`): per group, aggregates by `agg_rel` (step 3a), key
    columns read on `SqlEquiv`'s sample row, which lies in the group.

  `HAVING`, ordering by aggregates and bare columns (registry T9) are later sub-steps.
-/
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

/-- The statements of steps 3b-1 and 3b-2 (with `HAVING`). -/
def groupStmt (items : List SqlEquiv.SelectItem) (f : SqlEquiv.FromClause)
    (wh : Option SqlEquiv.Expr) (groupBy : List SqlEquiv.Expr)
    (having : Option SqlEquiv.Expr := none) : SqlEquiv.Stmt :=
  .query (.simple (.mk false items (some f) wh groupBy having [] none none))

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
      List.append_nil, hgbe, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      at hraw
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
      List.append_nil, hgbe, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      at hraw
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

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg

/-- Combine the typed group rows (through the aggregate and the projection) with `SqlEquiv`'s
    per-group rows. -/
theorem out_rel {G G' A B O : Type _} {GR : G → G' → Prop} {P1 : G → A → Prop} {P2 : A → B → Prop}
    {Φ : G' → Option O} {OR : B → O → Prop} (gs₀ : List G)
    (H : ∀ g ∈ gs₀, ∀ g' a b, GR g g' → P1 g a → P2 a b → ∃ o, Φ g' = some o ∧ OR b o) :
    ∀ {gs : List G} {gs' : List G'} {as : List A} {bs : List B}, (∀ g ∈ gs, g ∈ gs₀) →
      List.Forall₂ GR gs gs' → List.Forall₂ P1 gs as → List.Forall₂ P2 as bs →
      List.Forall₂ OR bs (gs'.filterMap Φ)
  | _, _, _, _, _, .nil, .nil, .nil => .nil
  | g :: _, _ :: _, _ :: _, _ :: _, hsub, .cons hg hgs, .cons h1 h1s, .cons h2 h2s => by
    obtain ⟨o, ho, hor⟩ := H g (hsub g List.mem_cons_self) _ _ _ hg h1 h2
    rw [List.filterMap_cons_some ho]
    exact .cons hor (out_rel gs₀ H (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hgs h1s h2s)

theorem items_vals_group (db : SqlEquiv.Database) (U : List SqlEquiv.Row) (row : SqlEquiv.Row) :
    ∀ {items : List SqlEquiv.SelectItem}, (∀ it ∈ items, ∃ e al, it = .exprItem e al) →
      (items.flatMap (SqlEquiv.evalSelectItemWithAggParam ee db U row)).map Prod.snd =
        items.map fun it => (SqlEquiv.evalExprWithAggParam ee db U row (itemExpr it)).getD (.null none)
  | [], _ => rfl
  | it :: rest, h => by
    obtain ⟨e, al, rfl⟩ := h it List.mem_cons_self
    simp only [List.flatMap_cons, List.map_append, List.map_cons,
      items_vals_group db U row fun x hx => h x (List.mem_cons_of_mem _ hx)]
    simp only [SqlEquiv.evalSelectItemWithAggParam, itemExpr]
    split <;> simp_all

theorem bareSampleRow_mem (argEval : SqlEquiv.Row → SqlEquiv.Expr → Option SqlEquiv.Value)
    (calls : List (Bool × SqlEquiv.MinMaxMode × Option SqlEquiv.Expr × Bool)) {rows : SqlEquiv.Table}
    {s : SqlEquiv.Row} (h : SqlEquiv.bareSampleRow argEval calls rows = some s) : s ∈ rows := by
  unfold SqlEquiv.bareSampleRow at h
  repeat' split at h
  all_goals first
    | exact List.mem_of_getLast? h
    | exact List.mem_of_mem_head? h
    | (rcases Option.or_eq_some_iff.mp h with h' | ⟨-, h'⟩
       · exact List.mem_of_find?_eq_some h'
       · exact List.mem_of_mem_head? h')
/-- A typed key row against `SqlEquiv`'s group key: the set keys of related values, typed per
    position. -/
def KRel {g : ℕ} (Δ : Fin g → SqlType) (k : Row g) (l : List (Option SqlEquiv.Value)) : Prop :=
  ∃ w : Fin g → SqlEquiv.Value, l = List.ofFn (fun i => some (w i).setKey) ∧
    ∀ i, TRel (Δ i) (k i) (w i)

theorem krel_iff {g : ℕ} {Δ : Fin g → SqlType} {k₁ k₂ : Row g} {l₁ l₂ : List (Option SqlEquiv.Value)}
    (h₁ : KRel Δ k₁ l₁) (h₂ : KRel Δ k₂ l₂) : k₁ = k₂ ↔ l₁ = l₂ := by
  obtain ⟨w₁, rfl, hw₁⟩ := h₁
  obtain ⟨w₂, rfl, hw₂⟩ := h₂
  rw [List.ofFn_inj, funext_iff, funext_iff]
  refine forall_congr' fun i => ?_
  rw [Option.some.injEq]
  exact trel_iff _ _ _ _ (hw₁ i) (hw₂ i)
theorem zip_rel {α β γ : Type _} {P : α → β → Prop} {Q : α → γ → Prop} {E : β → γ → Prop}
    (h : ∀ a b c, P a b → Q a c → E b c) : ∀ {as : List α} {bs : List β} {cs : List γ},
      List.Forall₂ P as bs → List.Forall₂ Q as cs → List.Forall₂ E bs cs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hp hps, .cons hq hqs => .cons (h _ _ _ hp hq) (zip_rel h hps hqs)

set_option maxHeartbeats 1000000 in
/-- **Elaborator correctness for `GROUP BY` (#352, roadmap step 3b-1).** For
    `SELECT … FROM f [WHERE p] GROUP BY c₁, …, cₘ`, with column keys and every item either a key
    column or an aggregate of step 3a, and `f` a `FROM` tree of step 2: when the statement
    elaborates, the typed query's groups relate, in order, to `SqlEquiv`'s. Hypotheses as
    `elabStmt_correct_join`'s. -/
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
        List.Forall₂ OutRel rs out := by
  obtain ⟨hty, sub, n, qf, cf, hf, q₀, hq₀, keyList, a, aggs, its, hk, haggs, hits, rfl⟩ :=
    elab_group_shape N hgi hgb hw h
  obtain ⟨hnames, hfrom⟩ := from_rel N hfold hfoldCI hwn hfix hD hrel sub fr hff hf
  simp only at hnames hfrom hty hnb ⊢
  -- typing
  obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
  obtain ⟨Γa, hΓa, -⟩ := Query.typeOf_project_eq_some.mp hΔ
  obtain ⟨Γ₀, Δk, Δa, hq₀ty, hks, has, -⟩ := Query.typeOf_aggregate_eq_some hΓa
  obtain ⟨-, hnbA, hnbq₀⟩ := hnb
  have hnbK := (hnbA Γ₀ hq₀ty).1
  have hnbAgg := (hnbA Γ₀ hq₀ty).2
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
  have htk : ∀ i : Fin keyList.length, Translates cf N.fold (groupBy[i.1]'(by omega)) keyList[i] := by
    intro i
    have h1 := (List.forall₂_iff_get.mp hK).2 i.1 (by omega) i.2
    simp only [List.get_eq_getElem] at h1
    obtain ⟨c, hc⟩ := hgc _ (List.getElem_mem (by omega : i.1 < groupBy.length))
    rw [hc] at h1 ⊢
    exact translates_of_elab cf N.fold _ rfl h1
  -- the typed query evaluates
  have hdivK : ∀ i : Fin keyList.length, (keyList[i]).divSafe = true :=
    fun i => Translates.divSafe _ _ (htk i)
  have hsafe : (Query.project (fun i : Fin its.length => (its[i]).1)
      (Query.aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀)).IsSafe := by
    refine ⟨hty, ?_⟩
    have hcols : ∀ i : Fin its.length, ((its[i]).1).divSafe = true := by
      intro i
      rcases (List.forall₂_iff_get.mp hits).2 i.1 (by have := hits.length_eq; omega) i.2 with
        ⟨j, -, hj⟩ | ⟨c, i', -, -, hj⟩ <;>
        (simp only [List.get_eq_getElem] at hj; show ((its[i.1]).1).divSafe = true; rw [hj]; rfl)
    have hda : ∀ j, (aggs j).divSafe = true := fun j => by
      obtain ⟨x, hx, hel⟩ := haggs j; exact agg_divSafe cf N.fold x hx hel
    simp only [Query.divSafe, hda, hdivq₀, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun i => hcols i, fun i => hdivK i, fun _ => trivial⟩
  obtain ⟨rs, hrs⟩ := Query.IsSafe.exists_eval_eq_ok hsafe hD
  refine ⟨rs, hrs, _, rfl, ?_⟩
  -- the typed evaluation, step by step
  rw [Query.eval_project] at hrs
  obtain ⟨rowsA, hA, hout⟩ := bind_ok hrs
  rw [Query.eval_aggregate, hR] at hA
  obtain ⟨R', hR', hA⟩ := bind_ok hA
  cases hR'
  obtain ⟨keyed, hkeyed, hgrp⟩ := bind_ok hA
  have hg0 : keyList.length ≠ 0 := by
    intro h0; apply hgb; exact List.eq_nil_of_length_eq_zero (by omega)
  have hgroups : Row.groups keyed = Row.groupAux [] keyed := by simp [Row.groups, hg0]
  -- the keyed rows
  have hKeyed : List.Forall₂ (fun r p => ∃ k, Expr.evalRow (fun i : Fin keyList.length => keyList[i]) r
      = .ok k ∧ p = (k, r)) R keyed :=
    (mapM_forall₂ hkeyed).imp fun r p h => bind_pure_ok h
  -- `SqlEquiv`'s side
  simp only [SqlEquiv.evalQuery]
  rw [SqlEquiv.evalSelect_eq_evalSelectCore]
  obtain ⟨F, Φ, hF, hΦ, heq⟩ := evalSelectCore_grouped _ _ _ _ _ _ _ _ _ _ items fr wh groupBy hgb
  rw [heq]
  -- over any source rows related to the typed input
  have final : ∀ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U →
      List.Forall₂ OutRel rs ((U.foldl F []).filterMap Φ) := by
    intro U hRU
    let kf : SqlEquiv.Row → List (Option SqlEquiv.Value) := fun u =>
      groupBy.map fun e => (SqlEquiv.evalExprWithDb db u e).map SqlEquiv.Value.setKey
    let E : Row keyList.length × Row n → SqlEquiv.Row → Prop := fun p u =>
      (RowRel cf N.fold p.2 u ∧ p.2.Conforms Γ₀) ∧
        Expr.evalRow (fun i : Fin keyList.length => keyList[i]) p.2 = .ok p.1 ∧ KRel Δk p.1 (kf u)
    -- each keyed row relates to its untyped row, keys included
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
    rw [foldl_insU kf F hF U [] List.nodup_nil]
    have hsub : ∀ grp ∈ Row.groupAux [] keyed, grp ∈ Row.groups keyed := by rw [hgroups]; exact fun _ h => h
    have hGO : Row.GroupsOf keyed (Row.groups keyed) := by
      rw [hgroups]; exact Row.groupsOf_groupAux (fun _ h => by simp at h) (fun x hx => hx)
    refine out_rel (Row.groups keyed) ?_ hsub hgrel
      (by rw [← hgroups]; exact mapM_forall₂ hgrp) (mapM_forall₂ hout)
    rintro ⟨k, rs'⟩ hgm ⟨key, us⟩ rowA r ⟨hkk, hrs'⟩ h1 h2
    obtain ⟨hne, -⟩ := hGO _ hgm
    simp only at hne hrs' hkk
    have hus : us ≠ [] := by
      rintro rfl; cases hrs'; exact hne rfl
    obtain ⟨s, hs⟩ : ∃ s, SqlEquiv.bareSampleRow (fun r e => SqlEquiv.evalExprWithDb db r e)
        (SqlEquiv.selectMinMaxCalls items none) us = some s :=
      Option.ne_none_iff_exists'.mp ((SqlEquiv.bareSampleRow_eq_none_iff _ _ _).not.mpr hus)
    have hsm := bareSampleRow_mem _ _ hs
    refine ⟨_, hΦ key us s hs, ?_⟩
    obtain ⟨A, hAe, rfl⟩ := bind_pure_ok h1
    have hr := Expr.evalRow_eq_ok_iff.mp h2
    have hrows' : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) rs' us :=
      hrs'.imp fun _ _ h => h.1
    unfold OutRel
    rw [items_vals_group db us s (fun it hit => by
      obtain ⟨e, al, h, -⟩ := groupItems_mem hgi it hit; exact ⟨e, al, h⟩)]
    apply List.forall₂_iff_get.mpr
    refine ⟨by simp [hits.length_eq], fun i h1' h2' => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
    have hi : i < its.length := by simpa using h1'
    have hi' : i < items.length := by simpa using h2'
    have hcase := (List.forall₂_iff_get.mp hits).2 i hi' hi
    simp only [List.get_eq_getElem] at hcase
    rcases hcase with ⟨j, hel, hj⟩ | ⟨c, i', hc, hel, hj⟩
    · -- an aggregate
      have hri : r ⟨i, hi⟩ = A j := by
        have h3 := hr ⟨i, hi⟩
        have h4 : ((its[i]).1).eval (Fin.append k A) = .ok (A j) := by
          rw [hj]; show Except.ok _ = _; rw [Fin.append_right]
        exact Except.ok.inj (h3.symm.trans h4)
      obtain ⟨x, al, hx, hcase'⟩ := groupItems_mem hgi _ (List.getElem_mem hi')
      have hfr : aggFragment (itemExpr items[i]) = true := by
        rw [hx]; simp only [itemExpr]
        rcases hcase' with h | ⟨c, rfl, -⟩
        · exact h
        · rw [hx] at hel; simp [itemExpr, elabAgg, throw, throwThe, MonadExceptOf.throw] at hel
      obtain ⟨v, hv, hvr⟩ := agg_rel cf N.fold db hrows' s _ hfr hel (hnbAgg j) (has j)
        (evalAll_get hAe j)
      rw [hri, hv]; exact hvr
    · -- a key column, read on the sample row
      have hri : r ⟨i, hi⟩ = k i' := by
        have h3 := hr ⟨i, hi⟩
        have h4 : ((its[i]).1).eval (Fin.append k A) = .ok (k i') := by
          rw [hj]; show Except.ok _ = _; rw [Fin.append_left]
        exact Except.ok.inj (h3.symm.trans h4)
      obtain ⟨rs_, -, hE_⟩ := forall₂_mem_right hrs' hsm
      have hki : (keyList[i']).eval rs_ = .ok (k i') := Expr.evalRow_eq_ok_iff.mp hE_.2.1 i'
      have htr := translates_of_elab cf N.fold (.col c) rfl hel
      obtain ⟨v, hv, hvr⟩ := Translates.eval_rel cf N.fold db hE_.1.1 hE_.1.2 htr (hnbK i') hki
      rw [hri, hc]
      simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
      exact hvr
  apply final
  rcases hq₀ with ⟨rfl, rfl⟩ | ⟨w, p, rfl, hp, rfl⟩
  · rw [hRf, Except.ok.injEq] at hR; subst hR; exact hrows
  · have hR' := hR
    simp only [Query.eval_select, hRf, bind, Except.bind] at hR'
    exact filter_rel _ _ db (translates_of_elab _ _ w (hw w rfl) hp) (hnbq₀.1 _ hsrc) hrows hR'

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg

/-! ### `HAVING` (roadmap step 3b-2) -/

section Having
variable {n g a : ℕ} (cols : Fin n → Column) (out : Fin (g + a) → Column) (fold : String → String)
  (keys : Fin g → Expr n) (aggs : Fin a → AggCall n)

/-- A `HAVING` predicate over the aggregate's output elaborates the untyped one: literals,
    aggregates of step 3a (their output column), key columns (their key column), comparisons,
    `AND`, `OR`, `NOT`. -/
inductive TranslatesH : SqlEquiv.Expr → Expr (g + a) → Prop
  | lit {v : SqlEquiv.Value} {w : Value} : elabValue v = some w → TranslatesH (.lit v) (.lit w)
  | litNull {v : SqlEquiv.Value} (τ : SqlType) : elabValue v = none →
      TranslatesH (.lit v) (.null τ)
  | agg {x : SqlEquiv.Expr} {j : Fin a} : aggFragment x = true →
      elabAgg cols fold x = .ok (aggs j) → TranslatesH x (.col (Fin.natAdd g j))
  | key {c : SqlEquiv.ColumnRef} {i : Fin g} : elabExpr cols fold noHook (.col c) = .ok (keys i) →
      TranslatesH (.col c) (.col (Fin.castAdd a i))
  | cmp {op : SqlEquiv.BinOp} {c : CmpOp} {x y : SqlEquiv.Expr} {x' y' : Expr (g + a)} :
      elabBinOp op = .ok (.cmp c) → TranslatesH x x' → TranslatesH y y' →
      TranslatesH (.binOp op x y) (.binary (.cmp c) (retypeNull out x' y') (retypeNull out y' x'))
  | and {x y : SqlEquiv.Expr} {x' y' : Expr (g + a)} : TranslatesH x x' → TranslatesH y y' →
      TranslatesH (.binOp .and x y) (.binary .and (retypeNull out x' y') (retypeNull out y' x'))
  | or {x y : SqlEquiv.Expr} {x' y' : Expr (g + a)} : TranslatesH x x' → TranslatesH y y' →
      TranslatesH (.binOp .or x y) (.binary .or (retypeNull out x' y') (retypeNull out y' x'))
  | not {x : SqlEquiv.Expr} {x' : Expr (g + a)} : TranslatesH x x' →
      TranslatesH (.unaryOp .not x) (.unary .not x')

/-- On a group's output row, a `HAVING` predicate that evaluates relates to `SqlEquiv`'s value of
    it over the group's rows and sample row. -/
theorem TranslatesH.eval_rel (db : SqlEquiv.Database) {Γ : Fin n → SqlType} {Δ : Fin (g + a) → SqlType}
    {k : Row g} {A : Row a} {rs : List (Row n)} {us : List SqlEquiv.Row} {s : SqlEquiv.Row}
    (hrows : List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) rs us)
    (hA : AggCall.evalAll aggs rs = .ok A) (hconf : Row.Conforms Δ (Fin.append k A : Row (g + a)))
    (hs : ∃ r, RowRel cols fold r s ∧ r.Conforms Γ ∧ Expr.evalRow keys r = .ok k)
    (hnbK : ∀ i, NoBoolOrder Γ (keys i)) (hnbAgg : ∀ j, AggNoBool Γ (aggs j))
    (has : ∀ j, ∃ σ, (aggs j).typeOf Γ = some σ) :
    ∀ {e : SqlEquiv.Expr} {e' : Expr (g + a)}, TranslatesH cols out fold keys aggs e e' →
      NoBoolOrder Δ e' → ∀ {d : Datum}, e'.eval (Fin.append k A) = .ok d →
        ∃ v, SqlEquiv.evalExprWithAggParam ee db us s e = some v ∧ DatumRel d v := by
  intro e e' ht
  induction ht with
  | lit hw =>
    intro _ d h
    cases h
    exact ⟨_, by simp [SqlEquiv.evalExprWithAggParam, ee, SqlEquiv.evalExprWithDb_lit],
      valRel_of_elabValue hw⟩
  | @litNull v τ hw =>
    intro _ d h
    cases h
    cases v <;> simp [elabValue] at hw
    rename_i t
    exact ⟨.null t, by simp [SqlEquiv.evalExprWithAggParam, ee, SqlEquiv.evalExprWithDb_lit], ⟨t, rfl⟩⟩
  | @agg x j hx hel =>
    intro _ d h
    have hd : d = A j := by
      have : (Expr.col (Fin.natAdd g j) : Expr (g + a)).eval (Fin.append k A) = .ok (A j) := by
        show Except.ok _ = _; rw [Fin.append_right]
      exact Except.ok.inj (h.symm.trans this)
    subst hd
    obtain ⟨σ, hσ⟩ := has j
    exact agg_rel cols fold db hrows s x hx hel (hnbAgg j) hσ (evalAll_get hA j)
  | @key c i hel =>
    intro _ d h
    have hd : d = k i := by
      have : (Expr.col (Fin.castAdd a i) : Expr (g + a)).eval (Fin.append k A) = .ok (k i) := by
        show Except.ok _ = _; rw [Fin.append_left]
      exact Except.ok.inj (h.symm.trans this)
    subst hd
    obtain ⟨r, hrow, hr, hk⟩ := hs
    have hki : (keys i).eval r = .ok (k i) := Expr.evalRow_eq_ok_iff.mp hk i
    obtain ⟨v, hv, hrel⟩ := Translates.eval_rel cols fold db hrow hr
      (translates_of_elab cols fold (.col c) rfl hel) (hnbK i) hki
    exact ⟨v, by simp [SqlEquiv.evalExprWithAggParam, ee, hv], hrel⟩
  | @cmp op c x y x' y' hop _ _ iha ihb =>
    intro hnb d h
    obtain ⟨hc, hna, hnb'⟩ := hnb
    obtain ⟨da, db', hea, heb, hd⟩ := eval_binary_ok h
    have hea' := hea; have heb' := heb
    rw [eval_retypeNull] at hea' heb'
    obtain ⟨va, hva, hra⟩ := iha (noBoolOrder_of_retypeNull out y' hna) hea'
    obtain ⟨vb, hvb, hrb⟩ := ihb (noBoolOrder_of_retypeNull out x' hnb') heb'
    obtain ⟨v, hv, hrel⟩ := cmp_agree hop hra hrb (fun h1 h2 p q hpq => by
      rcases hc with hc | hc | ⟨τ, hτ, hτb⟩
      · exact h1 hc
      · exact h2 hc
      · rcases Expr.eval_ok_or_divisionByZero hconf hτ with ⟨d', hd', hty⟩ | ⟨hdz, _⟩
        · rw [hea] at hd'; cases hd'
          rw [hpq.1] at hty
          exact hτb (by simpa [Datum.HasType, Value.type] using hty.symm)
        · rw [hea] at hdz; cases hdz) hd
    exact ⟨v, by simp [SqlEquiv.evalExprWithAggParam, hva, hvb, hv], hrel⟩
  | and _ _ iha ihb =>
    intro hnb d h
    obtain ⟨hna, hnb'⟩ := hnb
    obtain ⟨da, db', hea, heb, hd⟩ := eval_binary_ok h
    rw [eval_retypeNull] at hea heb
    obtain ⟨va, hva, hra⟩ := iha (noBoolOrder_of_retypeNull out _ hna) hea
    obtain ⟨vb, hvb, hrb⟩ := ihb (noBoolOrder_of_retypeNull out _ hnb') heb
    obtain ⟨v, hv, hrel⟩ := and_agree hra hrb hd
    exact ⟨v, by simp [SqlEquiv.evalExprWithAggParam, hva, hvb, hv], hrel⟩
  | or _ _ iha ihb =>
    intro hnb d h
    obtain ⟨hna, hnb'⟩ := hnb
    obtain ⟨da, db', hea, heb, hd⟩ := eval_binary_ok h
    rw [eval_retypeNull] at hea heb
    obtain ⟨va, hva, hra⟩ := iha (noBoolOrder_of_retypeNull out _ hna) hea
    obtain ⟨vb, hvb, hrb⟩ := ihb (noBoolOrder_of_retypeNull out _ hnb') heb
    obtain ⟨v, hv, hrel⟩ := or_agree hra hrb hd
    exact ⟨v, by simp [SqlEquiv.evalExprWithAggParam, hva, hvb, hv], hrel⟩
  | not _ iha =>
    intro hn d h
    obtain ⟨da, hea, hd⟩ := eval_unary_ok h
    obtain ⟨va, hva, hra⟩ := iha hn hea
    obtain ⟨v, hv, hrel⟩ := not_agree hra hd
    exact ⟨v, by simp [SqlEquiv.evalExprWithAggParam, hva, hv], hrel⟩
/-- The `HAVING` predicates of step 3b-2: literals, key columns, aggregates of step 3a,
    comparisons, `AND`, `OR`, `NOT`. -/
def havingFragment (groupBy : List SqlEquiv.Expr) : SqlEquiv.Expr → Bool
  | .lit _ => true
  | .col c => decide (SqlEquiv.Expr.col c ∈ groupBy)
  | .binOp op x y =>
    (match op with
     | .eq | .ne | .lt | .le | .gt | .ge | .and | .or => true
     | _ => false) && havingFragment groupBy x && havingFragment groupBy y
  | .unaryOp .not x => havingFragment groupBy x
  | e => aggFragment e

omit out keys aggs in
theorem elab_lit_not_col (v : SqlEquiv.Value) {e'' : Expr n}
    (h : elabExpr cols fold noHook (.lit v) = .ok e'') : ∀ idx, e'' ≠ .col idx := by
  unfold elabExpr at h
  simp only [noHook] at h
  cases v <;> simp only [elabValue, pure, Except.pure, Except.ok.injEq] at h <;> subst h <;> simp

omit out keys aggs in
theorem elab_binOp_not_col (op : SqlEquiv.BinOp) (x y : SqlEquiv.Expr) {e'' : Expr n}
    (h : elabExpr cols fold noHook (.binOp op x y) = .ok e'') : ∀ idx, e'' ≠ .col idx := by
  simp only [elabExpr, noHook] at h
  rcases hx : elabExpr cols fold noHook x with _ | x'
  · cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure]
  rcases hy : elabExpr cols fold noHook y with _ | y'
  · cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure]
  cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure] <;> subst h <;> simp

omit out keys aggs in
theorem elab_unary_not_col (op : SqlEquiv.UnaryOp) (x : SqlEquiv.Expr) {e'' : Expr n}
    (h : elabExpr cols fold noHook (.unaryOp op x) = .ok e'') : ∀ idx, e'' ≠ .col idx := by
  simp only [elabExpr, noHook] at h
  rcases hx : elabExpr cols fold noHook x with _ | x'
  · simp [hx, bind, Except.bind] at h
  simp only [hx, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  subst h; simp

omit out aggs in
/-- The aggregate hook declines an expression that is no aggregate of the list and does not
    elaborate to a key (the keys are columns). -/
theorem aggHook_none (X : List SqlEquiv.Expr) {e : SqlEquiv.Expr}
    (hX : X.findIdx? (· == e) = none) (hkc : ∀ i, ∃ idx, keys i = .col idx)
    (hnc : ∀ e'', elabExpr cols fold noHook e = .ok e'' → ∀ idx, e'' ≠ .col idx) :
    aggHook (a := a) cols fold keys X e = none := by
  simp only [aggHook, hX]
  split
  · rename_i e'' he
    rw [Option.map_eq_none_iff, List.find?_eq_none]
    intro i _
    obtain ⟨idx, hidx⟩ := hkc i
    simp only [beq_iff_eq, hidx]
    exact fun h => hnc e'' he idx h.symm
  · rfl
end Having

section HavingElab
variable {n a : ℕ} (cols : Fin n → Column) (fold : String → String) (keyList : List (Expr n))
  (out : Fin (keyList.length + a) → Column) (aggs : Fin a → AggCall n) (X : List SqlEquiv.Expr)
  (groupBy : List SqlEquiv.Expr)
  (hXf : ∀ x ∈ X, aggFragment x = true)
  (hXa : ∀ j (hj : j < X.length), ∃ hja : j < a, elabAgg cols fold X[j] = .ok (aggs ⟨j, hja⟩))
  (hkc : ∀ i : Fin keyList.length, ∃ idx, keyList[i] = .col idx)
  (hkey : ∀ c, SqlEquiv.Expr.col c ∈ groupBy →
    ∃ e', elabExpr cols fold noHook (.col c) = .ok e' ∧ e' ∈ keyList)
include hXf hXa hkc hkey

omit hXa hkc hkey in
theorem findIdx_none_of_not_agg {e : SqlEquiv.Expr} (he : aggFragment e = false) :
    X.findIdx? (· == e) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro y hy
  have := hXf y hy
  have hne : y ≠ e := by rintro rfl; simp_all
  simpa using hne

omit hXf hkc hkey in
/-- An aggregate leaf of `HAVING` reads its aggregate's output column. -/
theorem agg_leaf {e : SqlEquiv.Expr} {e' : Expr (keyList.length + a)} (hfr : aggFragment e = true)
    (hsub : ∀ x ∈ aggsOf e, x ∈ X)
    (h : elabExpr out fold (aggHook (a := a) cols fold (fun i : Fin keyList.length => keyList[i]) X) e =
      .ok e') :
    TranslatesH cols out fold (fun i : Fin keyList.length => keyList[i]) aggs e e' := by
  have hmem : e ∈ X := hsub e (by simp [aggsOf_aggFragment e hfr])
  obtain ⟨j, hj⟩ : ∃ j, X.findIdx? (· == e) = some j :=
    Option.isSome_iff_exists.mp (by
      rw [List.findIdx?_isSome, List.any_eq_true]; exact ⟨e, hmem, by simp⟩)
  obtain ⟨hjl, hje, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
  obtain ⟨hja, hel⟩ := hXa j hjl
  rw [elab_of_hook _ _ _ (hook_agg cols fold _ X hj hja), Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at hje
  exact .agg hfr (hje ▸ hel)

/-- The elaborated `HAVING` predicate translates the untyped one. -/
theorem translatesH_of_elab : ∀ (h : SqlEquiv.Expr) {e' : Expr (keyList.length + a)},
    havingFragment groupBy h = true → (∀ x ∈ aggsOf h, x ∈ X) →
    elabExpr out fold (aggHook (a := a) cols fold (fun i : Fin keyList.length => keyList[i]) X) h =
      .ok e' →
    TranslatesH cols out fold (fun i : Fin keyList.length => keyList[i]) aggs h e'
  | .lit v, e', _, _, h => by
    unfold elabExpr at h
    rw [aggHook_none cols fold _ X (findIdx_none_of_not_agg X hXf rfl)
      (fun i => hkc i) (fun _ h => elab_lit_not_col cols fold v h)] at h
    cases v <;> simp only [elabValue, pure, Except.pure, Except.ok.injEq] at h <;> subst h
    · exact .lit rfl
    · exact .lit rfl
    · exact .lit rfl
    · exact .lit rfl
    · exact .litNull _ rfl
  | .col c, e', hf, _, h => by
    simp only [havingFragment, decide_eq_true_eq] at hf
    obtain ⟨e₀, he₀, hmem⟩ := hkey c hf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, (List.finRange keyList.length).find?
        (fun k : Fin keyList.length => keyList[k] == keyList[i]'hi) = some i₀ :=
      Option.isSome_iff_exists.mp
        ((List.find?_isSome (p := fun k : Fin keyList.length => keyList[k] == keyList[i]'hi)).mpr
          ⟨⟨i, hi⟩, List.mem_finRange _, beq_self_eq_true (keyList[i]'hi)⟩)
    have hk₀ : keyList[i₀] = keyList[i]'hi := by simpa using List.find?_some hi₀
    rw [elab_key keyList out cols fold X (findIdx_none_of_not_agg X hXf rfl) he₀ hi₀,
      Except.ok.injEq] at h
    subst h
    exact .key (by rw [he₀, hk₀])
  | .binOp op x y, e', hf, hsub, h => by
    simp only [havingFragment, Bool.and_eq_true] at hf
    obtain ⟨⟨hop, hx⟩, hy⟩ := hf
    have hsx : ∀ z ∈ aggsOf x, z ∈ X := fun z hz => hsub z (by simp [aggsOf, hz])
    have hsy : ∀ z ∈ aggsOf y, z ∈ X := fun z hz => hsub z (by simp [aggsOf, hz])
    unfold elabExpr at h
    rw [aggHook_none cols fold _ X (findIdx_none_of_not_agg X hXf (by simp [aggFragment]))
      (fun i => hkc i) (fun _ h => elab_binOp_not_col cols fold op x y h)] at h
    dsimp only at h
    rcases hea : elabExpr out fold (aggHook (a := a) cols fold (fun i : Fin keyList.length => keyList[i]) X) x
      with _ | x'
    · cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure]
    rcases heb : elabExpr out fold (aggHook (a := a) cols fold (fun i : Fin keyList.length => keyList[i]) X) y
      with _ | y'
    · cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure]
    have ta := translatesH_of_elab x hx hsx hea
    have tb := translatesH_of_elab y hy hsy heb
    cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure] <;> subst h
    · exact .cmp rfl ta tb
    · exact .cmp rfl ta tb
    · exact .cmp rfl ta tb
    · exact .cmp rfl ta tb
    · exact .cmp rfl ta tb
    · exact .cmp rfl ta tb
    · exact .and ta tb
    · exact .or ta tb
  | .unaryOp op x, e', hf, hsub, h => by
    cases op <;> simp only [havingFragment] at hf
    · unfold elabExpr at h
      rw [aggHook_none cols fold _ X (findIdx_none_of_not_agg X hXf (by simp [aggFragment]))
        (fun i => hkc i) (fun _ h => elab_unary_not_col cols fold _ x h)] at h
      dsimp only at h
      obtain ⟨x', hx', rfl⟩ := bind_pure_ok h
      exact .not (translatesH_of_elab x hf (fun z hz => hsub z (by simpa [aggsOf] using hz)) hx')
    all_goals simp [aggFragment] at hf
  | .countStar, e', hf, hsub, h => agg_leaf cols fold keyList out aggs X hXa
      (by simpa [havingFragment] using hf) hsub h
  | .agg fn arg d, e', hf, hsub, h => agg_leaf cols fold keyList out aggs X hXa
      (by simpa [havingFragment] using hf) hsub h
  | .func _ _, _, hf, _, _ | .case _ _, _, hf, _, _ | .inList _ _ _, _, hf, _, _
  | .between _ _ _, _, hf, _, _ | .inSubquery _ _ _, _, hf, _, _ | .exists _ _, _, hf, _, _
  | .subquery _, _, hf, _, _ | .windowFn _ _ _, _, hf, _, _ => by
    simp [havingFragment, aggFragment] at hf

end HavingElab

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup
open SqlEquiv

/-- `evalSelectCore_grouped` with an optional `HAVING`: a group whose predicate is not `TRUE` on its
    sample row gives no row. -/
theorem evalSelectCore_grouped_having (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool) (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause) (wh : Option Expr) (groupBy : List Expr)
    (having : Option Expr) (hg : groupBy ≠ []) :
    ∃ (F : List (List (Option Value) × Table) → Row → List (List (Option Value) × Table))
      (Φ : List (Option Value) × Table → Option (List (String × Value))),
      (∀ gs u, (gs.map Prod.fst).Nodup →
        F gs u = insU (groupBy.map fun e => (exprEval db u e).map Value.setKey) u gs) ∧
      (∀ key rows s, bareSampleRow (exprEval db) (selectMinMaxCalls items having) rows = some s →
        Φ (key, rows) = if (having.all fun c => exprWithAggEval db rows s c == some (Value.bool true))
          then some (items.flatMap (selectItemWithAggEval db rows s)) else none) ∧
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
        (SelectStmt.mk false items (some from_) wh groupBy having [] none none) =
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
    cases having <;> simp [h]
end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectAgg

theorem having_aggs {groupBy : List SqlEquiv.Expr} : ∀ (h : SqlEquiv.Expr),
    havingFragment groupBy h = true → ∀ x ∈ aggsOf h, aggFragment x = true
  | .lit _, _, x, hx | .col _, _, x, hx => by simp [aggsOf] at hx
  | .binOp op p q, hf, x, hx => by
    simp only [havingFragment, Bool.and_eq_true] at hf
    simp only [aggsOf, List.mem_append] at hx
    rcases hx with hx | hx
    · exact having_aggs p hf.1.2 x hx
    · exact having_aggs q hf.2 x hx
  | .unaryOp op p, hf, x, hx => by
    cases op <;> simp only [havingFragment] at hf
    · exact having_aggs p hf x (by simpa [aggsOf] using hx)
    all_goals simp [aggFragment] at hf
  | .countStar, hf, x, hx => by simp only [aggsOf, List.mem_singleton] at hx; subst hx; rfl
  | .agg _ _ _, hf, x, hx => by simp only [aggsOf, List.mem_singleton] at hx; subst hx; simpa [havingFragment] using hf
  | .func _ _, hf, _, _ | .case _ _, hf, _, _ | .inList _ _ _, hf, _, _
  | .between _ _ _, hf, _, _ | .inSubquery _ _ _, hf, _, _ | .exists _ _, hf, _, _
  | .subquery _, hf, _, _ | .windowFn _ _ _, hf, _, _ => by simp [havingFragment, aggFragment] at hf

theorem having_cols {groupBy : List SqlEquiv.Expr} : ∀ (h : SqlEquiv.Expr),
    havingFragment groupBy h = true → ∀ c ∈ colsOutsideAggs h, SqlEquiv.Expr.col c ∈ groupBy
  | .lit _, _, c, hc => by simp [colsOutsideAggs] at hc
  | .col c', hf, c, hc => by
    simp only [colsOutsideAggs, List.mem_singleton] at hc; subst hc
    simpa [havingFragment] using hf
  | .binOp op p q, hf, c, hc => by
    simp only [havingFragment, Bool.and_eq_true] at hf
    simp only [colsOutsideAggs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact having_cols p hf.1.2 c hc
    · exact having_cols q hf.2 c hc
  | .unaryOp op p, hf, c, hc => by
    cases op <;> simp only [havingFragment] at hf
    · exact having_cols p hf c (by simpa [colsOutsideAggs] using hc)
    all_goals simp [aggFragment] at hf
  | .countStar, _, c, hc | .agg _ _ _, _, c, hc => by simp [colsOutsideAggs] at hc
  | .func _ _, hf, _, _ | .case _ _, hf, _, _ | .inList _ _ _, hf, _, _
  | .between _ _ _, hf, _, _ | .inSubquery _ _ _, hf, _, _ | .exists _ _, hf, _, _
  | .subquery _, hf, _, _ | .windowFn _ _ _, hf, _, _ => by simp [havingFragment, aggFragment] at hf

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg

theorem elab_col_is_col {m : ℕ} (cols : Fin m → Column) (fold : String → String) (c : SqlEquiv.ColumnRef)
    {e' : Expr m} (h : elabExpr cols fold noHook (.col c) = .ok e') : ∃ idx, e' = .col idx := by
  simp only [elabExpr, noHook, resolve] at h
  rcases hr : resolveColumn cols (c.table.map fold) (fold c.column) with _ | i
  · rename_i err
    cases err <;> simp [hr, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rw [hr] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨i, h.symm⟩

set_option maxHeartbeats 1000000 in
theorem elab_having_shape_some (N : NamedSchema) {items : List SqlEquiv.SelectItem}
    {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} {groupBy : List SqlEquiv.Expr}
    (hgi : groupItems groupBy items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c)
    (hw : ∀ w ∈ wh, isFragment w = true) {hav : SqlEquiv.Expr}
    (hhv : havingFragment groupBy hav = true) {e : Elaborated N.S}
    (h : elabStmt N (groupStmt items fr wh groupBy (some hav)) = .ok e) :
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
        ∃ p out, TranslatesH cf out N.fold (fun i : Fin keyList.length => keyList[i]) aggs hav p ∧
        e = ⟨its.length, .project (fun i => (its[i]).1)
          (.select p (.aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀)),
          fun i => (its[i]).2⟩ := by
  simp only [groupStmt, elabStmt, elabQuery, bind, Except.bind] at h
  rcases hraw : elabQueryRaw N (.simple (.mk false items (some fr) wh groupBy (some hav) [] none none))
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
      List.append_nil, hgbe, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      at hraw
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
      List.append_nil, hgbe, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      at hraw
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
      have hc' : SqlEquiv.Expr.col c ∈ groupBy := by
        split at hc
        · rcases List.mem_append.mp (mem_of_mem_eraseDups' _ le_rfl hc) with hc | hc
          · exact colRefs_mem hgi c hc
          · exact having_cols hav hhv c hc
        · simp at hc
      obtain ⟨e', he', hmem⟩ := hkey c hc'
      simp [he', hmem]
    simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mapM_nil,
      pure, Except.pure, List.map_nil, List.append_nil] at hraw
    split at hraw
    · cases hraw
    rename_i out hout
    split at hraw
    · cases hraw
    rename_i p hp
    have hp' : elabExpr out N.fold (aggHook (a := (aggList ++ []).length) cf N.fold
        (fun i : Fin keyList.length => keyList[i])
        ((List.filter aggFragment (List.map itemExpr items)) ++ aggsOf hav).eraseDups) hav = .ok p := by
      split at hp
      · simp only [Except.ok.injEq] at hp; subst hp; assumption
      · split at hp <;> simp [throw, throwThe, MonadExceptOf.throw] at hp
      · simp [throw, throwThe, MonadExceptOf.throw] at hp
    split at hraw
    · cases hraw
    rename_i its hits
    obtain ⟨keys', hk', rfl⟩ := finishSelect_nondistinct N.fold _ [] none none hraw
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hk'
    subst hk'
    -- the aggregates' list holds aggregates only, and the keys are columns
    have hXf : ∀ x ∈ (((items.map itemExpr).filter aggFragment) ++ aggsOf hav).eraseDups,
        aggFragment x = true := by
      intro x hx
      rcases List.mem_append.mp (List.mem_eraseDups.mp hx) with hx | hx
      · exact (List.mem_filter.mp hx).2
      · exact having_aggs hav hhv x hx
    have hkc : ∀ i : Fin keyList.length, ∃ idx, keyList[i] = .col idx := by
      intro i
      have h1 := (List.forall₂_iff_get.mp hK).2 i.1 (by have := hK.length_eq; omega) i.2
      simp only [List.get_eq_getElem] at h1
      obtain ⟨c, hc⟩ := hgc _ (List.getElem_mem (by have := hK.length_eq; omega : i.1 < groupBy.length))
      rw [hc] at h1
      exact elab_col_is_col cf N.fold c h1
    refine ⟨keyList, _, fun j => aggList[j], its, hk, ?_, ?_, p, out, ?_, rfl⟩
    rotate_left 2
    · refine translatesH_of_elab cf N.fold keyList out (fun j => aggList[j]) _ groupBy hXf ?_ hkc hkey
        hav hhv (fun x hx => List.mem_eraseDups.mpr (List.mem_append_right _ hx)) hp'
      intro j hj
      refine ⟨by simpa [hV.length_eq] using hj, ?_⟩
      have := (List.forall₂_iff_get.mp hV).2 j hj (by rw [← hV.length_eq]; exact hj)
      simpa using this
    · intro ⟨j, hj⟩
      have hjv : j < aggList.length := by simpa using hj
      have hjl := hV.length_eq ▸ hjv
      have hx := (List.forall₂_iff_get.mp hV).2 j hjl hjv
      simp only [List.get_eq_getElem] at hx
      have hm := List.mem_eraseDups.mp (List.getElem_mem hjl)
      rcases List.mem_append.mp hm with hm | hm
      · exact ⟨_, (List.mem_filter.mp hm).2, hx⟩
      · exact ⟨_, having_aggs hav hhv _ hm, hx⟩
    · refine forall₂_imp_mem (mapM_forall₂ hits) fun it hit x hx => ?_
      obtain ⟨e, al, rfl, hcase⟩ := groupItems_mem hgi it hit
      dsimp only at hx
      rcases hcase with hfr | ⟨c, rfl, hc⟩
      · -- an aggregate: its column among the aggregates
        have hmem : e ∈ (((items.map itemExpr).filter aggFragment) ++ aggsOf hav).eraseDups :=
          List.mem_eraseDups.mpr (List.mem_append_left _
            (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_, hit, rfl⟩, hfr⟩))
        obtain ⟨j, hj⟩ : ∃ j, (((items.map itemExpr).filter aggFragment) ++ aggsOf hav).eraseDups.findIdx?
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
        have hnone : (((items.map itemExpr).filter aggFragment) ++ aggsOf hav).eraseDups.findIdx?
            (· == SqlEquiv.Expr.col c) = none := by
          rw [List.findIdx?_eq_none_iff]
          intro y hy
          have := hXf y hy
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

theorem TranslatesH.divSafe {n g a : ℕ} {cols : Fin n → Column} {out : Fin (g + a) → Column}
    {fold : String → String} {keys : Fin g → Expr n} {aggs : Fin a → AggCall n}
    {e : SqlEquiv.Expr} {e' : Expr (g + a)} (h : TranslatesH cols out fold keys aggs e e') :
    e'.divSafe = true := by
  induction h with
  | lit _ | litNull _ _ | agg _ _ | key _ => rfl
  | cmp _ _ _ iha ihb | and _ _ iha ihb | or _ _ iha ihb =>
    simp [Expr.divSafe, divSafe_retypeNull, iha, ihb, BinOp.isDivision]
  | not _ iha => simpa [Expr.divSafe] using iha

/-- `out_rel` with a filter between the aggregate and the projection (`HAVING`): a group the typed
    filter drops gives no `SqlEquiv` row. -/
theorem out_rel_filter {G G' O : Type _} {m k : ℕ} {GR : G → G' → Prop} {P1 : G → Row m → Prop}
    {p : Expr m} {es : Fin k → Expr m} {Φ : G' → Option O} {OR : Row k → O → Prop} (gs₀ : List G)
    (H : ∀ g ∈ gs₀, ∀ g' rowA, GR g g' → P1 g rowA → ∀ t, p.evalTruth rowA = .ok t →
      (t.isTrue = true → ∀ r, Expr.evalRow es rowA = .ok r → ∃ o, Φ g' = some o ∧ OR r o) ∧
      (t.isTrue = false → Φ g' = none)) :
    ∀ {gs : List G} {gs' : List G'} {as : List (Row m)} {as' : List (Row m)} {bs : List (Row k)},
      (∀ g ∈ gs, g ∈ gs₀) → List.Forall₂ GR gs gs' → List.Forall₂ P1 gs as →
      p.filterRows as = .ok as' → List.Forall₂ (fun row r => Expr.evalRow es row = .ok r) as' bs →
      List.Forall₂ OR bs (gs'.filterMap Φ)
  | _, _, [], as', bs, _, .nil, .nil, hf, h2 => by
    simp only [Expr.filterRows, List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at hf
    subst hf; cases h2; exact .nil
  | g :: _, g' :: _, rowA :: _, as', bs, hsub, .cons hg hgs, .cons h1 h1s, hf, h2 => by
    obtain ⟨t, R'', hte, hrs, rfl⟩ := filterRows_cons_ok hf
    obtain ⟨hT, hF⟩ := H g (hsub g List.mem_cons_self) g' rowA hg h1 t hte
    have hsub' := fun x hx => hsub x (List.mem_cons_of_mem _ hx)
    cases ht : t.isTrue
    · rw [List.filterMap_cons_none (hF ht)]
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at h2
      exact out_rel_filter gs₀ H hsub' hgs h1s hrs h2
    · simp only [ht, ↓reduceIte] at h2
      cases h2 with
      | cons hr h2s =>
        obtain ⟨o, ho, hor⟩ := hT ht _ hr
        rw [List.filterMap_cons_some ho]
        exact .cons hor (out_rel_filter gs₀ H hsub' hgs h1s hrs h2s)

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg

set_option maxHeartbeats 1000000 in
/-- **Elaborator correctness for `GROUP BY … HAVING` (#352, roadmap step 3b-2).** As
    `elabStmt_correct_group`, with a `HAVING` predicate of literals, key columns, aggregates of
    step 3a, comparisons, `AND`, `OR` and `NOT` (`havingFragment`): the groups it keeps relate, in
    order. For
    `SELECT … FROM f [WHERE p] GROUP BY c₁, …, cₘ`, with column keys and every item either a key
    column or an aggregate of step 3a, and `f` a `FROM` tree of step 2: when the statement
    elaborates, the typed query's groups relate, in order, to `SqlEquiv`'s. Hypotheses as
    `elabStmt_correct_join`'s. -/
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
        List.Forall₂ OutRel rs out := by
  obtain ⟨hty, sub, n, qf, cf, hf, q₀, hq₀, keyList, a, aggs, its, hk, haggs, hits, p, out, htrH,
    rfl⟩ := elab_having_shape_some N hgi hgb hgc hw hhv h
  obtain ⟨hnames, hfrom⟩ := from_rel N hfold hfoldCI hwn hfix hD hrel sub fr hff hf
  simp only at hnames hfrom hty hnb ⊢
  -- typing
  obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
  obtain ⟨Γa, hΓa, -⟩ := Query.typeOf_project_eq_some.mp hΔ
  obtain ⟨hΓagg, -⟩ := Query.typeOf_select_eq_some.mp hΓa
  obtain ⟨Γ₀, Δk, Δa, hq₀ty, hks, has, hΓeq⟩ := Query.typeOf_aggregate_eq_some hΓagg
  obtain ⟨-, hnbP, hnbA, hnbq₀⟩ := hnb
  have hnbK := (hnbA Γ₀ hq₀ty).1
  have hnbAgg := (hnbA Γ₀ hq₀ty).2
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
  have htk : ∀ i : Fin keyList.length, Translates cf N.fold (groupBy[i.1]'(by omega)) keyList[i] := by
    intro i
    have h1 := (List.forall₂_iff_get.mp hK).2 i.1 (by omega) i.2
    simp only [List.get_eq_getElem] at h1
    obtain ⟨c, hc⟩ := hgc _ (List.getElem_mem (by omega : i.1 < groupBy.length))
    rw [hc] at h1 ⊢
    exact translates_of_elab cf N.fold _ rfl h1
  -- the typed query evaluates
  have hdivK : ∀ i : Fin keyList.length, (keyList[i]).divSafe = true :=
    fun i => Translates.divSafe _ _ (htk i)
  have hsafe : (Query.project (fun i : Fin its.length => (its[i]).1)
      (Query.select p (Query.aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀))).IsSafe := by
    refine ⟨hty, ?_⟩
    have hcols : ∀ i : Fin its.length, ((its[i]).1).divSafe = true := by
      intro i
      rcases (List.forall₂_iff_get.mp hits).2 i.1 (by have := hits.length_eq; omega) i.2 with
        ⟨j, -, hj⟩ | ⟨c, i', -, -, hj⟩ <;>
        (simp only [List.get_eq_getElem] at hj; show ((its[i.1]).1).divSafe = true; rw [hj]; rfl)
    have hda : ∀ j, (aggs j).divSafe = true := fun j => by
      obtain ⟨x, hx, hel⟩ := haggs j; exact agg_divSafe cf N.fold x hx hel
    simp only [Query.divSafe, hda, hdivq₀, TranslatesH.divSafe htrH, Bool.and_true, Bool.true_and,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun i => hcols i, fun i => hdivK i, fun _ => trivial⟩
  obtain ⟨rs, hrs⟩ := Query.IsSafe.exists_eval_eq_ok hsafe hD
  refine ⟨rs, hrs, _, rfl, ?_⟩
  -- the typed evaluation, step by step
  rw [Query.eval_project] at hrs
  obtain ⟨rowsF, hFl, hout⟩ := bind_ok hrs
  rw [Query.eval_select] at hFl
  obtain ⟨rowsA, hA, hfilt⟩ := bind_ok hFl
  rw [Query.eval_aggregate, hR] at hA
  obtain ⟨R', hR', hA⟩ := bind_ok hA
  cases hR'
  obtain ⟨keyed, hkeyed, hgrp⟩ := bind_ok hA
  have hg0 : keyList.length ≠ 0 := by
    intro h0; apply hgb; exact List.eq_nil_of_length_eq_zero (by omega)
  have hgroups : Row.groups keyed = Row.groupAux [] keyed := by simp [Row.groups, hg0]
  -- the keyed rows
  have hKeyed : List.Forall₂ (fun r p => ∃ k, Expr.evalRow (fun i : Fin keyList.length => keyList[i]) r
      = .ok k ∧ p = (k, r)) R keyed :=
    (mapM_forall₂ hkeyed).imp fun r p h => bind_pure_ok h
  -- `SqlEquiv`'s side
  simp only [SqlEquiv.evalQuery]
  rw [SqlEquiv.evalSelect_eq_evalSelectCore]
  obtain ⟨F, Φ, hF, hΦ, heq⟩ := evalSelectCore_grouped_having _ _ _ _ _ _ _ _ _ _ items fr wh groupBy (some hav) hgb
  rw [heq]
  -- over any source rows related to the typed input
  have final : ∀ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U →
      List.Forall₂ OutRel rs ((U.foldl F []).filterMap Φ) := by
    intro U hRU
    let kf : SqlEquiv.Row → List (Option SqlEquiv.Value) := fun u =>
      groupBy.map fun e => (SqlEquiv.evalExprWithDb db u e).map SqlEquiv.Value.setKey
    let E : Row keyList.length × Row n → SqlEquiv.Row → Prop := fun p u =>
      (RowRel cf N.fold p.2 u ∧ p.2.Conforms Γ₀) ∧
        Expr.evalRow (fun i : Fin keyList.length => keyList[i]) p.2 = .ok p.1 ∧ KRel Δk p.1 (kf u)
    -- each keyed row relates to its untyped row, keys included
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
    rw [foldl_insU kf F hF U [] List.nodup_nil]
    have hsub : ∀ grp ∈ Row.groupAux [] keyed, grp ∈ Row.groups keyed := by rw [hgroups]; exact fun _ h => h
    have hGO : Row.GroupsOf keyed (Row.groups keyed) := by
      rw [hgroups]; exact Row.groupsOf_groupAux (fun _ h => by simp at h) (fun x hx => hx)
    refine out_rel_filter (Row.groups keyed) ?_ hsub hgrel
      (by rw [← hgroups]; exact mapM_forall₂ hgrp) hfilt (mapM_forall₂ hout)
    rintro ⟨k, rs'⟩ hgm ⟨key, us⟩ rowA ⟨hkk, hrs'⟩ h1 t ht
    obtain ⟨hne, -⟩ := hGO _ hgm
    simp only at hne hrs' hkk
    have hus : us ≠ [] := by
      rintro rfl; cases hrs'; exact hne rfl
    obtain ⟨s, hs⟩ : ∃ s, SqlEquiv.bareSampleRow (fun r e => SqlEquiv.evalExprWithDb db r e)
        (SqlEquiv.selectMinMaxCalls items (some hav)) us = some s :=
      Option.ne_none_iff_exists'.mp ((SqlEquiv.bareSampleRow_eq_none_iff _ _ _).not.mpr hus)
    have hsm := bareSampleRow_mem _ _ hs
    obtain ⟨A, hAe, rfl⟩ := bind_pure_ok h1
    have hrows' : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) rs' us :=
      hrs'.imp fun _ _ h => h.1
    -- the `HAVING` decision agrees
    obtain ⟨rs_, -, hE_⟩ := forall₂_mem_right hrs' hsm
    have hdec : (SqlEquiv.evalExprWithAggParam ee db us s hav == some (.bool true)) = t.isTrue := by
      have hrsc : ∀ r ∈ rs', r.Conforms Γ₀ := fun r hr => by
        obtain ⟨u, -, h⟩ := forall₂_mem_left hrows' hr; exact h.2
      have hAc : Row.Conforms Δa A := by
        rcases AggCall.evalAll_ok_or_divisionByZero hrsc has with ⟨A', hA', hc⟩ | ⟨hdz, -⟩
        · rw [hAe, Except.ok.injEq] at hA'; subst hA'; exact hc
        · rw [hAe] at hdz; cases hdz
      have hkc : Row.Conforms Δk k := fun i =>
        Expr.hasType_of_eval_eq_ok hE_.1.2 (hks i) (Expr.evalRow_eq_ok_iff.mp hE_.2.1 i)
      have hconf : Row.Conforms Γa (Fin.append k A : Row (keyList.length + a)) := by
        rw [← hΓeq]; exact Row.conforms_append_iff.mpr ⟨hkc, hAc⟩
      obtain ⟨d, hd, hdt⟩ : ∃ d, p.eval (Fin.append k A) = .ok d ∧ d.toTruth = .ok t := by
        unfold Expr.evalTruth at ht
        rcases he : p.eval (Fin.append k A) with _ | d
        · simp [he, bind, Except.bind] at ht
        · simp only [he, bind, Except.bind] at ht
          exact ⟨d, rfl, ht⟩
      obtain ⟨v, hv, hrel⟩ := TranslatesH.eval_rel cf out N.fold _ aggs db hrows' hAe hconf
        ⟨rs_, hE_.1.1, hE_.1.2, hE_.2.1⟩ hnbK hnbAgg (fun j => ⟨_, has j⟩) htrH
        (hnbP _ hΓagg) hd
      rw [hv]; exact (isTrue_iff_where hrel hdt).symm
    rw [hΦ key us s hs]
    split
    · rename_i hc
      have hc' : (SqlEquiv.evalExprWithAggParam ee db us s hav == some (.bool true)) = true := hc
      rw [hdec] at hc'
      refine ⟨fun _ r h2 => ⟨_, rfl, ?_⟩, fun hf => by rw [hf] at hc'; cases hc'⟩
      have hr := Expr.evalRow_eq_ok_iff.mp h2
      unfold OutRel
      rw [items_vals_group db us s (fun it hit => by
        obtain ⟨e, al, h, -⟩ := groupItems_mem hgi it hit; exact ⟨e, al, h⟩)]
      apply List.forall₂_iff_get.mpr
      refine ⟨by simp [hits.length_eq], fun i h1' h2' => ?_⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
      have hi : i < its.length := by simpa using h1'
      have hi' : i < items.length := by simpa using h2'
      have hcase := (List.forall₂_iff_get.mp hits).2 i hi' hi
      simp only [List.get_eq_getElem] at hcase
      rcases hcase with ⟨j, hel, hj⟩ | ⟨c, i', hc, hel, hj⟩
      · -- an aggregate
        have hri : r ⟨i, hi⟩ = A j := by
          have h3 := hr ⟨i, hi⟩
          have h4 : ((its[i]).1).eval (Fin.append k A) = .ok (A j) := by
            rw [hj]; show Except.ok _ = _; rw [Fin.append_right]
          exact Except.ok.inj (h3.symm.trans h4)
        obtain ⟨x, al, hx, hcase'⟩ := groupItems_mem hgi _ (List.getElem_mem hi')
        have hfr : aggFragment (itemExpr items[i]) = true := by
          rw [hx]; simp only [itemExpr]
          rcases hcase' with h | ⟨c, rfl, -⟩
          · exact h
          · rw [hx] at hel; simp [itemExpr, elabAgg, throw, throwThe, MonadExceptOf.throw] at hel
        obtain ⟨v, hv, hvr⟩ := agg_rel cf N.fold db hrows' s _ hfr hel (hnbAgg j) (has j)
          (evalAll_get hAe j)
        rw [hri, hv]; exact hvr
      · -- a key column, read on the sample row
        have hri : r ⟨i, hi⟩ = k i' := by
          have h3 := hr ⟨i, hi⟩
          have h4 : ((its[i]).1).eval (Fin.append k A) = .ok (k i') := by
            rw [hj]; show Except.ok _ = _; rw [Fin.append_left]
          exact Except.ok.inj (h3.symm.trans h4)
        obtain ⟨rs_, -, hE_⟩ := forall₂_mem_right hrs' hsm
        have hki : (keyList[i']).eval rs_ = .ok (k i') := Expr.evalRow_eq_ok_iff.mp hE_.2.1 i'
        have htr := translates_of_elab cf N.fold (.col c) rfl hel
        obtain ⟨v, hv, hvr⟩ := Translates.eval_rel cf N.fold db hE_.1.1 hE_.1.2 htr (hnbK i') hki
        rw [hri, hc]
        simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
        exact hvr
    · rename_i hc
      have hc' : ¬ (SqlEquiv.evalExprWithAggParam ee db us s hav == some (.bool true)) = true := hc
      rw [hdec] at hc'
      exact ⟨fun ht' => absurd ht' hc', fun _ => rfl⟩
  apply final
  rcases hq₀ with ⟨rfl, rfl⟩ | ⟨w, p, rfl, hp, rfl⟩
  · rw [hRf, Except.ok.injEq] at hR; subst hR; exact hrows
  · have hR' := hR
    simp only [Query.eval_select, hRf, bind, Except.bind] at hR'
    exact filter_rel _ _ db (translates_of_elab _ _ w (hw w rfl) hp) (hnbq₀.1 _ hsrc) hrows hR'


end SqlBridge.CorrectGroup
