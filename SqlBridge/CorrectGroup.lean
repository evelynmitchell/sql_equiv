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
