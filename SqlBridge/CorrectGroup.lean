/-
  Elaborator correctness for `GROUP BY` and `HAVING` (#352, roadmap steps 3b-1 and 3b-2): the
  grouping and `HAVING` arguments. The statements are instances of `elabStmt_correct_grouped`
  (`SqlBridge/CorrectGrouped.lean`, step 3b-4), which also takes `ORDER BY` and bare columns.

  * Grouping: with distinct keys, `SqlEquiv`'s grouping step is `insU` (`addStep_new`,
    `addStep_found`, `foldl_insU`), and on related rows whose keys correspond (`KRel`,
    `krel_iff`: equal typed keys exactly when equal set keys, by `trel_iff`) the two groupings
    relate group by group, in order (`groupAux_rel`).
  * Items: `groupItems` (a key column or an aggregate of step 3a); the aggregates' hook resolves
    an aggregate to its output column and a key column to its key (`hook_agg`, `elab_key`).
  * `HAVING` (step 3b-2): `TranslatesH` relates the elaborator's predicate over the aggregate's
    output to `SqlEquiv`'s per-group predicate (`translatesH_of_elab`); they decide each group
    alike (`TranslatesH.eval_rel`).
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

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg

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
  (hXf : ∀ x ∈ X, aggFragment x = true ∨ ∃ c, x = .col c ∧ SqlEquiv.Expr.col c ∉ groupBy)
  (hXa : ∀ j (hj : j < X.length), aggFragment X[j] = true →
    ∃ hja : j < a, elabAgg cols fold X[j] = .ok (aggs ⟨j, hja⟩))
  (hkc : ∀ i : Fin keyList.length, ∃ idx, keyList[i] = .col idx)
  (hkey : ∀ c, SqlEquiv.Expr.col c ∈ groupBy →
    ∃ e', elabExpr cols fold noHook (.col c) = .ok e' ∧ e' ∈ keyList)
include hXf hXa hkc hkey

omit hXa hkc hkey in
/-- An expression that is neither an aggregate nor a column outside `GROUP BY` (a bare column) is
    not in the aggregates' list. -/
theorem findIdx_none_of_not_agg {e : SqlEquiv.Expr} (he : aggFragment e = false)
    (hc : ∀ c, e = .col c → SqlEquiv.Expr.col c ∈ groupBy) :
    X.findIdx? (· == e) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro y hy
  have hne : y ≠ e := by
    rintro rfl
    rcases hXf y hy with h | ⟨c, rfl, hn⟩
    · simp_all
    · exact hn (hc c rfl)
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
  simp only [beq_iff_eq] at hje
  obtain ⟨hja, hel⟩ := hXa j hjl (hje ▸ hfr)
  rw [elab_of_hook _ _ _ (hook_agg cols fold _ X hj hja), Except.ok.injEq] at h
  subst h
  exact .agg hfr (hje ▸ hel)

/-- The elaborated `HAVING` predicate translates the untyped one. -/
theorem translatesH_of_elab : ∀ (h : SqlEquiv.Expr) {e' : Expr (keyList.length + a)},
    havingFragment groupBy h = true → (∀ x ∈ aggsOf h, x ∈ X) →
    elabExpr out fold (aggHook (a := a) cols fold (fun i : Fin keyList.length => keyList[i]) X) h =
      .ok e' →
    TranslatesH cols out fold (fun i : Fin keyList.length => keyList[i]) aggs h e'
  | .lit v, e', _, _, h => by
    unfold elabExpr at h
    rw [aggHook_none cols fold _ X (findIdx_none_of_not_agg X groupBy hXf rfl (by simp))
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
    rw [elab_key keyList out cols fold X (findIdx_none_of_not_agg X groupBy hXf rfl (fun _ h => by cases h; exact hf)) he₀ hi₀,
      Except.ok.injEq] at h
    subst h
    exact .key (by rw [he₀, hk₀])
  | .binOp op x y, e', hf, hsub, h => by
    simp only [havingFragment, Bool.and_eq_true] at hf
    obtain ⟨⟨hop, hx⟩, hy⟩ := hf
    have hsx : ∀ z ∈ aggsOf x, z ∈ X := fun z hz => hsub z (by simp [aggsOf, hz])
    have hsy : ∀ z ∈ aggsOf y, z ∈ X := fun z hz => hsub z (by simp [aggsOf, hz])
    unfold elabExpr at h
    rw [aggHook_none cols fold _ X (findIdx_none_of_not_agg X groupBy hXf (by simp [aggFragment]) (by simp))
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
      rw [aggHook_none cols fold _ X (findIdx_none_of_not_agg X groupBy hXf (by simp [aggFragment]) (by simp))
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

theorem TranslatesH.divSafe {n g a : ℕ} {cols : Fin n → Column} {out : Fin (g + a) → Column}
    {fold : String → String} {keys : Fin g → Expr n} {aggs : Fin a → AggCall n}
    {e : SqlEquiv.Expr} {e' : Expr (g + a)} (h : TranslatesH cols out fold keys aggs e e') :
    e'.divSafe = true := by
  induction h with
  | lit _ | litNull _ _ | agg _ _ | key _ => rfl
  | cmp _ _ _ iha ihb | and _ _ iha ihb | or _ _ iha ihb =>
    simp [Expr.divSafe, divSafe_retypeNull, iha, ihb, BinOp.isDivision]
  | not _ iha => simpa [Expr.divSafe] using iha

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg

end SqlBridge.CorrectGroup
