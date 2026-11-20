/-
  The row a bare column reads next to one `MIN`/`MAX` (#352, roadmap step 3b-5; registry T9).

  The typed core's `AggCall.atExtreme` reads the column on the first row whose key is strictly
  best (`bestAt`), or on the last row when every key is `NULL`; `SqlEquiv`'s `bareSampleRow` takes
  the extreme value (`minMaxAgg`, the first strictly best of the non-`NULL` values) and reads the
  first row whose argument is that value. Both are the same fold on the keys' images in a linear
  order (`fbest`; `bestAt_fbest`, `extreme_fbest`), whose pick has only strictly worse keys before
  it (`fbest_inv`); so `SqlEquiv`'s search, which compares the untyped values structurally, finds
  that row too (`find_first_best`: an equal untyped value is the same typed value, `valRel_inj`).
  `atExtreme_rel` relates the two over related groups.
-/
import SqlBridge.CorrectAgg
import SqlBridge.CorrectOrder
import Mathlib.Data.String.Basic

namespace SqlBridge.CorrectExtreme

section FirstBest
variable {β α γ : Type _} [LinearOrder β]

/-- `k` is strictly better than `b`: greater when `wantMax`, else less. -/
def betterB (wantMax : Bool) (k b : β) : Bool := if wantMax then decide (b < k) else decide (k < b)

/-- The first strictly best entry of a list of keyed items, `none` keys skipped. -/
def fbest (wantMax : Bool) : Option (β × α) → List (Option β × α) → Option (β × α)
  | acc, [] => acc
  | acc, (none, _) :: ps => fbest wantMax acc ps
  | none, (some k, x) :: ps => fbest wantMax (some (k, x)) ps
  | some (b, y), (some k, x) :: ps =>
    fbest wantMax (if betterB wantMax k b then some (k, x) else some (b, y)) ps

theorem betterB_trans (wantMax : Bool) {a b c : β} (h₁ : betterB wantMax a b = true)
    (h₂ : betterB wantMax b c = true) : betterB wantMax a c = true := by
  cases wantMax <;> simp only [betterB, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at * <;>
    first | exact lt_trans h₂ h₁ | exact lt_trans h₁ h₂

theorem betterB_trans' (wantMax : Bool) {a b c : β} (h₁ : betterB wantMax a b = true)
    (h₂ : betterB wantMax c b = false) : betterB wantMax a c = true := by
  cases wantMax <;> simp_all [betterB]
  · exact lt_of_lt_of_le h₁ h₂
  · exact lt_of_le_of_lt h₂ h₁

theorem betterB_irrefl (wantMax : Bool) (a : β) : betterB wantMax a a = false := by
  cases wantMax <;> simp [betterB]

/-- The invariant of `fbest`: with no pick, every key so far is `none`; with a pick, every key
    before it is strictly worse, and none after it is better. -/
def FInv (wantMax : Bool) : Option (β × α) → List (Option β × α) → Prop
  | none, pre => ∀ p ∈ pre, p.1 = none
  | some (b, y), pre => ∃ l r, pre = l ++ (some b, y) :: r ∧
      (∀ p ∈ l, ∀ k, p.1 = some k → betterB wantMax b k = true) ∧
      (∀ p ∈ r, ∀ k, p.1 = some k → betterB wantMax k b = false)

theorem fbest_inv (wantMax : Bool) :
    ∀ (ps pre : List (Option β × α)) (acc : Option (β × α)), FInv wantMax acc pre →
      FInv wantMax (fbest wantMax acc ps) (pre ++ ps)
  | [], pre, acc, h => by simpa [fbest] using h
  | (none, x) :: ps, pre, acc, h => by
    have : FInv wantMax acc (pre ++ [(none, x)]) := by
      rcases acc with _ | ⟨b, y⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact h p hp
        · simp at hp; rw [hp]
      · obtain ⟨l, r, rfl, hl, hr⟩ := h
        refine ⟨l, r ++ [(none, x)], by simp, hl, fun p hp k hk => ?_⟩
        rcases List.mem_append.mp hp with hp | hp
        · exact hr p hp k hk
        · simp at hp; rw [hp] at hk; cases hk
    simpa [fbest] using fbest_inv wantMax ps _ acc this
  | (some k, x) :: ps, pre, none, h => by
    have : FInv wantMax (some (k, x)) (pre ++ [(some k, x)]) := by
      refine ⟨pre, [], rfl, fun p hp c hc => ?_, by simp⟩
      rw [h p hp] at hc; cases hc
    simpa [fbest] using fbest_inv wantMax ps _ _ this
  | (some k, x) :: ps, pre, some (b, y), h => by
    obtain ⟨l, r, rfl, hl, hr⟩ := h
    have : FInv wantMax (if betterB wantMax k b then some (k, x) else some (b, y))
        (l ++ (some b, y) :: r ++ [(some k, x)]) := by
      by_cases hkb : betterB wantMax k b = true
      · simp only [hkb, ↓reduceIte]
        refine ⟨l ++ (some b, y) :: r, [], by simp, fun p hp c hc => ?_, by simp⟩
        rcases List.mem_append.mp hp with hp | hp
        · exact betterB_trans wantMax hkb (hl p hp c hc)
        · rcases List.mem_cons.mp hp with rfl | hp
          · cases hc; exact hkb
          · exact betterB_trans' wantMax hkb (hr p hp c hc)
      · simp only [hkb, Bool.false_eq_true, ↓reduceIte]
        refine ⟨l, r ++ [(some k, x)], by simp, hl, fun p hp c hc => ?_⟩
        rcases List.mem_append.mp hp with hp | hp
        · exact hr p hp c hc
        · simp at hp; rw [hp] at hc; cases hc; simpa using hkb
    simpa [fbest] using fbest_inv wantMax ps _ _ this

/-- `fbest` picks by key only: a change of payload carries over. -/
theorem fbest_map (wantMax : Bool) (g : α → γ) :
    ∀ (ps : List (Option β × α)) (acc : Option (β × α)),
      fbest wantMax (acc.map fun p => (p.1, g p.2)) (ps.map fun p => (p.1, g p.2)) =
        (fbest wantMax acc ps).map fun p => (p.1, g p.2)
  | [], _ => rfl
  | (none, x) :: ps, acc => by simpa [fbest] using fbest_map wantMax g ps acc
  | (some k, x) :: ps, none => by simpa [fbest] using fbest_map wantMax g ps (some (k, x))
  | (some k, x) :: ps, some (b, y) => by
    have := fbest_map wantMax g ps (if betterB wantMax k b then some (k, x) else some (b, y))
    show fbest wantMax (if betterB wantMax k b then some (k, g x) else some (b, g y)) _ = _
    rw [show fbest wantMax (some (b, y)) ((some k, x) :: ps) =
      fbest wantMax (if betterB wantMax k b then some (k, x) else some (b, y)) ps from rfl]
    by_cases h : betterB wantMax k b = true
    · simp only [h, ↓reduceIte] at this ⊢; exact this
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at this ⊢; exact this

end FirstBest
section Instances
open SqlCore SqlBridge.Correct SqlBridge.CorrectAgg
variable {β : Type _} [LinearOrder β]

theorem pick_iff (wantMax : Bool) (x y : β) :
    (compare x y = if wantMax then .gt else .lt) ↔ betterB wantMax x y = true := by
  cases wantMax <;> simp [betterB, compare_gt_iff_gt, compare_lt_iff_lt]

/-- The typed `bestAt` is `fbest` over the keys' images in a linear order. -/
theorem bestAt_fbest {τ : SqlType} (f : Value → β)
    (hf : ∀ a b : Value, a.type = τ → b.type = τ → Value.cmp a b = .ok (compare (f a) (f b)))
    (wantMax : Bool) : ∀ (ps : List (Datum × Datum)) (acc : Option (Value × Datum)),
      (∀ p ∈ ps, p.1.HasType τ) → (∀ b y, acc = some (b, y) → b.type = τ) →
      ∃ r, bestAt (if wantMax then .gt else .lt) acc ps = .ok r ∧
        r.map Prod.snd = (fbest wantMax (acc.map fun p => (f p.1, p.2))
          (ps.map fun p => (p.1.map f, p.2))).map Prod.snd
  | [], acc, _, _ => ⟨acc, rfl, by cases acc <;> rfl⟩
  | (none, v) :: ps, acc, hps, hacc => by
    obtain ⟨r, hr, hrm⟩ := bestAt_fbest f hf wantMax ps acc (fun p hp => hps p (by simp [hp])) hacc
    exact ⟨r, by simpa [bestAt] using hr, by simpa [fbest] using hrm⟩
  | (some k, v) :: ps, none, hps, _ => by
    have hk : k.type = τ := hps _ List.mem_cons_self
    obtain ⟨r, hr, hrm⟩ := bestAt_fbest f hf wantMax ps (some (k, v))
      (fun p hp => hps p (by simp [hp])) (fun b y h => by cases h; exact hk)
    exact ⟨r, by simpa [bestAt] using hr, by simpa [fbest] using hrm⟩
  | (some k, v) :: ps, some (b, w), hps, hacc => by
    have hk : k.type = τ := hps _ List.mem_cons_self
    have hb : b.type = τ := hacc b w rfl
    have hcond : (compare (f k) (f b) = if wantMax then .gt else .lt) ↔
        betterB wantMax (f k) (f b) = true := pick_iff wantMax _ _
    let acc' : Option (Value × Datum) := if betterB wantMax (f k) (f b) then some (k, v) else some (b, w)
    obtain ⟨r, hr, hrm⟩ := bestAt_fbest f hf wantMax ps acc'
      (fun p hp => hps p (by simp [hp])) (fun b' y h => by
        simp only [acc'] at h; split at h <;> cases h <;> assumption)
    refine ⟨r, ?_, ?_⟩
    · simp only [bestAt, hf k b hk hb, bind, Except.bind]
      convert hr using 2
      simp only [acc']
      by_cases hbt : betterB wantMax (f k) (f b) = true
      · simp [hbt, hcond.mpr hbt]
      · have : ¬ (compare (f k) (f b) = if wantMax then .gt else .lt) := fun h => hbt (hcond.mp h)
        simp [hbt, this]
    · rw [hrm]
      show _ = (fbest wantMax (if betterB wantMax (f k) (f b) then some (f k, v) else some (f b, w))
        (ps.map fun p => (p.1.map f, p.2))).map Prod.snd
      simp only [acc']
      split <;> rfl

/-- `SqlEquiv`'s `extremeValue` fold over the non-`NULL` values is `fbest` over the related typed
    keys, with the untyped values as payload. -/
theorem extreme_fbest {τ : SqlType} (hτ : τ ≠ .bool) (f : Value → β)
    (hf : ∀ a b : Value, a.type = τ → b.type = τ → Value.cmp a b = .ok (compare (f a) (f b)))
    (wantMax : Bool) : ∀ {ks : List Datum} {ws : List SqlEquiv.Value}, List.Forall₂ (TRel τ) ks ws →
      ∀ (acc : Option (Value × SqlEquiv.Value)), (∀ b w, acc = some (b, w) → VRel τ b w) →
      (ws.filter fun v => !v.isNull).foldl (extremeStep wantMax) (acc.map Prod.snd) =
        (fbest wantMax (acc.map fun p => (f p.1, p.2))
          ((ks.zip ws).map fun p => (p.1.map f, p.2))).map Prod.snd
  | _, _, .nil, acc, _ => by cases acc <;> rfl
  | none :: _, _ :: _, .cons ⟨⟨t, rfl⟩, _⟩ hs, acc, hacc => by
    simpa [SqlEquiv.Value.isNull, fbest] using extreme_fbest hτ f hf wantMax hs acc hacc
  | some a :: _, w :: _, .cons ⟨ha, hty⟩ hs, none, _ => by
    have := extreme_fbest hτ f hf wantMax hs (some (a, w)) (fun b w' h => by
      cases h; exact ⟨ha, hty⟩)
    simpa [List.filter_cons, null_of_rel ha, extremeStep, fbest] using this
  | some a :: _, w :: _, .cons ⟨ha, hty⟩ hs, some (b, w₀), hacc => by
    have hb := hacc b w₀ rfl
    have hnb : ∀ x y, ¬ (b = .bool x ∧ a = .bool y) := by
      rintro x y ⟨rfl, -⟩; exact hτ (hb.2.symm.trans rfl)
    have hc := compare_of_cmp hb.1 ha hnb (hf b a hb.2 hty)
    have hcond : (SqlEquiv.Value.compare w₀ w == some (if wantMax then .lt else .gt)) =
        betterB wantMax (f a) (f b) := by
      rw [hc]
      cases wantMax <;>
        simp only [betterB, Bool.false_eq_true, ↓reduceIte, Option.some_beq_some] <;>
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
      · exact compare_gt_iff_gt
      · exact compare_lt_iff_lt
    let acc' : Option (Value × SqlEquiv.Value) :=
      if betterB wantMax (f a) (f b) then some (a, w) else some (b, w₀)
    have := extreme_fbest hτ f hf wantMax hs acc' (fun b' w' h => by
      simp only [acc'] at h; split at h <;> cases h
      · exact ⟨ha, hty⟩
      · exact hb)
    rw [List.filter_cons, null_of_rel ha]
    simp only [Bool.not_false, ↓reduceIte, List.foldl_cons, Option.map_some, extremeStep, hcond,
      List.zip_cons_cons, List.map_cons, Option.map_some, fbest]
    convert this using 2 <;> simp only [acc'] <;> split <;> rfl

end Instances
section Assembly
open SqlCore SqlBridge.Correct SqlBridge.CorrectAgg
variable {β : Type _} [LinearOrder β]

theorem valRel_inj {a b : Value} {x : SqlEquiv.Value} (ha : ValRel a x) (hb : ValRel b x) :
    a = b := by
  cases ha <;> cases hb <;> rfl

/-- The entry `fbest` picks is the first whose untyped key is structurally its key: an earlier
    entry's key is `NULL` or strictly worse, so it is a different value. -/
theorem find_first_best {τ : SqlType} {ρ : Type _} (f : Value → β) (wantMax : Bool)
    {T : List ((Datum × Datum) × (SqlEquiv.Value × ρ))}
    (hT : ∀ t ∈ T, TRel τ t.1.1 t.2.1) {b : β} {t₀ : (Datum × Datum) × (SqlEquiv.Value × ρ)}
    (hb : fbest wantMax none (T.map fun t => (t.1.1.map f, t)) = some (b, t₀)) :
    T.find? (fun t => t.2.1 == t₀.2.1) = some t₀ := by
  have hinv := fbest_inv wantMax (T.map fun t => (t.1.1.map f, t)) [] none (by intro p hp; simp at hp)
  rw [hb, List.nil_append] at hinv
  obtain ⟨l, r, hlr, hl, -⟩ := hinv
  have hT' : T = l.map Prod.snd ++ t₀ :: r.map Prod.snd := by
    have := congrArg (List.map Prod.snd) hlr
    simpa [List.map_map, Function.comp_def] using this
  -- the picked entry's typed key is `b`
  have ht₀ : t₀ ∈ T := by rw [hT']; simp
  obtain ⟨kb, hkb, hfb⟩ : ∃ kb, t₀.1.1 = some kb ∧ f kb = b := by
    have hm : (some b, t₀) ∈ T.map fun t => (t.1.1.map f, t) := by rw [hlr]; simp
    obtain ⟨t, -, ht⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at ht
    obtain ⟨h1, rfl⟩ := ht
    obtain ⟨kb, hkb, rfl⟩ := Option.map_eq_some_iff.mp h1
    exact ⟨kb, hkb, rfl⟩
  have hrel₀ := hT t₀ ht₀
  rw [hkb] at hrel₀
  rw [hT', List.find?_append, List.find?_eq_none.mpr ?hn]
  · simp
  intro t ht heq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
  have hpT : p.2 ∈ T := by
    have : p ∈ T.map fun t => (t.1.1.map f, t) := by rw [hlr]; simp [hp]
    obtain ⟨t', ht', hpt⟩ := List.mem_map.mp this
    rw [← hpt]; exact ht'
  have hpk : p.1 = p.2.1.1.map f := by
    have : p ∈ T.map fun t => (t.1.1.map f, t) := by rw [hlr]; simp [hp]
    obtain ⟨t', -, hpt⟩ := List.mem_map.mp this
    rw [← hpt]
  have hrelp := hT p.2 hpT
  have hw : p.2.2.1 = t₀.2.1 := by simpa using heq
  rcases hk : p.2.1.1 with _ | c
  · rw [hk] at hrelp
    obtain ⟨tn, htn⟩ := hrelp.1
    rw [hw] at htn
    have := null_of_rel hrel₀.1
    rw [htn] at this; simp [SqlEquiv.Value.isNull] at this
  · rw [hk] at hrelp
    have hc : c = kb := valRel_inj hrelp.1 (hw ▸ hrel₀.1)
    have := hl p hp (f c) (by rw [hpk, hk]; rfl)
    rw [hc, hfb, betterB_irrefl] at this
    cases this

end Assembly
section Rows
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectAgg SqlBridge.CorrectOrder
variable {n : ℕ} (cols : Fin n → Column) (fold : String → String) (db : SqlEquiv.Database)

/-- Related rows, with a key and a value evaluated on each: per row, the typed key and value, the
    untyped key and the untyped row. -/
theorem rows_triples {Γ : Fin n → SqlType} {τ : SqlType} {arg : SqlEquiv.Expr} {k' : Expr n}
    (harg : Translates cols fold arg k') (hnbk : NoBoolOrder Γ k') (hkty : k'.typeOf Γ = some τ)
    {c : SqlEquiv.ColumnRef} {e' : Expr n} (hcol : Translates cols fold (.col c) e')
    (hnbe : NoBoolOrder Γ e') :
    ∀ {rs : List (Row n)} {us : List SqlEquiv.Row} {ks vs : List Datum},
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) rs us →
      rs.mapM k'.eval = .ok ks → rs.mapM e'.eval = .ok vs →
      ∃ T : List ((Datum × Datum) × (SqlEquiv.Value × SqlEquiv.Row)),
        T.map Prod.fst = ks.zip vs ∧ T.map (fun t => t.2.2) = us ∧ ks.length = vs.length ∧
        ∀ t ∈ T, TRel τ t.1.1 t.2.1 ∧ SqlEquiv.evalExprWithDb db t.2.2 arg = some t.2.1 ∧
          ∃ v, SqlEquiv.evalExprWithDb db t.2.2 (.col c) = some v ∧ DatumRel t.1.2 v
  | [], [], ks, vs, .nil, hks, hvs => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hks hvs
    subst hks hvs
    exact ⟨[], rfl, rfl, rfl, by simp⟩
  | r :: rs, u :: us, ks, vs, .cons hru hrows, hks, hvs => by
    rw [List.mapM_cons] at hks hvs
    rcases hk : k'.eval r with _ | k
    · simp [hk, bind, Except.bind] at hks
    rcases hks' : rs.mapM k'.eval with _ | ks'
    · simp [hk, hks', bind, Except.bind] at hks
    simp only [hk, hks', bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hks
    rcases hv : e'.eval r with _ | v
    · simp [hv, bind, Except.bind] at hvs
    rcases hvs' : rs.mapM e'.eval with _ | vs'
    · simp [hv, hvs', bind, Except.bind] at hvs
    simp only [hv, hvs', bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hvs
    subst hks hvs
    obtain ⟨T, h1, h2, h3, h4⟩ := rows_triples harg hnbk hkty hcol hnbe hrows hks' hvs'
    obtain ⟨w, hw, hwr⟩ := Translates.eval_rel cols fold db hru.1 hru.2 harg hnbk hk
    obtain ⟨x, hx, hxr⟩ := Translates.eval_rel cols fold db hru.1 hru.2 hcol hnbe hv
    refine ⟨((k, v), (w, u)) :: T, by simp [h1], by simp [h2], by simp [h3], fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨⟨hwr, Expr.hasType_of_eval_eq_ok hru.2 hkty hk⟩, hw, x, hx, hxr⟩
    · exact h4 t ht

theorem forall₂_map_of {α β γ : Type _} {R : β → γ → Prop} {g : α → β} {g' : α → γ} :
    ∀ {T : List α}, (∀ t ∈ T, R (g t) (g' t)) → List.Forall₂ R (T.map g) (T.map g')
  | [], _ => .nil
  | _ :: _, h => .cons (h _ List.mem_cons_self) (forall₂_map_of fun t ht => h t (List.mem_cons_of_mem _ ht))

variable {β : Type _} [LinearOrder β]

/-- **A bare column next to one `MIN`/`MAX`** (registry T9): on related groups, the typed
    `AggCall.atExtreme` reads the column on the same row as `SqlEquiv`'s `bareSampleRow`, the first
    row whose argument is extreme, or the last row when every argument is `NULL`. -/
theorem atExtreme_rel_of {Γ : Fin n → SqlType} {τ : SqlType} (hτ : τ ≠ .bool) (f : Value → β)
    (hf : ∀ a b : Value, a.type = τ → b.type = τ → Value.cmp a b = .ok (compare (f a) (f b)))
    {wantMax : Bool} {mode : SqlEquiv.MinMaxMode} (hm : mode.bareRow = true)
    {arg : SqlEquiv.Expr} {k' : Expr n} (harg : Translates cols fold arg k')
    (hnbk : NoBoolOrder Γ k') (hkty : k'.typeOf Γ = some τ)
    {c : SqlEquiv.ColumnRef} {e' : Expr n} (hcol : Translates cols fold (.col c) e')
    (hnbe : NoBoolOrder Γ e') {rs : List (Row n)} {us : List SqlEquiv.Row}
    (hrows : List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) rs us)
    (hne : us ≠ []) {d : Datum}
    (hd : (AggCall.atExtreme (if wantMax then .gt else .lt) k' e').eval rs = .ok d) :
    ∃ s, SqlEquiv.bareSampleRow (fun r e => SqlEquiv.evalExprWithDb db r e)
        [(wantMax, mode, some arg, false)] us = some s ∧
      ∃ v, SqlEquiv.evalExprWithDb db s (.col c) = some v ∧ DatumRel d v := by
  simp only [AggCall.eval, bind, Except.bind] at hd
  rcases hks : rs.mapM k'.eval with _ | ks
  · simp [hks] at hd
  rcases hvs : rs.mapM e'.eval with _ | vs
  · simp [hks, hvs] at hd
  simp only [hks, hvs] at hd
  rcases hbest : bestAt (if wantMax then .gt else .lt) none (ks.zip vs) with _ | best
  · simp [hbest] at hd
  simp only [hbest, pure, Except.pure, Except.ok.injEq] at hd
  obtain ⟨T, hT1, hT2, hlen, hT⟩ := rows_triples cols fold db harg hnbk hkty hcol hnbe hrows hks hvs
  have hvsT : T.map (fun t => t.1.2) = vs := by
    have := congrArg (List.map Prod.snd) hT1
    rw [List.map_map, List.map_snd_zip (by omega)] at this
    exact this
  -- the typed pick
  have htyped : ∀ p ∈ ks.zip vs, p.1.HasType τ := by
    intro p hp
    rw [← hT1] at hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    exact (hT t ht).1.2
  obtain ⟨r, hr, hrm⟩ := bestAt_fbest f hf wantMax (ks.zip vs) none htyped (by simp)
  rw [hbest, Except.ok.injEq] at hr
  subst hr
  let Z := T.map fun t => (t.1.1.map f, t)
  have hZt : (ks.zip vs).map (fun p => (p.1.map f, p.2)) = Z.map (fun p => (p.1, p.2.1.2)) := by
    rw [← hT1]; simp [Z, List.map_map, Function.comp_def]
  have hfm1 := fbest_map wantMax (fun t : (Datum × Datum) × (SqlEquiv.Value × SqlEquiv.Row) => t.1.2) Z none
  simp only [Option.map_none] at hfm1
  rw [hZt, show (Option.map (fun p : Value × Datum => (f p.1, p.2)) none) = none from rfl, hfm1,
    Option.map_map] at hrm
  -- the untyped pick
  have hws : us.filterMap (fun u => SqlEquiv.evalExprWithDb db u arg) = T.map (fun t => t.2.1) := by
    rw [← hT2, List.filterMap_map]
    exact List.filterMap_eq_map_iff_forall_eq_some.mpr fun t ht => (hT t ht).2.1
  have hrelK : List.Forall₂ (TRel τ) (T.map fun t => t.1.1) (T.map fun t => t.2.1) :=
    forall₂_map_of fun t ht => (hT t ht).1
  have hmm := minMaxAgg_eq hτ mode wantMax hrelK
  have hext := extreme_fbest hτ f hf wantMax hrelK none (by simp)
  have hZu : ((T.map fun t => t.1.1).zip (T.map fun t => t.2.1)).map (fun p => (p.1.map f, p.2)) =
      Z.map (fun p => (p.1, p.2.2.1)) := by
    simp [Z, List.zip_map', List.map_map, Function.comp_def]
  have hfm2 := fbest_map wantMax (fun t : (Datum × Datum) × (SqlEquiv.Value × SqlEquiv.Row) => t.2.1) Z none
  simp only [Option.map_none] at hfm2
  rw [show (Option.map (fun p : Value × SqlEquiv.Value => (f p.1, p.2)) none) = none from rfl, hZu,
    hfm2, Option.map_map] at hext
  unfold SqlEquiv.bareSampleRow
  simp only [hm, ↓reduceIte, hws, hmm]
  rw [extremeValue_eq, show (none : Option SqlEquiv.Value) = (none : Option (Value × SqlEquiv.Value)).map Prod.snd from rfl, hext]
  rcases hZ : fbest wantMax none Z with _ | ⟨b, t₀⟩
  · -- every key `NULL`: the last row
    have hinv := fbest_inv wantMax Z [] none (by intro p hp; simp at hp)
    rw [hZ, List.nil_append] at hinv
    rw [hZ] at hrm
    have hbn : best = none := by
      rcases best with _ | ⟨b, y⟩
      · rfl
      · simp at hrm
    subst hbn
    simp only [Option.map_none, Option.getD_none]
    obtain ⟨tl, htl⟩ : ∃ tl, T.getLast? = some tl := by
      rcases hT0 : T with _ | ⟨t, T'⟩
      · rw [hT0] at hT2; simp at hT2; exact absurd hT2.symm (Ne.symm hne)
      · exact ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
    refine ⟨tl.2.2, ?_, ?_⟩
    · rw [← hT2, List.getLast?_map, htl]; rfl
    · obtain ⟨v, hv, hvr⟩ := (hT tl (List.mem_of_getLast? htl)).2.2
      refine ⟨v, hv, ?_⟩
      rw [← hd, ← hvsT, List.getLast?_map, htl]
      exact hvr
  · -- the first row whose key is extreme
    rw [hZ] at hrm
    obtain ⟨by', hby⟩ : ∃ by', best = some by' := by
      rcases best with _ | b'
      · simp at hrm
      · exact ⟨_, rfl⟩
    subst hby
    obtain ⟨kb', y⟩ := by'
    simp only [Option.map_some, Option.some.injEq, Function.comp_apply] at hrm
    have ht₀ : t₀ ∈ T := by
      have hinv := fbest_inv wantMax Z [] none (by intro p hp; simp at hp)
      rw [hZ, List.nil_append] at hinv
      obtain ⟨l, r, hlr, -, -⟩ := hinv
      have : (some b, t₀) ∈ Z := by rw [hlr]; simp
      obtain ⟨t, ht, he⟩ := List.mem_map.mp this
      simp only [Prod.mk.injEq] at he
      rw [← he.2]; exact ht
    obtain ⟨hrel₀, -, v, hv, hvr⟩ := hT t₀ ht₀
    have hkb : ∃ kb, t₀.1.1 = some kb := by
      have hinv := fbest_inv wantMax Z [] none (by intro p hp; simp at hp)
      rw [hZ, List.nil_append] at hinv
      obtain ⟨l, r, hlr, -, -⟩ := hinv
      have : (some b, t₀) ∈ Z := by rw [hlr]; simp
      obtain ⟨t, -, he⟩ := List.mem_map.mp this
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, rfl⟩ := he
      obtain ⟨kb, hkb, -⟩ := Option.map_eq_some_iff.mp h1
      exact ⟨kb, hkb⟩
    obtain ⟨kb, hkb⟩ := hkb
    rw [hkb] at hrel₀
    have hnn := null_of_rel hrel₀.1
    simp only [Option.map_some, Option.getD_some, Function.comp_apply]
    split
    · rename_i tn h
      simp only [Option.some.injEq] at h
      rw [h] at hnn; simp [SqlEquiv.Value.isNull] at hnn
    · rename_i h; cases h
    · rename_i m h
      simp only [Option.some.injEq] at h
      subst h
      have hfind := find_first_best f wantMax (fun t ht => (hT t ht).1) hZ
      refine ⟨t₀.2.2, ?_, v, hv, ?_⟩
      · rw [← hT2, List.find?_map]
        rw [find?_congr' (q := fun t => t.2.1 == t₀.2.1) (fun t ht => by
          simp only [Function.comp_apply, (hT t ht).2.1, Option.some_beq_some]), hfind]
        rfl
      · rw [← hd]; simp only; rw [hrm]; exact hvr

end Rows
section Dispatch
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectAgg
variable {n : ℕ} (cols : Fin n → Column) (fold : String → String) (db : SqlEquiv.Database)

/-- `atExtreme_rel_of` for a key of any non-boolean type: integers, rationals or strings. -/
theorem atExtreme_rel {Γ : Fin n → SqlType} {τ : SqlType} (hτ : τ ≠ .bool)
    {wantMax : Bool} {mode : SqlEquiv.MinMaxMode} (hm : mode.bareRow = true)
    {arg : SqlEquiv.Expr} {k' : Expr n} (harg : Translates cols fold arg k')
    (hnbk : NoBoolOrder Γ k') (hkty : k'.typeOf Γ = some τ)
    {c : SqlEquiv.ColumnRef} {e' : Expr n} (hcol : Translates cols fold (.col c) e')
    (hnbe : NoBoolOrder Γ e') {rs : List (Row n)} {us : List SqlEquiv.Row}
    (hrows : List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) rs us)
    (hne : us ≠ []) {d : Datum}
    (hd : (AggCall.atExtreme (if wantMax then .gt else .lt) k' e').eval rs = .ok d) :
    ∃ s, SqlEquiv.bareSampleRow (fun r e => SqlEquiv.evalExprWithDb db r e)
        [(wantMax, mode, some arg, false)] us = some s ∧
      ∃ v, SqlEquiv.evalExprWithDb db s (.col c) = some v ∧ DatumRel d v := by
  cases τ with
  | int =>
    exact atExtreme_rel_of cols fold db hτ (fun | .int z => z | _ => (0 : ℤ)) (fun a b ha hb => by
      cases a <;> cases b <;> simp_all [Value.type, Value.cmp, compareInt]) hm harg hnbk hkty hcol
      hnbe hrows hne hd
  | text =>
    exact atExtreme_rel_of cols fold db hτ (fun | .text s => s | _ => "") (fun a b ha hb => by
      cases a <;> cases b <;> simp_all [Value.type, Value.cmp, compareText]) hm harg hnbk hkty hcol
      hnbe hrows hne hd
  | decimal =>
    exact atExtreme_rel_of cols fold db hτ (fun | .decimal q => q | _ => (0 : ℚ)) (fun a b ha hb => by
      cases a <;> cases b <;> simp_all [Value.type, Value.cmp, compareDec]) hm harg hnbk hkty hcol
      hnbe hrows hne hd
  | bool => exact absurd rfl hτ

end Dispatch

end SqlBridge.CorrectExtreme
