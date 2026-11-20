import SqlBridge.CorrectJoin

namespace SqlBridge.CorrectAgg
open SqlCore SqlBridge.Correct

/-! ### Decimal normal form -/

/-- `mkDecimal` keeps the value and strips trailing zeros. -/
theorem mkDecimal_spec : ∀ (s : ℕ) (u : ℤ), ∃ u' s', SqlEquiv.Value.mkDecimal u s = .decimal u' s' ∧
    ((u' : ℚ) / (10 ^ s' : ℕ) = (u : ℚ) / (10 ^ s : ℕ)) ∧ (s' = 0 ∨ u' % 10 ≠ 0)
  | 0, u => ⟨u, 0, rfl, rfl, .inl rfl⟩
  | s + 1, u => by
    unfold SqlEquiv.Value.mkDecimal
    by_cases h : u % 10 = 0
    · simp only [h, beq_self_eq_true, ↓reduceIte]
      obtain ⟨u', s', he, hq, hn⟩ := mkDecimal_spec s (u / 10)
      refine ⟨u', s', he, ?_, hn⟩
      rw [hq]
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
      subst hk
      rw [Int.mul_ediv_cancel_left _ (by norm_num)]
      push_cast
      field_simp
      rw [pow_succ, mul_assoc]
    · have h' : (u % 10 == 0) = false := by simpa using h
      simp only [h', Bool.false_eq_true, ↓reduceIte]
      exact ⟨u, s + 1, rfl, rfl, .inr h⟩

/-- Two normal forms with the same value are equal. -/
theorem normal_unique {u₁ u₂ : ℤ} {s₁ s₂ : ℕ}
    (h : (u₁ : ℚ) / (10 ^ s₁ : ℕ) = (u₂ : ℚ) / (10 ^ s₂ : ℕ))
    (h₁ : s₁ = 0 ∨ u₁ % 10 ≠ 0) (h₂ : s₂ = 0 ∨ u₂ % 10 ≠ 0) : u₁ = u₂ ∧ s₁ = s₂ := by
  -- with `s₁ ≤ s₂`, `u₂ = u₁ * 10 ^ (s₂ - s₁)`
  have key : ∀ {u₁ u₂ : ℤ} {s₁ s₂ : ℕ}, s₁ ≤ s₂ →
      (u₁ : ℚ) / (10 ^ s₁ : ℕ) = (u₂ : ℚ) / (10 ^ s₂ : ℕ) → (s₂ = 0 ∨ u₂ % 10 ≠ 0) →
      u₁ = u₂ ∧ s₁ = s₂ := by
    intro u₁ u₂ s₁ s₂ hle h h₂
    have hu : u₂ = u₁ * 10 ^ (s₂ - s₁) := by
      have hp : (10 : ℚ) ^ s₂ = 10 ^ s₁ * 10 ^ (s₂ - s₁) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      push_cast at h
      field_simp at h
      rw [hp] at h
      have : (u₂ : ℚ) = u₁ * 10 ^ (s₂ - s₁) := by
        have h10 : (10 : ℚ) ^ s₁ ≠ 0 := by positivity
        apply mul_left_cancel₀ h10
        rw [← h]; ac_rfl
      exact_mod_cast this
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · subst heq; simp at hu; exact ⟨hu.symm, rfl⟩
    · exfalso
      rcases h₂ with h0 | hn
      · omega
      · apply hn
        rw [hu]
        obtain ⟨k, hk⟩ : ∃ k, s₂ - s₁ = k + 1 := ⟨s₂ - s₁ - 1, by omega⟩
        rw [hk, pow_succ]
        simp [← mul_assoc, Int.mul_emod_left]
  rcases le_total s₁ s₂ with hle | hle
  · exact key hle h h₂
  · obtain ⟨a, b⟩ := key hle h.symm h₁
    exact ⟨a.symm, b.symm⟩
open SqlCore SqlBridge.Correct

/-- Related values of one type are equal exactly when their untyped set keys are (`DISTINCT`). -/
theorem eq_iff_setKey {a b : Value} {x y : SqlEquiv.Value} (ha : ValRel a x) (hb : ValRel b y)
    (hty : a.type = b.type) : a = b ↔ x.setKey = y.setKey := by
  cases ha <;> cases hb <;> simp_all [Value.type, SqlEquiv.Value.setKey]
  rename_i u₁ s₁ u₂ s₂
  obtain ⟨a₁, t₁, he₁, hq₁, hn₁⟩ := mkDecimal_spec s₁ u₁
  obtain ⟨a₂, t₂, he₂, hq₂, hn₂⟩ := mkDecimal_spec s₂ u₂
  push_cast at hq₁ hq₂
  rw [he₁, he₂]
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := normal_unique (by push_cast; rw [hq₁, hq₂, h]) hn₁ hn₂
    rfl
  · intro h
    simp only [SqlEquiv.Value.decimal.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [← hq₁, ← hq₂]

/-- `DatumRel` with every value of type `τ`. -/
def TRel (τ : SqlType) (d : Datum) (v : SqlEquiv.Value) : Prop := DatumRel d v ∧ d.HasType τ

theorem null_of_rel {a : Value} {v : SqlEquiv.Value} (h : ValRel a v) : v.isNull = false := by
  cases h <;> rfl

theorem count_agree : ∀ {ds : List Datum} {vs : List SqlEquiv.Value}, List.Forall₂ DatumRel ds vs →
    (ds.filterMap id).length = (vs.filter fun v => !v.isNull).length
  | _, _, .nil => rfl
  | none :: _, _ :: _, .cons ⟨t, rfl⟩ hs => by
    simpa [SqlEquiv.Value.isNull] using count_agree hs
  | some a :: _, _ :: _, .cons h hs => by
    have ih := count_agree hs
    simp only [List.filterMap_cons, id, List.length_cons, List.filter_cons, null_of_rel h,
      Bool.not_false, ↓reduceIte] at ih ⊢
    omega

section Dedup
variable {α β γ : Type}

/-- Keep the first of each class of equal elements, in order (the typed counterpart of
    `dedupByKey`), with fuel `n ≥ l.length`. -/
def dedupFirst [DecidableEq α] : ℕ → List α → List α
  | _, [] => []
  | 0, l => l
  | n + 1, a :: l => a :: dedupFirst n (l.filter (· ≠ a))

theorem dedupFirst_spec [DecidableEq α] : ∀ (n : ℕ) (l : List α), l.length ≤ n →
    (dedupFirst n l).Nodup ∧ ∀ a, a ∈ dedupFirst n l ↔ a ∈ l
  | _, [], _ => by simp [dedupFirst]
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: l, h => by
    have hl : (l.filter (· ≠ a)).length ≤ n :=
      le_trans (List.length_filter_le _ _) (by simpa using h)
    obtain ⟨hnd, hmem⟩ := dedupFirst_spec n _ hl
    simp only [dedupFirst]
    refine ⟨List.nodup_cons.mpr ⟨fun ha => by simpa using (hmem a).mp ha, hnd⟩, fun b => ?_⟩
    rw [List.mem_cons, hmem, List.mem_filter]
    by_cases hb : b = a <;> simp [hb]

theorem forall₂_filter {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (h : ∀ a x, R a x → p a = q x) : ∀ {l l'}, List.Forall₂ R l l' →
      List.Forall₂ R (l.filter p) (l'.filter q)
  | _, _, .nil => .nil
  | a :: _, x :: _, .cons hax hs => by
    simp only [List.filter_cons, h a x hax]
    split
    · exact .cons hax (forall₂_filter h hs)
    · exact forall₂_filter h hs

/-- Related lists stay related under first-occurrence deduplication, when the relation matches
    equality on one side with equal keys on the other. -/
theorem dedup_rel [DecidableEq α] {R : α → β → Prop} {f : β → γ} [BEq γ] [LawfulBEq γ]
    (hR : ∀ a b x y, R a x → R b y → (a = b ↔ f x = f y)) : ∀ (n : ℕ) {l : List α} {l' : List β},
      l.length ≤ n → List.Forall₂ R l l' →
        List.Forall₂ R (dedupFirst n l) (SqlEquiv.dedupByKey f l')
  | _, _, _, _, .nil => by simp [dedupFirst]
  | 0, _ :: _, _, h, .cons _ _ => by simp at h
  | n + 1, a :: l, x :: l', h, .cons hax hs => by
    rw [SqlEquiv.dedupByKey_cons]
    simp only [dedupFirst]
    refine .cons hax (dedup_rel hR n (le_trans (List.length_filter_le _ _) (by simpa using h))
      (forall₂_filter (fun b y hby => ?_) hs))
    have := hR b a y x hby hax
    by_cases hb : b = a
    · simp [hb, this.mp hb]
    · have : ¬ f y = f x := fun e => hb (this.mpr e)
      simp [hb, this]

end Dedup

theorem setKey_ne_null {a : Value} {v : SqlEquiv.Value} (h : ValRel a v) :
    v.setKey ≠ .null none := by
  cases h <;> simp [SqlEquiv.Value.setKey]
  rename_i u s
  obtain ⟨u', s', he, -⟩ := mkDecimal_spec s u
  simp [he]

theorem trel_iff {τ : SqlType} : ∀ (a b : Datum) (x y : SqlEquiv.Value), TRel τ a x → TRel τ b y →
    (a = b ↔ x.setKey = y.setKey)
  | none, none, _, _, ⟨⟨t, rfl⟩, _⟩, ⟨⟨t', rfl⟩, _⟩ => by simp [SqlEquiv.Value.setKey]
  | none, some _, _, _, ⟨⟨t, rfl⟩, _⟩, ⟨hb, _⟩ => by
    simpa [SqlEquiv.Value.setKey] using (setKey_ne_null hb).symm
  | some _, none, _, _, ⟨ha, _⟩, ⟨⟨t, rfl⟩, _⟩ => by
    simpa [SqlEquiv.Value.setKey] using setKey_ne_null ha
  | some a, some b, _, _, ⟨ha, hta⟩, ⟨hb, htb⟩ => by
    simp only [Option.some.injEq]
    exact eq_iff_setKey ha hb (by simp_all [Datum.HasType])

/-- `COUNT(DISTINCT e)` agrees: distinct non-`NULL` typed values against `SqlEquiv`'s values
    deduplicated by set key, `NULL`s then dropped. -/
theorem count_distinct_agree {τ : SqlType} {ds : List Datum} {vs : List SqlEquiv.Value}
    (h : List.Forall₂ (TRel τ) ds vs) :
    ((ds.filterMap id).dedup).length =
      ((SqlEquiv.dedupByKey SqlEquiv.Value.setKey vs).filter fun v => !v.isNull).length := by
  have hrel := dedup_rel (trel_iff (τ := τ)) ds.length le_rfl h
  rw [← count_agree (hrel.imp fun _ _ h => h.1)]
  obtain ⟨hnd, hmem⟩ := dedupFirst_spec ds.length ds le_rfl
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup (List.nodup_dedup _) _).mpr
  · intro x
    simp [List.mem_dedup, List.mem_filterMap, hmem]
  · exact hnd.filterMap fun a a' b h1 h2 => by simp_all

end SqlBridge.CorrectAgg

namespace SqlBridge.CorrectAgg
open SqlCore SqlBridge.Correct

/-! ### `SUM` -/

/-- The rational value of a scaled integer `(u, s)`, `u / 10^s`. -/
def scaledQ (p : ℤ × ℕ) : ℚ := (p.1 : ℚ) / (10 ^ p.2 : ℕ)

/-- The rational value of a typed number. -/
def toQ : Value → ℚ
  | .int z => z
  | .decimal q => q
  | _ => 0

/-- `sumScaled`'s step aligns scales and adds. -/
def sumStep (a b : ℤ × ℕ) : ℤ × ℕ :=
  (a.1 * 10 ^ (max a.2 b.2 - a.2) + b.1 * 10 ^ (max a.2 b.2 - b.2), max a.2 b.2)

theorem scaledQ_step (a b : ℤ × ℕ) : scaledQ (sumStep a b) = scaledQ a + scaledQ b := by
  obtain ⟨u, s⟩ := a
  obtain ⟨v, t⟩ := b
  simp only [scaledQ, sumStep]
  have h1 : (10 : ℚ) ^ (max s t) = 10 ^ (max s t - s) * 10 ^ s := by
    rw [← pow_add, Nat.sub_add_cancel (le_max_left _ _)]
  have h2 : (10 : ℚ) ^ (max s t) = 10 ^ (max s t - t) * 10 ^ t := by
    rw [← pow_add, Nat.sub_add_cancel (le_max_right _ _)]
  push_cast
  rw [add_div]
  congr 1
  · rw [h1, mul_comm (10 ^ (max s t - s) : ℚ), mul_div_mul_right _ _ (by positivity)]
  · rw [h2, mul_comm (10 ^ (max s t - t) : ℚ), mul_div_mul_right _ _ (by positivity)]

theorem foldl_sumStep : ∀ (l : List (ℤ × ℕ)) (acc : ℤ × ℕ),
    scaledQ (l.foldl sumStep acc) = scaledQ acc + (l.map scaledQ).sum
  | [], acc => by simp
  | p :: l, acc => by
    rw [List.foldl_cons, foldl_sumStep l, scaledQ_step]
    simp [add_assoc]

theorem foldl_sumStep_int : ∀ (l : List (ℤ × ℕ)) (z : ℤ), (∀ p ∈ l, p.2 = 0) →
    l.foldl sumStep (z, 0) = (z + (l.map Prod.fst).sum, 0)
  | [], z, _ => by simp
  | (u, s) :: l, z, h => by
    have hs : s = 0 := h (u, s) (by simp)
    subst hs
    rw [List.foldl_cons]
    have : sumStep (z, 0) (u, 0) = (z + u, 0) := by simp [sumStep]
    rw [this, foldl_sumStep_int l (z + u) (fun p hp => h p (by simp [hp]))]
    simp [add_assoc]

theorem sumScaled_eq (vs : List SqlEquiv.Value) :
    SqlEquiv.sumScaled vs = (vs.filterMap SqlEquiv.Value.toScaled?).foldl sumStep (0, 0) := rfl
theorem sumFrom_q {τ : SqlType} (hτ : τ = .int ∨ τ = .decimal) : ∀ (acc : Value) (l : List Value),
    acc.type = τ → (∀ v ∈ l, v.type = τ) →
      ∃ w, sumFrom acc l = .ok w ∧ w.type = τ ∧ toQ w = toQ acc + (l.map toQ).sum
  | acc, [], hacc, _ => ⟨acc, rfl, hacc, by simp⟩
  | acc, v :: l, hacc, hl => by
    have hv := hl v (by simp)
    obtain ⟨s, hs, hsτ, hsq⟩ : ∃ s, acc.add v = .ok s ∧ s.type = τ ∧ toQ s = toQ acc + toQ v := by
      rcases hτ with rfl | rfl <;> cases acc <;> cases v <;>
        simp_all [Value.add, Value.type, toQ]
    obtain ⟨w, hw, hwτ, hwq⟩ := sumFrom_q hτ s l hsτ fun u hu => hl u (by simp [hu])
    refine ⟨w, by simp [sumFrom, hs, hw], hwτ, ?_⟩
    rw [hwq, hsq]; simp [add_assoc]

/-- The non-`NULL` typed values against `SqlEquiv`'s numeric views of the values. -/
theorem scaled_rel {τ : SqlType} (hτ : τ = .int ∨ τ = .decimal) : ∀ {ds : List Datum}
    {vs : List SqlEquiv.Value}, List.Forall₂ (TRel τ) ds vs →
      List.Forall₂ (fun a p => scaledQ p = toQ a ∧ (τ = .int → p.2 = 0) ∧ a.type = τ)
        (ds.filterMap id) (vs.filterMap SqlEquiv.Value.toScaled?)
  | _, _, .nil => .nil
  | none :: _, _ :: _, .cons ⟨⟨t, rfl⟩, _⟩ hs => by
    have ih := scaled_rel hτ hs
    rw [List.filterMap_cons_none rfl, List.filterMap_cons_none rfl]
    exact ih
  | some a :: _, _ :: _, .cons ⟨ha, hty⟩ hs => by
    have ih := scaled_rel hτ hs
    have hty' : a.type = τ := hty
    rw [List.filterMap_cons_some (f := id) (a := some a) (b := a) rfl]
    cases ha with
    | int z =>
      rw [List.filterMap_cons_some (f := SqlEquiv.Value.toScaled?) (b := (z, 0)) rfl]
      exact .cons ⟨by simp [scaledQ, toQ], fun _ => rfl, hty'⟩ ih
    | decimal u s =>
      rw [List.filterMap_cons_some (f := SqlEquiv.Value.toScaled?) (b := (u, s)) rfl]
      refine .cons ⟨by simp [scaledQ, toQ], fun h => ?_, hty'⟩ ih
      rw [h] at hty'; cases hty'
    | text _ => rcases hτ with rfl | rfl <;> cases hty'
    | bool _ => rcases hτ with rfl | rfl <;> cases hty'
theorem forall₂_mem_left {α β : Type _} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ {a}, a ∈ l → ∃ b ∈ l', R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab hs, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_mem_left hs h
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ {b}, b ∈ l' → ∃ a ∈ l, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab hs, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := forall₂_mem_right hs h
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem map_eq_of_forall₂ {α β γ : Type _} {f : β → γ} {g : α → γ} {P : α → β → Prop}
    (hP : ∀ a b, P a b → f b = g a) : ∀ {l : List α} {l' : List β}, List.Forall₂ P l l' →
      l'.map f = l.map g
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp [hP _ _ h, map_eq_of_forall₂ hP hs]

/-- The untyped values of a numeric column: `NULL`, or a number of the column's type. -/
theorem numeric_vals {τ : SqlType} (hτ : τ = .int ∨ τ = .decimal) : ∀ {ds : List Datum}
    {vs : List SqlEquiv.Value}, List.Forall₂ (TRel τ) ds vs → ∀ v ∈ vs,
      (∃ t, v = .null t) ∨ (∃ z, v = .int z ∧ τ = .int) ∨ (∃ u s, v = .decimal u s ∧ τ = .decimal)
  | _, _, .nil => by simp
  | d :: _, x :: _, .cons ⟨hx, hty⟩ hs => by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · cases d with
      | none => exact .inl hx
      | some a =>
        have hty' : a.type = τ := hty
        cases hx <;> rcases hτ with rfl | rfl <;> simp_all [Value.type]
    · exact numeric_vals hτ hs v hv

/-- `SUM` agrees, for an integer or decimal column, in every dialect's boolean mode (there are no
    booleans). -/
theorem sum_agree {τ : SqlType} (hτ : τ = .int ∨ τ = .decimal) (b : SqlEquiv.BoolSumAvg)
    {ds : List Datum} {vs : List SqlEquiv.Value} (h : List.Forall₂ (TRel τ) ds vs) {d : Datum}
    (hd : AggFn.sum.apply (ds.filterMap id) = .ok d) :
    ∃ v, SqlEquiv.sumAgg b vs = some v ∧ DatumRel d v := by
  have hnum := numeric_vals hτ h
  have hsc := scaled_rel hτ h
  have hbools : SqlEquiv.boolsForSumAvg b vs = some vs := by
    cases b with
    | asInt =>
      simp only [SqlEquiv.boolsForSumAvg, Option.some.injEq]
      conv => rhs; rw [← List.map_id vs]
      apply List.map_congr_left
      intro v hv
      rcases hnum v hv with ⟨t, rfl⟩ | ⟨z, rfl, -⟩ | ⟨u, s, rfl, -⟩ <;> rfl
    | error =>
      simp only [SqlEquiv.boolsForSumAvg, ite_eq_right_iff, reduceCtorEq, imp_false,
        Bool.not_eq_true, List.any_eq_false]
      intro v hv
      rcases hnum v hv with ⟨t, rfl⟩ | ⟨z, rfl, -⟩ | ⟨u, s, rfl, -⟩ <;> rfl
  have hnn : SqlEquiv.hasNonNumeric vs = false := by
    simp only [SqlEquiv.hasNonNumeric, List.any_eq_false]
    intro v hv
    rcases hnum v hv with ⟨t, rfl⟩ | ⟨z, rfl, -⟩ | ⟨u, s, rfl, -⟩ <;> simp
  have hcount : SqlEquiv.countNumeric vs = (ds.filterMap id).length := hsc.length_eq.symm
  simp only [SqlEquiv.sumAgg, hbools, Option.bind_some, hnn, Bool.false_eq_true, ↓reduceIte,
    hcount]
  rcases hX : ds.filterMap id with _ | ⟨a, l⟩
  · rw [hX] at hd
    simp only [AggFn.apply, Except.ok.injEq] at hd
    subst hd
    exact ⟨_, rfl, ⟨none, rfl⟩⟩
  · rw [hX] at hd hsc
    simp only [List.length_cons, Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, Option.some.injEq,
      exists_eq_left']
    have hall : ∀ v ∈ a :: l, v.type = τ := by
      intro v hv
      obtain ⟨p, -, ⟨-, -, h⟩⟩ := forall₂_mem_left hsc hv
      exact h
    obtain ⟨w, hw, hwτ, hwq⟩ := sumFrom_q hτ a l (hall a (by simp)) fun v hv => hall v (by simp [hv])
    simp only [AggFn.apply, hw, Functor.map, Except.map, Except.ok.injEq] at hd
    subst hd
    -- the rational value of the untyped sum
    have hq : scaledQ (SqlEquiv.sumScaled vs) = toQ w := by
      rw [sumScaled_eq, foldl_sumStep, hwq]
      simp only [scaledQ, Int.cast_zero, zero_div, zero_add]
      rw [map_eq_of_forall₂ (fun _ _ h => h.1) hsc]
      simp
    rcases hτ with rfl | rfl
    · -- integers: the untyped sum stays an integer, at scale 0
      obtain ⟨z, rfl⟩ : ∃ z, w = .int z := by cases w <;> simp_all [Value.type]
      have hnd : SqlEquiv.anyDecimal vs = false := by
        simp only [SqlEquiv.anyDecimal, List.any_eq_false]
        intro v hv
        rcases hnum v hv with ⟨t, rfl⟩ | ⟨z, rfl, -⟩ | ⟨u, s, rfl, h⟩ <;> simp_all
      have hz : SqlEquiv.sumScaled vs =
          (((vs.filterMap SqlEquiv.Value.toScaled?).map Prod.fst).sum, 0) := by
        rw [sumScaled_eq, foldl_sumStep_int _ 0 fun p hp => by
          obtain ⟨a, -, ⟨-, h, -⟩⟩ := forall₂_mem_right hsc hp
          exact h rfl]
        simp
      simp only [SqlEquiv.sumNumeric, hnd, Bool.false_eq_true, ↓reduceIte]
      rw [hz] at hq ⊢
      simp only [scaledQ, pow_zero, Nat.cast_one, div_one, toQ] at hq
      have : ((vs.filterMap SqlEquiv.Value.toScaled?).map Prod.fst).sum = z := by exact_mod_cast hq
      rw [this]; exact .int z
    · -- decimals: `mkDecimal` keeps the rational value
      obtain ⟨q, rfl⟩ : ∃ q, w = .decimal q := by cases w <;> simp_all [Value.type]
      have had : SqlEquiv.anyDecimal vs = true := by
        have ha : some a ∈ ds := by
          have : a ∈ ds.filterMap id := by rw [hX]; simp
          simpa using this
        obtain ⟨x, hx, ⟨hrel, hty⟩⟩ := forall₂_mem_left h ha
        have hty' : a.type = .decimal := hty
        simp only [SqlEquiv.anyDecimal, List.any_eq_true]
        refine ⟨x, hx, ?_⟩
        cases hrel <;> simp_all [Value.type]
      simp only [SqlEquiv.sumNumeric, had, ↓reduceIte]
      obtain ⟨u', s', he, hq', -⟩ := mkDecimal_spec (SqlEquiv.sumScaled vs).2 (SqlEquiv.sumScaled vs).1
      rw [he]
      have : q = (u' : ℚ) / (10 ^ s' : ℕ) := by
        rw [hq']; simpa [scaledQ, toQ] using hq.symm
      rw [this]; exact .decimal u' s'

end SqlBridge.CorrectAgg
