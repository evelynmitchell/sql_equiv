/-
  Elaborator correctness for aggregates without `GROUP BY` (#352, roadmap step 3a).

  `SELECT agg₁, …, aggₖ FROM f [WHERE p]`, each `aggᵢ` one of `COUNT(*)`, `COUNT([DISTINCT] e)`,
  `SUM(e)`, `MIN(e)`, `MAX(e)`, `e` in the fragment of #309 and `f` a `FROM` tree of step 2. The
  typed core elaborates it to `Query.aggregate` with no keys (one group, even for no rows),
  projected; `SqlEquiv` evaluates the items once over the filtered rows. `AVG` is left out until
  the rounding decision (registry rows 7 and T10), as are `DISTINCT` in `SUM`/`MIN`/`MAX` and
  bare columns (registry T9).

  * Values: on related lists of one type, `COUNT` (`count_agree`), `COUNT(DISTINCT)`
    (`count_distinct_agree`: the typed `dedup` against `dedupByKey Value.setKey`, through the
    decimal normal form `mkDecimal_spec`/`normal_unique`), `SUM` (`sum_agree`: `sumScaled`
    computes the rational sum, `foldl_sumStep`) and `MIN`/`MAX` (`minmax_agree`, through
    `compare_of_cmp`) agree, in every dialect mode (there are no booleans or mixed types).
  * Rows: an aggregate over related rows (`agg_rel`).
  * The elaborator's query (`elab_agg_shape`) and the statement (`elabStmt_correct_agg`).
-/
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

namespace SqlBridge.CorrectAgg
open SqlCore SqlBridge.Correct

/-! ### `MIN` / `MAX` -/

/-- Non-`NULL` values related, with their type. -/
def VRel (τ : SqlType) (a : Value) (x : SqlEquiv.Value) : Prop := ValRel a x ∧ a.type = τ

theorem nonnull_rel {τ : SqlType} : ∀ {ds : List Datum} {vs : List SqlEquiv.Value},
    List.Forall₂ (TRel τ) ds vs →
      List.Forall₂ (VRel τ) (ds.filterMap id) (vs.filter fun v => !v.isNull)
  | _, _, .nil => .nil
  | none :: _, _ :: _, .cons ⟨⟨t, rfl⟩, _⟩ hs => by
    simpa [SqlEquiv.Value.isNull] using nonnull_rel hs
  | some a :: _, _ :: _, .cons ⟨ha, hty⟩ hs => by
    rw [List.filterMap_cons_some (f := id) (a := some a) (b := a) rfl, List.filter_cons,
      null_of_rel ha]
    exact .cons ⟨ha, hty⟩ (nonnull_rel hs)

/-- The untyped fold of `extremeValue`. -/
def extremeStep (wantMax : Bool) (acc : Option SqlEquiv.Value) (v : SqlEquiv.Value) :
    Option SqlEquiv.Value :=
  match acc with
  | none => some v
  | some m =>
    if SqlEquiv.Value.compare m v == some (if wantMax then .lt else .gt) then some v else acc

theorem extremeValue_eq (wantMax : Bool) (vs : List SqlEquiv.Value) :
    SqlEquiv.extremeValue wantMax vs = vs.foldl (extremeStep wantMax) none := rfl

theorem extreme_rel {τ : SqlType} (hτ : τ ≠ .bool) (wantMax : Bool) :
    ∀ {l : List Value} {l' : List SqlEquiv.Value}, List.Forall₂ (VRel τ) l l' →
      ∀ {acc : Value} {acc' : SqlEquiv.Value}, VRel τ acc acc' → ∀ {w : Value},
        extremeFrom (if wantMax then .gt else .lt) acc l = .ok w →
        ∃ w', l'.foldl (extremeStep wantMax) (some acc') = some w' ∧ ValRel w w'
  | _, _, .nil, acc, acc', hacc, w, h => by
    simp only [extremeFrom, Except.ok.injEq] at h
    subst h; exact ⟨acc', rfl, hacc.1⟩
  | v :: l, v' :: l', .cons hv hs, acc, acc', hacc, w, h => by
    simp only [extremeFrom, bind, Except.bind] at h
    rcases ho : Value.cmp v acc with e | o
    · simp [ho] at h
    simp only [ho] at h
    have hswap : Value.cmp acc v = .ok o.swap := by
      rw [Value.cmp_swap, ho]; rfl
    have hnb : ∀ x y, ¬ (acc = .bool x ∧ v = .bool y) := by
      rintro x y ⟨rfl, rfl⟩; exact hτ (hacc.2.symm.trans rfl)
    have hc := compare_of_cmp hacc.1 hv.1 hnb hswap
    have hcond : (SqlEquiv.Value.compare acc' v' == some (if wantMax then .lt else .gt)) =
        decide (o = if wantMax then .gt else .lt) := by
      rw [hc]
      cases wantMax <;> cases o <;> rfl
    rw [List.foldl_cons]
    simp only [extremeStep, hcond]
    by_cases hp : o = if wantMax then .gt else .lt
    · simp only [hp, ↓reduceIte, decide_true] at h ⊢
      exact extreme_rel hτ wantMax hs hv h
    · simp only [hp, ↓reduceIte, decide_false, Bool.false_eq_true] at h ⊢
      exact extreme_rel hτ wantMax hs hacc h
/-- The untyped values of a column of a non-boolean type: `NULL`, or a value of that type. -/
theorem ordered_vals {τ : SqlType} (hτ : τ ≠ .bool) : ∀ {ds : List Datum}
    {vs : List SqlEquiv.Value}, List.Forall₂ (TRel τ) ds vs → ∀ v ∈ vs,
      (∃ t, v = .null t) ∨ (∃ z, v = .int z ∧ τ = .int) ∨ (∃ u s, v = .decimal u s ∧ τ = .decimal) ∨
        (∃ s, v = .string s ∧ τ = .text)
  | _, _, .nil => by simp
  | d :: _, x :: _, .cons ⟨hx, hty⟩ hs => by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · cases d with
      | none => exact .inl hx
      | some a =>
        have hty' : a.type = τ := hty
        cases hx <;> simp_all [Value.type]
    · exact ordered_vals hτ hs v hv

/-- On a column of a non-boolean type, `minMaxAgg` is `extremeValue` of the non-`NULL` values, in
    every dialect mode (there are no booleans, and numbers and strings do not mix). -/
theorem minMaxAgg_eq {τ : SqlType} (hτ : τ ≠ .bool) (mode : SqlEquiv.MinMaxMode) (wantMax : Bool)
    {ds : List Datum} {vs : List SqlEquiv.Value} (h : List.Forall₂ (TRel τ) ds vs) :
    SqlEquiv.minMaxAgg mode wantMax vs =
      some ((SqlEquiv.extremeValue wantMax (vs.filter fun v => !v.isNull)).getD (.null none)) := by
  have hvals := ordered_vals hτ h
  set V := vs.filter fun v => !v.isNull with hV
  have hVvals : ∀ v ∈ V, (∃ z, v = .int z ∧ τ = .int) ∨ (∃ u s, v = .decimal u s ∧ τ = .decimal) ∨
      (∃ s, v = .string s ∧ τ = .text) := by
    intro v hv
    rw [hV, List.mem_filter] at hv
    rcases hvals v hv.1 with ⟨t, rfl⟩ | h | h | h
    · simp [SqlEquiv.Value.isNull] at hv
    all_goals simp_all
  -- the pool `minMaxAgg` takes the extreme of is `V`; the predicates are `minMaxAgg`'s own
  have knil : ∀ {l : List SqlEquiv.Value} (p : SqlEquiv.Value → Bool), (∀ v ∈ l, p v = false) →
      l.filter p = [] := fun p h => List.filter_eq_nil_iff.mpr fun v hv => by simp [h v hv]
  have kself : ∀ {l : List SqlEquiv.Value} (p : SqlEquiv.Value → Bool), (∀ v ∈ l, p v = true) →
      l.filter p = l := fun p h => List.filter_eq_self.mpr h
  have kV : ∀ (p : SqlEquiv.Value → Bool), (∀ v ∈ vs, p v = !v.isNull) → vs.filter p = V :=
    fun p h => List.filter_congr h
  have kall : ∀ (p : SqlEquiv.Value → Bool), (∀ v ∈ V, p v = false) →
      (V.all p && !V.isEmpty) = false := by
    intro p h
    rcases hVe : V with _ | ⟨x, l⟩
    · rfl
    · have := h x (by rw [hVe]; exact List.mem_cons_self)
      simp [this]
  have hres : SqlEquiv.minMaxAgg mode wantMax vs =
      some ((SqlEquiv.extremeValue wantMax V).getD (.null none)) := by
    unfold SqlEquiv.minMaxAgg
    dsimp only
    rw [knil _ ?hb]
    case hb =>
      intro v hv
      rcases hvals v hv with ⟨t, rfl⟩ | ⟨z, rfl, -⟩ | ⟨u, s, rfl, -⟩ | ⟨s, rfl, -⟩ <;> rfl
    simp only [List.isEmpty_nil, ↓reduceIte, Option.bind_some]
    rw [kV _ ?ho]
    case ho =>
      intro v hv
      rcases hvals v hv with ⟨t, rfl⟩ | ⟨z, rfl, -⟩ | ⟨u, s, rfl, -⟩ | ⟨s, rfl, -⟩ <;> rfl
    rw [kall _ ?hab]
    case hab =>
      intro v hv
      rcases hVvals v hv with ⟨z, rfl, -⟩ | ⟨u, s, rfl, -⟩ | ⟨s, rfl, -⟩ <;> rfl
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases htext : τ = .text
    · rw [knil _ ?hn, kself _ ?hs]
      · simp
      case hn =>
        intro v hv
        rcases hVvals v hv with ⟨z, rfl, h⟩ | ⟨u, s, rfl, h⟩ | ⟨s, rfl, -⟩
        · rw [h] at htext; cases htext
        · rw [h] at htext; cases htext
        · rfl
      case hs =>
        intro v hv
        rcases hVvals v hv with ⟨z, rfl, h⟩ | ⟨u, s, rfl, h⟩ | ⟨s, rfl, -⟩
        · rw [h] at htext; cases htext
        · rw [h] at htext; cases htext
        · rfl
    · rw [kself _ ?hn, knil _ ?hs]
      · by_cases hVe : V = [] <;> simp [hVe]
      case hn =>
        intro v hv
        rcases hVvals v hv with ⟨z, rfl, -⟩ | ⟨u, s, rfl, -⟩ | ⟨s, rfl, h⟩
        · rfl
        · rfl
        · exact absurd h htext
      case hs =>
        intro v hv
        rcases hVvals v hv with ⟨z, rfl, -⟩ | ⟨u, s, rfl, -⟩ | ⟨s, rfl, h⟩
        · rfl
        · rfl
        · exact absurd h htext
  exact hres

/-- `MIN` and `MAX` agree on a column of a non-boolean type, in every dialect mode (there are no
    booleans, and numbers and strings do not mix). -/
theorem minmax_agree {τ : SqlType} (hτ : τ ≠ .bool) (mode : SqlEquiv.MinMaxMode) (wantMax : Bool)
    {ds : List Datum} {vs : List SqlEquiv.Value} (h : List.Forall₂ (TRel τ) ds vs) {d : Datum}
    (hd : (if wantMax then AggFn.max else AggFn.min).apply (ds.filterMap id) = .ok d) :
    ∃ v, SqlEquiv.minMaxAgg mode wantMax vs = some v ∧ DatumRel d v := by
  have hrel := nonnull_rel h
  have hres := minMaxAgg_eq hτ mode wantMax h
  set V := vs.filter fun v => !v.isNull with hV
  rw [hres]
  refine ⟨_, rfl, ?_⟩
  clear_value V
  rcases hX : ds.filterMap id with _ | ⟨a, l⟩
  · rw [hX] at hd hrel
    cases hrel
    cases wantMax <;> simp only [AggFn.apply, Except.ok.injEq, Bool.false_eq_true, ↓reduceIte] at hd <;>
      (subst hd; exact ⟨none, rfl⟩)
  · rw [hX] at hd hrel
    obtain ⟨x, l', hxa, hl', hVeq⟩ : ∃ x l', VRel τ a x ∧ List.Forall₂ (VRel τ) l l' ∧ V = x :: l' := by
      cases hrel with
      | cons hxa hl' => exact ⟨_, _, hxa, hl', rfl⟩
    rw [hVeq, extremeValue_eq, List.foldl_cons]
    simp only [extremeStep]
    have hd' : ∃ w, extremeFrom (if wantMax then .gt else .lt) a l = .ok w ∧ d = some w := by
      cases wantMax <;>
      · simp only [AggFn.apply, Bool.false_eq_true, ↓reduceIte, Functor.map, Except.map] at hd
        split at hd
        · cases hd
        · rename_i w hw; simp only [Except.ok.injEq] at hd; exact ⟨w, hw, hd.symm⟩
    obtain ⟨w, hw, rfl⟩ := hd'
    obtain ⟨w', hw', hrw⟩ := extreme_rel hτ wantMax hl' hxa hw
    rw [hw']
    exact hrw

end SqlBridge.CorrectAgg

namespace SqlBridge.CorrectAgg
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder

/-! ### Aggregates over related rows -/

/-- The aggregates of step 3a: `COUNT(*)`, `COUNT([DISTINCT] e)`, `SUM(e)`, `MIN(e)`, `MAX(e)` of a
    fragment expression (`AVG` and `DISTINCT` other than in `COUNT` are left out). -/
def aggFragment : SqlEquiv.Expr → Bool
  | .countStar => true
  | .agg .count (some e) _ => isFragment e
  | .agg (.sum _) (some e) false => isFragment e
  | .agg (.min _) (some e) false => isFragment e
  | .agg (.max _) (some e) false => isFragment e
  | _ => false

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String) (db : SqlEquiv.Database)

/-- An argument evaluated over related rows: the typed values against the untyped ones. -/
theorem eval_rows_rel {Γ : Fin n → SqlType} {w : SqlEquiv.Expr} {e : Expr n}
    (ht : Translates cols fold w e) (hnb : NoBoolOrder Γ e) {τ : SqlType}
    (hty : e.typeOf Γ = some τ) : ∀ {R : List (Row n)} {U : List SqlEquiv.Row} {ds : List Datum},
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U →
      List.Forall₂ (fun r d => e.eval r = .ok d) R ds →
      List.Forall₂ (TRel τ) ds (U.filterMap fun u => SqlEquiv.evalExprWithDb db u w)
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hru hrows, .cons hd hds => by
    obtain ⟨v, hv, hrel⟩ := Translates.eval_rel cols fold db hru.1 hru.2 ht hnb hd
    rw [List.filterMap_cons_some (f := fun u => SqlEquiv.evalExprWithDb db u w) hv]
    exact .cons ⟨hrel, Expr.hasType_of_eval_eq_ok hru.2 hty hd⟩ (eval_rows_rel ht hnb hty hrows hds)
/-- `SqlEquiv`'s expression evaluator, as `evalSelect` passes it to the aggregate evaluator. -/
abbrev ee : SqlEquiv.Database → SqlEquiv.Row → SqlEquiv.Expr → Option SqlEquiv.Value :=
  fun db' r e => SqlEquiv.evalExprWithDb db' r e

theorem call_eval {fn : AggFn} {dist : Bool} {e : Expr n} {R : List (Row n)} {d : Datum}
    (h : (AggCall.call fn dist e).eval R = .ok d) :
    ∃ ds, R.mapM e.eval = .ok ds ∧
      fn.apply (if dist then (ds.filterMap id).dedup else ds.filterMap id) = .ok d := by
  simp only [AggCall.eval, bind, Except.bind] at h
  split at h
  · cases h
  · exact ⟨_, by assumption, h⟩

/-- An aggregate of step 3a over related rows: the typed value against `SqlEquiv`'s. -/
theorem agg_rel {Γ : Fin n → SqlType} {R : List (Row n)} {U : List SqlEquiv.Row}
    (hrows : List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U)
    (row : SqlEquiv.Row) : ∀ (a : SqlEquiv.Expr), aggFragment a = true →
      ∀ {c : AggCall n}, elabAgg cols fold a = .ok c → AggNoBool Γ c →
      ∀ {σ : SqlType}, c.typeOf Γ = some σ → ∀ {d : Datum}, c.eval R = .ok d →
      ∃ v, SqlEquiv.evalExprWithAggParam ee db U row a = some v ∧ DatumRel d v
  | .countStar, _, c, hel, _, σ, _, d, hd => by
    simp only [elabAgg, pure, Except.pure, Except.ok.injEq] at hel
    subst hel
    simp only [AggCall.eval, Except.ok.injEq] at hd
    subst hd
    simp only [SqlEquiv.evalExprWithAggParam, Option.some.injEq, exists_eq_left']
    rw [hrows.length_eq]; exact .int _
  | .agg .count (some w) dist, hf, c, hel, hnb, σ, hty, d, hd => by
    simp only [elabAgg] at hel
    obtain ⟨e, he, rfl⟩ := bind_pure_ok hel
    have ht := translates_of_elab cols fold w hf he
    obtain ⟨τ, hτ⟩ : ∃ τ, e.typeOf Γ = some τ := by
      simp only [AggCall.typeOf, Option.map_eq_some_iff] at hty
      obtain ⟨τ, hτ, -⟩ := hty; exact ⟨τ, hτ⟩
    obtain ⟨ds, hds, happ⟩ := call_eval hd
    have hrel := eval_rows_rel cols fold db ht hnb hτ hrows (mapM_forall₂ hds)
    simp only [SqlEquiv.evalExprWithAggParam, SqlEquiv.evalAggOverTableParam, ee,
      Option.some.injEq, exists_eq_left']
    cases dist
    · simp only [AggFn.apply, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at happ
      subst happ
      rw [count_agree (hrel.imp fun _ _ h => h.1)]
      exact .int _
    · simp only [AggFn.apply, ↓reduceIte, Except.ok.injEq] at happ
      subst happ
      rw [count_distinct_agree hrel]
      exact .int _
  | .agg (.sum b) (some w) false, hf, c, hel, hnb, σ, hty, d, hd => by
    simp only [elabAgg] at hel
    obtain ⟨e, he, rfl⟩ := bind_pure_ok hel
    have ht := translates_of_elab cols fold w hf he
    obtain ⟨τ, hτ, hτn⟩ : ∃ τ, e.typeOf Γ = some τ ∧ (τ = .int ∨ τ = .decimal) := by
      simp only [AggCall.typeOf] at hty
      split at hty <;> simp_all
    obtain ⟨ds, hds, happ⟩ := call_eval hd
    have hrel := eval_rows_rel cols fold db ht hnb hτ hrows (mapM_forall₂ hds)
    simp only [Bool.false_eq_true, ↓reduceIte] at happ
    obtain ⟨v, hv, hvr⟩ := sum_agree hτn b hrel happ
    simp only [SqlEquiv.evalExprWithAggParam, SqlEquiv.evalAggOverTableParam, ee, Bool.false_eq_true,
      ↓reduceIte]
    exact ⟨v, hv, hvr⟩
  | .agg (.min m) (some w) false, hf, c, hel, hnb, σ, hty, d, hd => by
    simp only [elabAgg] at hel
    obtain ⟨e, he, rfl⟩ := bind_pure_ok hel
    have ht := translates_of_elab cols fold w hf he
    obtain ⟨τ, hτ, hτn⟩ : ∃ τ, e.typeOf Γ = some τ ∧ τ ≠ .bool := by
      simp only [AggCall.typeOf] at hty
      split at hty <;> simp_all <;> (subst_vars; decide)
    obtain ⟨ds, hds, happ⟩ := call_eval hd
    have hrel := eval_rows_rel cols fold db ht hnb hτ hrows (mapM_forall₂ hds)
    simp only [Bool.false_eq_true, ↓reduceIte] at happ
    obtain ⟨v, hv, hvr⟩ := minmax_agree hτn m false hrel (by simpa using happ)
    simp only [SqlEquiv.evalExprWithAggParam, SqlEquiv.evalAggOverTableParam, ee, Bool.false_eq_true,
      ↓reduceIte]
    exact ⟨v, hv, hvr⟩
  | .agg (.max m) (some w) false, hf, c, hel, hnb, σ, hty, d, hd => by
    simp only [elabAgg] at hel
    obtain ⟨e, he, rfl⟩ := bind_pure_ok hel
    have ht := translates_of_elab cols fold w hf he
    obtain ⟨τ, hτ, hτn⟩ : ∃ τ, e.typeOf Γ = some τ ∧ τ ≠ .bool := by
      simp only [AggCall.typeOf] at hty
      split at hty <;> simp_all <;> (subst_vars; decide)
    obtain ⟨ds, hds, happ⟩ := call_eval hd
    have hrel := eval_rows_rel cols fold db ht hnb hτ hrows (mapM_forall₂ hds)
    simp only [Bool.false_eq_true, ↓reduceIte] at happ
    obtain ⟨v, hv, hvr⟩ := minmax_agree hτn m true hrel (by simpa using happ)
    simp only [SqlEquiv.evalExprWithAggParam, SqlEquiv.evalAggOverTableParam, ee, Bool.false_eq_true,
      ↓reduceIte]
    exact ⟨v, hv, hvr⟩

end SqlBridge.CorrectAgg

namespace SqlBridge.CorrectAgg
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin

/-! ### Elaboration of `SELECT agg₁, …, aggₖ FROM f [WHERE p]` -/

/-- Every SELECT item is an aggregate of step 3a (with or without an alias). -/
def aggItems : List SqlEquiv.SelectItem → Bool
  | [] => true
  | .exprItem a _ :: rest => aggFragment a && aggItems rest
  | _ :: _ => false

/-- The expression of an item (`*` has none; unused for aggregate items). -/
def itemExpr : SqlEquiv.SelectItem → SqlEquiv.Expr
  | .exprItem e _ => e
  | .star _ => .countStar

/-- The statements of step 3a. -/
def aggStmt (items : List SqlEquiv.SelectItem) (f : SqlEquiv.FromClause)
    (wh : Option SqlEquiv.Expr) : SqlEquiv.Stmt :=
  .query (.simple (.mk false items (some f) wh [] none [] none none))

theorem aggsOf_aggFragment : ∀ a, aggFragment a = true → aggsOf a = [a]
  | .countStar, _ => by simp [aggsOf]
  | .agg _ _ _, _ => by simp [aggsOf]
  | .lit _, h | .col _, h | .binOp _ _ _, h | .unaryOp _ _, h | .func _ _, h | .case _ _, h
  | .inList _ _ _, h | .between _ _ _, h | .inSubquery _ _ _, h | .exists _ _, h | .subquery _, h
  | .windowFn _ _ _, h => by simp [aggFragment] at h

theorem colsOutsideAggs_aggFragment : ∀ a, aggFragment a = true → colsOutsideAggs a = []
  | .countStar, _ => by simp [colsOutsideAggs]
  | .agg _ _ _, _ => by simp [colsOutsideAggs]
  | .lit _, h | .col _, h | .binOp _ _ _, h | .unaryOp _ _, h | .func _ _, h | .case _ _, h
  | .inList _ _ _, h | .between _ _ _, h | .inSubquery _ _ _, h | .exists _ _, h | .subquery _, h
  | .windowFn _ _ _, h => by simp [aggFragment] at h

variable {f : SqlEquiv.SelectItem → Option SqlEquiv.Expr} (hf : ∀ e al, f (.exprItem e al) = some e)
include hf

theorem filterMap_aggItems : ∀ items, aggItems items = true →
    items.filterMap f = items.map itemExpr
  | [], _ => rfl
  | .exprItem e _ :: rest, h => by
    simp only [aggItems, Bool.and_eq_true] at h
    simp [hf, itemExpr, filterMap_aggItems rest h.2]
  | .star _ :: _, h => by simp [aggItems] at h

theorem aggsOfList_aggItems : ∀ items, aggItems items = true →
    aggsOfList (items.filterMap f) = items.map itemExpr
  | [], _ => by simp [aggsOfList]
  | .exprItem e _ :: rest, h => by
    simp only [aggItems, Bool.and_eq_true] at h
    simp [hf, aggsOfList, aggsOf_aggFragment e h.1, aggsOfList_aggItems rest h.2, itemExpr]
  | .star _ :: _, h => by simp [aggItems] at h

theorem colsOutsideAggsList_aggItems : ∀ items, aggItems items = true →
    colsOutsideAggsList (items.filterMap f) = []
  | [], _ => by simp [colsOutsideAggsList]
  | .exprItem e _ :: rest, h => by
    simp only [aggItems, Bool.and_eq_true] at h
    simp [hf, colsOutsideAggsList, colsOutsideAggs_aggFragment e h.1,
      colsOutsideAggsList_aggItems rest h.2]
  | .star _ :: _, h => by simp [aggItems] at h
theorem subsOfList_aggItems : ∀ items, aggItems items = true →
    subsOfList (items.filterMap f) = []
  | [], _ => by simp [subsOfList]
  | .exprItem e _ :: rest, h => by
    simp only [aggItems, Bool.and_eq_true] at h
    have he : subsOf e = [] := by
      cases e <;> simp_all [aggFragment, subsOf]
    simp [hf, subsOfList, he, subsOfList_aggItems rest h.2]
  | .star _ :: _, h => by simp [aggItems] at h
omit hf in
theorem forall₂_imp_mem {α β : Type _} {R S : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → (∀ a ∈ l, ∀ b, R a b → S a b) → List.Forall₂ S l l'
  | _, _, .nil, _ => .nil
  | _, _, .cons h hs, H => .cons (H _ List.mem_cons_self _ h)
      (forall₂_imp_mem hs fun a ha b hab => H a (List.mem_cons_of_mem _ ha) b hab)

omit hf in
theorem aggItems_mem : ∀ {items : List SqlEquiv.SelectItem}, aggItems items = true →
    ∀ it ∈ items, ∃ e al, it = .exprItem e al ∧ aggFragment e = true
  | [], _, _, h => by simp at h
  | .exprItem e al :: rest, h, it, hit => by
    simp only [aggItems, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hit with rfl | hit
    · exact ⟨e, al, rfl, h.1⟩
    · exact aggItems_mem h.2 it hit
  | .star _ :: _, h, _, _ => by simp [aggItems] at h

omit hf in
theorem selectHasWindowFn_aggItems : ∀ {items : List SqlEquiv.SelectItem},
    aggItems items = true → SqlEquiv.selectHasWindowFn items = false
  | [], _ => rfl
  | .exprItem a _ :: rest, h => by
    simp only [aggItems, Bool.and_eq_true] at h
    have ha : SqlEquiv.exprHasWindowFn a = false := by
      cases a <;> simp_all [aggFragment, SqlEquiv.exprHasWindowFn]
    have := selectHasWindowFn_aggItems h.2
    simp only [SqlEquiv.selectHasWindowFn, List.any_cons, ha, Bool.false_or] at this ⊢
    exact this
  | .star _ :: _, h => by simp [aggItems] at h

omit hf in
set_option maxHeartbeats 1000000 in
/-- The query the elaborator builds for `SELECT agg₁, …, aggₖ FROM f [WHERE p]`: the aggregate of
    the input with no keys, projected onto one column per item, the column of the item's own
    aggregate. -/
theorem elab_agg_shape (N : NamedSchema) {items : List SqlEquiv.SelectItem}
    {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} (hai : aggItems items = true)
    (hne : items ≠ []) {e : Elaborated N.S}
    (h : elabStmt N (aggStmt items fr wh) = .ok e) :
    e.q.typeOf.isSome ∧ ∃ n, ∃ qf : Query N.S n, ∃ cf,
      elabFrom N (fun sq => elabSubQuery N 15 sq) fr = .ok ⟨n, qf, cf⟩ ∧
      ∃ q₀ : Query N.S n, elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf wh = .ok q₀ ∧
      ∃ (a : ℕ) (aggs : Fin a → AggCall n) (keys : Fin 0 → Expr n)
        (its : List (Expr (0 + a) × Column)),
        (∀ j, ∃ x, aggFragment x = true ∧ elabAgg cf N.fold x = .ok (aggs j)) ∧
        List.Forall₂ (fun it x => ∃ j : Fin a, elabAgg cf N.fold (itemExpr it) = .ok (aggs j) ∧
          x.1 = .col (Fin.natAdd 0 j)) items its ∧
        e = ⟨its.length, .project (fun i => (its[i]).1) (.aggregate keys aggs q₀),
          fun i => (its[i]).2⟩ := by
  simp only [aggStmt, elabStmt, elabQuery, bind, Except.bind] at h
  rcases hraw : elabQueryRaw N (.simple (.mk false items (some fr) wh [] none [] none none))
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
  obtain ⟨q₀, hq₀, hraw'⟩ := bind_ok hraw
  clear hraw
  rename' hraw' => hraw
  have hne' : ((items.map itemExpr).eraseDups.isEmpty) = false := by
    cases items with
    | nil => exact absurd rfl hne
    | cons it rest => simp [List.eraseDups_cons]
  rw [aggsOfList_aggItems ?hf items hai, colsOutsideAggsList_aggItems ?hf2 items hai] at hraw
  case hf => intros; rfl
  case hf2 => intros; rfl
  simp only [List.map_nil, aggsOfList, aggsOfOpt, colsOutsideAggsList, colsOutsideAggsOpt,
    List.append_nil, List.eraseDups_nil, ite_self, List.filterMap_nil, List.isEmpty_nil,
    Bool.true_and, Option.isNone_none, Bool.and_true, List.mapM_nil, hne', Bool.false_eq_true,
    ↓reduceIte, pure, Except.pure, Bool.not_true, bind, Except.bind] at hraw
  -- no subquery node in the items: not the elaborator's subquery path (9.4b step 3)
  simp only [Option.toList_none, List.append_nil] at hraw
  rw [distinctSubs_eq_nil (subsOfList_aggItems (fun _ _ => rfl) items hai),
    selectHasWindowFn_aggItems hai] at hraw
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, List.map_nil, List.any_nil,
    Bool.or_self, ↓reduceIte] at hraw
  refine ⟨n, qf, cf, hf, q₀, hq₀, ?_⟩
  all_goals
    split at hraw
    · cases hraw
    rename_i aggList hv
    split at hraw
    · cases hraw
    rename_i out hout
    split at hraw
    · cases hraw
    rename_i its hits
    obtain ⟨keyList, hk, rfl⟩ := finishSelect_nondistinct N.fold _ [] none none hraw
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hk
    subst hk
    have hV := mapM_forall₂ hv
    refine ⟨_, fun j => aggList[j], fun i => [][i], its, ?_, ?_, rfl⟩
    · intro ⟨j, hj⟩
      have hjv : j < aggList.length := by simpa using hj
      have hjl : j < (items.map itemExpr).eraseDups.length := hV.length_eq ▸ hjv
      have hx := (List.forall₂_iff_get.mp hV).2 j hjl hjv
      simp only [List.get_eq_getElem] at hx
      have hm := List.mem_map.mp (List.mem_eraseDups.mp (List.getElem_mem hjl))
      obtain ⟨it, hit, hit'⟩ := hm
      obtain ⟨e, al, rfl, hfr⟩ := aggItems_mem hai it hit
      simp only [itemExpr] at hit'
      exact ⟨_, hit' ▸ hfr, hx⟩
    refine forall₂_imp_mem (mapM_forall₂ hits) fun it hit x hx => ?_
    obtain ⟨e, al, rfl, hfr⟩ := aggItems_mem hai it hit
    have hmem : e ∈ (items.map itemExpr).eraseDups :=
      List.mem_eraseDups.mpr (List.mem_map.mpr ⟨_, hit, rfl⟩)
    obtain ⟨j, hj⟩ : ∃ j, (items.map itemExpr).eraseDups.findIdx? (· == e) = some j :=
      Option.isSome_iff_exists.mp (by
        rw [List.findIdx?_isSome, List.any_eq_true]; exact ⟨e, hmem, by simp⟩)
    obtain ⟨hjl, hje, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
    simp only [beq_iff_eq] at hje
    have hjv : j < aggList.length := hV.length_eq ▸ hjl
    have hja : j < (aggList ++ []).length := by simpa using hjv
    have hhook : aggHook (a := (aggList ++ []).length) cf N.fold (fun i : Fin ([] : List (Expr n)).length => [][i])
        (List.map itemExpr items).eraseDups e = some (.col (Fin.natAdd _ ⟨j, hja⟩)) := by
      simp only [aggHook, hj, hja, ↓reduceDIte]
    have helab : elabExpr out N.fold (aggHook (a := (aggList ++ []).length) cf N.fold
        (fun i : Fin ([] : List (Expr n)).length => [][i]) (List.map itemExpr items).eraseDups) e =
        .ok (.col (Fin.natAdd _ ⟨j, hja⟩)) := by
      unfold elabExpr
      rw [hhook]; rfl
    dsimp only at hx
    rw [helab] at hx
    simp only at hx
    split at hx
    · rename_i τ hτ
      simp only [Except.ok.injEq] at hx
      subst hx
      refine ⟨⟨j, hja⟩, ?_, rfl⟩
      have := (List.forall₂_iff_get.mp hV).2 j hjl hjv
      simp only [List.get_eq_getElem, hje] at this
      simpa [itemExpr] using this
    · simp [throw, throwThe, MonadExceptOf.throw] at hx

end SqlBridge.CorrectAgg

namespace SqlBridge.CorrectAgg
open SqlEquiv

theorem evalSelectCore_agg (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool) (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause) (wh : Option Expr)
    (hAgg : hasAgg items = true) (hNoWin : hasWindowFn items = false) :
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk false items (some from_) wh [] none [] none none) =
    let src := match wh with
      | some c => (fromEval db from_).filter fun row => exprEval db row c == some (Value.bool true)
      | none => fromEval db from_
    [items.flatMap (selectItemWithAggEval db src
      ((bareSampleRow (exprEval db) (selectMinMaxCalls items none) src).getD []))] := by
  rw [evalSelectCore_eq_afterFilter]
  cases wh <;> simp [evalSelectAfterFilter, evalSelectProjectDistinct, hAgg, hNoWin] <;> rfl

/-- `evalSelectCore_agg` under an outer row: the source rows carry it at the end. -/
theorem evalSelectCore_agg_ctx (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool) (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause) (wh : Option Expr)
    (hAgg : hasAgg items = true) (hNoWin : hasWindowFn items = false) :
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk false items (some from_) wh [] none [] none none) =
    let base := (fromEval db from_).map fun row => row ++ outerRow
    let src := match wh with
      | some c => base.filter fun row => exprEval db row c == some (Value.bool true)
      | none => base
    [items.flatMap (selectItemWithAggEval db src
      ((bareSampleRow (exprEval db) (selectMinMaxCalls items none) src).getD []))] := by
  rw [evalSelectCore_eq_afterFilter]
  cases wh <;> simp [evalSelectAfterFilter, evalSelectProjectDistinct, hAgg, hNoWin] <;> rfl
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin

/-- Aggregate items have no window function (#429). -/
theorem selectHasAggregate_aggItems : ∀ {items : List SqlEquiv.SelectItem}, aggItems items = true →
    items ≠ [] → SqlEquiv.selectHasAggregate items = true
  | [], _, h => absurd rfl h
  | .exprItem a _ :: _, hai, _ => by
    simp only [aggItems, Bool.and_eq_true] at hai
    have : SqlEquiv.hasAggregate a = true := by
      have h := hai.1
      cases a <;> simp_all [aggFragment, SqlEquiv.hasAggregate]
    simp [SqlEquiv.selectHasAggregate, this]
  | .star _ :: _, hai, _ => by simp [aggItems] at hai

theorem evalAll_get {m : ℕ} {rs : List (Row m)} : ∀ {a : ℕ} {as : Fin a → AggCall m} {A : Row a},
    AggCall.evalAll as rs = .ok A → ∀ j, (as j).eval rs = .ok (A j)
  | 0, _, _, _, j => j.elim0
  | a + 1, as, A, h, j => by
    simp only [AggCall.evalAll, bind, Except.bind] at h
    split at h
    · cases h
    rename_i d hd
    split at h
    · cases h
    rename_i ds hds
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using hd
    · simpa using evalAll_get hds i

theorem agg_divSafe {m : ℕ} (cols : Fin m → Column) (fold : String → String) :
    ∀ (x : SqlEquiv.Expr), aggFragment x = true → ∀ {c : AggCall m}, elabAgg cols fold x = .ok c →
      c.divSafe = true
  | .countStar, _, c, h => by
    simp only [elabAgg, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | .agg .count (some w) _, hf, c, h | .agg (.sum _) (some w) false, hf, c, h
  | .agg (.min _) (some w) false, hf, c, h | .agg (.max _) (some w) false, hf, c, h => by
    simp only [elabAgg] at h
    obtain ⟨e, he, rfl⟩ := bind_pure_ok h
    exact Translates.divSafe cols fold (translates_of_elab cols fold w hf he)
  | .lit _, hf, _, _ | .col _, hf, _, _ | .binOp _ _ _, hf, _, _ | .unaryOp _ _, hf, _, _
  | .func _ _, hf, _, _ | .case _ _, hf, _, _ | .inList _ _ _, hf, _, _ | .between _ _ _, hf, _, _
  | .inSubquery _ _ _, hf, _, _ | .exists _ _, hf, _, _ | .subquery _, hf, _, _
  | .windowFn _ _ _, hf, _, _ | .agg _ none _, hf, _, _ | .agg (.avg _) _ _, hf, _, _
  | .agg (.sum _) _ true, hf, _, _ | .agg (.min _) _ true, hf, _, _
  | .agg (.max _) _ true, hf, _, _ => by simp [aggFragment] at hf

theorem items_vals (db : SqlEquiv.Database) (U : List SqlEquiv.Row) (row : SqlEquiv.Row) :
    ∀ {items : List SqlEquiv.SelectItem}, aggItems items = true →
      (items.flatMap (SqlEquiv.evalSelectItemWithAggParam ee db U row)).map Prod.snd =
        items.map fun it => (SqlEquiv.evalExprWithAggParam ee db U row (itemExpr it)).getD (.null none)
  | [], _ => rfl
  | .exprItem a al :: rest, hai => by
    simp only [aggItems, Bool.and_eq_true] at hai
    simp only [List.flatMap_cons, List.map_append, List.map_cons, items_vals db U row hai.2]
    simp only [SqlEquiv.evalSelectItemWithAggParam, itemExpr]
    split <;> simp_all
  | .star _ :: _, hai => by simp [aggItems] at hai
theorem mapM_ok_map {α β ε : Type _} {f : α → Except ε β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = .ok (g x)) → l.mapM f = .ok (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self,
      mapM_ok_map fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- **Elaborator correctness for aggregates without `GROUP BY` (#352, roadmap step 3a).** For
    `SELECT agg₁, …, aggₖ FROM f [WHERE p]`, each `aggᵢ` one of `COUNT(*)`,
    `COUNT([DISTINCT] e)`, `SUM(e)`, `MIN(e)`, `MAX(e)` over a fragment expression `e`, and `f` a
    `FROM` tree of step 2: when the statement elaborates, the typed query evaluates to one row,
    related to `SqlEquiv`'s one row. Hypotheses as `elabStmt_correct_join`'s. -/
theorem elabStmt_correct_agg_w (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (hai : aggItems items = true) (hne : items ≠ []) (hff : fromFragment fr = true)
    (hwo : ∀ {n : ℕ} (qf q₀ : Query N.S n) (cf : Fin n → Column),
      elabFrom N (fun sq => elabSubQuery N 15 sq) fr = .ok ⟨n, qf, cf⟩ →
      elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf wh = .ok q₀ →
      WhereOk cf N.fold db D wh qf q₀)
    {e : Elaborated N.S} (h : elabStmt N (aggStmt items fr wh) = .ok e) (hnb : QNoBoolOrder e.q) :
    e.q.IsSafe ∧ ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (aggStmt items fr wh)).2 = some out ∧
        List.Forall₂ OutRel rs out ∧
        ∀ ctx, List.Forall₂ OutRel rs (SqlEquiv.evalSelectWithContext db ctx
          (.mk false items (some fr) wh [] none [] none none)) := by
  obtain ⟨hty, n, qf, cf, hf, q₀, hq₀, a, aggs, keys, its, haggs, hits, rfl⟩ :=
    elab_agg_shape N hai hne h
  have hwo' := hwo qf q₀ cf hf hq₀
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
  -- the aggregate's input rows, related to `SqlEquiv`'s filtered rows
  have hdivq₀ : q₀.divSafe = true := hwo'.div _ hq₀ty hnbq₀ hdivf
  obtain ⟨R, hR⟩ := Query.IsSafe.exists_eval_eq_ok (q := q₀) ⟨by simp [hq₀ty], hdivq₀⟩ hD
  have hRU : ∃ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U :=
    ⟨_, hwo'.rel hq₀ty hnbq₀ hRf hR hrows⟩
  -- the aggregates over the input
  have hRconf : ∀ r ∈ R, r.Conforms Γ₀ := fun r hr => by
    obtain ⟨U, hU⟩ := hRU
    obtain ⟨u, -, h⟩ := forall₂_mem_left hU hr; exact h.2
  obtain ⟨A, hA⟩ : ∃ A, AggCall.evalAll aggs R = .ok A := by
    rcases AggCall.evalAll_ok_or_divisionByZero hRconf has with ⟨A, hA, -⟩ | ⟨-, j, hj⟩
    · exact ⟨A, hA⟩
    · obtain ⟨x, hx, hel⟩ := haggs j
      rw [agg_divSafe cf N.fold x hx hel] at hj; cases hj
  -- the typed query: one aggregate row, projected
  have hk : ∀ r : Row n, Expr.evalRow keys r = .ok (fun _ => none) := fun r =>
    Expr.evalRow_eq_ok_iff.mpr (fun i => i.elim0)
  set row0 : Row (0 + a) := Fin.append (fun _ => none : Row 0) A with hrow0
  have hagg : (Query.aggregate keys aggs q₀).eval D = .ok [row0] := by
    rw [Query.eval_aggregate, hR]
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
  -- each item's value, over any related source rows
  have final : ∀ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U →
      ∀ sample, List.Forall₂ DatumRel (List.ofFn r) (items.map fun it =>
        (SqlEquiv.evalExprWithAggParam ee db U sample (itemExpr it)).getD (.null none)) := by
    intro U hRU sample
    apply List.forall₂_iff_get.mpr
    refine ⟨by simp [hits.length_eq], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
    have hi : i < its.length := by simpa using h1
    obtain ⟨j, hel, hj⟩ := hcol ⟨i, hi⟩
    -- the typed value is the item's aggregate
    have hri : r ⟨i, hi⟩ = A j := by
      have h1 := (hex ⟨i, hi⟩).choose_spec
      have h2 : ((its[i]).1).eval row0 = .ok (A j) := by
        rw [hj]
        show Except.ok (row0 (Fin.natAdd 0 j)) = _
        rw [hrow0, Fin.append_right]
      exact Except.ok.inj (h1.symm.trans h2)
    simp only [hri]
    have hi' : i < items.length := by simpa using h2
    have hmem : items[i]'hi' ∈ items := List.getElem_mem hi'
    obtain ⟨x, al, hx, hfr⟩ := aggItems_mem hai _ hmem
    simp only [hx, itemExpr] at hel ⊢
    obtain ⟨v, hv, hvr⟩ := agg_rel cf N.fold db hRU sample x hfr hel (hnbAgg j) (has j) (evalAll_get hA j)
    rw [hv]
    exact hvr
  have hsafe : (Query.project (fun i : Fin its.length => (its[i]).1)
      (Query.aggregate keys aggs q₀)).IsSafe := by
    refine ⟨hty, ?_⟩
    have h1 : ∀ i : Fin its.length, ((its[i]).1).divSafe = true := fun i => by
      obtain ⟨j, -, hj⟩ := hcol i
      show ((its[i.1]).1).divSafe = true
      rw [hj]; rfl
    have h2 : ∀ j, (aggs j).divSafe = true := fun j => by
      obtain ⟨x, hx, hel⟩ := haggs j
      exact agg_divSafe cf N.fold x hx hel
    simp only [Query.divSafe, h2, hdivq₀, Bool.and_true, decide_true, Bool.and_self,
      decide_eq_true_eq, implies_true, IsEmpty.forall_iff]
    exact fun i => h1 i
  refine ⟨hsafe, [r], by rw [Query.eval_project, hagg]; simp [hrow, pure, Except.pure, bind, Except.bind], _, rfl, ?_, fun ctx => ?_⟩
  · -- `SqlEquiv`'s side: one row of the items' values
    simp only [SqlEquiv.evalQuery]
    rw [SqlEquiv.evalSelect_eq_evalSelectCore, evalSelectCore_agg _ _ _ _ _ _ _ _ _ _ _ _ _
      (selectHasAggregate_aggItems hai hne) (selectHasWindowFn_aggItems hai)]
    refine .cons ?_ .nil
    unfold OutRel
    rw [items_vals db _ _ hai]
    apply final
    exact hwo'.rel hq₀ty hnbq₀ hRf hR hrows
  · -- under an outer row (a subquery body)
    rw [SqlEquiv.evalSelectWithContext_eq_evalSelectCore, evalSelectCore_agg_ctx _ _ _ _ _ _ _ _ _
      _ _ _ _ _ (selectHasAggregate_aggItems hai hne) (selectHasWindowFn_aggItems hai)]
    refine .cons ?_ .nil
    unfold OutRel
    rw [items_vals db _ _ hai]
    apply final
    refine hwo'.rel hq₀ty hnbq₀ hRf hR ?_
    rw [List.forall₂_map_right_iff]
    exact hrows.imp fun r u h => ⟨rowRel_append ctx h.1, h.2⟩

/-- **Elaborator correctness for aggregates without `GROUP BY` (#352, roadmap step 3a).**
    `elabStmt_correct_agg_w` with a `WHERE` in the expression fragment. -/
theorem elabStmt_correct_agg (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (hai : aggItems items = true) (hne : items ≠ []) (hff : fromFragment fr = true)
    (hw : ∀ w ∈ wh, isFragment w = true)
    {e : Elaborated N.S} (h : elabStmt N (aggStmt items fr wh) = .ok e) (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (aggStmt items fr wh)).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  obtain ⟨-, rs, hrs, out, hout, hr, -⟩ := elabStmt_correct_agg_w N hfold hfoldCI hwn hfix hD hrel
    hai hne hff (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq) h hnb
  exact ⟨rs, hrs, out, hout, hr⟩

end SqlBridge.CorrectAgg
