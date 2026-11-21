/-
  `AVG` across the two evaluators (#352, roadmap step 3c). The typed core keeps the exact quotient
  (registry T10); `SqlEquiv` rounds it half away from zero to `max 16 s` places, `s` the inputs'
  scale (row 7). The two are related up to that rounding (`AvgRel`): the untyped value is the typed
  one rounded half away from zero to some `p ≥ 16` places, the same value when the quotient
  terminates within them.

  * `divRoundHalfAway_eq`: `SqlEquiv`'s integer division rounding half away from zero is
    `roundHalfAway` of the rational quotient.
  * `avg_agree`: over related values, `SqlEquiv`'s `AVG` is the typed one rounded.
  * `avg_rel`: the same over related rows, for `AVG(e)` with `e` in the fragment.
  * `cmp_agree_avg`: comparing an integer with an `AVG` agrees exactly when the quotient's
    denominator is at most `10¹⁶` (`compare_int_round`): the rounding cannot cross the integer.
-/
import SqlBridge.CorrectAgg
import Mathlib.Data.Rat.Floor

namespace SqlBridge.CorrectAvg
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectAgg SqlBridge.CorrectOrder

/-- A rational rounded to an integer, half away from zero. -/
def roundHalfAway (x : ℚ) : ℤ := if 0 ≤ x then ⌊x + 1 / 2⌋ else -⌊-x + 1 / 2⌋

/-- The untyped `AVG` value against the typed one: both `NULL`, or the untyped value is the typed
    quotient rounded half away from zero to some `p ≥ 16` places (registry rows 7 and T10). -/
def AvgRel (d : Datum) (v : SqlEquiv.Value) : Prop :=
  (d = none ∧ ∃ t, v = .null t) ∨ ∃ q p, d = some (.decimal q) ∧ SqlEquiv.avgPlaces ≤ p ∧
    v = SqlEquiv.Value.mkDecimal (roundHalfAway (q * 10 ^ p)) p

/-- `⌊N / b + 1/2⌋` for naturals, by the remainder. -/
theorem floor_half_nat (N b : ℕ) (hb : 0 < b) :
    ⌊((N : ℚ) / b) + 1 / 2⌋ = ((N / b : ℕ) : ℤ) + (if b ≤ 2 * (N % b) then 1 else 0) := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hr := Nat.mod_lt N hb
  have hN : (N : ℚ) / b = ((N / b : ℕ) : ℚ) + ((N % b : ℕ) : ℚ) / b := by
    have h : (N : ℚ) = b * (N / b : ℕ) + (N % b : ℕ) := by exact_mod_cast (Nat.div_add_mod N b).symm
    rw [h, add_div, mul_div_cancel_left₀ _ hbq.ne']
  rw [hN, add_assoc, Int.floor_natCast_add]
  congr 1
  have h0 : (0 : ℚ) ≤ ((N % b : ℕ) : ℚ) / b := by positivity
  have h1 : ((N % b : ℕ) : ℚ) / b < 1 := by rw [div_lt_one hbq]; exact_mod_cast hr
  rw [Int.floor_eq_iff]
  split
  · rename_i h2
    have h2' : (1 : ℚ) / 2 ≤ ((N % b : ℕ) : ℚ) / b := by
      rw [le_div_iff₀ hbq]; have : (b : ℚ) ≤ 2 * (N % b : ℕ) := by exact_mod_cast h2
      linarith
    push_cast; constructor <;> linarith
  · rename_i h2
    have h2' : ((N % b : ℕ) : ℚ) / b < 1 / 2 := by
      rw [div_lt_iff₀ hbq]; have : (2 * (N % b : ℕ) : ℚ) < b := by exact_mod_cast Nat.lt_of_not_le h2
      linarith
    push_cast; constructor <;> linarith

theorem cast_ite_succ (q : ℕ) (c : Prop) [Decidable c] :
    (((if c then q + 1 else q : ℕ)) : ℤ) = (q : ℤ) + (if c then 1 else 0) := by
  split <;> simp

/-- `SqlEquiv`'s rounding division is `roundHalfAway` of the rational quotient. -/
theorem divRoundHalfAway_eq (a : ℤ) (b : ℕ) (hb : 0 < b) :
    SqlEquiv.divRoundHalfAway a b = roundHalfAway ((a : ℚ) / b) := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  unfold SqlEquiv.divRoundHalfAway roundHalfAway
  by_cases ha : a < 0
  · have hneg : ¬ (0 : ℚ) ≤ (a : ℚ) / b := by
      rw [not_le]; exact div_neg_of_neg_of_pos (by exact_mod_cast ha) hbq
    simp only [ha, ↓reduceIte, hneg]
    have hN : -((a : ℚ) / b) = ((a.natAbs : ℕ) : ℚ) / b := by
      rw [← neg_div]; congr 1
      have haq : (a : ℚ) < 0 := by exact_mod_cast ha
      simp [abs_of_neg haq]
    rw [hN, floor_half_nat _ _ hb, cast_ite_succ]
  · have hnn : (0 : ℚ) ≤ (a : ℚ) / b := div_nonneg (by exact_mod_cast not_lt.mp ha) hbq.le
    simp only [ha, ↓reduceIte, hnn]
    have hN : (a : ℚ) / b = ((a.natAbs : ℕ) : ℚ) / b := by
      congr 1
      have haq : (0 : ℚ) ≤ a := by exact_mod_cast not_lt.mp ha
      simp [abs_of_nonneg haq]
    rw [hN, floor_half_nat _ _ hb, cast_ite_succ]

/-- `AVG` agrees up to rounding, for an integer or decimal column, in every dialect's boolean
    mode (there are no booleans). -/
theorem avg_agree {τ : SqlType} (hτ : τ = .int ∨ τ = .decimal) (b : SqlEquiv.BoolSumAvg)
    {ds : List Datum} {vs : List SqlEquiv.Value} (h : List.Forall₂ (TRel τ) ds vs) {d : Datum}
    (hd : AggFn.avg.apply (ds.filterMap id) = .ok d) :
    ∃ v, SqlEquiv.avgAgg b vs = some v ∧ AvgRel d v := by
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
  simp only [SqlEquiv.avgAgg, hbools, Option.bind_some, hnn, Bool.false_eq_true, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  rcases hX : ds.filterMap id with _ | ⟨a, l⟩
  · rw [hX] at hd hcount
    simp only [AggFn.apply, Except.ok.injEq] at hd
    subst hd
    refine .inl ⟨rfl, none, ?_⟩
    simp [SqlEquiv.avgNumeric, hcount]
  · rw [hX] at hd hsc hcount
    have hall : ∀ v ∈ a :: l, v.type = τ := by
      intro v hv
      obtain ⟨p, -, ⟨-, -, h⟩⟩ := forall₂_mem_left hsc hv
      exact h
    obtain ⟨w, hw, hwτ, hwq⟩ := sumFrom_q hτ a l (hall a (by simp)) fun v hv => hall v (by simp [hv])
    have hq : scaledQ (SqlEquiv.sumScaled vs) = toQ w := by
      rw [sumScaled_eq, foldl_sumStep, hwq]
      simp only [scaledQ, Int.cast_zero, zero_div, zero_add]
      rw [map_eq_of_forall₂ (fun _ _ h => h.1) hsc]
      simp
    -- the typed mean: the exact quotient
    obtain ⟨q, rfl, hqv⟩ : ∃ q, d = some (.decimal q) ∧ q = toQ w / ((l.length + 1 : ℕ) : ℚ) := by
      simp only [AggFn.apply, hw, bind, Except.bind, pure, Except.pure] at hd
      clear hX hsc hall hwq hq hcount hnum h hbools hnn
      rcases hτ with rfl | rfl <;> cases w <;> simp only [Value.type, reduceCtorEq] at hwτ
      · simp only [meanOf, Except.ok.injEq] at hd
        exact ⟨_, hd.symm, by simp [toQ]⟩
      · simp only [meanOf, Except.ok.injEq] at hd
        exact ⟨_, hd.symm, by simp [toQ]⟩
    refine .inr ⟨q, max SqlEquiv.avgPlaces (SqlEquiv.sumScaled vs).2, rfl, le_max_left _ _, ?_⟩
    simp only [SqlEquiv.avgNumeric, hcount, List.length_cons, Nat.add_one_ne_zero, beq_iff_eq,
      ↓reduceIte, Option.getD_some]
    rw [divRoundHalfAway_eq _ _ (by omega)]
    congr 2
    rw [hqv, ← hq]
    simp only [scaledQ]
    have hs : (SqlEquiv.sumScaled vs).2 ≤ max SqlEquiv.avgPlaces (SqlEquiv.sumScaled vs).2 :=
      le_max_right _ _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
    rw [hk, Nat.add_sub_cancel_left]
    push_cast
    rw [pow_add]
    field_simp

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String) (db : SqlEquiv.Database)

/-- `AVG(e)` of the fragment: not `DISTINCT`, `e` in the fragment. -/
def avgFragment : SqlEquiv.Expr → Bool
  | .agg (.avg _) (some e) false => isFragment e
  | _ => false

/-- `AVG(e)` over related rows: `SqlEquiv`'s value is the typed one rounded (`AvgRel`). -/
theorem avg_rel {Γ : Fin n → SqlType} {R : List (Row n)} {U : List SqlEquiv.Row}
    (hrows : List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U)
    (row : SqlEquiv.Row) (a : SqlEquiv.Expr) (hf : avgFragment a = true)
    {c : AggCall n} (hel : elabAgg cols fold a = .ok c) (hnb : AggNoBool Γ c)
    {σ : SqlType} (hty : c.typeOf Γ = some σ) {d : Datum} (hd : c.eval R = .ok d) :
    ∃ v, SqlEquiv.evalExprWithAggParam ee db U row a = some v ∧ AvgRel d v := by
  match a, hf with
  | .agg (.avg b) (some w) false, hf =>
    simp only [elabAgg] at hel
    obtain ⟨e, he, rfl⟩ := bind_pure_ok hel
    have ht := translates_of_elab cols fold w hf he
    obtain ⟨τ, hτ, hτn⟩ : ∃ τ, e.typeOf Γ = some τ ∧ (τ = .int ∨ τ = .decimal) := by
      simp only [AggCall.typeOf] at hty
      split at hty <;> simp_all
    obtain ⟨ds, hds, happ⟩ := call_eval hd
    have hrel := eval_rows_rel cols fold db ht hnb hτ hrows (mapM_forall₂ hds)
    simp only [Bool.false_eq_true, ↓reduceIte] at happ
    obtain ⟨v, hv, hvr⟩ := avg_agree hτn b hrel happ
    simp only [SqlEquiv.evalExprWithAggParam, SqlEquiv.evalAggOverTableParam, ee, Bool.false_eq_true,
      ↓reduceIte]
    exact ⟨v, hv, hvr⟩

/-! ### Comparing an integer with an `AVG` (step 6c) -/

theorem roundHalfAway_sub_le (x : ℚ) : |(roundHalfAway x : ℚ) - x| ≤ 1 / 2 := by
  unfold roundHalfAway
  split
  · have h1 := Int.floor_le (x + 1 / 2)
    have h2 := Int.lt_floor_add_one (x + 1 / 2)
    rw [abs_le]; constructor <;> linarith
  · have h1 := Int.floor_le (-x + 1 / 2)
    have h2 := Int.lt_floor_add_one (-x + 1 / 2)
    push_cast
    rw [abs_le]; constructor <;> linarith

theorem roundHalfAway_intCast (m : ℤ) : roundHalfAway (m : ℚ) = m := by
  have h := roundHalfAway_sub_le (m : ℚ)
  rw [abs_le] at h
  have h1 : ((roundHalfAway (m : ℚ) - m : ℤ) : ℚ) ≤ 1 / 2 := by push_cast; linarith
  have h2 : (-(1 / 2) : ℚ) ≤ ((roundHalfAway (m : ℚ) - m : ℤ) : ℚ) := by push_cast; linarith
  have h3 : roundHalfAway (m : ℚ) - m < 1 := by
    have : ((roundHalfAway (m : ℚ) - m : ℤ) : ℚ) < ((1 : ℤ) : ℚ) := by push_cast at h1 ⊢; linarith
    exact_mod_cast this
  have h4 : -1 < roundHalfAway (m : ℚ) - m := by
    have : ((-1 : ℤ) : ℚ) < ((roundHalfAway (m : ℚ) - m : ℤ) : ℚ) := by push_cast at h2 ⊢; linarith
    exact_mod_cast this
  omega

/-- An integer and a rational with a small denominator differ by at least `10⁻ᵖ`, or not at
    all. -/
theorem int_sub_ge (z : ℤ) (q : ℚ) (p : ℕ) (hden : q.den ≤ 10 ^ p) (hne : (z : ℚ) ≠ q) :
    1 ≤ |q * 10 ^ p - z * 10 ^ p| := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hq : q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
  have hk : q.num - z * q.den ≠ 0 := by
    intro h0
    apply hne
    have : (q.num : ℚ) = z * q.den := by exact_mod_cast sub_eq_zero.mp h0
    rw [hq, this, mul_div_cancel_right₀ _ hd.ne']
  have hk1 : (1 : ℚ) ≤ |((q.num - z * q.den : ℤ) : ℚ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  have hp : (q.den : ℚ) ≤ 10 ^ p := by exact_mod_cast hden
  have he : q * 10 ^ p - z * 10 ^ p = ((q.num - z * q.den : ℤ) : ℚ) * (10 ^ p / q.den) := by
    conv_lhs => rw [hq]
    push_cast; field_simp
  rw [he, abs_mul, abs_of_pos (div_pos (by positivity) hd)]
  have h1 : (1 : ℚ) ≤ 10 ^ p / q.den := by rw [le_div_iff₀ hd]; linarith
  calc (1 : ℚ) = 1 * 1 := by ring
    _ ≤ _ := mul_le_mul hk1 h1 (by norm_num) (abs_nonneg _)

/-- **Rounding to `p` places does not move a rational across an integer** when its denominator is
    at most `10ᵖ`. -/
theorem compare_int_round (z : ℤ) (q : ℚ) (p : ℕ) (hden : q.den ≤ 10 ^ p) :
    compare (z : ℚ) ((roundHalfAway (q * 10 ^ p) : ℚ) / (10 ^ p : ℕ)) = compare (z : ℚ) q := by
  have hP : (0 : ℚ) < 10 ^ p := by positivity
  have hr := roundHalfAway_sub_le (q * 10 ^ p)
  rw [abs_le] at hr
  push_cast
  rcases lt_trichotomy (z : ℚ) q with h | h | h
  · have hg := int_sub_ge z q p hden h.ne
    rw [abs_of_pos (by nlinarith)] at hg
    rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt, lt_div_iff₀ hP]
    linarith
  · subst h
    have : (z : ℚ) * 10 ^ p = ((z * 10 ^ p : ℤ) : ℚ) := by push_cast; ring
    rw [this, roundHalfAway_intCast]
    push_cast
    rw [mul_div_cancel_right₀ _ hP.ne']
  · have hg := int_sub_ge z q p hden h.ne'
    rw [abs_of_neg (by nlinarith)] at hg
    rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt, div_lt_iff₀ hP]
    linarith

/-- **A comparison of a non-decimal value with an `AVG`** agrees across the evaluators when the
    quotient's denominator is at most `10¹⁶`: `SqlEquiv`'s rounding cannot move it across an
    integer (and anything else than a number does not compare). A decimal could sit between the
    quotient and its rounding. -/
theorem cmp_agree_avg {op : SqlEquiv.BinOp} {c : CmpOp} (hop : elabBinOp op = .ok (.cmp c))
    {a b : Datum} {a' b' : SqlEquiv.Value} (ha : DatumRel a a') (hat : ∀ q, a ≠ some (.decimal q))
    (hb : AvgRel b b') (hden : ∀ q, b = some (.decimal q) → q.den ≤ 10 ^ SqlEquiv.avgPlaces)
    {d : Datum} (h : SqlCore.evalBinOp (.cmp c) a b = .ok d) :
    ∃ v, SqlEquiv.evalBinOp op (some a') (some b') = some v ∧ DatumRel d v := by
  rcases hb with ⟨rfl, t, rfl⟩ | ⟨q, p, rfl, hp, rfl⟩
  · exact cmp_agree hop ha (show DatumRel none (.null t) from ⟨t, rfl⟩) (fun _ _ x y hxy => by cases hxy.2) h
  · obtain ⟨u', s', he, hq, -⟩ := CorrectAgg.mkDecimal_spec p (roundHalfAway (q * 10 ^ p))
    rw [he]
    have hbr : DatumRel (some (.decimal ((u' : ℚ) / (10 ^ s' : ℕ)))) (.decimal u' s') :=
      ValRel.decimal u' s'
    refine cmp_agree hop ha hbr (fun _ _ x y hxy => by cases hxy.2) ?_
    rw [← h, hq]
    rcases a with _ | x
    · rfl
    · cases x with
      | decimal r => exact absurd rfl (hat r)
      | text t => simp [SqlCore.evalBinOp, CmpOp.eval_some_some, Value.cmp] at h
      | bool t => simp [SqlCore.evalBinOp, CmpOp.eval_some_some, Value.cmp] at h
      | int z =>
      have hden' : q.den ≤ 10 ^ p :=
        (hden q rfl).trans (Nat.pow_le_pow_right (by norm_num) hp)
      simp only [SqlCore.evalBinOp, CmpOp.eval_some_some, Value.cmp, compareDec,
        compare_int_round z q p hden']

end SqlBridge.CorrectAvg
