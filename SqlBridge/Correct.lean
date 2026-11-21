/-
  Elaborator correctness (#309), for the fragment `SELECT e₁, …, eₖ FROM t WHERE p` with literal,
  column, comparison, `AND`, `OR` and `NOT` expressions.

  Typed and untyped values are related, not converted (`ValRel`, `DatumRel`): a typed decimal is a
  rational, an untyped one a scaled integer in any scale, and an untyped `NULL` carries a type tag.

  * Scalars: the untyped comparison, `AND`, `OR` and `NOT` agree with the typed ones on related
    operands, including three-valued `NULL` handling and short-circuiting (`cmp_agree`, …).
  * Expressions: `translates_of_elab` reads the elaborator's output for a fragment expression as a
    `Translates` derivation, and `Translates.eval_rel` shows that on related rows a typed value is
    related to the untyped one. Ordering comparisons of two booleans are excluded (`NoBoolOrder`):
    the typed core orders `false < true`, `SqlEquiv` does not order booleans.
  * Names (#351): the schema may fold names (`NamedSchema.fold`) when it keeps them equal ignoring
    case (`(fold s).toLower = s.toLower`; `id` and `String.toLower`, the Spider schemas' fold, do).
    `SqlEquiv` compares column keys ignoring case, so `rowRel_qualified` holds for any such fold;
    tables are looked up by the name as written, so `DbRel` asks the untyped database to answer
    every spelling the fold maps to a table's key.
-/
import SqlBridge.Elab
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace SqlBridge.Correct

/-- `compare` is determined by `<` and `=`. -/
theorem compare_congr {α β : Type} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (hlt : a < b ↔ c < d) (heq : a = b ↔ c = d) : compare a b = compare c d := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (hlt.mp h)]
  · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr (heq.mp h)]
  · have hcd : d < c := by
      rcases lt_trichotomy c d with h' | h' | h'
      · exact absurd (hlt.mpr h') (not_lt.mpr h.le)
      · exact absurd (heq.mpr h') (ne_of_gt h)
      · exact h'
    rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr hcd]

/-- A scaled integer `u / 10^s` as a rational, rescaled to `10^m` with `s ≤ m`. -/
theorem scaled_eq (u : ℤ) {s m : ℕ} (h : s ≤ m) :
    ((u : ℚ) / (10 ^ s : ℕ)) = ((u * 10 ^ (m - s) : ℤ) : ℚ) / (10 ^ m : ℕ) := by
  have hm : m = s + (m - s) := by omega
  rw [hm, pow_add]
  push_cast
  have h10 : (10 : ℚ) ^ s ≠ 0 := by positivity
  have h10' : (10 : ℚ) ^ (s + (m - s) - s) ≠ 0 := by positivity
  rw [show s + (m - s) - s = m - s by omega]
  field_simp

/-- Untyped decimal comparison (scaled integers) agrees with comparison of the rationals. -/
theorem compare_scaled (u₁ u₂ : ℤ) (s₁ s₂ : ℕ) :
    compare ((u₁ : ℚ) / (10 ^ s₁ : ℕ)) ((u₂ : ℚ) / (10 ^ s₂ : ℕ)) =
      compare (u₁ * 10 ^ (max s₁ s₂ - s₁)) (u₂ * 10 ^ (max s₁ s₂ - s₂)) := by
  rw [scaled_eq u₁ (le_max_left s₁ s₂), scaled_eq u₂ (le_max_right s₁ s₂)]
  have hpos : (0 : ℚ) < (10 ^ max s₁ s₂ : ℕ) := by positivity
  apply compare_congr
  · rw [div_lt_div_iff_of_pos_right hpos]; exact_mod_cast Iff.rfl
  · rw [div_left_inj' hpos.ne']; exact_mod_cast Iff.rfl


/-- Typed and untyped values agree (#309): the same integer, string or boolean, or a decimal
    whose rational value is the untyped scaled integer `u / 10^s` (in any scale). -/
inductive ValRel : SqlCore.Value → SqlEquiv.Value → Prop
  | int (z : ℤ) : ValRel (.int z) (.int z)
  | text (s : String) : ValRel (.text s) (.string s)
  | bool (b : Bool) : ValRel (.bool b) (.bool b)
  | decimal (u : ℤ) (s : ℕ) : ValRel (.decimal ((u : ℚ) / (10 ^ s : ℕ))) (.decimal u s)

/-- A typed datum and an untyped value agree: `NULL` with an untyped `NULL` of any type tag. -/
def DatumRel : SqlCore.Datum → SqlEquiv.Value → Prop
  | none, v => ∃ t, v = .null t
  | some a, v => ValRel a v

theorem isEq_compare_int (a b : ℤ) : (compare a b).isEq = (a == b) := by
  rcases lt_trichotomy a b with h | h | h
  · simp [compare_lt_iff_lt.mpr h, h.ne]
  · simp [h]
  · simp [compare_gt_iff_gt.mpr h, h.ne']

theorem isEq_compare_string (a b : String) : (compare a b).isEq = (a == b) := by
  rw [Bool.eq_iff_iff, Ordering.isEq_iff_eq_eq, beq_iff_eq]
  exact Std.compare_eq_iff_eq

/-- The untyped integer–decimal comparison agrees with the rationals. -/
theorem compare_int_scaled (a u : ℤ) (s : ℕ) :
    compare (a : ℚ) ((u : ℚ) / (10 ^ s : ℕ)) = compare (a * 10 ^ s) u := by
  have h := compare_scaled a u 0 s
  simp only [pow_zero, Nat.cast_one, div_one, Nat.zero_max, Nat.sub_zero, Nat.sub_self,
    mul_one] at h
  exact h

theorem compare_scaled_int (u b : ℤ) (s : ℕ) :
    compare ((u : ℚ) / (10 ^ s : ℕ)) (b : ℚ) = compare u (b * 10 ^ s) := by
  have h := compare_scaled u b s 0
  simp only [pow_zero, Nat.cast_one, div_one, Nat.max_zero, Nat.sub_zero, Nat.sub_self,
    mul_one] at h
  exact h

theorem isEq_iff_compare {α : Type} [LinearOrder α] (a b : α) : (compare a b).isEq = decide (a = b) := by
  rcases lt_trichotomy a b with h | h | h
  · simp [compare_lt_iff_lt.mpr h, h.ne]
  · simp [h]
  · simp [compare_gt_iff_gt.mpr h, h.ne']

open SqlCore in
/-- Untyped equality agrees with the typed comparison's outcome. -/
theorem eq_of_cmp {a b : SqlCore.Value} {a' b' : SqlEquiv.Value} (ha : ValRel a a')
    (hb : ValRel b b') {o : Ordering} (h : Value.cmp a b = .ok o) : a'.eq b' = some o.isEq := by
  cases ha <;> cases hb <;> simp only [Value.cmp, reduceCtorEq] at h <;> cases h <;>
    simp only [SqlEquiv.Value.eq, Option.some.injEq]
  · exact (isEq_compare_int _ _).symm
  · simp only [compareDec]; rw [compare_int_scaled, isEq_compare_int]
  · exact (isEq_compare_string _ _).symm
  · simp only [compareBool]; rename_i x y; cases x <;> cases y <;> rfl
  · simp only [compareDec]; rw [compare_scaled_int, isEq_compare_int]
  · simp only [compareDec]; rw [compare_scaled, isEq_compare_int]

open SqlCore in
/-- Untyped ordering agrees with the typed comparison, except on two booleans. -/
theorem compare_of_cmp {a b : SqlCore.Value} {a' b' : SqlEquiv.Value} (ha : ValRel a a')
    (hb : ValRel b b') (hnb : ∀ x y, ¬ (a = .bool x ∧ b = .bool y)) {o : Ordering}
    (h : Value.cmp a b = .ok o) : a'.compare b' = some o := by
  cases ha <;> cases hb <;> simp only [Value.cmp, reduceCtorEq] at h <;> cases h <;>
    simp only [SqlEquiv.Value.compare, Option.some.injEq]
  · rfl
  · simp only [compareDec]; rw [compare_int_scaled]
  · rfl
  · exact absurd ⟨rfl, rfl⟩ (hnb _ _)
  · simp only [compareDec]; rw [compare_scaled_int]
  · simp only [compareDec]; rw [compare_scaled]


theorem ValRel.ne_null {a : SqlCore.Value} {a' : SqlEquiv.Value} (h : ValRel a a') (t) :
    a' ≠ .null t := by
  cases h <;> simp

/-- The untyped comparison operators on two non-`NULL` values. -/
theorem untyped_cmp_nonnull (op : SqlEquiv.BinOp) {a b : SqlEquiv.Value}
    (ha : ∀ t, a ≠ .null t) (hb : ∀ t, b ≠ .null t) :
    SqlEquiv.evalBinOp op (some a) (some b) =
      match op with
      | .eq => (a.eq b).map SqlEquiv.Value.bool
      | .ne => (a.eq b).map (fun x => SqlEquiv.Value.bool (!x))
      | .lt => (a.compare b).map (fun o => SqlEquiv.Value.bool (o == .lt))
      | .le => (a.compare b).map (fun o => SqlEquiv.Value.bool (o != .gt))
      | .gt => (a.compare b).map (fun o => SqlEquiv.Value.bool (o == .gt))
      | .ge => (a.compare b).map (fun o => SqlEquiv.Value.bool (o != .lt))
      | _ => SqlEquiv.evalBinOp op (some a) (some b) := by
  cases op <;> try rfl
  all_goals cases a <;> cases b <;> simp_all [SqlEquiv.evalBinOp]

open SqlCore in
/-- A comparison: the untyped operator agrees with the typed one on related operands. -/
theorem cmp_agree {op : SqlEquiv.BinOp} {c : CmpOp} (hop : elabBinOp op = .ok (.cmp c))
    {a b : Datum} {a' b' : SqlEquiv.Value} (ha : DatumRel a a') (hb : DatumRel b b')
    (hnb : c ≠ .eq → c ≠ .ne → ∀ x y, ¬ (a = some (.bool x) ∧ b = some (.bool y)))
    {d : Datum} (h : SqlCore.evalBinOp (.cmp c) a b = .ok d) :
    ∃ v, SqlEquiv.evalBinOp op (some a') (some b') = some v ∧ DatumRel d v := by
  cases op <;> simp only [elabBinOp, pure, Except.pure, reduceCtorEq, Except.ok.injEq,
    BinOp.cmp.injEq] at hop <;> subst hop
  all_goals
    rcases a with _ | x
    · obtain ⟨t, rfl⟩ := ha
      simp [SqlCore.evalBinOp, CmpOp.eval, Truth.toDatum] at h
      subst h
      exact ⟨.null none, by cases b' <;> rfl, ⟨none, rfl⟩⟩
    rcases b with _ | y
    · obtain ⟨t, rfl⟩ := hb
      simp [SqlCore.evalBinOp, CmpOp.eval, Truth.toDatum] at h
      subst h
      exact ⟨.null none, by cases a' <;> rfl, ⟨none, rfl⟩⟩
    simp only [DatumRel] at ha hb
    simp only [SqlCore.evalBinOp, CmpOp.eval] at h
    rcases hc : Value.cmp x y with _ | o
    · simp [hc] at h
    simp only [hc, Except.map_ok, Except.ok.injEq] at h
    subst h
    rw [untyped_cmp_nonnull _ ha.ne_null hb.ne_null]
  · exact ⟨_, by rw [eq_of_cmp ha hb hc]; rfl, by cases o <;> exact ValRel.bool _⟩
  · exact ⟨_, by rw [eq_of_cmp ha hb hc]; rfl, by cases o <;> exact ValRel.bool _⟩
  all_goals
    have hcmp := compare_of_cmp ha hb (fun x' y' hxy => hnb (by decide) (by decide) x' y'
      ⟨by rw [hxy.1], by rw [hxy.2]⟩) hc
    exact ⟨_, by rw [hcmp]; rfl, by cases o <;> exact ValRel.bool _⟩


open SqlCore in
/-- A typed operand of a logical operator is `NULL` or a boolean. -/
theorem toTruth_ok_cases {a : Datum} {t : Truth} (h : a.toTruth = .ok t) :
    (a = none ∧ t = .unknown) ∨ ∃ x, a = some (.bool x) ∧ t = .ofBool x := by
  rcases a with _ | (_ | _ | x | _) <;> simp [Datum.toTruth] at h
  · exact .inl ⟨rfl, h.symm⟩
  · exact .inr ⟨x, rfl, h.symm⟩

open SqlCore in
theorem not_agree {a : Datum} {a' : SqlEquiv.Value} (ha : DatumRel a a') {d : Datum}
    (h : evalUnOp .not a = .ok d) :
    ∃ v, SqlEquiv.evalUnaryOp .not (some a') = some v ∧ DatumRel d v := by
  simp only [evalUnOp] at h
  rcases hta : a.toTruth with _ | ta
  · simp [hta] at h
  simp only [hta, Except.map_ok, Except.ok.injEq] at h
  subst h
  rcases toTruth_ok_cases hta with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
  · obtain ⟨t, rfl⟩ := ha
    exact ⟨.null none, rfl, ⟨none, rfl⟩⟩
  · cases ha
    exact ⟨.bool (!x), rfl, by cases x <;> exact ValRel.bool _⟩

open SqlCore in
theorem and_agree {a b : Datum} {a' b' : SqlEquiv.Value} (ha : DatumRel a a')
    (hb : DatumRel b b') {d : Datum} (h : SqlCore.evalBinOp .and a b = .ok d) :
    ∃ v, SqlEquiv.evalBinOp .and (some a') (some b') = some v ∧ DatumRel d v := by
  simp only [SqlCore.evalBinOp] at h
  rcases hta : a.toTruth with _ | ta
  · simp [hta] at h
  rcases htb : b.toTruth with _ | tb
  · simp [hta, htb] at h
  simp only [hta, htb] at h
  cases h
  rcases toTruth_ok_cases hta with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩ <;>
    rcases toTruth_ok_cases htb with ⟨rfl, rfl⟩ | ⟨y, rfl, rfl⟩
  · obtain ⟨t, rfl⟩ := ha; obtain ⟨u, rfl⟩ := hb
    exact ⟨.null none, rfl, ⟨none, rfl⟩⟩
  · obtain ⟨t, rfl⟩ := ha; cases hb
    cases y
    · exact ⟨.bool false, rfl, ValRel.bool _⟩
    · exact ⟨.null none, rfl, ⟨none, rfl⟩⟩
  · cases ha; obtain ⟨u, rfl⟩ := hb
    cases x
    · exact ⟨.bool false, rfl, ValRel.bool _⟩
    · exact ⟨.null none, rfl, ⟨none, rfl⟩⟩
  · cases ha; cases hb
    exact ⟨.bool (x && y), rfl, by cases x <;> cases y <;> exact ValRel.bool _⟩

open SqlCore in
theorem or_agree {a b : Datum} {a' b' : SqlEquiv.Value} (ha : DatumRel a a')
    (hb : DatumRel b b') {d : Datum} (h : SqlCore.evalBinOp .or a b = .ok d) :
    ∃ v, SqlEquiv.evalBinOp .or (some a') (some b') = some v ∧ DatumRel d v := by
  simp only [SqlCore.evalBinOp] at h
  rcases hta : a.toTruth with _ | ta
  · simp [hta] at h
  rcases htb : b.toTruth with _ | tb
  · simp [hta, htb] at h
  simp only [hta, htb] at h
  cases h
  rcases toTruth_ok_cases hta with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩ <;>
    rcases toTruth_ok_cases htb with ⟨rfl, rfl⟩ | ⟨y, rfl, rfl⟩
  · obtain ⟨t, rfl⟩ := ha; obtain ⟨u, rfl⟩ := hb
    exact ⟨.null none, rfl, ⟨none, rfl⟩⟩
  · obtain ⟨t, rfl⟩ := ha; cases hb
    cases y
    · exact ⟨.null none, rfl, ⟨none, rfl⟩⟩
    · exact ⟨.bool true, rfl, ValRel.bool _⟩
  · cases ha; obtain ⟨u, rfl⟩ := hb
    cases x
    · exact ⟨.null none, rfl, ⟨none, rfl⟩⟩
    · exact ⟨.bool true, rfl, ValRel.bool _⟩
  · cases ha; cases hb
    exact ⟨.bool (x || y), rfl, by cases x <;> cases y <;> exact ValRel.bool _⟩


/-! ### Expressions -/

section Exprs
open SqlCore

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String)

/-- The typed expression elaborates the untyped one, in the fragment of #309: literals, columns,
    comparisons, `AND`, `OR`, `NOT` and (roadmap step 4) `BETWEEN`. `retypeNull` only gives an untyped `NULL` operand a type. -/
inductive Translates : SqlEquiv.Expr → Expr n → Prop
  | lit {v : SqlEquiv.Value} {w : Value} : elabValue v = some w → Translates (.lit v) (.lit w)
  | litNull {v : SqlEquiv.Value} (τ : SqlType) : elabValue v = none →
      Translates (.lit v) (.null τ)
  | col {c : SqlEquiv.ColumnRef} {i : Fin n} :
      resolveColumn cols (c.table.map fold) (fold c.column) = .ok i →
      Translates (.col c) (.col i)
  | cmp {op : SqlEquiv.BinOp} {c : CmpOp} {a b : SqlEquiv.Expr} {a' b' : Expr n} :
      elabBinOp op = .ok (.cmp c) → Translates a a' → Translates b b' →
      Translates (.binOp op a b) (.binary (.cmp c) (retypeNull cols a' b') (retypeNull cols b' a'))
  | and {a b : SqlEquiv.Expr} {a' b' : Expr n} : Translates a a' → Translates b b' →
      Translates (.binOp .and a b) (.binary .and (retypeNull cols a' b') (retypeNull cols b' a'))
  | or {a b : SqlEquiv.Expr} {a' b' : Expr n} : Translates a a' → Translates b b' →
      Translates (.binOp .or a b) (.binary .or (retypeNull cols a' b') (retypeNull cols b' a'))
  | not {a : SqlEquiv.Expr} {a' : Expr n} : Translates a a' →
      Translates (.unaryOp .not a) (.unary .not a')
  /-- `e BETWEEN lo AND hi` (roadmap step 4): both evaluators read it as `e >= lo AND e <= hi`. -/
  | between {e lo hi : SqlEquiv.Expr} {e' lo' hi' : Expr n} :
      Translates e e' → Translates lo lo' → Translates hi hi' →
      Translates (.between e lo hi)
        (.binary .and (.binary (.cmp .ge) e' (retypeNull cols lo' e'))
          (.binary (.cmp .le) e' (retypeNull cols hi' e')))

/-- No ordering comparison (`<`, `<=`, `>`, `>=`) has boolean operands: the typed core orders
    `false < true`, `SqlEquiv` does not order booleans (#309 excludes this case). -/
def NoBoolOrder (Γ : Fin n → SqlType) : Expr n → Prop
  | .binary (.cmp c) a b =>
    (c = .eq ∨ c = .ne ∨ ∃ τ, a.typeOf Γ = some τ ∧ τ ≠ .bool) ∧ NoBoolOrder Γ a ∧ NoBoolOrder Γ b
  | .binary _ a b => NoBoolOrder Γ a ∧ NoBoolOrder Γ b
  | .unary _ a => NoBoolOrder Γ a
  | _ => True

/-- No argument of an aggregate call orders booleans (see `NoBoolOrder`). -/
def AggNoBool (Γ : Fin n → SqlType) : AggCall n → Prop
  | .countStar => True
  | .call _ _ e => NoBoolOrder Γ e
  | .first e => NoBoolOrder Γ e
  | .atExtreme _ k e => NoBoolOrder Γ k ∧ NoBoolOrder Γ e

/-- An untyped row agrees with a typed one: every column the elaborator resolves reads a related
    value through `SqlEquiv`'s lookup. -/
def RowRel (r : Row n) (u : SqlEquiv.Row) : Prop :=
  ∀ (q : Option String) (name : String) (i : Fin n), resolveColumn cols (q.map fold) (fold name) = .ok i →
    ∃ v, u.getQualified q name = some v ∧ DatumRel (r i) v

theorem eval_retypeNull (e o : Expr n) (r : Row n) :
    (retypeNull cols e o).eval r = e.eval r := by
  unfold retypeNull
  split <;> rfl

theorem noBoolOrder_retypeNull {Γ : Fin n → SqlType} {e : Expr n} (o : Expr n)
    (h : NoBoolOrder Γ e) : NoBoolOrder Γ (retypeNull cols e o) := by
  unfold retypeNull
  split
  · trivial
  · exact h

theorem noBoolOrder_of_retypeNull {Γ : Fin n → SqlType} {e : Expr n} (o : Expr n)
    (h : NoBoolOrder Γ (retypeNull cols e o)) : NoBoolOrder Γ e := by
  unfold retypeNull at h
  split at h
  · trivial
  · exact h

/-- A binary expression that evaluates: both operands evaluate, and the operator applies. -/
theorem eval_binary_ok {op : BinOp} {a b : Expr n} {r : Row n} {d : Datum}
    (h : (Expr.binary op a b).eval r = .ok d) :
    ∃ da db, a.eval r = .ok da ∧ b.eval r = .ok db ∧ evalBinOp op da db = .ok d := by
  simp only [Expr.eval_binary] at h
  rcases hea : a.eval r with _ | da
  · simp [hea, bind, Except.bind] at h
  rcases heb : b.eval r with _ | db
  · simp [hea, heb, bind, Except.bind] at h
  simp only [hea, heb, bind, Except.bind] at h
  exact ⟨da, db, rfl, rfl, h⟩

theorem eval_unary_ok {op : UnOp} {a : Expr n} {r : Row n} {d : Datum}
    (h : (Expr.unary op a).eval r = .ok d) :
    ∃ da, a.eval r = .ok da ∧ evalUnOp op da = .ok d := by
  simp only [Expr.eval_unary] at h
  rcases hea : a.eval r with _ | da
  · simp [hea, bind, Except.bind] at h
  simp only [hea, bind, Except.bind] at h
  exact ⟨da, rfl, h⟩

theorem valRel_of_elabValue {v : SqlEquiv.Value} {w : Value} (h : elabValue v = some w) :
    ValRel w v := by
  cases v <;> simp only [elabValue, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact .int _
  · exact .text _
  · exact .bool _
  · exact .decimal _ _

/-- The expression theorem of #309: on related rows, a typed expression that evaluates gives a
    value related to the untyped expression's. -/
theorem Translates.eval_rel {Γ : Fin n → SqlType} (db : SqlEquiv.Database) {r : Row n}
    {u : SqlEquiv.Row} (hrow : RowRel cols fold r u) (hr : r.Conforms Γ) :
    ∀ {e : SqlEquiv.Expr} {e' : Expr n}, Translates cols fold e e' → NoBoolOrder Γ e' →
      ∀ {d : Datum}, e'.eval r = .ok d →
        ∃ v, SqlEquiv.evalExprWithDb db u e = some v ∧ DatumRel d v := by
  intro e e' ht
  induction ht with
  | lit hw =>
    intro _ d h
    cases h
    exact ⟨_, SqlEquiv.evalExprWithDb_lit .., valRel_of_elabValue hw⟩
  | @litNull v τ hw =>
    intro _ d h
    cases h
    cases v <;> simp [elabValue] at hw
    exact ⟨_, SqlEquiv.evalExprWithDb_lit .., ⟨_, rfl⟩⟩
  | col hres =>
    intro _ d h
    cases h
    obtain ⟨v, hv, hrel⟩ := hrow _ _ _ hres
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_col, hv], hrel⟩
  | @cmp op c a b a' b' hop _ _ iha ihb =>
    intro hnb d h
    obtain ⟨hc, hna, hnb'⟩ := hnb
    obtain ⟨da, db', hea, heb, hd⟩ := eval_binary_ok h
    have hea' := hea; have heb' := heb
    rw [eval_retypeNull] at hea' heb'
    obtain ⟨va, hva, hra⟩ := iha (noBoolOrder_of_retypeNull cols b' hna) hea'
    obtain ⟨vb, hvb, hrb⟩ := ihb (noBoolOrder_of_retypeNull cols a' hnb') heb'
    obtain ⟨v, hv, hrel⟩ := cmp_agree hop hra hrb (fun h1 h2 x y hxy => by
      rcases hc with hc | hc | ⟨τ, hτ, hτb⟩
      · exact h1 hc
      · exact h2 hc
      · rcases Expr.eval_ok_or_divisionByZero hr hτ with ⟨d', hd', hty⟩ | ⟨hdz, _⟩
        · rw [hea] at hd'; cases hd'
          rw [hxy.1] at hty
          exact hτb (by simpa [Datum.HasType, Value.type] using hty.symm)
        · rw [hea] at hdz; cases hdz) hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_binOp, hva, hvb, hv], hrel⟩
  | and _ _ iha ihb =>
    intro hnb d h
    obtain ⟨hna, hnb'⟩ := hnb
    obtain ⟨da, db', hea, heb, hd⟩ := eval_binary_ok h
    rw [eval_retypeNull] at hea heb
    obtain ⟨va, hva, hra⟩ := iha (noBoolOrder_of_retypeNull cols _ hna) hea
    obtain ⟨vb, hvb, hrb⟩ := ihb (noBoolOrder_of_retypeNull cols _ hnb') heb
    obtain ⟨v, hv, hrel⟩ := and_agree hra hrb hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_binOp, hva, hvb, hv], hrel⟩
  | or _ _ iha ihb =>
    intro hnb d h
    obtain ⟨hna, hnb'⟩ := hnb
    obtain ⟨da, db', hea, heb, hd⟩ := eval_binary_ok h
    rw [eval_retypeNull] at hea heb
    obtain ⟨va, hva, hra⟩ := iha (noBoolOrder_of_retypeNull cols _ hna) hea
    obtain ⟨vb, hvb, hrb⟩ := ihb (noBoolOrder_of_retypeNull cols _ hnb') heb
    obtain ⟨v, hv, hrel⟩ := or_agree hra hrb hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_binOp, hva, hvb, hv], hrel⟩
  | not _ iha =>
    intro hn d h
    obtain ⟨da, hea, hd⟩ := eval_unary_ok h
    obtain ⟨va, hva, hra⟩ := iha hn hea
    obtain ⟨v, hv, hrel⟩ := not_agree hra hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_unaryOp, hva, hv], hrel⟩
  | @between e lo hi e' lo' hi' _ _ _ ihe ihlo ihhi =>
    intro hnb d h
    obtain ⟨⟨hc₁, hne, hnlo⟩, ⟨hc₂, -, hnhi⟩⟩ := hnb
    obtain ⟨d₁, d₂, h₁, h₂, hd⟩ := eval_binary_ok h
    obtain ⟨de, dlo, hee, helo, hd₁⟩ := eval_binary_ok h₁
    obtain ⟨de', dhi, hee', hehi, hd₂⟩ := eval_binary_ok h₂
    rw [hee, Except.ok.injEq] at hee'; subst hee'
    rw [eval_retypeNull] at helo hehi
    obtain ⟨ve, hve, hre⟩ := ihe hne hee
    obtain ⟨vlo, hvlo, hrlo⟩ := ihlo (noBoolOrder_of_retypeNull cols e' hnlo) helo
    obtain ⟨vhi, hvhi, hrhi⟩ := ihhi (noBoolOrder_of_retypeNull cols e' hnhi) hehi
    -- an ordering comparison: the operand `e'` is not boolean
    have hnobool : ∀ (hc : CmpOp.ge = .eq ∨ CmpOp.ge = .ne ∨ ∃ τ, e'.typeOf Γ = some τ ∧ τ ≠ .bool)
        (x y : Bool) (o : Datum), ¬ (de = some (.bool x) ∧ o = some (.bool y)) := by
      intro hc x y o hxy
      rcases hc with hc | hc | ⟨τ, hτ, hτb⟩
      · cases hc
      · cases hc
      · rcases Expr.eval_ok_or_divisionByZero hr hτ with ⟨d', hd', hty⟩ | ⟨hdz, _⟩
        · rw [hee] at hd'; cases hd'
          rw [hxy.1] at hty
          exact hτb (by simpa [Datum.HasType, Value.type] using hty.symm)
        · rw [hee] at hdz; cases hdz
    have hc₂' : CmpOp.ge = .eq ∨ CmpOp.ge = .ne ∨ ∃ τ, e'.typeOf Γ = some τ ∧ τ ≠ .bool := by
      rcases hc₂ with hc | hc | h3
      · cases hc
      · cases hc
      · exact .inr (.inr h3)
    obtain ⟨v₁, hv₁, hr₁⟩ := cmp_agree (op := .ge) rfl hre hrlo
      (fun _ _ x y => hnobool hc₁ x y dlo) hd₁
    obtain ⟨v₂, hv₂, hr₂⟩ := cmp_agree (op := .le) rfl hre hrhi
      (fun _ _ x y => hnobool hc₂' x y dhi) hd₂
    obtain ⟨v, hv, hrel⟩ := and_agree hr₁ hr₂ hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_between]; simp only [hve, hvlo, hvhi, hv₁, hv₂, hv],
      hrel⟩

/-- The untyped expressions of the #309 fragment: literals, columns, comparisons, `AND`, `OR`,
    `NOT` and (roadmap step 4) `BETWEEN`. -/
def isFragment : SqlEquiv.Expr → Bool
  | .lit _ => true
  | .col _ => true
  | .binOp op a b =>
    (match op with
     | .eq | .ne | .lt | .le | .gt | .ge | .and | .or => true
     | _ => false) && isFragment a && isFragment b
  | .unaryOp .not a => isFragment a
  | .between e lo hi => isFragment e && isFragment lo && isFragment hi
  | _ => false

/-- Elaborating a fragment expression (without a hook, names folded by `fold`) gives a translation. -/
theorem translates_of_elab : ∀ (e : SqlEquiv.Expr) {e' : Expr n}, isFragment e = true →
    elabExpr cols fold noHook e = .ok e' → Translates cols fold e e'
  | .lit v, e', _, h => by
    unfold elabExpr at h
    simp only [noHook] at h
    cases v <;> simp only [elabValue, pure, Except.pure, Except.ok.injEq] at h <;> subst h
    · exact .lit rfl
    · exact .lit rfl
    · exact .lit rfl
    · exact .lit rfl
    · exact .litNull _ rfl
  | .col c, e', _, h => by
    simp only [elabExpr, noHook, resolve] at h
    rcases hr : resolveColumn cols (c.table.map fold) (fold c.column) with _ | i
    · rename_i err
      cases err <;> simp [hr, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · rw [hr] at h
      simp only [pure, Except.pure] at h
      cases h
      exact .col hr
  | .binOp op a b, e', hf, h => by
    simp only [isFragment, Bool.and_eq_true] at hf
    obtain ⟨⟨hop, ha⟩, hb⟩ := hf
    simp only [elabExpr, noHook] at h
    rcases hea : elabExpr cols fold noHook a with _ | a'
    · cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure]
    rcases heb : elabExpr cols fold noHook b with _ | b'
    · cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure]
    have ta := translates_of_elab a ha hea
    have tb := translates_of_elab b hb heb
    cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure] <;> subst h
    · exact .cmp rfl ta tb
    · exact .cmp rfl ta tb
    · exact .cmp rfl ta tb
    · exact .cmp rfl ta tb
    · exact .cmp rfl ta tb
    · exact .cmp rfl ta tb
    · exact .and ta tb
    · exact .or ta tb
  | .unaryOp op a, e', hf, h => by
    cases op <;> simp only [isFragment, Bool.false_eq_true] at hf
    simp only [elabExpr, noHook] at h
    rcases hea : elabExpr cols fold noHook a with _ | a'
    · simp [hea, bind, Except.bind] at h
    simp only [hea, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .not (translates_of_elab a hf hea)
  | .func _ _, _, hf, _ | .agg _ _ _, _, hf, _ | .countStar, _, hf, _
  | .«case» _ _, _, hf, _ | .inList _ _ _, _, hf, _ | .inSubquery _ _ _, _, hf, _
  | .exists _ _, _, hf, _ | .subquery _, _, hf, _
  | .windowFn _ _ _, _, hf, _ => by simp [isFragment] at hf
  | .between x lo hi, e', hf, h => by
    simp only [isFragment, Bool.and_eq_true] at hf
    obtain ⟨⟨hx, hlo⟩, hhi⟩ := hf
    simp only [elabExpr, noHook] at h
    rcases hex : elabExpr cols fold noHook x with _ | x'
    · simp [hex, bind, Except.bind] at h
    rcases helo : elabExpr cols fold noHook lo with _ | lo'
    · simp [hex, helo, bind, Except.bind] at h
    rcases hehi : elabExpr cols fold noHook hi with _ | hi'
    · simp [hex, helo, hehi, bind, Except.bind] at h
    simp only [hex, helo, hehi, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .between (translates_of_elab x hx hex) (translates_of_elab lo hlo helo)
      (translates_of_elab hi hhi hehi)

end Exprs


/-! ### Column lookup -/

section Lookup
open SqlCore

theorem endsWith_iff_suffix (s p : String) : s.endsWith p = true ↔ p.toList <:+ s.toList := by
  have : s.endsWith p = s.toSlice.endsWith p := rfl
  rw [this, String.Slice.endsWith_string_iff]; simp

theorem toList_toLower (s : String) : s.toLower.toList = s.toList.map Char.toLower := by
  simp [String.toLower, String.toList_map]

theorem toList_qualified (Q c : String) : (s!"{Q}.{c}").toList = Q.toList ++ '.' :: c.toList := by
  simp [toString]

theorem toList_dot : ".".toList = ['.'] := by decide

theorem toLower_dot : Char.toLower '.' = '.' := by decide

theorem eq_dot_of_toLower (c : Char) (h : c.toLower = '.') : c = '.' := by
  unfold Char.toLower at h; split at h
  · rename_i hc; have := congrArg Char.val h; simp at this hc
    exfalso
    have h1 := congrArg UInt32.toNat this
    rw [UInt32.toNat_add] at h1
    have h2 : (65:UInt32).toNat ≤ c.val.toNat := hc.1
    have h3 : c.val.toNat ≤ (90:UInt32).toNat := hc.2
    simp at h1 h2 h3; omega
  · exact h

theorem dot_not_mem_map_toLower {l : List Char} (h : '.' ∉ l) : '.' ∉ l.map Char.toLower := by
  simp only [List.mem_map, not_exists, not_and]
  intro c hc he; exact h (eq_dot_of_toLower c he ▸ hc)

/-- The part after the last dot is determined. -/
theorem eq_of_append_dot {a b : List Char} (ha : '.' ∉ a) (hb : '.' ∉ b) :
    ∀ {l t : List Char}, l ++ '.' :: a = t ++ '.' :: b → a = b
  | [], [], h => by simpa using h
  | [], x :: t, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.2 ▸ List.mem_append_right t List.mem_cons_self) ha
  | x :: l, [], h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.2 ▸ List.mem_append_right l List.mem_cons_self) hb
  | x :: l, y :: t, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    exact eq_of_append_dot ha hb h.2

theorem lookupCI_eq_find? (u : SqlEquiv.Row) (key : String) :
    u.lookupCI key = (u.find? fun kv => kv.1.toLower == key.toLower).map (·.2) := by
  induction u with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k, v⟩ := kv
    by_cases h : k.toLower = key.toLower <;> simp [SqlEquiv.Row.lookupCI, h, ih]

theorem find?_ofFn_of_unique {α : Type _} {m : ℕ} (f : Fin m → α) (p : α → Bool) (i : Fin m)
    (hi : p (f i) = true) (hu : ∀ j, p (f j) = true → j = i) :
    (List.ofFn f).find? p = some (f i) := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨hi, i.1, by simp, by simp, fun j hj => ?_⟩
  have hjm : j < m := by omega
  simp only [List.getElem_ofFn, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.eq_false_iff]
  intro hp
  have := hu ⟨j, hjm⟩ hp
  simp [Fin.ext_iff] at this; omega

theorem char_toLower_toLower (c : Char) : c.toLower.toLower = c.toLower := by
  unfold Char.toLower
  split
  · rename_i hc
    split
    · rename_i hc2
      exfalso
      simp only [ge_iff_le, UInt32.le_iff_toNat_le] at hc hc2
      rw [UInt32.toNat_add] at hc2
      simp at hc hc2
      omega
    · rfl
  · rfl

/-- Lowercasing is idempotent, so `String.toLower` is a fold `rowRel_qualified` accepts. -/
theorem string_toLower_toLower (s : String) : s.toLower.toLower = s.toLower := by
  apply String.toList_inj.mp
  simp [toList_toLower, List.map_map, Function.comp_def, char_toLower_toLower]

/-- Rows as `evalFrom` builds them for a base table: the key of column `j` is `Q.name_j`, with `Q`
the table name or alias as written. On such rows a column reference the elaborator resolves
(names and qualifier folded by `fold`, the typed columns qualified by `fold Q`) finds the related
value, provided column names have no dots and are distinct ignoring case, and `fold` keeps a name
equal to itself ignoring case (`id` and `String.toLower` do; #351). -/
theorem rowRel_qualified {m : ℕ} (fold : String → String)
    (hfold : ∀ s, (fold s).toLower = s.toLower) (Q : String) (base : Fin m → Column) (r : Row m)
    (w : Fin m → SqlEquiv.Value) (hw : ∀ j, DatumRel (r j) (w j))
    (hdot : ∀ j, '.' ∉ (base j).name.toList)
    (hnd : ∀ j k, (base j).name.toLower = (base k).name.toLower → j = k) :
    RowRel (requalify (fold Q) base) fold r
      (List.ofFn fun j => (s!"{Q}.{(base j).name}", w j)) := by
  intro q name i hres
  have hm := (resolveColumn_eq_ok_iff.mp hres).1
  have hname : (base i).name = fold name := by
    cases q <;> simp_all [requalify, Column.Matches]
  -- the reference names column `i` up to case
  have hnl : name.toLower = (base i).name.toLower := by
    rw [hname, hfold]
  refine ⟨w i, ?_, hw i⟩
  have hlow : ∀ j, (base j).name.toList.map Char.toLower = (base i).name.toList.map Char.toLower →
      j = i := fun j h => hnd j i (String.toList_inj.mp (by simpa [toList_toLower] using h))
  cases q with
  | some q' =>
    have hq : q'.toLower = Q.toLower := by
      have : fold Q = fold q' := by simpa [requalify, Column.Matches] using hm.2
      rw [← hfold q', ← this, hfold]
    have hkey : (s!"{q'}.{name}").toLower = (s!"{Q}.{(base i).name}").toLower := by
      apply String.toList_inj.mp
      have h1 := congrArg String.toList hq
      have h2 := congrArg String.toList hnl
      simp only [toList_toLower] at h1 h2
      simp only [toList_toLower, toList_qualified, List.map_append, List.map_cons, toLower_dot,
        h1, h2]
    simp only [SqlEquiv.Row.getQualified, lookupCI_eq_find?]
    rw [hkey, find?_ofFn_of_unique _ _ i]
    · rfl
    · simp
    · intro j hj
      apply hlow j
      have := String.toList_inj.mpr (beq_iff_eq.mp hj)
      simp only [toList_toLower, toList_qualified, List.map_append, List.map_cons] at this
      have := List.append_cancel_left this
      simpa using this
  | none =>
    simp only [SqlEquiv.Row.getQualified]
    rw [hnl]
    have hd := dot_not_mem_map_toLower (hdot i)
    rw [find?_ofFn_of_unique _ _ i]
    · simp only [Bool.or_eq_true, endsWith_iff_suffix]
      right
      simp only [toString, String.toList_append, toList_toLower, List.map_append, toList_dot, List.map_cons, toLower_dot, List.append_assoc, List.singleton_append]
      exact List.suffix_append _ _
    · intro j hj
      simp only [Bool.or_eq_true, beq_iff_eq, endsWith_iff_suffix] at hj
      rcases hj with h | ⟨t, ht⟩
      · have := congrArg String.toList h
        simp only [toString, String.toList_append, toList_toLower, List.map_append,
          toList_dot, List.map_cons, toLower_dot, List.append_assoc, List.singleton_append] at this
        exact absurd (this ▸ List.mem_append_right _ List.mem_cons_self) hd
      · simp only [toString, String.toList_append, toList_toLower, List.map_append,
          toList_dot, List.map_cons, toLower_dot, List.append_assoc, List.singleton_append] at ht
        exact hlow j (eq_of_append_dot (dot_not_mem_map_toLower (hdot j)) hd ht.symm)
end Lookup

/-! ### Statements -/

theorem aggsOf_frag : ∀ e, isFragment e = true → aggsOf e = []
  | .lit _, _ => by simp [aggsOf]
  | .col _, _ => by simp [aggsOf]
  | .binOp op a b, h => by
    simp only [isFragment, Bool.and_eq_true] at h
    simp [aggsOf, aggsOf_frag a h.1.2, aggsOf_frag b h.2]
  | .unaryOp .not a, h => by simp [aggsOf, aggsOf_frag a (by simpa [isFragment] using h)]
  | .unaryOp .neg _, h | .unaryOp .isNull _, h | .unaryOp .isNotNull _, h => by simp [isFragment] at h
  | .func .., h | .agg .., h | .countStar, h | .«case» .., h | .inList .., h | .inSubquery .., h
  | .exists .., h | .subquery .., h | .windowFn .., h => by simp [isFragment] at h
  | .between x lo hi, h => by
    simp only [isFragment, Bool.and_eq_true] at h
    simp [aggsOf, aggsOf_frag x h.1.1, aggsOf_frag lo h.1.2, aggsOf_frag hi h.2]

def itemsFragment : List SqlEquiv.SelectItem → Bool
  | [] => true
  | .exprItem e _ :: rest => isFragment e && itemsFragment rest
  | .star _ :: _ => false

theorem subsOf_frag : ∀ e, isFragment e = true → subsOf e = []
  | .lit _, _ => by simp [subsOf]
  | .col _, _ => by simp [subsOf]
  | .binOp op a b, h => by
    simp only [isFragment, Bool.and_eq_true] at h
    simp [subsOf, subsOf_frag a h.1.2, subsOf_frag b h.2]
  | .unaryOp .not a, h => by simp [subsOf, subsOf_frag a (by simpa [isFragment] using h)]
  | .unaryOp .neg _, h | .unaryOp .isNull _, h | .unaryOp .isNotNull _, h => by simp [isFragment] at h
  | .func .., h | .agg .., h | .countStar, h | .«case» .., h | .inList .., h | .inSubquery .., h
  | .exists .., h | .subquery .., h | .windowFn .., h => by simp [isFragment] at h
  | .between x lo hi, h => by
    simp only [isFragment, Bool.and_eq_true] at h
    simp [subsOf, subsOf_frag x h.1.1, subsOf_frag lo h.1.2, subsOf_frag hi h.2]

theorem aggsOfList_items {f : SqlEquiv.SelectItem → Option SqlEquiv.Expr}
    (hf : ∀ e al, f (.exprItem e al) = some e) : ∀ items, itemsFragment items = true →
    aggsOfList (items.filterMap f) = []
  | [], _ => by simp [aggsOfList]
  | .exprItem e _ :: rest, h => by
    simp only [itemsFragment, Bool.and_eq_true] at h
    simp [hf, aggsOfList, aggsOf_frag e h.1, aggsOfList_items hf rest h.2]
  | .star _ :: _, h => by simp [itemsFragment] at h

/-! ### Queries -/

section Query
open SqlCore

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String)

/-- An output row: the typed cells relate, in order, to the untyped values; names are dropped. -/
def OutRel {k : ℕ} (d : Row k) (u : SqlEquiv.Row) : Prop :=
  List.Forall₂ DatumRel (List.ofFn d) (u.map (·.2))

theorem divSafe_retypeNull (e o : Expr n) : (retypeNull cols e o).divSafe = e.divSafe := by
  unfold retypeNull; split <;> simp [Expr.divSafe]

theorem Translates.divSafe {e : SqlEquiv.Expr} {e' : Expr n} (h : Translates cols fold e e') :
    e'.divSafe = true := by
  induction h <;> simp_all [Expr.divSafe, divSafe_retypeNull, BinOp.isDivision]

/-- Whether a typed truth value is `TRUE` agrees with the untyped `WHERE` test. -/
theorem isTrue_iff_where {d : Datum} {v : SqlEquiv.Value} (hv : DatumRel d v) {t : Truth}
    (ht : d.toTruth = .ok t) : t.isTrue = (some v == some (SqlEquiv.Value.bool true)) := by
  rcases toTruth_ok_cases ht with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
  · obtain ⟨τ, rfl⟩ := hv
    rfl
  · cases hv
    cases x <;> rfl

theorem filterRows_cons_ok {p : Expr n} {r : Row n} {R R' : List (Row n)}
    (h : p.filterRows (r :: R) = .ok R') :
    ∃ t R'', p.evalTruth r = .ok t ∧ p.filterRows R = .ok R'' ∧
      R' = if t.isTrue then r :: R'' else R'' := by
  unfold Expr.filterRows at h ⊢
  generalize hF : (fun r => do return if (← p.evalTruth r).isTrue then some r else none :
    Row n → Except EvalError (Option (Row n))) = F at h ⊢
  rw [List.filterMapM_cons] at h
  rcases hte : p.evalTruth r with e | t
  · have hFr : F r = .error e := by rw [← hF]; simp [hte, bind, Except.bind]
    rw [hFr] at h; simp [bind, Except.bind] at h
  have hFr : F r = .ok (if t.isTrue then some r else none) := by
    rw [← hF]; simp [hte, bind, Except.bind, pure, Except.pure]
  rcases hrs : List.filterMapM F R with _ | R''
  · rw [hFr, hrs] at h
    cases hb : t.isTrue <;> simp only [hb] at h <;> simp [bind, Except.bind] at h
  · refine ⟨t, R'', rfl, rfl, ?_⟩
    rw [hFr, hrs] at h
    cases hb : t.isTrue <;> simp only [hb] at h ⊢ <;>
      simp [bind, Except.bind, pure, Except.pure] at h ⊢ <;> exact h.symm

theorem filter_rel (db : SqlEquiv.Database) {Γ : Fin n → SqlType} {w : SqlEquiv.Expr} {p : Expr n}
    (ht : Translates cols fold w p) (hnb : NoBoolOrder Γ p) :
    ∀ {R : List (Row n)} {U : List SqlEquiv.Row},
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U →
      ∀ {R' : List (Row n)}, p.filterRows R = .ok R' →
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R'
        (U.filter fun u => SqlEquiv.evalExprWithDb db u w == some (.bool true))
  | _, _, .nil, R', h => by
    simp only [Expr.filterRows, List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | r :: R, u :: U, .cons hru hrest, R', h => by
    obtain ⟨t, R'', hte, hrs, rfl⟩ := filterRows_cons_ok h
    have ih := filter_rel db ht hnb hrest hrs
    have hev : ∃ d, p.eval r = .ok d ∧ d.toTruth = .ok t := by
      unfold Expr.evalTruth at hte
      rcases he : p.eval r with _ | d
      · simp [he, bind, Except.bind] at hte
      · simp only [he, bind, Except.bind] at hte
        exact ⟨d, rfl, hte⟩
    obtain ⟨d, hd, hdt⟩ := hev
    obtain ⟨v, hv, hrel⟩ := Translates.eval_rel cols fold db hru.1 hru.2 ht hnb hd
    have key := isTrue_iff_where hrel hdt
    rw [← hv] at key
    simp only [List.filter_cons, ← key]
    cases t.isTrue
    · exact ih
    · exact .cons hru ih

/-- The `SELECT` items and their elaborations: each item is an expression that translates. -/
def ItemsRel (items : List SqlEquiv.SelectItem) (its : List (Expr n × Column)) : Prop :=
  List.Forall₂ (fun it x => ∃ e al, it = .exprItem e al ∧ Translates cols fold e x.1) items its

/-- The value `SqlEquiv` gives an expression item; an error becomes `NULL`. -/
def itemValue (db : SqlEquiv.Database) (u : SqlEquiv.Row) : SqlEquiv.SelectItem → SqlEquiv.Value
  | .exprItem e _ => (SqlEquiv.evalExprWithDb db u e).getD (.null none)
  | .star _ => .null none

theorem map_snd_flatMap_items (db : SqlEquiv.Database) (u : SqlEquiv.Row) :
    ∀ {items its}, ItemsRel cols fold items its →
      (items.flatMap (SqlEquiv.evalSelectItem db u)).map (·.2) = items.map (itemValue db u)
  | _, _, .nil => rfl
  | _, _, .cons ⟨e, al, rfl, _⟩ rest => by
    simp only [List.flatMap_cons, List.map_append, List.map_cons, map_snd_flatMap_items db u rest]
    simp only [SqlEquiv.evalSelectItem, itemValue]
    split <;> simp_all

theorem row_rel (db : SqlEquiv.Database) {Γ : Fin n → SqlType} {r : Row n} {u : SqlEquiv.Row}
    (hrow : RowRel cols fold r u) (hr : r.Conforms Γ) {items : List SqlEquiv.SelectItem}
    {its : List (Expr n × Column)} (hits : ItemsRel cols fold items its)
    (hnb : ∀ i : Fin its.length, NoBoolOrder Γ (its[i]).1) {d : Row its.length}
    (hd : Expr.evalRow (fun i : Fin its.length => (its[i]).1) r = .ok d) :
    OutRel d (items.flatMap (SqlEquiv.evalSelectItem db u)) := by
  unfold OutRel
  rw [map_snd_flatMap_items cols fold db u hits, List.forall₂_iff_get]
  have hlen := hits.length_eq
  refine ⟨by simp [hlen], fun i h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
  have hi : i < its.length := by simpa using h1
  obtain ⟨e, al, hit, htr⟩ := (List.forall₂_iff_get.mp hits).2 i (by omega) hi
  simp only [List.get_eq_getElem] at hit htr
  rw [hit]
  have hev := (Expr.evalRow_eq_ok_iff.mp hd) ⟨i, hi⟩
  obtain ⟨v, hv, hrel⟩ := Translates.eval_rel cols fold db hrow hr htr (hnb ⟨i, hi⟩) hev
  simpa [itemValue, hv] using hrel

theorem project_rel (db : SqlEquiv.Database) {Γ : Fin n → SqlType}
    {items : List SqlEquiv.SelectItem} {its : List (Expr n × Column)}
    (hits : ItemsRel cols fold items its) (hnb : ∀ i : Fin its.length, NoBoolOrder Γ (its[i]).1) :
    ∀ {R : List (Row n)} {U : List SqlEquiv.Row},
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U →
      ∀ {out}, R.mapM (Expr.evalRow fun i : Fin its.length => (its[i]).1) = .ok out →
      List.Forall₂ OutRel out (U.map fun u => items.flatMap (SqlEquiv.evalSelectItem db u))
  | _, _, .nil, out, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | r :: R, u :: U, .cons hru hrest, out, h => by
    rw [List.mapM_cons] at h
    rcases hd : Expr.evalRow (fun i : Fin its.length => (its[i]).1) r with _ | d
    · rw [hd] at h; simp [bind, Except.bind] at h
    rcases hR : R.mapM (Expr.evalRow fun i : Fin its.length => (its[i]).1) with _ | out'
    · rw [hd, hR] at h; simp [bind, Except.bind] at h
    rw [hd, hR] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .cons (row_rel cols fold db hru.1 hru.2 hits hnb hd) (project_rel db hits hnb hrest hR)

theorem itemsRel_of_elab (N : NamedSchema) :
    ∀ (items : List SqlEquiv.SelectItem) {its : List (Expr n × Column)},
      itemsFragment items = true → elabItems N cols items = .ok its → ItemsRel cols N.fold items its
  | [], its, _, h => by
    simp only [elabItems, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | .exprItem e al :: rest, its, hf, h => by
    simp only [itemsFragment, Bool.and_eq_true] at hf
    simp only [elabItems] at h
    rcases he : elabExpr cols N.fold noHook e with _ | e'
    · simp [he, bind, Except.bind] at h
    rcases hτ : e'.typeOf (ctx cols) with _ | τ
    · simp [he, hτ, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    rcases hr : elabItems N cols rest with _ | its'
    · simp [he, hτ, hr, bind, Except.bind] at h
    simp only [he, hτ, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .cons ⟨e, al, rfl, translates_of_elab cols N.fold e hf.1 he⟩ (itemsRel_of_elab N rest hf.2 hr)
  | .star _ :: _, _, hf, _ => by simp [itemsFragment] at hf

end Query

section Statement
open SqlCore

theorem hasAggregate_frag : ∀ e, isFragment e = true → SqlEquiv.hasAggregate e = false
  | .lit _, _ => by simp [SqlEquiv.hasAggregate]
  | .col _, _ => by simp [SqlEquiv.hasAggregate]
  | .binOp op a b, h => by
    simp only [isFragment, Bool.and_eq_true] at h
    simp [SqlEquiv.hasAggregate, hasAggregate_frag a h.1.2, hasAggregate_frag b h.2]
  | .unaryOp .not a, h => by
    simp [SqlEquiv.hasAggregate, hasAggregate_frag a (by simpa [isFragment] using h)]
  | .unaryOp .neg _, h | .unaryOp .isNull _, h | .unaryOp .isNotNull _, h => by simp [isFragment] at h
  | .func .., h | .agg .., h | .countStar, h | .«case» .., h | .inList .., h | .inSubquery .., h
  | .exists .., h | .subquery .., h | .windowFn .., h => by simp [isFragment] at h
  | .between x lo hi, h => by
    simp only [isFragment, Bool.and_eq_true] at h
    simp [SqlEquiv.hasAggregate, hasAggregate_frag x h.1.1, hasAggregate_frag lo h.1.2, hasAggregate_frag hi h.2]

theorem hasWindowFn_frag : ∀ e, isFragment e = true → SqlEquiv.exprHasWindowFn e = false
  | .lit _, _ => by simp [SqlEquiv.exprHasWindowFn]
  | .col _, _ => by simp [SqlEquiv.exprHasWindowFn]
  | .binOp op a b, h => by
    simp only [isFragment, Bool.and_eq_true] at h
    simp [SqlEquiv.exprHasWindowFn, hasWindowFn_frag a h.1.2, hasWindowFn_frag b h.2]
  | .unaryOp .not a, h => by
    simp [SqlEquiv.exprHasWindowFn, hasWindowFn_frag a (by simpa [isFragment] using h)]
  | .unaryOp .neg _, h | .unaryOp .isNull _, h | .unaryOp .isNotNull _, h => by simp [isFragment] at h
  | .func .., h | .agg .., h | .countStar, h | .«case» .., h | .inList .., h | .inSubquery .., h
  | .exists .., h | .subquery .., h | .windowFn .., h => by simp [isFragment] at h
  | .between x lo hi, h => by
    simp only [isFragment, Bool.and_eq_true] at h
    simp [SqlEquiv.exprHasWindowFn, hasWindowFn_frag x h.1.1, hasWindowFn_frag lo h.1.2, hasWindowFn_frag hi h.2]

theorem selectHasAggregate_frag : ∀ items, itemsFragment items = true →
    SqlEquiv.selectHasAggregate items = false
  | [], _ => rfl
  | .exprItem e _ :: rest, h => by
    simp only [itemsFragment, Bool.and_eq_true] at h
    have := selectHasAggregate_frag rest h.2
    simp only [SqlEquiv.selectHasAggregate, List.any_cons, hasAggregate_frag e h.1,
      Bool.false_or] at this ⊢
    exact this
  | .star _ :: _, h => by simp [itemsFragment] at h

theorem selectHasWindowFn_frag : ∀ items, itemsFragment items = true →
    SqlEquiv.selectHasWindowFn items = false
  | [], _ => rfl
  | .exprItem e _ :: rest, h => by
    simp only [itemsFragment, Bool.and_eq_true] at h
    have := selectHasWindowFn_frag rest h.2
    simp only [SqlEquiv.selectHasWindowFn, List.any_cons, hasWindowFn_frag e h.1,
      Bool.false_or] at this ⊢
    exact this
  | .star _ :: _, h => by simp [itemsFragment] at h

theorem forall₂_and_left {α β : Type _} {P : α → β → Prop} {Q : α → Prop} :
    ∀ {l₁ l₂}, List.Forall₂ P l₁ l₂ → (∀ a ∈ l₁, Q a) →
      List.Forall₂ (fun a b => P a b ∧ Q a) l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons h hs, hq =>
    .cons ⟨h, hq _ List.mem_cons_self⟩ (forall₂_and_left hs fun a ha => hq a (List.mem_cons_of_mem _ ha))

/-! ### The statement theorem -/

/-- A base-table row: the untyped row lists the schema's columns in order, under their names, with
    related values. -/
def TableRowRel {m : ℕ} (base : Fin m → Column) (r : Row m) (u : SqlEquiv.Row) : Prop :=
  ∃ w : Fin m → SqlEquiv.Value, u = List.ofFn (fun j => ((base j).name, w j)) ∧
    ∀ j, DatumRel (r j) (w j)

/-- The untyped database `db` holds, for each table, rows related to the typed ones, under every
    spelling `s` of its name that the schema's `fold` maps to the table's key. `SqlEquiv` looks a
    table up by the name as the query spells it, so `db` must answer each such spelling alike: the
    `Database` decides how names match (registry row 20, #372; the Spider harness lowercases). With
    `fold = id` this is one name per table. -/
def DbRel (N : NamedSchema) (db : SqlEquiv.Database) (D : Database N.S) : Prop :=
  ∀ s T, (N.fold s, T) ∈ N.tables → List.Forall₂ (TableRowRel (N.S.columns T)) (D T) (db s)

/-- Column names that `SqlEquiv`'s lookup finds unambiguously: no dots, distinct ignoring case. -/
structure WellNamed (N : NamedSchema) : Prop where
  noDot : ∀ T j, '.' ∉ (N.S.columns T j).name.toList
  distinct : ∀ T j k, (N.S.columns T j).name.toLower = (N.S.columns T k).name.toLower → j = k

/-- No predicate, join condition, projection, grouping key or aggregate argument of the query
    orders two booleans (see `NoBoolOrder`), and no `ORDER BY` key is boolean (`SqlEquiv` does not order booleans; #352). -/
def QNoBoolOrder {S : DbSchema} : {n : ℕ} → Query S n → Prop
  | _, .select p q => (∀ Γ, q.typeOf = some Γ → NoBoolOrder Γ p) ∧ QNoBoolOrder q
  | _, .project es q => (∀ Γ, q.typeOf = some Γ → ∀ i, NoBoolOrder Γ (es i)) ∧ QNoBoolOrder q
  | _, .orderBy keys q =>
    (∀ Γ, q.typeOf = some Γ → ∀ i, (keys i).e.typeOf Γ ≠ some .bool) ∧ QNoBoolOrder q
  | _, .limit _ _ q => QNoBoolOrder q
  | _, .join θ q₁ q₂ => (∀ Γ Δ, q₁.typeOf = some Γ → q₂.typeOf = some Δ →
      NoBoolOrder (Fin.append Γ Δ) θ) ∧ QNoBoolOrder q₁ ∧ QNoBoolOrder q₂
  | _, .aggregate keys aggs q => (∀ Γ, q.typeOf = some Γ →
      (∀ i, NoBoolOrder Γ (keys i)) ∧ ∀ j, AggNoBool Γ (aggs j)) ∧ QNoBoolOrder q
  | _, _ => True

/-- The statements of #309: `SELECT e₁, …, eₖ FROM t [AS a] [WHERE p]`. -/
def fragmentStmt (items : List SqlEquiv.SelectItem) (name : String) (al : Option String)
    (wh : Option SqlEquiv.Expr) : SqlEquiv.Stmt :=
  .query (.simple (.mk false items (some (.table ⟨name, al⟩)) wh [] none [] none none))

theorem fragment_rows (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hwn : WellNamed N) {db : SqlEquiv.Database}
    {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D) {name : String} {T : N.S.Table}
    (hT : (N.fold name, T) ∈ N.tables) (al : Option String) :
    List.Forall₂
      (fun r u => RowRel (requalify (N.fold (al.getD name)) (N.S.columns T)) N.fold r u ∧
        r.Conforms (N.S.ctx T))
      (D T) (SqlEquiv.evalFrom db (.table ⟨name, al⟩)) := by
  rw [SqlEquiv.evalFrom_table]
  refine forall₂_and_left ?_ (fun r hr => hD T r hr)
  rw [List.forall₂_map_right_iff]
  refine (hrel name T hT).imp ?_
  rintro r u ⟨w, rfl, hw⟩
  simp only [List.map_ofFn]
  exact rowRel_qualified N.fold hfold _ _ r w hw (hwn.noDot T) (hwn.distinct T)

theorem elabStmt_correct (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hwn : WellNamed N)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {name : String} {al : Option String}
    {wh : Option SqlEquiv.Expr} (hit : itemsFragment items = true)
    (hw : ∀ w ∈ wh, isFragment w = true) {e : Elaborated N.S}
    (h : elabStmt N (fragmentStmt items name al wh) = .ok e) (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (fragmentStmt items name al wh)).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  simp only [fragmentStmt, elabStmt, elabQuery, elabQueryRaw, elabSelect] at h
  rw [elabSelectF] at h
  simp only [elabFrom, lookupTable, List.map_nil, aggsOfList, aggsOfOpt,
    List.append_nil, List.isEmpty_nil, Option.isNone_none, Bool.and_true, Bool.true_and] at h
  rw [aggsOfList_items ?hf items hit] at h
  case hf => intros; rfl
  rcases hT : N.tables.find? (fun x => x.1 == N.fold name) with _ | ⟨nm, T⟩
  · simp [hT, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  have hmem : (N.fold name, T) ∈ N.tables := by
    have h1 := List.mem_of_find?_eq_some hT
    have h2 := List.find?_some hT
    simp only [beq_iff_eq] at h2; subst h2; exact h1
  simp only [hT] at h
  have hrows := fragment_rows N hfold hwn hD hrel hmem al
  have hdiv : ∀ {its : List (Expr (N.S.arity T) × Column)},
      ItemsRel (requalify (N.fold (al.getD name)) (N.S.columns T)) N.fold items its →
      ∀ i : Fin its.length, (its[i]).1.divSafe = true := fun hir i => by
    obtain ⟨_, _, _, htr⟩ := (List.forall₂_iff_get.mp hir).2 i.1 (by have := hir.length_eq; omega) i.2
    exact Translates.divSafe _ _ htr
  cases wh with
  | none =>
    rcases hits : elabItems N (requalify (N.fold (al.getD name)) (N.S.columns T)) items with _ | its
    · simp [hits, bind, Except.bind, pure, Except.pure] at h
    have hir := itemsRel_of_elab _ N items hit hits
    simp [hits, finishSelect, bind, Except.bind, pure, Except.pure] at h
    split at h
    swap
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hty
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨rs, hrs⟩ := Query.IsSafe.exists_eval_eq_ok (q := Query.project (fun i => (its[i]).1)
      (Query.table T)) ⟨hty, by simpa [Query.divSafe] using hdiv hir⟩ hD
    refine ⟨rs, hrs, _, rfl, ?_⟩
    simp only [SqlEquiv.evalQuery]
    rw [SqlEquiv.evalSelect_nondistinct_project _ _ _ (selectHasAggregate_frag items hit)
      (selectHasWindowFn_frag items hit)]
    simp only [Query.eval_project, Query.eval_table, bind, Except.bind] at hrs
    exact project_rel _ _ db hir (fun i => hnb.1 _ rfl i) hrows hrs
  | some w =>
    rcases hp : elabExpr (requalify (N.fold (al.getD name)) (N.S.columns T)) N.fold noHook w with _ | p
    · simp [subsOf_frag w (hw w rfl), hp, bind, Except.bind, pure, Except.pure] at h
    have htp := translates_of_elab _ _ w (hw w rfl) hp
    rcases hits : elabItems N (requalify (N.fold (al.getD name)) (N.S.columns T)) items with _ | its
    · simp [subsOf_frag w (hw w rfl), hp, hits, bind, Except.bind, pure,
        Except.pure] at h
    have hir := itemsRel_of_elab _ N items hit hits
    simp [subsOf_frag w (hw w rfl), hp, hits, finishSelect, bind, Except.bind, pure,
        Except.pure] at h
    have hstep : (if (Query.project (fun i => (its[i]).1) (Query.select p (Query.table T))).typeOf.isSome
        then Except.ok (ε := ElabError) (⟨its.length, Query.project (fun i => (its[i]).1)
          (Query.select p (Query.table T)), fun i => (its[i]).2⟩ : Elaborated N.S)
        else throw (ElabError.typeError "query")) = .ok e := by
      rcases hsel : (Query.select p (Query.table T)).typeOf with _ | Γ <;>
        simp only [hsel] at h <;> simpa using h
    clear h
    split at hstep
    swap
    · simp [throw, throwThe, MonadExceptOf.throw] at hstep
    rename_i hty
    simp only [Except.ok.injEq] at hstep
    subst hstep
    have hsel : (Query.select p (Query.table T)).typeOf = some (N.S.ctx T) := by
      revert hty
      simp only [Query.typeOf]
      by_cases hb : p.typeOf (N.S.ctx T) = some .bool <;> simp [hb, bind]
    obtain ⟨rs, hrs⟩ := Query.IsSafe.exists_eval_eq_ok (q := Query.project (fun i => (its[i]).1)
      (Query.select p (Query.table T)))
      ⟨hty, by simpa [Query.divSafe, Translates.divSafe _ _ htp] using hdiv hir⟩ hD
    refine ⟨rs, hrs, _, rfl, ?_⟩
    simp only [SqlEquiv.evalQuery]
    rw [SqlEquiv.evalSelect_nondistinct_project_where _ _ _ _ (selectHasAggregate_frag items hit)
      (selectHasWindowFn_frag items hit)]
    simp only [Query.eval_project, Query.eval_select, Query.eval_table, bind, Except.bind] at hrs
    rcases hf : p.filterRows (D T) with _ | R'
    · rw [hf] at hrs; cases hrs
    rw [hf] at hrs
    have hfr := filter_rel _ _ db htp (hnb.2.1 _ rfl) hrows hf
    exact project_rel _ _ db hir (fun i => hnb.1 _ hsel i) hfr hrs

end Statement

end SqlBridge.Correct

