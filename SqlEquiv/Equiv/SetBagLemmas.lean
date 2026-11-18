/-
  Set/Bag Equivalence Helper Lemmas

  Lemmas about List.eraseDups and List.Perm needed for proving
  set operation axioms under bag and set equivalence.
-/
import SqlEquiv.Equiv.Defs

namespace SqlEquiv

-- ============================================================================
-- perm_ext_iff_of_nodup (proved from core lemmas, avoids Batteries import)
-- ============================================================================

/-- Two Nodup lists with the same membership are permutations.
    Proved via `perm_iff_count` + `Nodup.count` from Lean core. -/
theorem perm_ext_iff_of_nodup [BEq α] [LawfulBEq α]
    {l₁ l₂ : List α} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) :
    l₁.Perm l₂ ↔ ∀ a, a ∈ l₁ ↔ a ∈ l₂ := by
  constructor
  · intro h a; exact h.mem_iff
  · intro h
    rw [List.perm_iff_count]
    intro a
    rw [d₁.count, d₂.count]
    simp [h a]

-- ============================================================================
-- eraseDups membership and Nodup lemmas
-- ============================================================================

/-- Membership is preserved by eraseDups: `a ∈ l.eraseDups ↔ a ∈ l`.
    Uses strong induction on list length because `eraseDups_cons` recurses
    on `(xs.filter ...).eraseDups`, not `xs.eraseDups`. -/
theorem mem_eraseDups [BEq α] [LawfulBEq α] {a : α} {l : List α} :
    a ∈ l.eraseDups ↔ a ∈ l := by
  suffices ∀ (n : Nat) (l : List α), l.length ≤ n → (a ∈ l.eraseDups ↔ a ∈ l) from
    this l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp
    | cons _ _ => simp at hl
  | succ k ih =>
    intro l hl
    match l with
    | [] => simp
    | x :: xs =>
      rw [List.eraseDups_cons, List.mem_cons, List.mem_cons]
      have hfilt_len : (xs.filter (! · == x)).length ≤ k :=
        Nat.le_trans (List.length_filter_le _ _) (by simp at hl; omega)
      have ihf := ih _ hfilt_len
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr (List.mem_filter.mp (ihf.mp h)).1
      · rintro (rfl | h)
        · exact Or.inl rfl
        · by_cases heq : a = x
          · exact Or.inl heq
          · exact Or.inr (ihf.mpr (List.mem_filter.mpr ⟨h, by simp [heq]⟩))

/-- eraseDups produces a list with no duplicates.
    Uses strong induction like `mem_eraseDups`. -/
theorem nodup_eraseDups [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup := by
  suffices ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.Nodup from
    this l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp
    | cons _ _ => simp at hl
  | succ k ih =>
    intro l hl
    match l with
    | [] => simp
    | x :: xs =>
      rw [List.eraseDups_cons, List.nodup_cons]
      have hfilt_len : (xs.filter (! · == x)).length ≤ k :=
        Nat.le_trans (List.length_filter_le _ _) (by simp at hl; omega)
      refine ⟨?_, ih _ hfilt_len⟩
      intro hmem
      have := (List.mem_filter.mp (mem_eraseDups.mp hmem)).2
      simp at this

-- ============================================================================
-- Perm lemmas for eraseDups
-- ============================================================================

/-- If two lists are permutations, their eraseDups are permutations -/
theorem Perm_eraseDups [BEq α] [LawfulBEq α] {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : l₁.eraseDups.Perm l₂.eraseDups := by
  apply (perm_ext_iff_of_nodup (nodup_eraseDups l₁) (nodup_eraseDups l₂)).mpr
  intro a
  rw [mem_eraseDups, mem_eraseDups]
  exact h.mem_iff

-- ============================================================================
-- eraseDups/filter interaction (needed since INTERSECT/EXCEPT dedup, #223)
-- ============================================================================

/-- Filtering commutes with eraseDups: both preserve first-occurrence order,
    so `(l.eraseDups).filter p = (l.filter p).eraseDups`.
    Strong induction on length (eraseDups_cons recurses on a filtered tail). -/
theorem filter_eraseDups [BEq α] [LawfulBEq α] (p : α → Bool) (l : List α) :
    l.eraseDups.filter p = (l.filter p).eraseDups := by
  suffices ∀ (n : Nat) (l : List α), l.length ≤ n →
      l.eraseDups.filter p = (l.filter p).eraseDups from
    this l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp
    | cons _ _ => simp at hl
  | succ k ih =>
    intro l hl
    match l with
    | [] => simp
    | x :: xs =>
      have hfilt_len : (xs.filter (! · == x)).length ≤ k :=
        Nat.le_trans (List.length_filter_le _ _) (by simp at hl; omega)
      cases hp : p x with
      | true =>
        simp only [List.eraseDups_cons, List.filter_cons, hp, ↓reduceIte]
        rw [ih _ hfilt_len]
        congr 1
        congr 1
        rw [List.filter_filter, List.filter_filter]
        apply List.filter_congr
        intro a _
        exact Bool.and_comm ..
      | false =>
        simp only [List.eraseDups_cons, List.filter_cons, hp, Bool.false_eq_true,
          ↓reduceIte]
        rw [ih _ hfilt_len]
        congr 1
        rw [List.filter_filter]
        apply List.filter_congr
        intro a _
        by_cases hax : a = x
        · subst hax; simp [hp]
        · simp [hax]

/-- eraseDups is the identity on lists without duplicates -/
theorem eraseDups_eq_self_of_nodup [BEq α] [LawfulBEq α] {l : List α}
    (h : l.Nodup) : l.eraseDups = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.eraseDups_cons]
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp h
    have hfilt : xs.filter (fun b => !b == x) = xs := by
      rw [List.filter_eq_self]
      intro a ha
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
      intro heq
      exact hx (heq ▸ ha)
    rw [hfilt, ih hxs]

/-- eraseDups is idempotent -/
theorem eraseDups_eraseDups [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.eraseDups = l.eraseDups :=
  eraseDups_eq_self_of_nodup (nodup_eraseDups l)

/-- contains on a filtered list: membership plus the predicate -/
theorem contains_filter [BEq α] [LawfulBEq α] (l : List α) (p : α → Bool) (x : α) :
    (l.filter p).contains x = (l.contains x && p x) := by
  rw [Bool.eq_iff_iff]
  simp [List.mem_filter]

/-- contains is invariant under eraseDups -/
theorem contains_eraseDups [BEq α] [LawfulBEq α] (l : List α) (x : α) :
    l.eraseDups.contains x = l.contains x := by
  by_cases h : x ∈ l <;> simp [mem_eraseDups, h]

-- ============================================================================
-- Filter + contains membership lemma
-- ============================================================================

/-- Membership in filter-contains: `x ∈ l.filter (r.contains ·) ↔ x ∈ l ∧ x ∈ r` -/
theorem mem_filter_contains [BEq α] [LawfulBEq α] {x : α} {l r : List α} :
    x ∈ l.filter (r.contains ·) ↔ x ∈ l ∧ x ∈ r := by
  simp [List.mem_filter]

-- ============================================================================
-- eraseDups + append membership
-- ============================================================================

/-- Membership in eraseDups of append -/
theorem mem_eraseDups_append [BEq α] [LawfulBEq α] {a : α} {l₁ l₂ : List α} :
    a ∈ (l₁ ++ l₂).eraseDups ↔ a ∈ l₁ ∨ a ∈ l₂ := by
  rw [mem_eraseDups, List.mem_append]

-- ============================================================================
-- Key-based dedup and value keys of set operations (#324)
-- ============================================================================

section DedupByKey
variable {α β : Type} [BEq β]

theorem dedupByKey_nil (f : α → β) : dedupByKey f ([] : List α) = [] := by
  rw [dedupByKey]

theorem dedupByKey_cons (f : α → β) (x : α) (xs : List α) :
    dedupByKey f (x :: xs) = x :: dedupByKey f (xs.filter fun y => !(f y == f x)) := by
  rw [dedupByKey]

variable [LawfulBEq β]

omit [LawfulBEq β] in
/-- The keys of `dedupByKey f l` are the keys of `l` without duplicates. -/
theorem map_dedupByKey (f : α → β) (l : List α) :
    (dedupByKey f l).map f = (l.map f).eraseDups := by
  suffices ∀ (n : Nat) (l : List α), l.length ≤ n →
      (dedupByKey f l).map f = (l.map f).eraseDups from this l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp [dedupByKey_nil]
    | cons _ _ => simp at hl
  | succ k ih =>
    intro l hl
    match l with
    | [] => simp [dedupByKey_nil]
    | x :: xs =>
      have hlen : (xs.filter fun y => !(f y == f x)).length ≤ k :=
        Nat.le_trans (List.length_filter_le _ _) (by simp at hl; omega)
      rw [dedupByKey_cons, List.map_cons, ih _ hlen, List.map_cons, List.eraseDups_cons,
        List.filter_map]
      rfl

theorem mem_map_dedupByKey {f : α → β} {l : List α} {k : β} :
    k ∈ (dedupByKey f l).map f ↔ k ∈ l.map f := by
  rw [map_dedupByKey, mem_eraseDups]

/-- Filtering by a predicate that only looks at the key commutes with `dedupByKey`. -/
theorem filter_dedupByKey (f : α → β) (p : α → Bool)
    (hp : ∀ x y, f x = f y → p x = p y) (l : List α) :
    (dedupByKey f l).filter p = dedupByKey f (l.filter p) := by
  suffices ∀ (n : Nat) (l : List α), l.length ≤ n →
      (dedupByKey f l).filter p = dedupByKey f (l.filter p) from this l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp [dedupByKey_nil]
    | cons _ _ => simp at hl
  | succ k ih =>
    intro l hl
    match l with
    | [] => simp [dedupByKey_nil]
    | x :: xs =>
      have hlen : (xs.filter fun y => !(f y == f x)).length ≤ k :=
        Nat.le_trans (List.length_filter_le _ _) (by simp at hl; omega)
      rw [dedupByKey_cons]
      cases hpx : p x with
      | true =>
        rw [List.filter_cons_of_pos hpx, List.filter_cons_of_pos hpx, dedupByKey_cons, ih _ hlen,
          List.filter_filter, List.filter_filter]
        congr 2
        apply List.filter_congr
        intro y _
        exact Bool.and_comm ..
      | false =>
        rw [List.filter_cons_of_neg (by simp [hpx]), List.filter_cons_of_neg (by simp [hpx]),
          ih _ hlen, List.filter_filter]
        congr 1
        apply List.filter_congr
        intro y _
        by_cases hy : f y = f x
        · simp [hy, hp y x hy, hpx]
        · simp [hy]

theorem dedupByKey_dedupByKey (f : α → β) (l : List α) :
    dedupByKey f (dedupByKey f l) = dedupByKey f l := by
  suffices ∀ (n : Nat) (l : List α), l.length ≤ n →
      dedupByKey f (dedupByKey f l) = dedupByKey f l from this l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp [dedupByKey_nil]
    | cons _ _ => simp at hl
  | succ k ih =>
    intro l hl
    match l with
    | [] => simp [dedupByKey_nil]
    | x :: xs =>
      have hlen : (xs.filter fun y => !(f y == f x)).length ≤ k :=
        Nat.le_trans (List.length_filter_le _ _) (by simp at hl; omega)
      rw [dedupByKey_cons, dedupByKey_cons,
        filter_dedupByKey f (fun y => !(f y == f x)) (fun a b h => by simp [h]),
        List.filter_filter]
      have hq : (xs.filter fun y => !(f y == f x) && !(f y == f x)) =
          xs.filter fun y => !(f y == f x) := by
        apply List.filter_congr; intro y _; simp
      rw [hq, ih _ hlen]

end DedupByKey

/-- Renaming a row's columns does not change its value key. -/
theorem Row.valueKey_renameTo (ns : Option (List String)) (row : Row) :
    Row.valueKey (Row.renameTo ns row) = Row.valueKey row := by
  cases ns with
  | none => rfl
  | some ns =>
    simp only [Row.renameTo]
    split
    · next h =>
      simp only [Row.valueKey]
      rw [List.map_snd_zip (by simp [h])]
    · rfl

theorem map_valueKey_renameTo (ns : Option (List String)) (r : Table) :
    (r.map (Row.renameTo ns)).map Row.valueKey = r.map Row.valueKey := by
  rw [List.map_map]
  apply List.map_congr_left
  intro row _
  exact Row.valueKey_renameTo ns row

theorem map_valueKey_unionAll (ns : Option (List String)) (l r : Table) :
    (applySetOp .unionAll ns l r).map Row.valueKey = l.map Row.valueKey ++ r.map Row.valueKey := by
  simp only [applySetOp, List.map_append, map_valueKey_renameTo]

theorem map_valueKey_union (ns : Option (List String)) (l r : Table) :
    (applySetOp .union ns l r).map Row.valueKey =
      (l.map Row.valueKey ++ r.map Row.valueKey).eraseDups := by
  simp only [applySetOp, map_dedupByKey, List.map_append, map_valueKey_renameTo]

theorem mem_valueKey_union {ns : Option (List String)} {l r : Table} {k : List Value} :
    k ∈ (applySetOp .union ns l r).map Row.valueKey ↔
      k ∈ l.map Row.valueKey ∨ k ∈ r.map Row.valueKey := by
  rw [map_valueKey_union, mem_eraseDups, List.mem_append]

theorem mem_valueKey_intersect {ns : Option (List String)} {l r : Table} {k : List Value} :
    k ∈ (applySetOp .intersect ns l r).map Row.valueKey ↔
      k ∈ l.map Row.valueKey ∧ k ∈ r.map Row.valueKey := by
  rw [applySetOp, mem_map_dedupByKey]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by simpa [List.mem_map] using hc⟩
  · rintro ⟨⟨x, hx, rfl⟩, hr⟩
    exact ⟨x, ⟨hx, by simpa [List.mem_map] using hr⟩, rfl⟩

theorem mem_valueKey_except {ns : Option (List String)} {l r : Table} {k : List Value} :
    k ∈ (applySetOp .exceptOp ns l r).map Row.valueKey ↔
      k ∈ l.map Row.valueKey ∧ k ∉ r.map Row.valueKey := by
  rw [applySetOp, mem_map_dedupByKey]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by simpa [List.mem_map] using hc⟩
  · rintro ⟨⟨x, hx, rfl⟩, hr⟩
    exact ⟨x, ⟨hx, by simpa [List.mem_map] using hr⟩, rfl⟩

end SqlEquiv
