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

end SqlEquiv
