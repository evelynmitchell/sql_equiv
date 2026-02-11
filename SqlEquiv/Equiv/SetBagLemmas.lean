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
