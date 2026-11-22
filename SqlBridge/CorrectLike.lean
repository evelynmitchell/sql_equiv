/-
  `LIKE` across the two evaluators (#352). Both simulate the pattern's automaton (`%` any
  sequence, `_` any one character, no `ESCAPE`); the typed core's takes a character comparison,
  `SqlEquiv`'s compares exactly and, for sqlite's case-insensitive `LIKE` (registry row 8),
  lowercases both sides first.

  * `likeMatch_eq`: `SqlEquiv`'s matcher is the typed core's case-sensitive one.
  * `likeMatchCI_eq`: lowercasing both sides and matching exactly is matching while ignoring
    ASCII case. Lowercasing keeps `%` and `_` and turns no other character into one.
-/
import SqlBridge.Elab

namespace SqlBridge.Correct
open SqlCore

/-! ### `LIKE`: the two matchers agree -/

theorem likePatClosure_eq : ∀ p : List Char, SqlEquiv.likePatClosure p = likeClosure p := by
  intro p
  induction p using SqlEquiv.likePatClosure.induct with
  | case1 p ih => simp [SqlEquiv.likePatClosure, likeClosure, ih]
  | case2 p h =>
    have h1 : SqlEquiv.likePatClosure p = [p] := by
      unfold SqlEquiv.likePatClosure
      split
      · exact absurd rfl (h _)
      · rfl
    have h2 : likeClosure p = [p] := by
      unfold likeClosure
      split
      · exact absurd rfl (h _)
      · rfl
    rw [h1, h2]

theorem likePatStep_eq (c : Char) (p : List Char) :
    SqlEquiv.likePatStep c p = likeStep (fun a b => a == b) c p := by
  unfold SqlEquiv.likePatStep likeStep
  split <;> simp [likePatClosure_eq]

theorem likePatRun_eq : ∀ (s : List Char) (sts : List (List Char)),
    SqlEquiv.likePatRun sts s = likeRun (fun a b => a == b) sts s
  | [], sts => rfl
  | c :: s, sts => by
    simp only [SqlEquiv.likePatRun, likeRun]
    rw [likePatRun_eq s]
    congr 2
    exact List.flatMap_congr (fun p _ => likePatStep_eq c p) |>.symm ▸ rfl

/-- `SqlEquiv`'s `LIKE` is the typed core's case-sensitive one. -/
theorem likeMatch_eq (s p : String) : SqlEquiv.likeMatch s p = likeText false s p := by
  simp [SqlEquiv.likeMatch, likeText, likePatRun_eq, likePatClosure_eq]

/-- The states of the automaton that accept a text: `p` accepts `s`. -/
def LikeAcc (eq : Char → Char → Bool) : List Char → List Char → Prop
  | p, [] => p = []
  | p, c :: s => ∃ p' ∈ likeStep eq c p, LikeAcc eq p' s

theorem likeRun_iff (eq : Char → Char → Bool) : ∀ (s : List Char) (sts : List (List Char)),
    likeRun eq sts s = true ↔ ∃ p ∈ sts, LikeAcc eq p s
  | [], sts => by simp [likeRun, LikeAcc]
  | c :: s, sts => by
    simp only [likeRun, LikeAcc]
    rw [likeRun_iff eq s]
    constructor
    · rintro ⟨p', hp', hacc⟩
      obtain ⟨p, hp, hstep⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hp')
      exact ⟨p, hp, p', hstep, hacc⟩
    · rintro ⟨p, hp, p', hstep, hacc⟩
      exact ⟨p', List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨p, hp, hstep⟩), hacc⟩

theorem toLower_eq_pct (c : Char) : c.toLower = '%' ↔ c = '%' := by
  refine ⟨fun h => ?_, fun h => by subst h; decide⟩
  unfold Char.toLower at h; split at h
  · rename_i hc; have := congrArg Char.val h; simp at this hc
    exfalso
    have h1 := congrArg UInt32.toNat this
    rw [UInt32.toNat_add] at h1
    have h2 : (65:UInt32).toNat ≤ c.val.toNat := hc.1
    have h3 : c.val.toNat ≤ (90:UInt32).toNat := hc.2
    simp at h1 h2 h3; omega
  · exact h

theorem toLower_eq_und (c : Char) : c.toLower = '_' ↔ c = '_' := by
  refine ⟨fun h => ?_, fun h => by subst h; decide⟩
  unfold Char.toLower at h; split at h
  · rename_i hc; have := congrArg Char.val h; simp at this hc
    exfalso
    have h1 := congrArg UInt32.toNat this
    rw [UInt32.toNat_add] at h1
    have h2 : (65:UInt32).toNat ≤ c.val.toNat := hc.1
    have h3 : c.val.toNat ≤ (90:UInt32).toNat := hc.2
    simp at h1 h2 h3; omega
  · exact h

theorem likeClosure_map_toLower : ∀ p : List Char,
    likeClosure (p.map Char.toLower) = (likeClosure p).map (List.map Char.toLower) := by
  intro p
  induction p using likeClosure.induct with
  | case1 p ih =>
    have : Char.toLower '%' = '%' := by decide
    simp only [List.map_cons, this, likeClosure, ih]
  | case2 p h =>
    have h2 : likeClosure p = [p] := by
      unfold likeClosure; split
      · exact absurd rfl (h _)
      · rfl
    have h1 : likeClosure (p.map Char.toLower) = [p.map Char.toLower] := by
      unfold likeClosure; split
      · rename_i q hq
        cases p with
        | nil => simp at hq
        | cons d p =>
          simp only [List.map_cons, List.cons.injEq] at hq
          exact absurd (congrArg (· :: p) ((toLower_eq_pct d).mp hq.1)) (h p)
      · rfl
    rw [h1, h2]; rfl

theorem likeStep_map_toLower (c : Char) (p : List Char) :
    likeStep (fun a b => a == b) c.toLower (p.map Char.toLower) =
      (likeStep (fun a b => a.toLower == b.toLower) c p).map (List.map Char.toLower) := by
  cases p with
  | nil => simp [likeStep]
  | cons d p =>
    by_cases h1 : d = '%'
    · subst h1
      have : Char.toLower '%' = '%' := by decide
      simp only [List.map_cons, this, likeStep]
      exact likeClosure_map_toLower ('%' :: p)
    by_cases h2 : d = '_'
    · subst h2
      have : Char.toLower '_' = '_' := by decide
      simp only [List.map_cons, this, likeStep]
      exact likeClosure_map_toLower p
    have h1' : d.toLower ≠ '%' := fun h => h1 ((toLower_eq_pct d).mp h)
    have h2' : d.toLower ≠ '_' := fun h => h2 ((toLower_eq_und d).mp h)
    have e1 : likeStep (fun a b => a == b) c.toLower (d.toLower :: p.map Char.toLower) =
        if d.toLower == c.toLower then likeClosure (p.map Char.toLower) else [] := by
      unfold likeStep; split <;> simp_all
    have e2 : likeStep (fun a b => a.toLower == b.toLower) c (d :: p) =
        if d.toLower == c.toLower then likeClosure p else [] := by
      unfold likeStep; split <;> simp_all
    rw [List.map_cons, e1, e2]
    split <;> simp [likeClosure_map_toLower]

theorem likeAcc_map_toLower : ∀ (s p : List Char),
    LikeAcc (fun a b => a.toLower == b.toLower) p s ↔
      LikeAcc (fun a b => a == b) (p.map Char.toLower) (s.map Char.toLower)
  | [], p => by simp [LikeAcc]
  | c :: s, p => by
    simp only [List.map_cons, LikeAcc, likeStep_map_toLower, List.mem_map]
    constructor
    · rintro ⟨p', hp', hacc⟩
      exact ⟨_, ⟨p', hp', rfl⟩, (likeAcc_map_toLower s p').mp hacc⟩
    · rintro ⟨_, ⟨p', hp', rfl⟩, hacc⟩
      exact ⟨p', hp', (likeAcc_map_toLower s p').mpr hacc⟩

/-- `SqlEquiv`'s case-insensitive `LIKE` (both sides lowercased, then matched exactly) is the
    typed core's (characters compared ignoring ASCII case): lowercasing keeps `%` and `_` and
    makes no other character one of them. -/
theorem likeMatchCI_eq (s p : String) :
    SqlEquiv.likeMatch (s.map Char.toLower) (p.map Char.toLower) = likeText true s p := by
  rw [likeMatch_eq, Bool.eq_iff_iff]
  simp only [likeText, Bool.false_eq_true, ↓reduceIte, String.toList_map, likeRun_iff,
    likeClosure_map_toLower, List.mem_map]
  constructor
  · rintro ⟨_, ⟨p', hp', rfl⟩, hacc⟩
    exact ⟨p', hp', (likeAcc_map_toLower _ p').mpr hacc⟩
  · rintro ⟨p', hp', hacc⟩
    exact ⟨_, ⟨p', hp', rfl⟩, (likeAcc_map_toLower _ p').mp hacc⟩

end SqlBridge.Correct
