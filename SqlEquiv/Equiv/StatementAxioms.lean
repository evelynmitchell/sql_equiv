/-
  SQL Equivalence - Statement-Level Axioms (SET ops, JOINs, Subqueries, Pagination)
-/
import SqlEquiv.Equiv.Defs
import SqlEquiv.Equiv.SetBagLemmas
import SqlEquiv.Equiv.ValueLemmas

namespace SqlEquiv

-- ============================================================================
-- Set Operation Theorems (UNION, INTERSECT, EXCEPT)
-- ============================================================================

-- ## Provable theorems (4)
--
-- These 4 axioms have been converted to theorems with full proofs using the
-- evalQuery_simple/evalQuery_compound infrastructure axioms.

/-- UNION ALL keeps all duplicates from both sides -/
theorem union_all_length (db : Database) (a b : SelectStmt) :
    (evalQuery db (Query.compound (Query.simple a) .unionAll (Query.simple b))).length =
    (evalQuery db (Query.simple a)).length + (evalQuery db (Query.simple b)).length := by
  simp only [evalQuery_compound, evalQuery_simple]
  exact List.length_append

/-- A EXCEPT A = empty (self-difference is empty) -/
theorem except_self_empty (db : Database) (a : SelectStmt) :
    evalQuery db (Query.compound (Query.simple a) .exceptOp (Query.simple a)) = [] := by
  simp only [evalQuery_compound, evalQuery_simple, applySetOp]
  generalize evalSelect db a = l
  have h : (l.filter fun row => !l.contains row) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx h
    simp at h
    exact absurd hx h
  rw [h, List.eraseDups_nil]

/-- INTERSECT with empty is empty -/
theorem intersect_empty_right (db : Database) (a : SelectStmt) :
    let emptySelect := SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none
    evalQuery db (Query.compound (Query.simple a) .intersect (Query.simple emptySelect)) = [] := by
  simp only [evalQuery_compound, evalQuery_simple, applySetOp]
  have h : evalSelect db (SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none) = [] :=
    evalSelect_filter_all_false db false [.star none] none (.lit (.bool false)) [] none [] none none
      (by rfl) (fun row => by simp [evalExprWithDb_lit])
  rw [h]
  have hfilt : (List.filter (fun (_ : Row) => false) (evalSelect db a)) = [] := by
    rw [List.filter_eq_nil_iff]; intro x _ hx; exact absurd hx (by simp)
  simp [hfilt]

/-- INTERSECT is idempotent under set equivalence: A INTERSECT A ≃ˢ A.
    Downgraded from ≃ᵩ by #223: INTERSECT now deduplicates (SQL set semantics),
    so when A has duplicate rows, A INTERSECT A = eraseDups A, which is neither
    equal to nor a permutation of A (a duplicated row appears once vs. twice),
    ruling out both ≃ᵩ and ≃ᵇ. -/
theorem intersect_idempotent (a : SelectStmt) :
    Query.compound (Query.simple a) .intersect (Query.simple a) ≃ˢ
    Query.simple a := by
  intro db row
  simp only [evalQuery_compound, evalQuery_simple, applySetOp, mem_eraseDups,
    List.mem_filter]
  exact ⟨fun h => h.1, fun h => ⟨h, List.contains_iff_mem.mpr h⟩⟩

-- ## Bag/Set equivalence theorems (9)
--
-- These 9 axioms held under set/bag semantics but not under exact list equality
-- (ordering/multiplicity differences). With the introduction of ≃ᵇ (bag equiv,
-- same elements with same multiplicities) and ≃ˢ (set equiv, same membership),
-- they are now fully proved theorems.
--
-- Equivalence hierarchy: ≃ᵩ (exact) → ≃ᵇ (bag/Perm) → ≃ˢ (set/membership)
--
-- 3 Bag (≃ᵇ): union_all_comm, union_comm, union_assoc
-- 1 Exact (≃ᵩ): intersect_assoc
-- 6 Set (≃ˢ): intersect_comm, intersect_idempotent, union_idempotent,
--              union_empty_right, union_intersect_distrib, intersect_union_distrib

/-- UNION ALL is commutative under bag equivalence -/
theorem union_all_comm (a b : SelectStmt) :
    Query.compound (Query.simple a) .unionAll (Query.simple b) ≃ᵇ
    Query.compound (Query.simple b) .unionAll (Query.simple a) := by
  intro db
  simp only [evalQuery_compound, evalQuery_simple]
  exact List.perm_append_comm

/-- UNION is commutative under bag equivalence -/
theorem union_comm (a b : SelectStmt) :
    Query.compound (Query.simple a) .union (Query.simple b) ≃ᵇ
    Query.compound (Query.simple b) .union (Query.simple a) := by
  intro db
  simp only [evalQuery_compound, evalQuery_simple]
  exact Perm_eraseDups List.perm_append_comm

/-- UNION is associative under bag equivalence -/
theorem union_assoc (a b c : Query) :
    Query.compound (Query.compound a .union b) .union c ≃ᵇ
    Query.compound a .union (Query.compound b .union c) := by
  intro db
  simp only [evalQuery_compound, applySetOp]
  apply (perm_ext_iff_of_nodup (nodup_eraseDups _) (nodup_eraseDups _)).mpr
  intro row
  simp only [mem_eraseDups, List.mem_append]
  exact or_assoc

/-- INTERSECT is associative under exact equality.
    Unlike the other set operations, both sides filter the same list (evalQuery db a)
    in the same order — only the predicate differs, and the predicates are equivalent.
    Survives the #223 dedup because filter commutes with eraseDups
    (`filter_eraseDups`: both preserve first-occurrence order), so both sides
    normalize to `eraseDups` of the same doubly-filtered list. -/
theorem intersect_assoc (a b c : Query) :
    Query.compound (Query.compound a .intersect b) .intersect c ≃ᵩ
    Query.compound a .intersect (Query.compound b .intersect c) := by
  intro db
  simp only [evalQuery_compound, applySetOp]
  rw [filter_eraseDups, eraseDups_eraseDups, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [contains_eraseDups, contains_filter]
  exact Bool.and_comm ..

/-- INTERSECT is commutative under set equivalence -/
theorem intersect_comm (a b : SelectStmt) :
    Query.compound (Query.simple a) .intersect (Query.simple b) ≃ˢ
    Query.compound (Query.simple b) .intersect (Query.simple a) := by
  intro db row
  simp only [evalQuery_compound, evalQuery_simple, applySetOp, mem_eraseDups,
    mem_filter_contains]
  exact And.comm

/-- UNION is idempotent under set equivalence -/
theorem union_idempotent (a : SelectStmt) :
    Query.compound (Query.simple a) .union (Query.simple a) ≃ˢ
    Query.simple a := by
  intro db row
  simp only [evalQuery_compound, evalQuery_simple, applySetOp, mem_eraseDups,
    List.mem_append]
  exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩

/-- UNION with empty is identity under set equivalence -/
theorem union_empty_right (a : SelectStmt) :
    Query.compound (Query.simple a) .union
      (Query.simple (SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none)) ≃ˢ
    Query.simple a := by
  intro db row
  simp only [evalQuery_compound, evalQuery_simple, applySetOp, mem_eraseDups,
    List.mem_append]
  have hempty : evalSelect db (SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none) = [] :=
    evalSelect_filter_all_false db false [.star none] none (.lit (.bool false)) [] none [] none none
      (by rfl) (fun _row => by simp [evalExprWithDb_lit])
  rw [hempty]
  simp

-- Note: EXCEPT is NOT commutative, so we don't have a commutativity axiom for it

/-- Distributivity: A UNION (B INTERSECT C) = (A UNION B) INTERSECT (A UNION C)
    under set equivalence -/
theorem union_intersect_distrib (a b c : Query) :
    Query.compound a .union (Query.compound b .intersect c) ≃ˢ
    Query.compound (Query.compound a .union b) .intersect (Query.compound a .union c) := by
  intro db row
  simp only [evalQuery_compound, applySetOp, mem_eraseDups, List.mem_append,
    mem_filter_contains]
  exact or_and_left

/-- Distributivity: A INTERSECT (B UNION C) = (A INTERSECT B) UNION (A INTERSECT C)
    under set equivalence -/
theorem intersect_union_distrib (a b c : Query) :
    Query.compound a .intersect (Query.compound b .union c) ≃ˢ
    Query.compound (Query.compound a .intersect b) .union (Query.compound a .intersect c) := by
  intro db row
  simp only [evalQuery_compound, applySetOp, mem_filter_contains, mem_eraseDups,
    List.mem_append]
  exact and_or_left

-- ============================================================================
-- JOIN Theorems
-- ============================================================================

/-- Helper: filterMap with constant none produces empty list -/
private theorem List.filterMap_none {α β : Type} (l : List α) :
    l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Helper: flatMap with constant empty list produces empty list -/
private theorem List.flatMap_const_nil {α β : Type} (l : List α) :
    l.flatMap (fun _ => ([] : List β)) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [List.flatMap_cons, ih]

/-- Helper: filterMap (some ∘ f) = map f -/
private theorem List.filterMap_some_comp {α β : Type} (l : List α) (f : α → β) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [List.map_cons, ih]

/-- flatMap with constant-length bodies: total length = outer length × inner length -/
private theorem List.length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (n : Nat)
    (h : ∀ x ∈ l, (f x).length = n) :
    (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a List.mem_cons_self]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- flatMap with bounded-length bodies: total ≤ outer × bound -/
private theorem List.length_flatMap_le {α β : Type} (l : List α) (f : α → List β) (n : Nat)
    (h : ∀ x ∈ l, (f x).length ≤ n) :
    (l.flatMap f).length ≤ l.length * n := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := h a List.mem_cons_self
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    calc (f a).length + (rest.flatMap f).length
        ≤ n + rest.length * n := Nat.add_le_add ha hrest
      _ = (rest.length + 1) * n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- flatMap with at-least-1 bodies gives length ≥ outer length -/
private theorem List.length_flatMap_ge_length {α β : Type} (l : List α) (f : α → List β)
    (h : ∀ x ∈ l, (f x).length ≥ 1) :
    (l.flatMap f).length ≥ l.length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := h a List.mem_cons_self
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

/-- Left join body always produces at least one row -/
private theorem left_join_body_length_ge_one (matchingRows : List Row) (rightHead : Option Row)
    (lr : Row) :
    (if matchingRows.isEmpty then
      match rightHead with
      | some rightRow => [lr ++ rightRow.map fun (k, _) => (k, Value.null none)]
      | none => [lr]
    else
      matchingRows).length ≥ 1 := by
  cases matchingRows with
  | nil => simp; cases rightHead <;> simp
  | cons _ _ => simp

/-- Right join body always produces at least one row -/
private theorem right_join_body_length_ge_one (matchingRows : List Row) (leftHead : Option Row)
    (rr : Row) :
    (if matchingRows.isEmpty then
      match leftHead with
      | some leftRow => [leftRow.map (fun (k, _) => (k, Value.null none)) ++ rr]
      | none => [rr]
    else
      matchingRows).length ≥ 1 := by
  cases matchingRows with
  | nil => simp; cases leftHead <;> simp
  | cons _ _ => simp

/-- Helper: if f(a) has ≥ 1 element and all elements satisfy P, then ∃ b ∈ l.flatMap f, P b -/
private theorem exists_mem_flatMap_of_length_ge_one {α β : Type} (f : α → List β)
    (l : List α) (a : α) (ha : a ∈ l) (P : β → Prop)
    (hLen : (f a).length ≥ 1) (hP : ∀ b ∈ f a, P b) :
    ∃ b ∈ l.flatMap f, P b := by
  have hNE := List.ne_nil_of_length_pos (by omega : 0 < (f a).length)
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hNE
  exact ⟨b, List.mem_flatMap.mpr ⟨a, ha, hb⟩, hP b hb⟩

/-- INNER JOIN with ON TRUE is equivalent to CROSS JOIN -/
theorem inner_join_true_is_cross (db : Database) (a b : FromClause) :
    evalFrom db (.join a .inner b (some (.lit (.bool true)))) =
    evalFrom db (.join a .cross b none) := by
  rw [evalFrom_inner_join, evalFrom_cross_join]
  simp only -- unfold let rightRows bindings
  congr 1; funext lr
  dsimp
  simp only [evalExprWithDb_lit, List.filterMap_some_comp]

/-- INNER JOIN with ON FALSE produces empty result -/
theorem inner_join_false_empty (db : Database) (a b : FromClause) :
    evalFrom db (.join a .inner b (some (.lit (.bool false)))) = [] := by
  rw [evalFrom_inner_join]; simp only
  generalize evalFrom db a = leftRows
  generalize evalFrom db b = rightRows
  induction leftRows with
  | nil => rfl
  | cons lr rest ih =>
    simp only [List.flatMap_cons, ih, List.append_nil]
    simp only [evalExprWithDb_lit, List.filterMap_none]

/-- LEFT JOIN with ON FALSE returns all left rows with NULLs for right -/
theorem left_join_false_all_left (db : Database) (a b : FromClause) :
    let result := evalFrom db (.join a .left b (some (.lit (.bool false))))
    let leftRows := evalFrom db a
    result.length = leftRows.length := by
  simp only
  rw [evalFrom_left_join]; simp only
  generalize evalFrom db a = leftRows
  generalize evalFrom db b = rightRows
  induction leftRows with
  | nil => rfl
  | cons lr rest ih =>
    simp only [List.flatMap_cons, List.length_append, ih]
    dsimp
    simp only [evalExprWithDb_lit, List.filterMap_none, List.isEmpty_nil, ite_true]
    cases rightRows.head? <;> simp <;> omega

/-- CROSS JOIN cardinality: |A CROSS JOIN B| = |A| * |B| -/
theorem cross_join_cardinality (db : Database) (a b : FromClause) :
    let rowsA := evalFrom db a
    let rowsB := evalFrom db b
    let rowsAB := evalFrom db (.join a .cross b none)
    rowsAB.length = rowsA.length * rowsB.length := by
  simp only []
  rw [evalFrom_cross_join]; simp only []
  apply List.length_flatMap_const
  intro lr _
  exact List.length_map ..

/-- CROSS JOIN cardinality is symmetric: |A x B| = |B x A| -/
theorem cross_join_cardinality_comm (db : Database) (a b : FromClause) :
    let rowsAB := evalFrom db (.join a .cross b none)
    let rowsBA := evalFrom db (.join b .cross a none)
    rowsAB.length = rowsBA.length := by
  simp only []
  have h1 := cross_join_cardinality db a b
  have h2 := cross_join_cardinality db b a
  simp only [] at h1 h2
  rw [h1, h2, Nat.mul_comm]

/-- INNER JOIN cardinality upper bound: |A INNER JOIN B| <= |A| * |B| -/
theorem inner_join_cardinality_le (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rowsA := evalFrom db a
    let rowsB := evalFrom db b
    let rowsAB := evalFrom db (.join a .inner b on_)
    rowsAB.length ≤ rowsA.length * rowsB.length := by
  simp only []
  rw [evalFrom_inner_join]; simp only []
  apply List.length_flatMap_le
  intro lr _
  exact List.length_filterMap_le ..

/-- LEFT JOIN cardinality: |A LEFT JOIN B| >= |A| -/
theorem left_join_cardinality_ge (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rowsA := evalFrom db a
    let rowsAB := evalFrom db (.join a .left b on_)
    rowsAB.length ≥ rowsA.length := by
  simp only []
  rw [evalFrom_left_join]; simp only []
  apply List.length_flatMap_ge_length
  intro lr _
  exact left_join_body_length_ge_one _ ((evalFrom db b).head?) lr

/-- RIGHT JOIN cardinality: |A RIGHT JOIN B| >= |B| -/
theorem right_join_cardinality_ge (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rowsB := evalFrom db b
    let rowsAB := evalFrom db (.join a .right b on_)
    rowsAB.length ≥ rowsB.length := by
  simp only []
  rw [evalFrom_right_join]; simp only []
  apply List.length_flatMap_ge_length
  intro rr _
  exact right_join_body_length_ge_one _ ((evalFrom db a).head?) rr

/-- INNER JOIN with empty left produces empty result -/
theorem inner_join_empty_left (db : Database) (a b : FromClause) (on_ : Option Expr)
    (h : evalFrom db a = []) :
    evalFrom db (.join a .inner b on_) = [] := by
  rw [evalFrom_inner_join]; simp only [h]; rfl

/-- INNER JOIN with empty right produces empty result -/
theorem inner_join_empty_right (db : Database) (a b : FromClause) (on_ : Option Expr)
    (h : evalFrom db b = []) :
    evalFrom db (.join a .inner b on_) = [] := by
  rw [evalFrom_inner_join]; simp only [h, List.filterMap_nil]
  exact List.flatMap_const_nil _

/-- CROSS JOIN with empty left produces empty result -/
theorem cross_join_empty_left (db : Database) (a b : FromClause)
    (h : evalFrom db a = []) :
    evalFrom db (.join a .cross b none) = [] := by
  rw [evalFrom_cross_join]; simp only [h]; rfl

/-- CROSS JOIN with empty right produces empty result -/
theorem cross_join_empty_right (db : Database) (a b : FromClause)
    (h : evalFrom db b = []) :
    evalFrom db (.join a .cross b none) = [] := by
  rw [evalFrom_cross_join]; simp only [h, List.map_nil]
  exact List.flatMap_const_nil _

/-- Join associativity for CROSS JOIN: (A × B) × C has same cardinality as A × (B × C) -/
theorem cross_join_assoc_cardinality (db : Database) (a b c : FromClause) :
    let abc1 := evalFrom db (.join (.join a .cross b none) .cross c none)
    let abc2 := evalFrom db (.join a .cross (.join b .cross c none) none)
    abc1.length = abc2.length := by
  simp only []
  have h1 := cross_join_cardinality db (.join a .cross b none) c
  have h2 := cross_join_cardinality db a (.join b .cross c none)
  have hab := cross_join_cardinality db a b
  have hbc := cross_join_cardinality db b c
  simp only [] at h1 h2 hab hbc
  rw [h1, h2, hab, hbc, Nat.mul_assoc]

/-- INNER JOIN condition can be moved to WHERE (join-to-where conversion) -/
theorem inner_join_to_where (db : Database) (t1 t2 : TableRef) (cond : Expr) :
    let joinFrom := FromClause.join (.table t1) .inner (.table t2) (some cond)
    let crossFrom := FromClause.join (.table t1) .cross (.table t2) none
    let joinResult := evalFrom db joinFrom
    let crossFiltered := (evalFrom db crossFrom).filter fun row =>
      evalExprWithDb db row cond == some (.bool true)
    joinResult = crossFiltered := by
  simp only []
  rw [evalFrom_inner_join, evalFrom_cross_join]; simp only []
  rw [List.filter_flatMap]
  congr 1; funext lr
  generalize evalFrom db (.table t2) = rightRows
  induction rightRows with
  | nil => simp
  | cons rr rest ih =>
    simp only [List.filterMap_cons, List.map_cons, List.filter_cons]
    generalize hv : evalExprWithDb db (lr ++ rr) cond = v
    cases v with
    | none => simp; exact ih
    | some val =>
      cases val with
      | bool b => cases b <;> simp <;> exact ih
      | int _ => simp; exact ih
      | decimal _ _ => simp; exact ih
      | string _ => simp; exact ih
      | null _ => simp; exact ih

/-- LEFT JOIN preserves all left rows: every left row appears in the result -/
theorem left_join_preserves_left (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let leftRows := evalFrom db a
    let joinResult := evalFrom db (.join a .left b on_)
    ∀ lr ∈ leftRows, ∃ jr ∈ joinResult, ∀ (k : String) (v : Value),
      (k, v) ∈ lr → (k, v) ∈ jr := by
  simp only []
  rw [evalFrom_left_join]; simp only []
  intro lr hlr
  apply exists_mem_flatMap_of_length_ge_one _ _ lr hlr
  · -- body has length ≥ 1
    exact left_join_body_length_ge_one _ _ lr
  · -- every element of body preserves lr's columns
    intro jr hjr k v hkv
    -- hjr : jr ∈ (if matchingRows.isEmpty then ... else matchingRows)
    -- Split the if-then-else in hjr
    split at hjr
    · -- isEmpty = true: null-padded branch
      split at hjr
      · -- head? = some rightRow: jr ∈ [lr ++ rightRow.map null]
        simp at hjr; rw [hjr]; exact List.mem_append.mpr (.inl hkv)
      · -- head? = none: jr ∈ [lr]
        simp at hjr; rw [hjr]; exact hkv
    · -- isEmpty = false: jr ∈ matchingRows (compiled filterMap)
      -- Extract the source right row from filterMap membership
      rw [List.mem_filterMap] at hjr
      obtain ⟨rr, _, hf⟩ := hjr
      -- Case split on_ to reduce the compiled match and extract jr = lr ++ rr
      cases on_ with
      | none => simp at hf; rw [← hf]; exact List.mem_append.mpr (.inl hkv)
      | some cond =>
        simp only at hf
        generalize hv : evalExprWithDb db (lr ++ rr) cond = v at hf
        cases v with
        | none => simp at hf
        | some val =>
          cases val with
          | bool b => cases b <;> simp at hf; rw [← hf]; exact List.mem_append.mpr (.inl hkv)
          | int _ => simp at hf
          | decimal _ _ => simp at hf
          | string _ => simp at hf
          | null _ => simp at hf

/-- RIGHT JOIN preserves all right rows: every right row appears in the result -/
theorem right_join_preserves_right (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rightRows := evalFrom db b
    let joinResult := evalFrom db (.join a .right b on_)
    ∀ rr ∈ rightRows, ∃ jr ∈ joinResult, ∀ (k : String) (v : Value),
      (k, v) ∈ rr → (k, v) ∈ jr := by
  simp only []
  rw [evalFrom_right_join]; simp only []
  intro rr hrr
  apply exists_mem_flatMap_of_length_ge_one _ _ rr hrr
  · -- body has length ≥ 1
    exact right_join_body_length_ge_one _ _ rr
  · -- every element of body preserves rr's columns
    intro jr hjr k v hkv
    split at hjr
    · -- isEmpty = true: null-padded branch
      split at hjr
      · -- head? = some leftRow: jr ∈ [leftRow.map null ++ rr]
        simp at hjr; rw [hjr]; exact List.mem_append.mpr (.inr hkv)
      · -- head? = none: jr ∈ [rr]
        simp at hjr; rw [hjr]; exact hkv
    · -- isEmpty = false: jr ∈ matchingRows (compiled filterMap)
      rw [List.mem_filterMap] at hjr
      obtain ⟨lr, _, hf⟩ := hjr
      cases on_ with
      | none => simp at hf; rw [← hf]; exact List.mem_append.mpr (.inr hkv)
      | some cond =>
        simp only at hf
        generalize hv : evalExprWithDb db (lr ++ rr) cond = v at hf
        cases v with
        | none => simp at hf
        | some val =>
          cases val with
          | bool b => cases b <;> simp at hf; rw [← hf]; exact List.mem_append.mpr (.inr hkv)
          | int _ => simp at hf
          | decimal _ _ => simp at hf
          | string _ => simp at hf
          | null _ => simp at hf

/-- INNER JOIN is a subset of CROSS JOIN (when ON is given) -/
theorem inner_subset_cross (db : Database) (a b : FromClause) (cond : Expr) :
    let innerResult := evalFrom db (.join a .inner b (some cond))
    let crossResult := evalFrom db (.join a .cross b none)
    innerResult.length ≤ crossResult.length := by
  simp only []
  have h1 := inner_join_cardinality_le db a b (some cond)
  have h2 := cross_join_cardinality db a b
  simp only [] at h1 h2
  omega

/-- flatMap length equality when per-element contributions match -/
private theorem flatMap_length_eq_of_forall {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, (f x).length = (g x).length) :
    (l.flatMap f).length = (l.flatMap g).length := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append]
    rw [h a List.mem_cons_self]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- Filter predicate is false on null-mapped rows when find? returns none on the left part -/
private theorem filter_pred_false_on_null_mapped (rightRow : Row) (col : String) :
    (match (rightRow.map fun (k, _) => (k, Value.null none)).find?
        (fun (k, _) => k == col) with
    | some (_, v) => !isNullValue v
    | none => false) = false := by
  induction rightRow with
  | nil => simp
  | cons hd rest ih =>
    simp only [List.map_cons, List.find?_cons]
    cases hd.1 == col with
    | true => simp [isNullValue]
    | false => exact ih

/-- Converting LEFT JOIN to INNER JOIN by filtering out NULLs:
    If we filter the result of LEFT JOIN to exclude rows where right columns are NULL,
    the resulting list has the same length as the INNER JOIN result.

    Preconditions:
    - rightCol does not appear in left table rows (qualified column from right table)
    - rightCol exists and is non-null in every right table row -/
theorem left_join_filter_null_is_inner (db : Database) (a b : FromClause) (on_ : Option Expr)
    (rightCol : String)
    (hNotInLeft : ∀ lr ∈ evalFrom db a,
      lr.find? (fun (k, _) => k == rightCol) = none)
    (hRightNonNull : ∀ rr ∈ evalFrom db b,
      (match rr.find? (fun (k, _) => k == rightCol) with
      | some (_, v) => !isNullValue v
      | none => false) = true) :
    let leftResult := evalFrom db (.join a .left b on_)
    let innerResult := evalFrom db (.join a .inner b on_)
    let filtered := leftResult.filter fun row =>
      match row.find? (fun (k, _) => k == rightCol) with
      | some (_, v) => !isNullValue v
      | none => false
    filtered.length = innerResult.length := by
  simp only []
  rw [evalFrom_left_join, evalFrom_inner_join]; simp only []
  rw [List.filter_flatMap]
  apply flatMap_length_eq_of_forall
  intro lr hlr
  -- Bridge hNotInLeft to the .fst form used in the goal after rw [evalFrom_left_join].
  -- The theorem's `fun (k, _) => k == rightCol` compiles to two different forms:
  --   hypothesis: `fun x => match x with | (k, snd) => k == rightCol`
  --   goal (after rw): `fun x => x.fst == rightCol`
  -- These are definitionally equal, so `have` with type ascription bridges them.
  have hNotInLeft' : List.find? (fun (x : String × Value) => x.fst == rightCol) lr = none :=
    hNotInLeft lr hlr
  split
  · -- isEmpty = true: inner join filterMap is empty
    rename_i hIsEmpty
    have hInnerEmpty := List.isEmpty_iff.mp hIsEmpty
    split
    · -- head? = some rightRow: left body = [lr ++ rightRow.map null]
      rename_i rightRow _
      simp only [List.filter_cons, List.filter_nil]
      rw [List.find?_append, hNotInLeft', Option.none_or]
      -- Bridge filter_pred_false_on_null_mapped to goal's .fst form
      have hNullFalse : (match (List.map (fun (x : String × Value) => (x.fst, Value.null none))
          rightRow).find? (fun (x : String × Value) => x.fst == rightCol) with
        | some (_, v) => !isNullValue (some v) | none => false) = false :=
        filter_pred_false_on_null_mapped rightRow rightCol
      rw [hNullFalse, hInnerEmpty]; simp
    · -- head? = none: left body = [lr]
      simp only [List.filter_cons, List.filter_nil]
      have hpred : (match List.find? (fun (x : String × Value) => x.fst == rightCol) lr with
        | some (_, v) => !isNullValue (some v) | none => false) = false := by rw [hNotInLeft']
      rw [hpred, hInnerEmpty]; simp
  · -- isEmpty = false: left body = filterMap (same as inner)
    -- Show filter preserves all elements (all matched rows have non-null rightCol)
    congr 1
    rw [List.filter_eq_self]
    intro mr hmr
    rw [List.mem_filterMap] at hmr
    obtain ⟨rr, hrr, hf⟩ := hmr
    -- Bridge hRightNonNull to goal's .fst form
    have hRightNonNull' : (match List.find? (fun (x : String × Value) => x.fst == rightCol)
        rr with | some (_, v) => !isNullValue (some v) | none => false) = true :=
      hRightNonNull rr hrr
    cases on_ with
    | none =>
      simp at hf; rw [← hf]
      rw [List.find?_append, hNotInLeft', Option.none_or]
      exact hRightNonNull'
    | some cond =>
      simp only at hf
      generalize hv : evalExprWithDb db (lr ++ rr) cond = v at hf
      cases v with
      | none => simp at hf
      | some val =>
        cases val with
        | bool b =>
          cases b with
          | true =>
            simp at hf; rw [← hf]
            rw [List.find?_append, hNotInLeft', Option.none_or]
            exact hRightNonNull'
          | false => simp at hf
        | int _ => simp at hf
        | decimal _ _ => simp at hf
        | string _ => simp at hf
        | null _ => simp at hf

-- ============================================================================
-- Subquery Theorems
-- ============================================================================

/-- EXISTS on empty subquery is FALSE -/
theorem exists_empty_false (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.exists false (.simple sel)) = some (.bool false) := by
  rw [evalExprWithDb_exists_simple]; simp [h]

/-- NOT EXISTS on empty subquery is TRUE -/
theorem not_exists_empty_true (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.exists true (.simple sel)) = some (.bool true) := by
  rw [evalExprWithDb_exists_simple]; simp [h]

/-- EXISTS on non-empty subquery is TRUE -/
theorem exists_nonempty_true (db : Database) (row : Row) (sel : SelectStmt)
    (h : (evalSelectWithContext db row sel).length > 0) :
    evalExprWithDb db row (Expr.exists false (.simple sel)) = some (.bool true) := by
  rw [evalExprWithDb_exists_simple]
  have hne : (evalSelectWithContext db row sel).isEmpty = false := by
    cases hlist : evalSelectWithContext db row sel with
    | nil => simp [hlist] at h
    | cons _ _ => rfl
  simp [hne]

/-- NOT EXISTS on non-empty subquery is FALSE -/
theorem not_exists_nonempty_false (db : Database) (row : Row) (sel : SelectStmt)
    (h : (evalSelectWithContext db row sel).length > 0) :
    evalExprWithDb db row (Expr.exists true (.simple sel)) = some (.bool false) := by
  rw [evalExprWithDb_exists_simple]
  have hne : (evalSelectWithContext db row sel).isEmpty = false := by
    cases hlist : evalSelectWithContext db row sel with
    | nil => simp [hlist] at h
    | cons _ _ => rfl
  simp [hne]

/-- Double negation: NOT NOT EXISTS = EXISTS (generic over SubQuery payloads, #218) -/
theorem not_not_exists (sel : SubQuery) :
    Expr.exists true sel ≃ₑ Expr.unaryOp .not (Expr.exists false sel) := by
  intro row
  simp only [evalExpr, evalExprWithDb_unaryOp, evalExprWithDb_exists, evalUnaryOp]
  cases evalSubQueryWithContext (fun _ => []) row sel with
  | nil => rfl
  | cons _ _ => rfl

/-- x IN (empty subquery) = FALSE: when subquery is empty, IN returns FALSE;
    otherwise falls through to IN(e, sel).
    Requires that e evaluates without error (non-none) for all rows. -/
theorem in_empty_subquery_false (e : Expr) (sel : SelectStmt)
    (hE : ∀ row, evalExpr row e ≠ none) :
    Expr.inSubquery e false (.simple sel) ≃ₑ
    Expr.case [(Expr.unaryOp .not (Expr.exists false (.simple sel)), Expr.lit (.bool false))]
              (some (Expr.inSubquery e false (.simple sel))) := by
  intro row
  simp only [evalExpr] at hE ⊢
  rw [evalExprWithDb_case]
  cases hsel : evalSelectWithContext (fun _ => []) row sel with
  | nil =>
    -- Subquery empty: NOT EXISTS = true → CASE returns FALSE
    -- LHS: IN on empty = false (since e evaluates to some value by hE)
    have hcond : evalExprWithDb (fun _ => []) row (Expr.unaryOp .not (Expr.exists false (.simple sel))) = some (.bool true) := by
      rw [evalExprWithDb_unaryOp, evalExprWithDb_exists_simple, hsel]
      simp [List.isEmpty, evalUnaryOp]
    rw [evalCase_cons_true _ _ _ _ _ _ hcond, evalExprWithDb_lit]
    rw [evalExprWithDb_inSubquery_simple, hsel]
    cases hev : evalExprWithDb (fun _ => []) row e with
    | none => exact absurd hev (hE row)
    | some v => simp [List.any]
  | cons hd tl =>
    -- Subquery non-empty: NOT EXISTS = false → falls to ELSE = IN(e, sel)
    have hcond : evalExprWithDb (fun _ => []) row (Expr.unaryOp .not (Expr.exists false (.simple sel))) = some (.bool false) := by
      rw [evalExprWithDb_unaryOp, evalExprWithDb_exists_simple, hsel]
      simp [List.isEmpty, evalUnaryOp]
    rw [evalCase_cons_false _ _ _ _ _ _ hcond, evalCase_nil_some]

/-- x NOT IN (empty subquery) = TRUE: when subquery is empty, NOT IN returns TRUE;
    otherwise falls through to NOT IN(e, sel).
    Requires that e evaluates without error (non-none) for all rows. -/
theorem not_in_empty_subquery_true (e : Expr) (sel : SelectStmt)
    (hE : ∀ row, evalExpr row e ≠ none) :
    Expr.inSubquery e true (.simple sel) ≃ₑ
    Expr.case [(Expr.unaryOp .not (Expr.exists false (.simple sel)), Expr.lit (.bool true))]
              (some (Expr.inSubquery e true (.simple sel))) := by
  intro row
  simp only [evalExpr] at hE ⊢
  rw [evalExprWithDb_case]
  cases hsel : evalSelectWithContext (fun _ => []) row sel with
  | nil =>
    -- Subquery empty: NOT EXISTS = true → CASE returns TRUE
    -- LHS: NOT IN on empty = true (since e evaluates to some value by hE)
    have hcond : evalExprWithDb (fun _ => []) row (Expr.unaryOp .not (Expr.exists false (.simple sel))) = some (.bool true) := by
      rw [evalExprWithDb_unaryOp, evalExprWithDb_exists_simple, hsel]
      simp [List.isEmpty, evalUnaryOp]
    rw [evalCase_cons_true _ _ _ _ _ _ hcond, evalExprWithDb_lit]
    rw [evalExprWithDb_inSubquery_simple, hsel]
    cases hev : evalExprWithDb (fun _ => []) row e with
    | none => exact absurd hev (hE row)
    | some v => simp [List.any]
  | cons hd tl =>
    -- Subquery non-empty: NOT EXISTS = false → falls to ELSE = NOT IN(e, sel)
    have hcond : evalExprWithDb (fun _ => []) row (Expr.unaryOp .not (Expr.exists false (.simple sel))) = some (.bool false) := by
      rw [evalExprWithDb_unaryOp, evalExprWithDb_exists_simple, hsel]
      simp [List.isEmpty, evalUnaryOp]
    rw [evalCase_cons_false _ _ _ _ _ _ hcond, evalCase_nil_some]

/-- Scalar subquery returning empty = NULL -/
theorem scalar_subquery_empty_null (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.subquery (.simple sel)) = some (.null none) := by
  rw [evalExprWithDb_subquery_simple, h]; rfl

/-- EXISTS can be rewritten as COUNT(*) > 0 (semantic equivalence) -/
theorem exists_as_count_gt_zero (db : Database) (row : Row) (sel : SelectStmt) :
    let existsResult := evalExprWithDb db row (Expr.exists false (.simple sel))
    let subRows := evalSelectWithContext db row sel
    existsResult = some (.bool (subRows.length > 0)) := by
  simp only
  rw [evalExprWithDb_exists_simple]
  cases evalSelectWithContext db row sel with
  | nil => rfl
  | cons _ _ => rfl

/-- NOT EXISTS can be rewritten as COUNT(*) = 0 (semantic equivalence) -/
theorem not_exists_as_count_eq_zero (db : Database) (row : Row) (sel : SelectStmt) :
    let existsResult := evalExprWithDb db row (Expr.exists true (.simple sel))
    let subRows := evalSelectWithContext db row sel
    existsResult = some (.bool (subRows.length == 0)) := by
  simp only
  rw [evalExprWithDb_exists_simple]
  cases evalSelectWithContext db row sel with
  | nil => rfl
  | cons _ _ => rfl

/-- Helper: list.any p = !(list.filter p).isEmpty -/
private theorem List.any_eq_not_isEmpty_filter {α : Type} (p : α → Bool) (l : List α) :
    l.any p = !(l.filter p).isEmpty := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.any_cons, List.filter_cons]
    cases hp : p a <;> simp [ih]

/-- Helper: (l.map f).isEmpty = l.isEmpty -/
private theorem List.isEmpty_map {α β : Type} (f : α → β) (l : List α) :
    (l.map f).isEmpty = l.isEmpty := by
  cases l <;> rfl

/-- Helper: (l.map f).any p = l.any (fun x => p (f x)) -/
private theorem List.any_map {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).any p = l.any (fun x => p (f x)) := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [List.any_cons, ih]

/-- IN subquery is equivalent to EXISTS with equality condition.
    x IN (SELECT tableName.col FROM t) ≡ EXISTS (SELECT 1 FROM t WHERE t.col = x)
    Requires that e evaluates to a value and is stable under row extension.
    The hNoAgg/hNoWin conditions are needed because hasAggregate/exprHasWindowFn are
    partial functions. For concrete items (.col, .lit), use `native_decide`. -/
theorem in_subquery_as_exists (db : Database) (row : Row) (e : Expr)
    (tableName : String) (colName : String) (v : Value)
    (heval : evalExprWithDb db row e = some v)
    (hstable : ∀ extra : Row, evalExprWithDb db (row ++ extra) e = some v)
    (hNoAggCol : selectHasAggregate [.exprItem (.col ⟨some tableName, colName⟩) none] = false)
    (hNoWinCol : selectHasWindowFn [.exprItem (.col ⟨some tableName, colName⟩) none] = false)
    (hNoAggLit : selectHasAggregate [.exprItem (.lit (.int 1)) none] = false)
    (hNoWinLit : selectHasWindowFn [.exprItem (.lit (.int 1)) none] = false) :
    let inSub := Expr.inSubquery e false
      (.simple (SelectStmt.mk false [.exprItem (.col ⟨some tableName, colName⟩) none]
        (some (.table ⟨tableName, none⟩)) none [] none [] none none))
    let existsSub := Expr.exists false
      (.simple (SelectStmt.mk false [.exprItem (.lit (.int 1)) none]
        (some (.table ⟨tableName, none⟩))
        (some (.binOp .eq (.col ⟨some tableName, colName⟩) e))
        [] none [] none none))
    evalExprWithDb db row inSub = evalExprWithDb db row existsSub := by
  simp only []
  -- Unfold both sides
  rw [evalExprWithDb_inSubquery_simple, evalExprWithDb_exists_simple]
  -- Substitute heval into the IN side
  rw [heval]
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- Simplify both evalSelectWithContext calls
  rw [evalSelectWithContext_simple_project db row _ _ hNoAggCol hNoWinCol]
  rw [evalSelectWithContext_simple_project_where db row _ _ _ hNoAggLit hNoWinLit]
  -- LHS: (contextRows.map project_col).any matchPred
  -- RHS: !(contextRows.filter filterPred |>.map project_lit).isEmpty
  congr 1
  -- Transform LHS using list algebra
  rw [List.any_map, List.isEmpty_map, List.any_eq_not_isEmpty_filter]
  -- Now: Value.bool (!(filter pred1 ctx).isEmpty) = Value.bool (!(filter pred2 ctx).isEmpty)
  congr 1  -- strip Value.bool
  congr 1  -- strip !
  congr 1  -- strip .isEmpty
  -- goal: filter pred1 ctx = filter pred2 ctx where ctx = map (row ++ ·) baseRows
  -- Can't use funext because hstable requires r = row ++ extra
  apply List.filter_congr
  intro r hr
  -- r ∈ List.map (row ++ ·) baseRows, so r = row ++ extra for some extra
  obtain ⟨extra, _, rfl⟩ := List.mem_map.mp hr
  -- Per-row equivalence: IN match pred = EXISTS WHERE pred
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evalSelectItem,
    evalExprWithDb_binOp]
  rw [hstable extra]
  -- Case split on column evaluation to reduce nested match + head?
  cases hcol : evalExprWithDb db (row ++ extra) (.col ⟨some tableName, colName⟩) with
  | none => cases v <;> rfl
  | some colVal =>
    simp only [List.head?_cons]
    rw [Value.eq_comm v colVal]
    cases colVal <;> cases v <;> rfl

/-- NOT IN subquery is equivalent to NOT EXISTS with equality condition.
    Requires that e evaluates to a value and is stable under row extension. -/
theorem not_in_subquery_as_not_exists (db : Database) (row : Row) (e : Expr)
    (tableName : String) (colName : String) (v : Value)
    (heval : evalExprWithDb db row e = some v)
    (hstable : ∀ extra : Row, evalExprWithDb db (row ++ extra) e = some v)
    (hNoAggCol : selectHasAggregate [.exprItem (.col ⟨some tableName, colName⟩) none] = false)
    (hNoWinCol : selectHasWindowFn [.exprItem (.col ⟨some tableName, colName⟩) none] = false)
    (hNoAggLit : selectHasAggregate [.exprItem (.lit (.int 1)) none] = false)
    (hNoWinLit : selectHasWindowFn [.exprItem (.lit (.int 1)) none] = false) :
    let notInSub := Expr.inSubquery e true
      (.simple (SelectStmt.mk false [.exprItem (.col ⟨some tableName, colName⟩) none]
        (some (.table ⟨tableName, none⟩)) none [] none [] none none))
    let notExistsSub := Expr.exists true
      (.simple (SelectStmt.mk false [.exprItem (.lit (.int 1)) none]
        (some (.table ⟨tableName, none⟩))
        (some (.binOp .eq (.col ⟨some tableName, colName⟩) e))
        [] none [] none none))
    evalExprWithDb db row notInSub = evalExprWithDb db row notExistsSub := by
  simp only []
  rw [evalExprWithDb_inSubquery_simple, evalExprWithDb_exists_simple]
  rw [heval]
  simp only [↓reduceIte]
  rw [evalSelectWithContext_simple_project db row _ _ hNoAggCol hNoWinCol]
  rw [evalSelectWithContext_simple_project_where db row _ _ _ hNoAggLit hNoWinLit]
  congr 1  -- strip some
  -- List algebra transformations
  rw [List.any_map, List.isEmpty_map, List.any_eq_not_isEmpty_filter]
  -- Goal: Value.bool (!(!(filter pred1 ctx).isEmpty)) = Value.bool ((filter pred2 ctx).isEmpty)
  congr 1  -- strip Value.bool
  -- Goal: !(!(filter pred1 ctx).isEmpty) = (filter pred2 ctx).isEmpty
  simp only [Bool.not_not]
  -- Goal: (filter pred1 ctx).isEmpty = (filter pred2 ctx).isEmpty
  congr 1  -- strip .isEmpty
  -- Goal: filter pred1 ctx = filter pred2 ctx
  apply List.filter_congr
  intro r hr
  obtain ⟨extra, _, rfl⟩ := List.mem_map.mp hr
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evalSelectItem,
    evalExprWithDb_binOp]
  rw [hstable extra]
  cases hcol : evalExprWithDb db (row ++ extra) (.col ⟨some tableName, colName⟩) with
  | none => cases v <;> rfl
  | some colVal =>
    simp only [List.head?_cons]
    rw [Value.eq_comm v colVal]
    cases colVal <;> cases v <;> rfl

/-- Subquery with LIMIT 1 returns at most one row -/
theorem subquery_limit_one (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 1) offset
    (evalSelectWithContext db row sel).length ≤ 1 := by
  simp only
  rw [evalSelectWithContext_limit_offset]
  simp [List.length_take]
  omega

/-- Scalar subquery is equivalent to first value of subquery with LIMIT 1 -/
theorem scalar_subquery_is_first (db : Database) (row : Row) (sel : SelectStmt) :
    let result := evalExprWithDb db row (Expr.subquery (.simple sel))
    let subRows := evalSelectWithContext db row sel
    result = match subRows.head? with
      | some subRow => subRow.head?.map (·.2)
      | none => some (.null none) := by
  simp only
  exact evalExprWithDb_subquery_simple db row sel

/-- EXISTS is monotonic: more rows in subquery doesn't change TRUE to FALSE -/
theorem exists_monotonic (db : Database) (row : Row) (sel1 sel2 : SelectStmt)
    (h : ∀ r ∈ evalSelectWithContext db row sel1,
         r ∈ evalSelectWithContext db row sel2) :
    evalExprWithDb db row (Expr.exists false (.simple sel1)) = some (.bool true) →
    evalExprWithDb db row (Expr.exists false (.simple sel2)) = some (.bool true) := by
  rw [evalExprWithDb_exists_simple, evalExprWithDb_exists_simple]
  intro hprem
  cases hsel1 : evalSelectWithContext db row sel1 with
  | nil => simp [hsel1] at hprem
  | cons r rs =>
    have hr := h r (hsel1 ▸ List.mem_cons_self ..)
    cases hsel2 : evalSelectWithContext db row sel2 with
    | nil => exact absurd hsel2 (List.ne_nil_of_mem hr)
    | cons _ _ => rfl

/-- Adding WHERE TRUE to subquery doesn't change result -/
theorem subquery_where_true (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ none groupBy having orderBy limit offset
    let selWithTrue := SelectStmt.mk distinct items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset
    evalSelectWithContext db row sel = evalSelectWithContext db row selWithTrue := by
  simp only
  apply evalSelectWithContext_where_congr
  intro r
  simp [evalExprWithDb_lit]

/-- Adding WHERE FALSE to subquery makes it empty (requires no aggregates) -/
theorem subquery_where_false (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (hNoAgg : selectHasAggregate items = false) :
    let selWithFalse := SelectStmt.mk distinct items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset
    evalSelectWithContext db row selWithFalse = [] := by
  simp only
  apply evalSelectWithContext_filter_all_false
  · exact hNoAgg
  · intro r; simp [evalExprWithDb_lit]

/-- IN with single-value subquery is equivalent to equality.
    Requires that the expression and value have compatible types (val.eq v produces some result). -/
theorem in_singleton_subquery (db : Database) (row : Row) (e : Expr) (sel : SelectStmt)
    (colName : String) (v : Value)
    (h : evalSelectWithContext db row sel = [[(colName, v)]])
    (hCompat : ∀ val, evalExprWithDb db row e = some val → ∃ b, val.eq v = some b) :
    evalExprWithDb db row (Expr.inSubquery e false (.simple sel)) =
    evalExprWithDb db row (Expr.binOp .eq e (Expr.lit v)) := by
  rw [evalExprWithDb_inSubquery_simple, h]
  simp [List.any, List.head?]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  cases hev : evalExprWithDb db row e with
  | none => rfl
  | some val =>
    obtain ⟨b, hb⟩ := hCompat val hev
    cases val <;> cases v <;> simp_all [evalBinOp, Value.eq]

-- ============================================================================
-- Helper lemmas for anti-join proof
-- ============================================================================

/-- filter-then-map equals flatMap with conditional -/
private theorem list_filter_map_eq_flatMap {α β : Type} (l : List α) (p : α → Bool) (f : α → β) :
    (l.filter p).map f = l.flatMap (fun x => if p x then [f x] else []) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.flatMap_cons]
    cases hp : p a <;> simp [List.filter, hp, ih]

/-- filter-then-map distributes through flatMap -/
private theorem list_filter_map_of_flatMap {α β γ : Type} (l : List α) (g : α → List β)
    (p : β → Bool) (f : β → γ) :
    ((l.flatMap g).filter p).map f = l.flatMap (fun x => ((g x).filter p).map f) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.filter_append, List.map_append, ih]

/-- flatMap congruence with membership -/
private theorem list_flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self]
    exact congrArg _ (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

/-- lookup on l₁ ++ l₂: if l₁.lookup = none, falls through to l₂ -/
private theorem lookup_append_none_left :
    ∀ (l₁ l₂ : List (String × Value)) (key : String),
    l₁.lookup key = none → (l₁ ++ l₂).lookup key = l₂.lookup key
  | [], _, _, _ => by simp
  | (_k, _v) :: rest, l₂, key, h => by
    simp only [List.cons_append, List.lookup] at h ⊢
    split
    · rename_i heq; simp only [heq] at h; exact nomatch h
    · rename_i hne
      simp only [hne] at h
      exact lookup_append_none_left rest l₂ key h

/-- isNullValue of any lookup on a null-padded list is true -/
private theorem isNullValue_lookup_nullPad :
    ∀ (l : List (String × Value)) (key : String),
    isNullValue ((l.map (fun (k, _) => (k, Value.null none))).lookup key) = true
  | [], _ => by simp [isNullValue]
  | (_k, _v) :: rest, key => by
    simp only [List.map_cons, List.lookup]
    split
    · simp [isNullValue]
    · exact isNullValue_lookup_nullPad rest key

/-- filter_append + showing null-padded right side filters to empty -/
private theorem filter_null_pad_empty (lr : List (String × Value))
    (rr : List (String × Value)) (tName : String)
    (hProj : (lr ++ rr).filter (fun (k, _) => k.startsWith s!"{tName}.") =
             lr.filter (fun (k, _) => k.startsWith s!"{tName}.")) :
    (List.map (fun (k, _) => (k, Value.null none)) rr).filter
      (fun (k, _) => k.startsWith s!"{tName}.") = [] := by
  -- From hProj: lr.filter P ++ rr.filter P = lr.filter P, so rr.filter P = []
  rw [List.filter_append] at hProj
  have hRrEmpty : rr.filter (fun (k, _) => k.startsWith s!"{tName}.") = [] := by
    have : (lr.filter (fun (k, _) => k.startsWith s!"{tName}.") ++
            rr.filter (fun (k, _) => k.startsWith s!"{tName}.")).length =
           (lr.filter (fun (k, _) => k.startsWith s!"{tName}.")).length := by
      rw [hProj]
    rw [List.length_append] at this
    have hlen : (rr.filter (fun (k, _) => k.startsWith s!"{tName}.")).length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero hlen
  -- The null-padded list has the same keys as rr, so its filter is also []
  rw [List.filter_eq_nil_iff] at hRrEmpty ⊢
  intro ⟨k, v⟩ hMem
  simp only [List.mem_map] at hMem
  obtain ⟨⟨k', v'⟩, hk'Mem, hEq⟩ := hMem
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨rfl, _⟩ := hEq
  exact hRrEmpty ⟨k', v'⟩ hk'Mem

/-- If a join match exists with a qualified row from s,
    then the IN subquery returns true. -/
theorem join_match_implies_in_subquery (db : Database) (row : Row)
    (x : Expr) (sName yCol : String) (sRow : Row)
    (hMem : sRow ∈ evalFrom db (.table ⟨sName, some sName⟩))
    (hStable : ∀ extra : Row, evalExprWithDb db row x = evalExprWithDb db (row ++ extra) x)
    (hNoAgg : selectHasAggregate [.exprItem (.col ⟨some sName, yCol⟩) none] = false)
    (hNoWin : selectHasWindowFn [.exprItem (.col ⟨some sName, yCol⟩) none] = false)
    (hMatch : evalExprWithDb db (row ++ sRow)
                (Expr.binOp .eq x (.col ⟨some sName, yCol⟩)) = some (.bool true)) :
    evalExprWithDb db row (Expr.inSubquery x false
      (.simple (SelectStmt.mk false
        [.exprItem (.col ⟨some sName, yCol⟩) none]
        (some (.table ⟨sName, some sName⟩))
        none [] none [] none none))) = some (.bool true) := by
  rw [evalExprWithDb_binOp] at hMatch
  rw [← hStable sRow] at hMatch
  generalize hv : evalExprWithDb db row x = valX at hMatch
  generalize hw : evalExprWithDb db (row ++ sRow) (.col ⟨some sName, yCol⟩) = valY at hMatch
  cases valX with
  | none => simp [evalBinOp] at hMatch
  | some v =>
    cases valY with
    | none => simp [evalBinOp] at hMatch
    | some w =>
      have heq := eq_true_of_evalBinOp_eq hMatch
      rw [evalExprWithDb_inSubquery_simple, hv]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [evalSelectWithContext_simple_project db row _ _ hNoAgg hNoWin]
      rw [List.any_map, List.any_map]
      congr 1; congr 1
      rw [List.any_eq_true]
      refine ⟨sRow, hMem, ?_⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evalSelectItem, hw,
        List.head?_cons]
      rw [Option.beq_some_true_iff]
      exact heq

/-- NOT IN subquery can be unnested to an anti-join pattern.
    SELECT t.* FROM t WHERE t.x NOT IN (SELECT s.y FROM s)
    ≡ SELECT t.* FROM t LEFT JOIN s ON t.x = s.y WHERE s.y IS NULL

    The anti-join returns rows from t that have no matching rows in s.

    Preconditions:
    - hStable: t.xCol eval is stable when extra columns are appended
    - hEvalSome: t.xCol always evaluates to some value (not none/error)
    - hNoAgg/hNoWin: subquery items have no aggregates/window functions
    - hProjT: t.* projection on combined row equals projection on t row alone
    - hNotInLeft: s.yCol is not present in left table rows -/
theorem not_in_subquery_unnest_to_antijoin (db : Database)
    (tName sName : String) (xCol yCol : String)
    (hStable : ∀ row ∈ evalFrom db (.table ⟨tName, some tName⟩), ∀ extra : Row,
      evalExprWithDb db row (.col ⟨some tName, xCol⟩) =
      evalExprWithDb db (row ++ extra) (.col ⟨some tName, xCol⟩))
    (hEvalSome : ∀ row ∈ evalFrom db (.table ⟨tName, some tName⟩),
      ∃ v, evalExprWithDb db row (.col ⟨some tName, xCol⟩) = some v)
    (hNoAgg : selectHasAggregate [.exprItem (.col ⟨some sName, yCol⟩) none] = false)
    (hNoWin : selectHasWindowFn [.exprItem (.col ⟨some sName, yCol⟩) none] = false)
    (hProjT : ∀ tRow ∈ evalFrom db (.table ⟨tName, some tName⟩),
      ∀ sRow ∈ evalFrom db (.table ⟨sName, some sName⟩),
      (tRow ++ sRow).filter (fun (k, _) => k.startsWith s!"{tName}.") =
      tRow.filter (fun (k, _) => k.startsWith s!"{tName}."))
    (hNotInLeft : ∀ lr ∈ evalFrom db (.table ⟨tName, some tName⟩),
      lr.getQualified (some sName) yCol = none) :
    let notInForm := SelectStmt.mk false
        [.star (some tName)]  -- SELECT t.*
        (some (.table ⟨tName, some tName⟩))  -- FROM t
        (some (.inSubquery
          (.col ⟨some tName, xCol⟩)
          true  -- negated (NOT IN)
          (.simple (SelectStmt.mk false
            [.exprItem (.col ⟨some sName, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩))
            none [] none [] none none))))  -- WHERE t.x NOT IN (SELECT s.y FROM s)
        [] none [] none none
    let antijoinForm := SelectStmt.mk false
        [.star (some tName)]  -- SELECT t.*
        (some (.join
          (.table ⟨tName, some tName⟩)
          .left  -- LEFT JOIN
          (.table ⟨sName, some sName⟩)
          (some (.binOp .eq
            (.col ⟨some tName, xCol⟩)
            (.col ⟨some sName, yCol⟩)))))  -- LEFT JOIN s ON t.x = s.y
        (some (.unaryOp .isNull (.col ⟨some sName, yCol⟩)))  -- WHERE s.y IS NULL
        [] none [] none none
    evalSelect db notInForm = evalSelect db antijoinForm := by
  simp only []
  -- Decompose LHS: SELECT t.* FROM t WHERE NOT IN(...)
  rw [evalSelect_nondistinct_project_where db [.star (some tName)]
    (.table ⟨tName, some tName⟩)
    (Expr.inSubquery (.col ⟨some tName, xCol⟩) true
      (.simple (SelectStmt.mk false [.exprItem (.col ⟨some sName, yCol⟩) none]
        (some (.table ⟨sName, some sName⟩)) none [] none [] none none)))
    (selectHasAggregate_qualified_star tName) (selectHasWindowFn_qualified_star tName)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evalSelectItem_qualified_star]
  -- Decompose RHS: SELECT t.* FROM t LEFT JOIN s ON ... WHERE IS NULL(...)
  rw [evalSelect_nondistinct_project_where db [.star (some tName)]
    (.join (.table ⟨tName, some tName⟩) .left (.table ⟨sName, some sName⟩)
      (some (.binOp .eq (.col ⟨some tName, xCol⟩) (.col ⟨some sName, yCol⟩))))
    (.unaryOp .isNull (.col ⟨some sName, yCol⟩))
    (selectHasAggregate_qualified_star tName) (selectHasWindowFn_qualified_star tName)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evalSelectItem_qualified_star]
  -- Expand LEFT JOIN
  rw [evalFrom_left_join]
  dsimp only []
  -- Goal: (tRows.filter notInPred).map proj = ((tRows.flatMap ljBody).filter isNullPred).map proj
  -- Convert LHS to flatMap form
  rw [list_filter_map_eq_flatMap]
  -- Convert RHS: push filter/map into flatMap
  rw [list_filter_map_of_flatMap]
  -- Both sides: tRows.flatMap (...)
  -- Show per-element equality
  apply list_flatMap_congr_mem
  intro lr hlr
  -- Goal: (if notInPred lr then [proj lr] else []) =
  --        ((ljBody lr).filter isNullPred).map proj
  -- Define matchingRows - use generalize since set requires Mathlib
  -- Goal: (if notInPred lr then [proj lr] else []) =
  --       ((ljBody lr).filter isNullPred).map proj
  -- Use 'show' to restate goal with a 'let' binding for matchingRows
  -- This bridges the compiled match form via definitional equality
  show (if (evalExprWithDb db lr
      (Expr.inSubquery (.col ⟨some tName, xCol⟩) true
        (.simple (SelectStmt.mk false [.exprItem (.col ⟨some sName, yCol⟩) none]
          (some (.table ⟨sName, some sName⟩)) none [] none [] none none)))
      == some (Value.bool true)) = true
    then [lr.filter (fun x => x.fst.startsWith s!"{tName}.")] else []) =
    (let matchingRows := (evalFrom db (.table ⟨sName, some sName⟩)).filterMap (fun rr =>
      match evalExprWithDb db (lr ++ rr)
          (.binOp .eq (.col ⟨some tName, xCol⟩) (.col ⟨some sName, yCol⟩)) with
      | some (.bool true) => some (lr ++ rr)
      | _ => none)
    ((if matchingRows.isEmpty then
      match (evalFrom db (.table ⟨sName, some sName⟩)).head? with
      | some rightRow => [lr ++ rightRow.map (fun (k, _) => (k, Value.null none))]
      | none => [lr]
    else matchingRows).filter (fun row =>
      evalExprWithDb db row (.unaryOp .isNull (.col ⟨some sName, yCol⟩))
      == some (Value.bool true))).map (fun row =>
      row.filter (fun x => x.fst.startsWith s!"{tName}.")))
  -- Now generalize the fresh filterMap (which matches because show restated the goal)
  generalize hMatchDef : (evalFrom db (.table ⟨sName, some sName⟩)).filterMap (fun rr =>
    match evalExprWithDb db (lr ++ rr)
        (.binOp .eq (.col ⟨some tName, xCol⟩) (.col ⟨some sName, yCol⟩)) with
    | some (.bool true) => some (lr ++ rr)
    | _ => none) = matchingRows
  -- Case split on whether matchingRows is empty
  by_cases hEmpty : matchingRows = []
  · -- Case: no matching rows (anti-join keeps this row)
    -- First show NOT IN returns true
    have hNotInTrue : evalExprWithDb db lr
        (.inSubquery (.col ⟨some tName, xCol⟩) true
          (.simple (SelectStmt.mk false [.exprItem (.col ⟨some sName, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩)) none [] none [] none none)))
        = some (.bool true) := by
      rw [evalExprWithDb_inSubquery_simple]
      obtain ⟨v, hv⟩ := hEvalSome lr hlr
      rw [hv]
      simp only [↓reduceIte]
      congr 1; congr 1
      rw [Bool.not_eq_true']
      -- Show hasMatch = false by contradiction
      rw [evalSelectWithContext_simple_project db lr _ _ hNoAgg hNoWin]
      rw [List.any_map, List.any_map]
      -- Goal: (sRows.any f) = false — prove via cases
      cases hAny : (evalFrom db (.table ⟨sName, some sName⟩)).any _ with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨sRow, hsMem, hTrue⟩ := List.any_eq_true.mp hAny
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evalSelectItem] at hTrue
        generalize hcol : evalExprWithDb db (lr ++ sRow) (.col ⟨some sName, yCol⟩) = colResult at hTrue
        cases colResult with
        | none => simp [List.head?] at hTrue; cases v <;> simp [Value.eq] at hTrue
        | some colVal =>
          simp only [List.head?_cons] at hTrue
          rw [beq_iff_eq] at hTrue
          have hEqMatch := evalBinOp_eq_of_eq_true hTrue
          have hJoinMatch : evalExprWithDb db (lr ++ sRow)
              (.binOp .eq (.col ⟨some tName, xCol⟩) (.col ⟨some sName, yCol⟩))
              = some (.bool true) := by
            rw [evalExprWithDb_binOp, ← hStable lr hlr sRow, hv, hcol]
            exact hEqMatch
          -- But matchingRows is empty, so filterMap returns none for sRow
          have hFM : (fun rr => match evalExprWithDb db (lr ++ rr)
                (.binOp .eq (.col ⟨some tName, xCol⟩) (.col ⟨some sName, yCol⟩)) with
              | some (.bool true) => some (lr ++ rr)
              | _ => none) sRow = none := by
            have := List.filterMap_eq_nil_iff.mp (hMatchDef.trans hEmpty) sRow hsMem
            exact this
          simp [hJoinMatch] at hFM
    -- LHS: if notInPred lr then [proj lr] else []
    rw [show (evalExprWithDb db lr
        (.inSubquery (.col ⟨some tName, xCol⟩) true
          (.simple (SelectStmt.mk false [.exprItem (.col ⟨some sName, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩)) none [] none [] none none)))
        == some (Value.bool true)) = true from by rw [beq_iff_eq]; exact hNotInTrue]
    simp only [↓reduceIte]
    -- RHS: matchingRows = [] → isEmpty = true
    rw [show matchingRows.isEmpty = true from by rw [hEmpty]; rfl]
    simp only [↓reduceIte]
    -- Case split on sRows.head?
    cases hsHead : (evalFrom db (.table ⟨sName, some sName⟩)).head? with
    | none =>
      -- s is empty: ljBody = [lr]
      simp only [List.filter_cons, List.filter_nil]
      rw [show (evalExprWithDb db lr (.unaryOp .isNull (.col ⟨some sName, yCol⟩))
          == some (Value.bool true)) = true from by
        rw [beq_iff_eq, evalExprWithDb_unaryOp, evalExprWithDb_col]
        rw [hNotInLeft lr hlr]
        simp [evalUnaryOp, isNullValue]]
      simp
    | some rightRow =>
      -- s is non-empty: ljBody = [lr ++ nullPad(rightRow)]
      simp only [List.filter_cons, List.filter_nil]
      rw [show (evalExprWithDb db (lr ++ List.map (fun x => (x.1, Value.null none)) rightRow)
          (.unaryOp .isNull (.col ⟨some sName, yCol⟩))
          == some (Value.bool true)) = true from by
        rw [beq_iff_eq, evalExprWithDb_unaryOp, evalExprWithDb_col]
        simp only [Row.getQualified]
        have hLrNone : lr.lookup s!"{sName}.{yCol}" = none := by
          have := hNotInLeft lr hlr; simp only [Row.getQualified] at this; exact this
        rw [lookup_append_none_left _ _ _ hLrNone]
        simp [evalUnaryOp, isNullValue_lookup_nullPad]]
      simp only [↓reduceIte]
      -- Show proj(lr ++ nullPad(rightRow)) = proj(lr)
      congr 1
      dsimp only []
      rw [List.filter_append]
      have hRightMem := List.mem_of_head? hsHead
      rw [filter_null_pad_empty lr rightRow tName (hProjT lr hlr rightRow hRightMem)]
      simp
  · -- Case: matchingRows non-empty (anti-join filters this row out)
    have hMatchNE : ∃ x, x ∈ matchingRows := by
      cases hne : matchingRows with
      | nil => exact absurd hne hEmpty
      | cons a _ => exact ⟨a, List.mem_cons_self⟩
    obtain ⟨matchRow, hMatchMem⟩ := hMatchNE
    rw [← hMatchDef] at hMatchMem
    simp only [List.mem_filterMap] at hMatchMem
    obtain ⟨sRow, hsMem, hFM⟩ := hMatchMem
    -- Extract the eval condition: eval must be some (.bool true) for filterMap to return some
    have hEqTrue : evalExprWithDb db (lr ++ sRow)
        (.binOp .eq (.col ⟨some tName, xCol⟩) (.col ⟨some sName, yCol⟩))
        = some (.bool true) := by
      generalize heval : evalExprWithDb db (lr ++ sRow)
        (.binOp .eq (.col ⟨some tName, xCol⟩) (.col ⟨some sName, yCol⟩)) = r at hFM
      cases r with
      | none => exact nomatch hFM
      | some v => cases v with
        | bool b => cases b with
          | true => rfl
          | false => exact nomatch hFM
        | null _ => exact nomatch hFM
        | int _ => exact nomatch hFM
        | decimal _ _ => exact nomatch hFM
        | string _ => exact nomatch hFM
    simp only [hEqTrue] at hFM
    simp only [Option.some.injEq] at hFM
    -- Use join_match_implies_in_subquery for IN = true
    have hINTrue := join_match_implies_in_subquery db lr
      (.col ⟨some tName, xCol⟩) sName yCol sRow hsMem
      (hStable lr hlr) hNoAgg hNoWin hEqTrue
    -- NOT IN = !(IN) = false
    have hNotInFalse : evalExprWithDb db lr
        (.inSubquery (.col ⟨some tName, xCol⟩) true
          (.simple (SelectStmt.mk false [.exprItem (.col ⟨some sName, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩)) none [] none [] none none)))
        = some (.bool false) := by
      rw [evalExprWithDb_inSubquery_simple]
      obtain ⟨v, hv⟩ := hEvalSome lr hlr
      rw [hv]; simp only [↓reduceIte]
      rw [evalExprWithDb_inSubquery_simple] at hINTrue
      rw [hv] at hINTrue
      simp only [Bool.false_eq_true, ↓reduceIte] at hINTrue
      have := Option.some.inj hINTrue
      have := Value.bool.inj this
      rw [this]; decide
    -- LHS: if false then [proj lr] else [] = []
    rw [show (evalExprWithDb db lr
        (.inSubquery (.col ⟨some tName, xCol⟩) true
          (.simple (SelectStmt.mk false [.exprItem (.col ⟨some sName, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩)) none [] none [] none none)))
        == some (Value.bool true)) = false from by rw [hNotInFalse]; decide]
    simp only
    -- RHS: matchingRows non-empty, so ljBody = matchingRows
    rw [show matchingRows.isEmpty = false from by
      cases matchingRows with
      | nil => exact absurd rfl hEmpty
      | cons _ _ => rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- Show: (matchingRows.filter isNullPred).map proj = []
    rw [show matchingRows.filter (fun row =>
        evalExprWithDb db row (.unaryOp .isNull (.col ⟨some sName, yCol⟩))
        == some (Value.bool true)) = [] from by
      rw [List.filter_eq_nil_iff]
      intro joinRow hjMem
      rw [← hMatchDef] at hjMem
      simp only [List.mem_filterMap] at hjMem
      obtain ⟨sRow', hsMem', hFM'⟩ := hjMem
      -- Extract eval condition from the filterMap match
      have hEqTrue' : evalExprWithDb db (lr ++ sRow')
          (.binOp .eq (.col ⟨some tName, xCol⟩) (.col ⟨some sName, yCol⟩))
          = some (.bool true) := by
        generalize evalExprWithDb db (lr ++ sRow') _ = r at hFM'
        cases r with
        | none => exact nomatch hFM'
        | some v => cases v with
          | bool b => cases b with | true => rfl | false => exact nomatch hFM'
          | null _ => exact nomatch hFM'
          | int _ => exact nomatch hFM'
          | decimal _ _ => exact nomatch hFM'
          | string _ => exact nomatch hFM'
      simp only [hEqTrue'] at hFM'
      simp only [Option.some.injEq] at hFM'
      -- hFM' : lr ++ sRow' = joinRow; substitute
      rw [← hFM']
      -- Goal: (eval isNull (lr ++ sRow') == some (bool true)) = false
      rw [evalExprWithDb_binOp, ← hStable lr hlr sRow'] at hEqTrue'
      obtain ⟨vx, hvx⟩ := hEvalSome lr hlr
      rw [hvx] at hEqTrue'
      generalize hw : evalExprWithDb db (lr ++ sRow')
        (.col ⟨some sName, yCol⟩) = yResult at hEqTrue'
      cases yResult with
      | none => simp [evalBinOp] at hEqTrue'
      | some yVal =>
        rw [show (evalExprWithDb db (lr ++ sRow')
            (.unaryOp .isNull (.col ⟨some sName, yCol⟩))
            == some (Value.bool true)) = false from by
          rw [evalExprWithDb_unaryOp, hw]
          have hNotNull := Value.eq_some_true_not_null_right (eq_true_of_evalBinOp_eq hEqTrue')
          cases yVal with
          | null t => exact absurd rfl (hNotNull t)
          | int n => simp [evalUnaryOp, isNullValue]
          | decimal _ _ => simp [evalUnaryOp, isNullValue]
          | string s => simp [evalUnaryOp, isNullValue]
          | bool b => simp [evalUnaryOp, isNullValue]]
        decide]
    simp

/-- At the expression level: if x IN (SELECT s.y FROM s) evaluates to true,
    then there exists a matching row in s such that x = s.y in the join.

    This captures the logical essence of the unnesting transformation:
    membership in a subquery result corresponds to a successful join match.

    The subquery uses a qualified column reference ⟨some sName, yCol⟩ to avoid
    column shadowing when evalSelectWithContext prepends the outer row.

    The hStable precondition ensures x evaluates the same with or without
    extra columns appended (holds for ground expressions or expressions
    referencing only outer-table columns).

    The hNoAgg/hNoWin preconditions are needed because selectHasAggregate/selectHasWindowFn
    depend on partial functions (hasAggregate/exprHasWindowFn respectively), so the kernel
    cannot reduce them. For concrete items (.col), use `native_decide`. -/
theorem in_subquery_implies_join_match (db : Database) (row : Row)
    (x : Expr) (sName yCol : String)
    (hStable : ∀ extra : Row, evalExprWithDb db row x = evalExprWithDb db (row ++ extra) x)
    (hNoAgg : selectHasAggregate [.exprItem (.col ⟨some sName, yCol⟩) none] = false)
    (hNoWin : selectHasWindowFn [.exprItem (.col ⟨some sName, yCol⟩) none] = false)
    (h : evalExprWithDb db row (Expr.inSubquery x false
           (.simple (SelectStmt.mk false
             [.exprItem (.col ⟨some sName, yCol⟩) none]
             (some (.table ⟨sName, some sName⟩))
             none [] none [] none none))) = some (.bool true)) :
    ∃ sRow ∈ evalFrom db (.table ⟨sName, some sName⟩),
      evalExprWithDb db (row ++ sRow)
        (Expr.binOp .eq x (.col ⟨some sName, yCol⟩)) = some (.bool true) := by
  -- Unfold the IN subquery
  rw [evalExprWithDb_inSubquery_simple] at h
  -- Case split on evalExprWithDb db row x
  generalize hv : evalExprWithDb db row x = val at h
  cases val with
  | none => simp at h
  | some v =>
    -- Now h : some (.bool (if false then ... else hasMatch)) = some (.bool true)
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    -- h : some (.bool (any ...)) = some (.bool true)
    -- Decompose evalSelectWithContext using simple_project
    rw [evalSelectWithContext_simple_project db row _ _ hNoAgg hNoWin] at h
    -- Push through the two List.map layers
    rw [List.any_map, List.any_map] at h
    -- h : some (.bool (baseRows.any f)) = some (.bool true)
    -- Extract the boolean equality
    have hAny : (evalFrom db (.table ⟨sName, some sName⟩)).any
      (fun qRow => match (([.exprItem (.col ⟨some sName, yCol⟩) none].flatMap
        (evalSelectItem db (row ++ qRow))).head?) with
        | some (_, subVal) => v.eq subVal == some true
        | none => false) = true := by
      have hinj := Option.some.inj h
      exact Value.bool.inj hinj
    rw [List.any_eq_true] at hAny
    obtain ⟨qRow, hqMem, hqMatch⟩ := hAny
    refine ⟨qRow, hqMem, ?_⟩
    -- Need to show evalExprWithDb db (row ++ qRow) (.binOp .eq x (.col ...)) = some (.bool true)
    rw [evalExprWithDb_binOp, ← hStable qRow, hv]
    -- From hqMatch, we know the evalSelectItem produced a row whose head matches
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evalSelectItem] at hqMatch
    generalize hcol : evalExprWithDb db (row ++ qRow) (.col ⟨some sName, yCol⟩) = colResult at hqMatch
    cases colResult with
    | none =>
      simp [List.head?] at hqMatch
      cases v <;> simp [Value.eq] at hqMatch
    | some colVal =>
      simp [List.head?] at hqMatch
      -- hqMatch is now v.eq colVal = some true (simp simplified == to =)
      exact evalBinOp_eq_of_eq_true hqMatch

-- ============================================================================
-- Subquery Unnesting Theorems
-- ============================================================================

/-- Subquery unnesting: IN subquery can be rewritten as a semi-join with DISTINCT.
    SELECT DISTINCT t.* FROM t WHERE t.x IN (SELECT s.y FROM s)
    ≡ SELECT DISTINCT t.* FROM t JOIN s ON t.x = s.y

    This is a key database optimization. The DISTINCT is required because
    the join may produce duplicates when multiple s rows have the same y value.

    NULL handling: Both forms exclude rows where t.x is NULL (IN returns NULL
    which WHERE treats as FALSE; JOIN condition evaluates to NULL/no match).
    Similarly, NULL values in s.y don't cause differences - they simply
    don't match in either form.

    Preconditions:
    - hStable: t.xCol eval is stable when extra columns are appended
    - hNoAgg/hNoWin: subquery items have no aggregates/window functions
    - hProjT: .star (some tName) projection on tRow ++ sRow = projection on tRow alone -/
theorem in_subquery_unnest_to_join (db : Database)
    (tName sName : String) (xCol yCol : String)
    (hStable : ∀ row ∈ evalFrom db (.table ⟨tName, some tName⟩), ∀ extra : Row,
      evalExprWithDb db row (.col ⟨some tName, xCol⟩) =
      evalExprWithDb db (row ++ extra) (.col ⟨some tName, xCol⟩))
    (hNoAgg : selectHasAggregate [.exprItem (.col ⟨some sName, yCol⟩) none] = false)
    (hNoWin : selectHasWindowFn [.exprItem (.col ⟨some sName, yCol⟩) none] = false)
    (hProjT : ∀ tRow ∈ evalFrom db (.table ⟨tName, some tName⟩),
      ∀ sRow ∈ evalFrom db (.table ⟨sName, some sName⟩),
      (tRow ++ sRow).filter (fun (k, _) => k.startsWith s!"{tName}.") =
      tRow.filter (fun (k, _) => k.startsWith s!"{tName}.")) :
    let inSubqueryForm := SelectStmt.mk true  -- DISTINCT
        [.star (some tName)]  -- SELECT DISTINCT t.*
        (some (.table ⟨tName, some tName⟩))  -- FROM t
        (some (.inSubquery
          (.col ⟨some tName, xCol⟩)
          false  -- not negated (IN, not NOT IN)
          (.simple (SelectStmt.mk false
            [.exprItem (.col ⟨some sName, yCol⟩) none]  -- qualified
            (some (.table ⟨sName, some sName⟩))
            none [] none [] none none))))  -- WHERE t.x IN (SELECT s.y FROM s)
        [] none [] none none
    let joinForm := SelectStmt.mk true  -- DISTINCT
        [.star (some tName)]  -- SELECT DISTINCT t.*
        (some (.join
          (.table ⟨tName, some tName⟩)
          .inner
          (.table ⟨sName, some sName⟩)
          (some (.binOp .eq
            (.col ⟨some tName, xCol⟩)
            (.col ⟨some sName, yCol⟩)))))  -- FROM t JOIN s ON t.x = s.y
        none [] none [] none none
    (evalSelect db inSubqueryForm).Perm (evalSelect db joinForm) := by
  simp only []
  -- Abbreviations for readability
  let tRows := evalFrom db (.table ⟨tName, some tName⟩)
  let sRows := evalFrom db (.table ⟨sName, some sName⟩)
  let proj := fun (row : Row) => row.filter (fun (k, _) => k.startsWith s!"{tName}.")
  let inExpr := Expr.inSubquery (.col ⟨some tName, xCol⟩) false
    (.simple (SelectStmt.mk false [.exprItem (.col ⟨some sName, yCol⟩) none]
      (some (.table ⟨sName, some sName⟩)) none [] none [] none none))
  let eqExpr := Expr.binOp .eq (.col ⟨some tName, xCol⟩) (.col ⟨some sName, yCol⟩)
  -- Decompose LHS: SELECT DISTINCT t.* FROM t WHERE IN(...)
  rw [evalSelect_distinct_project_where db [.star (some tName)]
    (.table ⟨tName, some tName⟩) inExpr
    (selectHasAggregate_qualified_star tName) (selectHasWindowFn_qualified_star tName)]
  -- Decompose RHS: SELECT DISTINCT t.* FROM t JOIN s ON ...
  rw [evalSelect_distinct_project db [.star (some tName)]
    (.join (.table ⟨tName, some tName⟩) .inner (.table ⟨sName, some sName⟩) (some eqExpr))
    (selectHasAggregate_qualified_star tName) (selectHasWindowFn_qualified_star tName)]
  -- Simplify: [.star (some tName)].flatMap (evalSelectItem db row) = proj row
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evalSelectItem_qualified_star]
  -- Both sides are now (...).eraseDups, use Perm on nodup lists with same membership
  apply (perm_ext_iff_of_nodup (nodup_eraseDups _) (nodup_eraseDups _)).mpr
  intro v
  rw [mem_eraseDups, mem_eraseDups]
  -- Need: v ∈ (tRows.filter IN).map proj ↔ v ∈ (evalFrom db (.join ...)).map proj
  constructor
  · -- Forward: IN subquery → join match
    intro hv
    rw [List.mem_map] at hv ⊢
    obtain ⟨tRow, htRow, hproj⟩ := hv
    rw [List.mem_filter] at htRow
    obtain ⟨htMem, hIN⟩ := htRow
    rw [beq_iff_eq] at hIN
    -- Use in_subquery_implies_join_match to get matching sRow
    have hStableRow := hStable tRow htMem
    obtain ⟨sRow, hsMem, hMatch⟩ := in_subquery_implies_join_match db tRow
      (.col ⟨some tName, xCol⟩) sName yCol hStableRow hNoAgg hNoWin hIN
    -- tRow ++ sRow ∈ join result
    refine ⟨tRow ++ sRow, ?_, ?_⟩
    · -- Membership in join
      rw [evalFrom_inner_join]; dsimp only []
      simp only [List.mem_flatMap, List.mem_filterMap]
      exact ⟨tRow, htMem, sRow, hsMem, by rw [hMatch]⟩
    · -- proj(tRow ++ sRow) = proj(tRow) = v
      rw [hProjT tRow htMem sRow hsMem]; exact hproj
  · -- Backward: join match → IN subquery
    intro hv
    rw [List.mem_map] at hv ⊢
    obtain ⟨joinRow, hjMem, hproj⟩ := hv
    -- Decompose join membership
    rw [evalFrom_inner_join] at hjMem; dsimp only [] at hjMem
    simp only [List.mem_flatMap, List.mem_filterMap] at hjMem
    obtain ⟨tRow, htMem, sRow, hsMem, hfm⟩ := hjMem
    split at hfm
    · rename_i hMatch
      simp only [Option.some.injEq] at hfm; subst hfm
      -- Use join_match_implies_in_subquery to get IN = true
      have hStableRow := hStable tRow htMem
      have hIN := join_match_implies_in_subquery db tRow
        (.col ⟨some tName, xCol⟩) sName yCol sRow hsMem hStableRow hNoAgg hNoWin hMatch
      refine ⟨tRow, ?_, ?_⟩
      · -- tRow ∈ filtered
        rw [List.mem_filter]
        exact ⟨htMem, by rw [beq_iff_eq]; exact hIN⟩
      · -- proj(tRow) = v
        rw [← hProjT tRow htMem sRow hsMem]; exact hproj
    · simp at hfm

-- ============================================================================
-- ORDER BY Theorems
-- ============================================================================

/-- ORDER BY preserves row count -/
theorem order_by_preserves_count (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (orderBy : List OrderByItem) :
    let selNoOrder := SelectStmt.mk distinct items from_ where_ groupBy having [] limit offset
    let selWithOrder := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit offset
    (evalSelect db selNoOrder).length = (evalSelect db selWithOrder).length := by
  simp only []
  exact evalSelect_orderBy_length db distinct items from_ where_ groupBy having [] orderBy limit offset


/-- Different ORDER BY clauses produce same number of rows -/
theorem order_by_length_invariant (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (col : Expr) :
    let selAscDesc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .asc, OrderByItem.mk col .desc] limit offset
    let selDesc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .desc] limit offset
    (evalSelect db selAscDesc).length = (evalSelect db selDesc).length := by
  simp only []
  exact evalSelect_orderBy_length db distinct items from_ where_ groupBy having
    [OrderByItem.mk col .asc, OrderByItem.mk col .desc] [OrderByItem.mk col .desc] limit offset


-- ============================================================================
-- LIMIT Theorems
-- ============================================================================

/-- LIMIT 0 returns empty result -/
theorem limit_zero_empty (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 0) offset
    evalSelect db sel = [] := by
  simp only []
  rw [evalSelect_limit_offset]
  simp [List.take_zero]

/-- LIMIT n returns at most n rows -/
theorem limit_upper_bound (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) (n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) offset
    (evalSelect db sel).length ≤ n := by
  simp only []
  rw [evalSelect_limit_offset]
  simp [List.length_take]
  omega

/-- No LIMIT returns all rows (LIMIT none vs LIMIT large) -/
theorem limit_none_all_rows (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let selNoLimit := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none offset
    let count := (evalSelect db selNoLimit).length
    let selLargeLimit := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some count) offset
    evalSelect db selNoLimit = evalSelect db selLargeLimit := by
  simp only []
  rw [evalSelect_limit_offset (limit := none)]
  rw [evalSelect_limit_offset (limit := some _)]
  simp [List.take_length]

/-- LIMIT is monotonic: larger limit gives superset (by length) -/
theorem limit_monotonic (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) (m n : Nat) (h : m ≤ n) :
    let selM := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some m) offset
    let selN := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) offset
    (evalSelect db selM).length ≤ (evalSelect db selN).length := by
  simp only []
  rw [evalSelect_limit_offset (limit := some m)]
  rw [evalSelect_limit_offset (limit := some n)]
  simp [List.length_take]
  omega

/-- LIMIT 1 returns at most one row -/
theorem limit_one_singleton (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 1) offset
    (evalSelect db sel).length ≤ 1 := by
  simp only []
  rw [evalSelect_limit_offset]
  simp [List.length_take]
  omega

-- ============================================================================
-- OFFSET Theorems
-- ============================================================================

-- Helper lemmas: specialize evalSelect_limit_offset for concrete limit/offset values
-- These avoid `let` bindings on the RHS, making `rw` reliable.

private theorem evalSelect_SN (db : Database) (d : Bool) (i : List SelectItem)
    (f : Option FromClause) (w : Option Expr) (g : List Expr) (hv : Option Expr)
    (ob : List OrderByItem) (lim : Nat) (off : Nat) :
  evalSelect db (SelectStmt.mk d i f w g hv ob (some lim) (some off)) =
    ((evalSelect db (SelectStmt.mk d i f w g hv ob none none)).drop off).take lim := by
  rw [evalSelect_limit_offset]

private theorem evalSelect_S0 (db : Database) (d : Bool) (i : List SelectItem)
    (f : Option FromClause) (w : Option Expr) (g : List Expr) (hv : Option Expr)
    (ob : List OrderByItem) (lim : Nat) :
  evalSelect db (SelectStmt.mk d i f w g hv ob (some lim) none) =
    (evalSelect db (SelectStmt.mk d i f w g hv ob none none)).take lim := by
  rw [evalSelect_limit_offset]

private theorem evalSelect_0N (db : Database) (d : Bool) (i : List SelectItem)
    (f : Option FromClause) (w : Option Expr) (g : List Expr) (hv : Option Expr)
    (ob : List OrderByItem) (off : Nat) :
  evalSelect db (SelectStmt.mk d i f w g hv ob none (some off)) =
    (evalSelect db (SelectStmt.mk d i f w g hv ob none none)).drop off := by
  rw [evalSelect_limit_offset]

/-- OFFSET 0 is identity -/
theorem offset_zero_identity (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) :
    let selNoOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit none
    let selZeroOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some 0)
    evalSelect db selNoOffset = evalSelect db selZeroOffset := by
  simp only []
  rw [evalSelect_limit_offset (offset := none)]
  rw [evalSelect_limit_offset (offset := some 0)]
  simp [List.drop_zero]

/-- OFFSET >= base row count returns empty.
    Note: count is measured from the base query (no limit, no offset) to ensure soundness. -/
theorem offset_too_large_empty (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) (n : Nat) :
    let selBase := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none
    let count := (evalSelect db selBase).length
    let selOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some (count + n))
    evalSelect db selOffset = [] := by
  simp only []
  rw [evalSelect_limit_offset]
  generalize evalSelect db (SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none) = base
  have hdrop : base.drop (base.length + n) = [] := List.drop_eq_nil_of_le (by omega)
  cases limit <;> simp [hdrop]

/-- OFFSET reduces row count -/
theorem offset_reduces_count (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) (n : Nat) :
    let selNoOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit none
    let selOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some n)
    (evalSelect db selOffset).length ≤ (evalSelect db selNoOffset).length := by
  simp only []
  cases limit with
  | none =>
    rw [evalSelect_0N]
    generalize evalSelect db (SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none) = base
    simp [List.length_drop]
  | some L =>
    rw [evalSelect_SN, evalSelect_S0]
    generalize evalSelect db (SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none) = base
    simp [List.length_take, List.length_drop]; omega

/-- OFFSET is monotonic: larger offset gives fewer or equal rows -/
theorem offset_monotonic (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) (m n : Nat) (h : m ≤ n) :
    let selM := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some m)
    let selN := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some n)
    (evalSelect db selN).length ≤ (evalSelect db selM).length := by
  simp only []
  cases limit with
  | none =>
    rw [evalSelect_0N (off := n), evalSelect_0N (off := m)]
    generalize evalSelect db (SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none) = base
    simp [List.length_drop]; omega
  | some L =>
    rw [evalSelect_SN (off := n), evalSelect_SN (off := m)]
    generalize evalSelect db (SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none) = base
    simp [List.length_take, List.length_drop]; omega

-- ============================================================================
-- LIMIT + OFFSET Combination Theorems
-- ============================================================================

-- Helper: take n ++ take m from drop n = take (n + m)
private theorem take_add_eq {α : Type} (n m : Nat) (l : List α) :
    l.take n ++ (l.drop n).take m = l.take (n + m) := by
  induction n generalizing l with
  | zero => simp
  | succ k ih =>
    cases l with
    | nil => simp
    | cons x xs =>
      simp only [show k + 1 + m = (k + m) + 1 from by omega]
      show (x :: xs.take k) ++ (xs.drop k).take m = x :: xs.take (k + m)
      rw [List.cons_append]
      exact congrArg (x :: ·) (ih xs)

/-- LIMIT and OFFSET compose: OFFSET m then LIMIT n = skip m, take n -/
theorem limit_offset_compose (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (m n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) (some m)
    let selAll := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none
    evalSelect db sel = ((evalSelect db selAll).drop m).take n := by
  simp only []
  rw [evalSelect_SN]

/-- OFFSET then LIMIT 0 = empty regardless of offset -/
theorem offset_limit_zero_empty (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 0) (some offset)
    evalSelect db sel = [] := by
  simp only []
  rw [evalSelect_SN]
  simp [List.take_zero]

/-- Total pagination: LIMIT n OFFSET m returns at most n rows -/
theorem pagination_upper_bound (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (m n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) (some m)
    (evalSelect db sel).length ≤ n := by
  simp only []
  rw [evalSelect_SN]
  exact List.length_take_le n _

/-- Pagination identity: OFFSET 0 LIMIT count = all rows -/
theorem pagination_identity (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) :
    let selAll := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none
    let count := (evalSelect db selAll).length
    let selPaged := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some count) (some 0)
    evalSelect db selAll = evalSelect db selPaged := by
  simp only []
  rw [evalSelect_SN]
  simp [List.drop_zero, List.take_length]

/-- Consecutive pages cover all rows: page1 ++ page2 when properly offset -/
theorem consecutive_pages (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (pageSize : Nat) :
    let selPage1 := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some pageSize) (some 0)
    let selPage2 := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some pageSize) (some pageSize)
    let selBoth := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some (pageSize * 2)) (some 0)
    evalSelect db selPage1 ++ evalSelect db selPage2 = evalSelect db selBoth := by
  simp only []
  rw [evalSelect_SN (off := 0), evalSelect_SN (off := pageSize), evalSelect_SN (off := 0)]
  generalize evalSelect db (SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none) = base
  simp [List.drop_zero]
  rw [take_add_eq pageSize pageSize base, show pageSize + pageSize = pageSize * 2 from by omega]

/-- ORDER BY + LIMIT: first n rows are deterministic (assuming stable sort) -/
theorem order_limit_deterministic (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) none
    let selAll := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none
    evalSelect db sel = (evalSelect db selAll).take n := by
  simp only []
  rw [evalSelect_S0]


end SqlEquiv
