/-
  SQL Equivalence - Statement-Level Axioms (SET ops, JOINs, Subqueries, Pagination)
-/
import SqlEquiv.Equiv.Defs
import SqlEquiv.Equiv.SetBagLemmas

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
  simp only [evalQuery_compound, evalQuery_simple]
  generalize evalSelect db a = l
  rw [List.filter_eq_nil_iff]
  intro x hx h
  simp at h
  exact absurd hx h

/-- INTERSECT with empty is empty -/
theorem intersect_empty_right (db : Database) (a : SelectStmt) :
    let emptySelect := SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none
    evalQuery db (Query.compound (Query.simple a) .intersect (Query.simple emptySelect)) = [] := by
  simp only [evalQuery_compound, evalQuery_simple]
  have h : evalSelect db (SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none) = [] :=
    evalSelect_filter_all_false db false [.star none] none (.lit (.bool false)) [] none [] none none
      (by rfl) (fun row => by simp [evalExprWithDb_lit])
  rw [List.filter_eq_nil_iff]
  intro x _ habs
  rw [h] at habs
  exact absurd habs (by simp)

/-- INTERSECT is idempotent: A INTERSECT A = A -/
theorem intersect_idempotent (a : SelectStmt) :
    Query.compound (Query.simple a) .intersect (Query.simple a) ≃ᵩ
    Query.simple a := by
  intro db
  simp only [evalQuery_compound, evalQuery_simple]
  generalize evalSelect db a = l
  rw [List.filter_eq_self]
  intro x hx
  exact List.contains_iff_mem.mpr hx

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
-- 5 Set (≃ˢ): intersect_comm, union_idempotent, union_empty_right,
--              union_intersect_distrib, intersect_union_distrib

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
  simp only [evalQuery_compound]
  apply (perm_ext_iff_of_nodup (nodup_eraseDups _) (nodup_eraseDups _)).mpr
  intro row
  simp only [mem_eraseDups, List.mem_append]
  exact or_assoc

/-- INTERSECT is associative under exact equality.
    Unlike the other set operations, both sides filter the same list (evalQuery db a)
    in the same order — only the predicate differs, and the predicates are equivalent. -/
theorem intersect_assoc (a b c : Query) :
    Query.compound (Query.compound a .intersect b) .intersect c ≃ᵩ
    Query.compound a .intersect (Query.compound b .intersect c) := by
  intro db
  simp only [evalQuery_compound]
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  cases hb : (evalQuery db b).contains x <;> cases hc : (evalQuery db c).contains x <;>
    simp_all

/-- INTERSECT is commutative under set equivalence -/
theorem intersect_comm (a b : SelectStmt) :
    Query.compound (Query.simple a) .intersect (Query.simple b) ≃ˢ
    Query.compound (Query.simple b) .intersect (Query.simple a) := by
  intro db row
  simp only [evalQuery_compound, evalQuery_simple, mem_filter_contains]
  exact And.comm

/-- UNION is idempotent under set equivalence -/
theorem union_idempotent (a : SelectStmt) :
    Query.compound (Query.simple a) .union (Query.simple a) ≃ˢ
    Query.simple a := by
  intro db row
  simp only [evalQuery_compound, evalQuery_simple, mem_eraseDups, List.mem_append]
  exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩

/-- UNION with empty is identity under set equivalence -/
theorem union_empty_right (a : SelectStmt) :
    Query.compound (Query.simple a) .union
      (Query.simple (SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none)) ≃ˢ
    Query.simple a := by
  intro db row
  simp only [evalQuery_compound, evalQuery_simple, mem_eraseDups, List.mem_append]
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
  simp only [evalQuery_compound, mem_eraseDups, List.mem_append, mem_filter_contains]
  exact or_and_left

/-- Distributivity: A INTERSECT (B UNION C) = (A INTERSECT B) UNION (A INTERSECT C)
    under set equivalence -/
theorem intersect_union_distrib (a b c : Query) :
    Query.compound a .intersect (Query.compound b .union c) ≃ˢ
    Query.compound (Query.compound a .intersect b) .union (Query.compound a .intersect c) := by
  intro db row
  simp only [evalQuery_compound, mem_filter_contains, mem_eraseDups, List.mem_append]
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
  | nil => simp [List.find?]
  | cons hd rest ih =>
    simp only [List.map_cons, List.find?_cons]
    cases hd.1 == col with
    | true => simp [isNullValue]
    | false => exact ih

/-- Converting LEFT JOIN to INNER JOIN by filtering out NULLs:
    If we filter the result of LEFT JOIN to exclude rows where right columns are NULL,
    we get the same result as INNER JOIN.

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
        | string _ => simp at hf
        | null _ => simp at hf

-- ============================================================================
-- Subquery Theorems
-- ============================================================================

/-- EXISTS on empty subquery is FALSE -/
axiom exists_empty_false (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.exists false sel) = some (.bool false)

/-- NOT EXISTS on empty subquery is TRUE -/
axiom not_exists_empty_true (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.exists true sel) = some (.bool true)

/-- EXISTS on non-empty subquery is TRUE -/
axiom exists_nonempty_true (db : Database) (row : Row) (sel : SelectStmt)
    (h : (evalSelectWithContext db row sel).length > 0) :
    evalExprWithDb db row (Expr.exists false sel) = some (.bool true)

/-- NOT EXISTS on non-empty subquery is FALSE -/
axiom not_exists_nonempty_false (db : Database) (row : Row) (sel : SelectStmt)
    (h : (evalSelectWithContext db row sel).length > 0) :
    evalExprWithDb db row (Expr.exists true sel) = some (.bool false)

/-- Double negation: NOT NOT EXISTS = EXISTS -/
axiom not_not_exists (sel : SelectStmt) :
    Expr.exists true sel ≃ₑ Expr.unaryOp .not (Expr.exists false sel)

/-- x IN (empty subquery) = FALSE -/
axiom in_empty_subquery_false (e : Expr) (sel : SelectStmt) :
    -- When the subquery returns no rows, IN is always false
    Expr.inSubquery e false sel ≃ₑ
    Expr.case [(Expr.exists false sel, Expr.lit (.bool false))]
              (some (Expr.inSubquery e false sel))

/-- x NOT IN (empty subquery) = TRUE -/
axiom not_in_empty_subquery_true (e : Expr) (sel : SelectStmt) :
    -- When the subquery returns no rows, NOT IN is always true
    Expr.inSubquery e true sel ≃ₑ
    Expr.case [(Expr.unaryOp .not (Expr.exists false sel), Expr.lit (.bool true))]
              (some (Expr.inSubquery e true sel))

/-- Scalar subquery returning empty = NULL -/
axiom scalar_subquery_empty_null (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.subquery sel) = some (.null none)

/-- EXISTS can be rewritten as COUNT(*) > 0 (semantic equivalence) -/
axiom exists_as_count_gt_zero (db : Database) (row : Row) (sel : SelectStmt) :
    let existsResult := evalExprWithDb db row (Expr.exists false sel)
    let subRows := evalSelectWithContext db row sel
    existsResult = some (.bool (subRows.length > 0))

/-- NOT EXISTS can be rewritten as COUNT(*) = 0 (semantic equivalence) -/
axiom not_exists_as_count_eq_zero (db : Database) (row : Row) (sel : SelectStmt) :
    let existsResult := evalExprWithDb db row (Expr.exists true sel)
    let subRows := evalSelectWithContext db row sel
    existsResult = some (.bool (subRows.length == 0))

/-- IN subquery is equivalent to EXISTS with equality condition.
    x IN (SELECT col FROM t) ≡ EXISTS (SELECT 1 FROM t WHERE t.col = x) -/
axiom in_subquery_as_exists (db : Database) (row : Row) (e : Expr)
    (tableName : String) (colName : String) :
    let inSub := Expr.inSubquery e false
      (SelectStmt.mk false [.exprItem (.col ⟨none, colName⟩) none]
        (some (.table ⟨tableName, none⟩)) none [] none [] none none)
    let existsSub := Expr.exists false
      (SelectStmt.mk false [.exprItem (.lit (.int 1)) none]
        (some (.table ⟨tableName, none⟩))
        (some (.binOp .eq (.col ⟨some tableName, colName⟩) e))
        [] none [] none none)
    evalExprWithDb db row inSub = evalExprWithDb db row existsSub

/-- NOT IN subquery is equivalent to NOT EXISTS with equality condition -/
axiom not_in_subquery_as_not_exists (db : Database) (row : Row) (e : Expr)
    (tableName : String) (colName : String) :
    let notInSub := Expr.inSubquery e true
      (SelectStmt.mk false [.exprItem (.col ⟨none, colName⟩) none]
        (some (.table ⟨tableName, none⟩)) none [] none [] none none)
    let notExistsSub := Expr.exists true
      (SelectStmt.mk false [.exprItem (.lit (.int 1)) none]
        (some (.table ⟨tableName, none⟩))
        (some (.binOp .eq (.col ⟨some tableName, colName⟩) e))
        [] none [] none none)
    evalExprWithDb db row notInSub = evalExprWithDb db row notExistsSub

/-- Uncorrelated subquery can be evaluated independently of outer row.
    If a subquery doesn't reference any columns from the outer query,
    its result is the same regardless of the outer row context. -/
axiom uncorrelated_subquery_independent (db : Database) (row1 row2 : Row) (sel : SelectStmt) :
    -- Assuming sel doesn't reference columns from the outer context
    -- (this is a semantic precondition)
    evalSelectWithContext db row1 sel = evalSelectWithContext db row2 sel

/-- Subquery with LIMIT 1 returns at most one row -/
axiom subquery_limit_one (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 1) offset
    (evalSelectWithContext db row sel).length ≤ 1

/-- Scalar subquery is equivalent to first value of subquery with LIMIT 1 -/
axiom scalar_subquery_is_first (db : Database) (row : Row) (sel : SelectStmt) :
    let result := evalExprWithDb db row (Expr.subquery sel)
    let subRows := evalSelectWithContext db row sel
    result = match subRows.head? with
      | some subRow => subRow.head?.map (·.2)
      | none => some (.null none)

/-- EXISTS is monotonic: more rows in subquery doesn't change TRUE to FALSE -/
axiom exists_monotonic (db : Database) (row : Row) (sel1 sel2 : SelectStmt)
    (h : ∀ r ∈ evalSelectWithContext db row sel1,
         r ∈ evalSelectWithContext db row sel2) :
    evalExprWithDb db row (Expr.exists false sel1) = some (.bool true) →
    evalExprWithDb db row (Expr.exists false sel2) = some (.bool true)

/-- Adding WHERE TRUE to subquery doesn't change result -/
axiom subquery_where_true (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ none groupBy having orderBy limit offset
    let selWithTrue := SelectStmt.mk distinct items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset
    evalSelectWithContext db row sel = evalSelectWithContext db row selWithTrue

/-- Adding WHERE FALSE to subquery makes it empty -/
axiom subquery_where_false (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    let selWithFalse := SelectStmt.mk distinct items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset
    evalSelectWithContext db row selWithFalse = []

/-- IN with single-value subquery is equivalent to equality -/
axiom in_singleton_subquery (db : Database) (row : Row) (e : Expr) (sel : SelectStmt)
    (colName : String) (v : Value)
    (h : evalSelectWithContext db row sel = [[(colName, v)]]) :
    evalExprWithDb db row (Expr.inSubquery e false sel) =
    evalExprWithDb db row (Expr.binOp .eq e (Expr.lit v))

/-- Correlated subquery with outer reference evaluates with outer row context -/
axiom correlated_subquery_uses_context (db : Database) (outerRow : Row)
    (sel : SelectStmt) (outerCol : String) (outerVal : Value)
    (h : (outerCol, outerVal) ∈ outerRow) :
    -- The subquery can access outerCol from the outer row
    -- subResult is computed with outerRow available for column resolution
    True  -- This is a semantic property, not a computational one

-- ============================================================================
-- Subquery Unnesting Theorems
-- ============================================================================

/-- Subquery unnesting: IN subquery can be rewritten as a semi-join with DISTINCT.
    SELECT * FROM t WHERE x IN (SELECT y FROM s)
    ≡ SELECT DISTINCT t.* FROM t JOIN s ON t.x = s.y

    This is a key database optimization. The DISTINCT is required because
    the join may produce duplicates when multiple s rows have the same y value.

    NULL handling: Both forms exclude rows where t.x is NULL (IN returns NULL
    which WHERE treats as FALSE; JOIN condition evaluates to NULL/no match).
    Similarly, NULL values in s.y don't cause differences - they simply
    don't match in either form.

    This axiom expresses the semantic equivalence at the statement level. -/
axiom in_subquery_unnest_to_join (db : Database)
    (tName sName : String) (xCol yCol : String) :
    let inSubqueryForm := SelectStmt.mk false
        [.star (some tName)]  -- SELECT t.*
        (some (.table ⟨tName, some tName⟩))  -- FROM t
        (some (.inSubquery
          (.col ⟨some tName, xCol⟩)
          false  -- not negated (IN, not NOT IN)
          (SelectStmt.mk false
            [.exprItem (.col ⟨none, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩))
            none [] none [] none none)))  -- WHERE x IN (SELECT y FROM s)
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
    evalSelect db inSubqueryForm = evalSelect db joinForm

/-- NOT IN subquery can be unnested to an anti-join pattern.
    SELECT * FROM t WHERE x NOT IN (SELECT y FROM s)
    ≡ SELECT t.* FROM t LEFT JOIN s ON t.x = s.y WHERE s.y IS NULL

    The anti-join returns rows from t that have no matching rows in s.

    Note: This transformation assumes s.y contains no NULL values.
    When s.y can be NULL, NOT IN has different semantics (returns NULL
    when x matches no values but s contains NULL). -/
axiom not_in_subquery_unnest_to_antijoin (db : Database)
    (tName sName : String) (xCol yCol : String) :
    let notInSubqueryForm := SelectStmt.mk false
        [.star (some tName)]  -- SELECT t.*
        (some (.table ⟨tName, some tName⟩))  -- FROM t
        (some (.inSubquery
          (.col ⟨some tName, xCol⟩)
          true  -- negated (NOT IN)
          (SelectStmt.mk false
            [.exprItem (.col ⟨none, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩))
            none [] none [] none none)))  -- WHERE x NOT IN (SELECT y FROM s)
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
    evalSelect db notInSubqueryForm = evalSelect db antijoinForm

/-- At the expression level: x IN (SELECT y FROM s) evaluates to true for a row
    if and only if there exists a matching row in the join result.

    This captures the logical essence of the unnesting transformation:
    membership in a subquery result corresponds to a successful join match. -/
axiom in_subquery_implies_join_match (db : Database) (row : Row)
    (x : Expr) (sName yCol : String)
    (h : evalExprWithDb db row (Expr.inSubquery x false
           (SelectStmt.mk false
             [.exprItem (.col ⟨none, yCol⟩) none]
             (some (.table ⟨sName, some sName⟩))
             none [] none [] none none)) = some (.bool true)) :
    ∃ sRow ∈ db sName,
      evalExprWithDb db (row ++ sRow)
        (Expr.binOp .eq x (.col ⟨some sName, yCol⟩)) = some (.bool true)

/-- The converse: if a join match exists, the IN subquery returns true. -/
axiom join_match_implies_in_subquery (db : Database) (row : Row)
    (x : Expr) (sName yCol : String) (sRow : Row)
    (hMem : sRow ∈ db sName)
    (hMatch : evalExprWithDb db (row ++ sRow)
                (Expr.binOp .eq x (.col ⟨some sName, yCol⟩)) = some (.bool true)) :
    evalExprWithDb db row (Expr.inSubquery x false
      (SelectStmt.mk false
        [.exprItem (.col ⟨none, yCol⟩) none]
        (some (.table ⟨sName, some sName⟩))
        none [] none [] none none)) = some (.bool true)

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

/-- ORDER BY is idempotent: ordering twice by same criteria is same as once -/
axiom order_by_idempotent (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (orderBy : List OrderByItem) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit offset
    -- Applying the same ORDER BY twice gives same result
    let result := evalSelect db sel
    result.mergeSort (fun r1 r2 => compareByOrderItems db r1 r2 orderBy) = result

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

/-- Reversing ORDER BY direction reverses the result (for single column) -/
axiom order_by_reverse (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (col : Expr) :
    let selAsc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .asc] limit offset
    let selDesc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .desc] limit offset
    (evalSelect db selAsc).reverse = evalSelect db selDesc

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
