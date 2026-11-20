/-
  Elaborator correctness for grouped queries ordered by aggregates (#352, roadmap step 3b-3): the
  sorting argument. The statement is an instance of `elabStmt_correct_grouped`
  (`SqlBridge/CorrectGrouped.lean`). The elaborator sorts the aggregate's output by the aggregates'
  columns; `SqlEquiv` sorts the grouped rows together with per-group key rows
  (`groupOrderKeyRow`), whose columns `__group_orderkey_k` the rewritten keys
  (`groupOrderByItems`) read back.

  * `sorted_gen`: step 1's sorting argument for any relation between typed keyed rows and
    `SqlEquiv`'s sorted items.
  * `keyRow_lookup`: the `k`-th key column of `projected ++ keyRow` is read back, when no output
    name can capture it (`KeyNameFree`).
-/
import SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroupOrder
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectGroup

/-- The sorting argument of step 1 for any relation between typed keyed rows and `SqlEquiv`'s
    sorted items: if `SqlEquiv`'s comparator agrees with the typed key comparison on related pairs,
    and the key rows are typed (no booleans), the typed insertion sort and `SqlEquiv`'s merge sort
    put related pairs in the same order. -/
theorem sorted_gen {m o : ℕ} {β : Type _} (keys : Fin o → SortKey m) (τ : Fin o → SqlType)
    (cmp : β → β → Bool) (PR : Row o × Row m → β → Prop)
    (htyped : ∀ x y, PR x y → ∀ i, (x.1 i).HasType (τ i))
    (hagree : ∀ x₁ y₁ x₂ y₂, PR x₁ y₁ → PR x₂ y₂ →
      cmp y₁ y₂ = decide (cmpKeyRows keys x₁.1 x₂.1 ≠ .gt))
    {K : List (Row o × Row m)} {Y : List β} (hKY : List.Forall₂ PR K Y) :
    ∃ W : List ((Row o × Row m) × β),
      sortKeyed keys K = W.map Prod.fst ∧ Y.mergeSort cmp = W.map Prod.snd ∧
        ∀ w ∈ W, PR w.1 w.2 := by
  obtain ⟨hlenKY, hzip⟩ := List.forall₂_iff_zip.mp hKY
  let Z := K.zip Y
  have hZ1 : Z.map Prod.fst = K := List.map_fst_zip (by omega)
  have hZ2 : Z.map Prod.snd = Y := List.map_snd_zip (by omega)
  have hmem : ∀ z ∈ Z, PR z.1 z.2 := fun z hz => hzip hz
  let le : Row o × Row m → Row o × Row m → Bool :=
    fun x y => decide (cmpKeyRows keys x.1 y.1 ≠ .gt)
  let W := Z.mergeSort fun a b => le a.1 b.1
  refine ⟨W, ?_, ?_, fun w hw => hmem w (List.mem_mergeSort.mp hw)⟩
  · have htK : ∀ x ∈ K, ∀ i, (x.1 i).HasType (τ i) := by
      intro x hx i
      rw [← hZ1] at hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      exact htyped _ _ (hmem z hz) i
    obtain ⟨htot, htrans⟩ := keyed_total_trans keys τ K htK
    rw [sortKeyed, insertionSort_congr (s := fun x y => le x y = true) (fun a b => by simp [le]),
      ← SortBridge.mergeSort_eq_insertionSort_of_mem le K htrans htot]
    conv_lhs => rw [← hZ1]
    exact (List.map_mergeSort (r := fun a b => le a.1 b.1) (s := le) (f := Prod.fst) (l := Z)
      (fun _ _ _ _ => rfl)).symm
  · rw [← hZ2]
    exact (List.map_mergeSort (fun a ha b hb =>
      (hagree _ _ _ _ (hmem a ha) (hmem b hb)).symm)).symm
end SqlBridge.CorrectGroupOrder

namespace SqlBridge.CorrectGroupOrder
open SqlEquiv SqlBridge.CorrectGroup

end SqlBridge.CorrectGroupOrder

namespace SqlBridge.CorrectGroupOrder
open SqlBridge.Correct SqlBridge.CorrectOrder

/-! ### The names of `SqlEquiv`'s per-group sort-key columns -/

theorem toLower_of_isDigit {c : Char} (h : c.isDigit = true) : c.toLower = c := by
  unfold Char.toLower
  rw [dite_eq_right_iff]
  intro hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  exfalso
  have h2 := h.2
  have h3 := hc.1
  rw [ge_iff_le, UInt32.le_iff_toNat_le] at h3
  rw [UInt32.le_iff_toNat_le] at h2
  have : ('A' : Char).val.toNat = 65 := rfl
  have : ('9' : Char).val.toNat = 57 := rfl
  omega

theorem toList_groupOrderKeyName (k : ℕ) :
    (SqlEquiv.groupOrderKeyName k).toList = "__group_orderkey_".toList ++ Nat.toDigits 10 k := by
  simp [SqlEquiv.groupOrderKeyName, toString, Nat.repr, String.toList_append]

theorem toLower_groupOrderKeyName (k : ℕ) :
    (SqlEquiv.groupOrderKeyName k).toLower = SqlEquiv.groupOrderKeyName k := by
  apply String.toList_inj.mp
  rw [toList_toLower, toList_groupOrderKeyName, List.map_append]
  refine congrArg₂ (· ++ ·) (by decide) ?_
  conv_rhs => rw [← List.map_id (Nat.toDigits 10 k)]
  exact List.map_congr_left fun c hc =>
    toLower_of_isDigit (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

theorem dot_not_mem_groupOrderKeyName (k : ℕ) : '.' ∉ (SqlEquiv.groupOrderKeyName k).toList := by
  rw [toList_groupOrderKeyName, List.mem_append, not_or]
  refine ⟨by decide, fun h => ?_⟩
  have hd := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  revert hd; decide

theorem groupOrderKeyName_inj {j k : ℕ}
    (h : SqlEquiv.groupOrderKeyName j = SqlEquiv.groupOrderKeyName k) : j = k := by
  have h' := congrArg String.toList h
  rw [toList_groupOrderKeyName, toList_groupOrderKeyName, List.append_cancel_left_eq] at h'
  have : Nat.repr j = Nat.repr k := by simp [Nat.repr, h']
  exact Nat.repr_inj.mp this

/-- Output names that cannot capture a sort-key reference: no dot, and not a sort-key name
    (ignoring case). -/
def KeyNameFree (p : SqlEquiv.Row) : Prop :=
  ∀ kv ∈ p, '.' ∉ kv.1.toList ∧ ∀ k, kv.1.toLower ≠ SqlEquiv.groupOrderKeyName k

/-- Reading the `i`-th sort-key column of `projected ++ keyRow`. -/
theorem keyRow_lookup {o : ℕ} (p : SqlEquiv.Row) (hp : KeyNameFree p) (vs : Fin o → SqlEquiv.Value)
    (i : Fin o) :
    (p ++ (List.finRange o).map fun j : Fin o => (SqlEquiv.groupOrderKeyName j, vs j)).getQualified none
      (SqlEquiv.groupOrderKeyName i) = some (vs i) := by
  rw [getQualified_append_noMatch p _ none _ (fun kv h => (hp kv h).1)
    (fun _ kv h => by rw [toLower_groupOrderKeyName]; exact (hp kv h).2 i)]
  have := getQualified_none_append_match ((List.finRange o).map fun j : Fin o =>
      (SqlEquiv.groupOrderKeyName j, vs j)) [] (SqlEquiv.groupOrderKeyName i)
    (fun kv h => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
      exact dot_not_mem_groupOrderKeyName j)
    (kv := (SqlEquiv.groupOrderKeyName i, vs i)) ?_
  · simpa using this
  · rw [List.find?_map]
    have : (List.finRange o).find? ((fun kv : String × SqlEquiv.Value =>
        kv.1.toLower == (SqlEquiv.groupOrderKeyName ↑i).toLower) ∘
        fun j : Fin o => (SqlEquiv.groupOrderKeyName j, vs j)) = some i := by
      rw [List.find?_eq_some_iff_getElem]
      refine ⟨by simp, i.1, by simp, by simp, fun j hj => ?_⟩
      simp only [Function.comp_apply, toLower_groupOrderKeyName, List.getElem_finRange]
      rw [Bool.not_eq_true', beq_eq_false_iff_ne]
      intro h
      have := groupOrderKeyName_inj h
      simp at this; omega
    rw [this]; rfl

theorem range_zip_eq {α : Type _} (l : List α) :
    (List.range l.length).zip l = (List.finRange l.length).map fun j => (j.1, l[j]) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- With every sort key evaluating, the key row has one column per key, in order. -/
theorem groupOrderKeyRow_eq (db : SqlEquiv.Database)
    (ev : SqlEquiv.Database → SqlEquiv.Table → SqlEquiv.Row → SqlEquiv.Expr → Option SqlEquiv.Value)
    (orderBy : List SqlEquiv.OrderByItem) (rows : SqlEquiv.Table) (s p : SqlEquiv.Row)
    (vs : Fin orderBy.length → SqlEquiv.Value)
    (h : ∀ i : Fin orderBy.length, ev db rows (p ++ s) orderBy[i].expr = some (vs i)) :
    SqlEquiv.groupOrderKeyRow db ev orderBy rows s p =
      (List.finRange orderBy.length).map fun j : Fin orderBy.length =>
        (SqlEquiv.groupOrderKeyName j, vs j) := by
  rw [SqlEquiv.groupOrderKeyRow, range_zip_eq, List.filterMap_map]
  rw [List.filterMap_eq_map_iff_forall_eq_some.mpr]
  intro j _
  simp
  exact h j

theorem length_groupOrderByItems (orderBy : List SqlEquiv.OrderByItem) :
    (SqlEquiv.groupOrderByItems orderBy).length = orderBy.length := by
  simp [SqlEquiv.groupOrderByItems]

theorem getElem_groupOrderByItems (orderBy : List SqlEquiv.OrderByItem) (i : ℕ)
    (h : i < (SqlEquiv.groupOrderByItems orderBy).length) :
    (SqlEquiv.groupOrderByItems orderBy)[i] =
      ⟨.col ⟨none, SqlEquiv.groupOrderKeyName i⟩, (orderBy[i]'(by simpa [length_groupOrderByItems] using h)).dir,
        (orderBy[i]'(by simpa [length_groupOrderByItems] using h)).nulls⟩ := by
  simp [SqlEquiv.groupOrderByItems]

end SqlBridge.CorrectGroupOrder

namespace SqlBridge.CorrectGroupOrder
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGroup

/-- The statements of step 3b-3: grouped, ordered by aggregates, with `LIMIT` / `OFFSET`. -/
def groupOrderStmt (items : List SqlEquiv.SelectItem) (f : SqlEquiv.FromClause)
    (wh : Option SqlEquiv.Expr) (groupBy : List SqlEquiv.Expr) (orderBy : List SqlEquiv.OrderByItem)
    (lim off : Option ℕ) : SqlEquiv.Stmt :=
  .query (.simple (.mk false items (some f) wh groupBy none orderBy lim off))

theorem aggsOfList_orderBy {f : SqlEquiv.OrderByItem → SqlEquiv.Expr} (hf : ∀ o, f o = o.expr) :
    ∀ orderBy : List SqlEquiv.OrderByItem, (∀ o ∈ orderBy, aggFragment o.expr = true) →
      aggsOfList (orderBy.map f) = orderBy.map SqlEquiv.OrderByItem.expr
  | [], _ => rfl
  | o :: os, h => by
    simp only [List.map_cons, aggsOfList, hf, aggsOf_aggFragment _ (h o List.mem_cons_self),
      aggsOfList_orderBy hf os (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.singleton_append]

theorem colsOutsideAggsList_orderBy {f : SqlEquiv.OrderByItem → SqlEquiv.Expr}
    (hf : ∀ o, f o = o.expr) :
    ∀ orderBy : List SqlEquiv.OrderByItem, (∀ o ∈ orderBy, aggFragment o.expr = true) →
      colsOutsideAggsList (orderBy.map f) = []
  | [], _ => rfl
  | o :: os, h => by
    simp only [List.map_cons, colsOutsideAggsList, hf,
      colsOutsideAggs_aggFragment _ (h o List.mem_cons_self),
      colsOutsideAggsList_orderBy hf os (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.append_nil]

end SqlBridge.CorrectGroupOrder


namespace SqlBridge.CorrectGroupOrder
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGroup

theorem compareBy_agree' (exprEval : SqlEquiv.Database → SqlEquiv.Row → SqlEquiv.Expr →
    Option SqlEquiv.Value) (db : SqlEquiv.Database) (r₁ r₂ : SqlEquiv.Row)
    (items : List SqlEquiv.OrderByItem) {m o : ℕ} (hl : items.length = o) (keys : Fin o → SortKey m)
    (a b : Row o)
    (h : ∀ i : Fin o, SqlEquiv.orderKeyCmp (items[i.1]'(by omega))
      (exprEval db r₁ (items[i.1]'(by omega)).expr) (exprEval db r₂ (items[i.1]'(by omega)).expr) =
        toB ((keys i).cmpDatum (a i) (b i))) :
    SqlEquiv.compareByOrderItemsParam exprEval db r₁ r₂ items = decide (cmpKeyRows keys a b ≠ .gt) := by
  subst hl
  exact compareBy_agree exprEval db r₁ r₂ items keys a b h

/-- The output names of `SqlEquiv`'s projected group row are the items' names. -/
theorem names_of_items (db : SqlEquiv.Database) (U : List SqlEquiv.Row) (row : SqlEquiv.Row) :
    ∀ {items : List SqlEquiv.SelectItem}, (∀ it ∈ items, ∃ e al, it = .exprItem e al) →
      ∀ kv ∈ items.flatMap (SqlEquiv.evalSelectItemWithAggParam ee db U row),
        ∃ it ∈ items, kv.1 = outName it
  | [], _, kv, h => by simp at h
  | it :: rest, h, kv, hkv => by
    obtain ⟨e, al, rfl⟩ := h it List.mem_cons_self
    rw [List.flatMap_cons, List.mem_append] at hkv
    rcases hkv with hkv | hkv
    · refine ⟨_, List.mem_cons_self, ?_⟩
      simp only [SqlEquiv.evalSelectItemWithAggParam] at hkv
      split at hkv <;> simp_all [outName]
    · obtain ⟨it', hit', h'⟩ :=
        names_of_items db U row (fun x hx => h x (List.mem_cons_of_mem _ hx)) kv hkv
      exact ⟨it', List.mem_cons_of_mem _ hit', h'⟩

end SqlBridge.CorrectGroupOrder
