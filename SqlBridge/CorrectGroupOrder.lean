/-
  Elaborator correctness for grouped queries ordered by aggregates (#352, roadmap step 3b-3).

  `SELECT … FROM f [WHERE p] GROUP BY c₁, …, cₘ ORDER BY a₁, … [LIMIT n] [OFFSET m]`, the items
  and keys as in step 3b-1, every sort key an aggregate of step 3a. The elaborator sorts the
  aggregate's output by the aggregates' columns (`elab_group_order_shape`); `SqlEquiv` sorts the
  grouped rows together with per-group key rows (`groupOrderKeyRow`), whose columns
  `__group_orderkey_k` the rewritten keys (`groupOrderByItems`) read back.

  * `sorted_gen`: step 1's sorting argument for any relation between typed keyed rows and
    `SqlEquiv`'s sorted items.
  * `evalSelectCore_grouped_ordered`: `SqlEquiv`'s grouped, ordered path in closed form.
  * `keyRow_lookup`: the `k`-th key column of `projected ++ keyRow` is read back, when no output
    name can capture it (`KeyNameFree`).
  * `elabStmt_correct_group_ordered`: the statement.
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

/-- `SqlEquiv`'s `GROUP BY … ORDER BY … [LIMIT] [OFFSET]` (no `HAVING`): the grouped rows and the
    per-group sort-key rows, both built over the same grouping, sorted together. -/
theorem evalSelectCore_grouped_ordered (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool) (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause) (wh : Option Expr) (groupBy : List Expr)
    (orderBy : List OrderByItem) (lim off : Option Nat) (hg : groupBy ≠ []) :
    ∃ (F F' : List (List (Option Value) × Table) → Row → List (List (Option Value) × Table))
      (Φ Ψ : List (Option Value) × Table → Option Row),
      (∀ gs u, (gs.map Prod.fst).Nodup →
        F gs u = insU (groupBy.map fun e => (exprEval db u e).map Value.setKey) u gs) ∧
      (∀ gs u, (gs.map Prod.fst).Nodup →
        F' gs u = insU (groupBy.map fun e => (exprEval db u e).map Value.setKey) u gs) ∧
      (∀ key rows s, bareSampleRow (exprEval db) (selectMinMaxCalls items none) rows = some s →
        Φ (key, rows) = some (items.flatMap (selectItemWithAggEval db rows s))) ∧
      (∀ key rows s, bareSampleRow (exprEval db) (selectMinMaxCalls items none) rows = some s →
        Ψ (key, rows) = some (groupOrderKeyRow db exprWithAggEval orderBy rows s
          (items.flatMap (selectItemWithAggEval db rows s)))) ∧
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
        (SelectStmt.mk false items (some from_) wh groupBy none orderBy lim off) =
      applyOrderByLimitOffsetAligned compareEval db (groupOrderByItems orderBy) lim off true
        (((match wh with
          | some c => (fromEval db from_).filter fun row => exprEval db row c == some (Value.bool true)
          | none => fromEval db from_).foldl F' []).filterMap Ψ)
        (((match wh with
          | some c => (fromEval db from_).filter fun row => exprEval db row c == some (Value.bool true)
          | none => fromEval db from_).foldl F []).filterMap Φ) := by
  have hne : groupBy.isEmpty = false := by cases groupBy <;> simp_all
  refine ⟨?F, ?F', ?Φ, ?Ψ, ?h1, ?h1', ?h2, ?h2', ?h3⟩
  case h3 =>
    rw [evalSelectCore_eq_afterFilter]
    cases wh <;> simp [evalSelectAfterFilter, evalSelectProjectDistinct, evalSelectGroupOrderKeys,
      hne] <;> rfl
  case h1 =>
    intro gs u h
    split
    · rename_i x hx; exact addStep_found _ u gs h hx
    · rename_i hx; exact addStep_new _ u gs hx
  case h1' =>
    intro gs u h
    split
    · rename_i x hx; exact addStep_found _ u gs h hx
    · rename_i hx; exact addStep_new _ u gs hx
  case h2 =>
    intro key rows s h
    simp [h]
  case h2' =>
    intro key rows s h
    simp [h]

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

set_option maxHeartbeats 1000000 in
theorem elab_group_order_shape (N : NamedSchema) {items : List SqlEquiv.SelectItem}
    {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} {groupBy : List SqlEquiv.Expr}
    (hgi : groupItems groupBy items = true) (hgb : groupBy ≠ [])
    (hw : ∀ w ∈ wh, isFragment w = true) {orderBy : List SqlEquiv.OrderByItem}
    (hob : ∀ o ∈ orderBy, aggFragment o.expr = true) {lim off : Option ℕ} {e : Elaborated N.S}
    (h : elabStmt N (groupOrderStmt items fr wh groupBy orderBy lim off) = .ok e) :
    e.q.typeOf.isSome ∧ ∃ sub n, ∃ qf : Query N.S n, ∃ cf, elabFrom N sub fr = .ok ⟨n, qf, cf⟩ ∧
      ∃ q₀ : Query N.S n,
        ((wh = none ∧ q₀ = qf) ∨ ∃ w p, wh = some w ∧
          elabExpr cf N.fold noHook w = .ok p ∧ q₀ = .select p qf) ∧
      ∃ (keyList : List (Expr n)) (a : ℕ) (aggs : Fin a → AggCall n)
        (its : List (Expr (keyList.length + a) × Column)) (sk : List (SortKey (keyList.length + a))),
        groupBy.mapM (elabExpr cf N.fold noHook) = .ok keyList ∧
        (∀ j, ∃ x, aggFragment x = true ∧ elabAgg cf N.fold x = .ok (aggs j)) ∧
        List.Forall₂ (fun it x =>
          (∃ j : Fin a, elabAgg cf N.fold (itemExpr it) = .ok (aggs j) ∧
            x.1 = .col (Fin.natAdd _ j)) ∨
          (∃ c, ∃ i : Fin keyList.length, itemExpr it = .col c ∧
            elabExpr cf N.fold noHook (.col c) = .ok keyList[i] ∧ x.1 = .col (Fin.castAdd a i)))
          items its ∧
        List.Forall₂ (fun o k => ∃ j : Fin a, elabAgg cf N.fold o.expr = .ok (aggs j) ∧
          k.e = .col (Fin.natAdd _ j) ∧ k.desc = (o.dir == .desc) ∧
          k.nullsFirst = (o.nulls == .first)) orderBy sk ∧
        e = ⟨its.length, limitWrap lim off
          (if sk.length = 0 then .project (fun i => (its[i]).1)
            (.aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀)
           else .project (fun i => (its[i]).1)
            (.orderBy (fun i : Fin sk.length => sk[i])
              (.aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀))),
          fun i => (its[i]).2⟩ := by
  simp only [groupOrderStmt, elabStmt, elabQuery, bind, Except.bind] at h
  rcases hraw : elabQueryRaw N (.simple (.mk false items (some fr) wh groupBy none orderBy lim off))
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
  have hgbe : groupBy.isEmpty = false := by
    cases groupBy with
    | nil => exact absurd rfl hgb
    | cons _ _ => rfl
  cases wh
  case' none =>
    simp only [pure, Except.pure, bind, Except.bind] at hraw
    rw [aggsOfList_groupItems ?hf items hgi, colsOutsideAggsList_groupItems ?hf2 items hgi,
      aggsOfList_orderBy ?hf3 orderBy hob, colsOutsideAggsList_orderBy ?hf4 orderBy hob] at hraw
    case hf => intros; rfl
    case hf2 => intros; rfl
    case hf3 => intro o; cases o; rfl
    case hf4 => intro o; cases o; rfl
    simp only [aggsOfOpt, colsOutsideAggsOpt, List.append_nil, hgbe, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
      at hraw
    refine ⟨_, n, qf, cf, hf, qf, .inl ⟨rfl, rfl⟩, ?_⟩
  case' some w =>
    simp only [subsOf_frag w (hw w rfl), List.foldl_nil, List.isEmpty_nil, ↓reduceIte] at hraw
    rcases hp : elabExpr cf N.fold noHook w with _ | p
    · simp [hp, bind, Except.bind] at hraw
    simp only [hp, bind, Except.bind, pure, Except.pure] at hraw
    rw [aggsOfList_groupItems ?hf items hgi, colsOutsideAggsList_groupItems ?hf2 items hgi,
      aggsOfList_orderBy ?hf3 orderBy hob, colsOutsideAggsList_orderBy ?hf4 orderBy hob] at hraw
    case hf => intros; rfl
    case hf2 => intros; rfl
    case hf3 => intro o; cases o; rfl
    case hf4 => intro o; cases o; rfl
    simp only [aggsOfOpt, colsOutsideAggsOpt, List.append_nil, hgbe, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
      at hraw
    refine ⟨_, n, qf, cf, hf, .select p qf, .inr ⟨w, p, rfl, hp, rfl⟩, ?_⟩
  all_goals
    split at hraw
    · cases hraw
    rename_i keyList hk
    split at hraw
    · cases hraw
    rename_i aggList hv
    have hK := mapM_forall₂ hk
    have hV := mapM_forall₂ hv
    -- every item column is a key, so there are no bare columns
    have hkey : ∀ c, SqlEquiv.Expr.col c ∈ groupBy → ∃ e', elabExpr cf N.fold noHook (.col c) = .ok e' ∧
        e' ∈ keyList := fun c hc => by
      obtain ⟨e', he', h⟩ := forall₂_mem_left hK hc
      exact ⟨e', h, he'⟩
    rw [List.filterMap_eq_nil_iff.mpr ?hb] at hraw
    case hb =>
      intro c hc
      have hc' : c ∈ colRefs items := by
        split at hc
        · exact mem_of_mem_eraseDups' _ le_rfl hc
        · simp at hc
      obtain ⟨e', he', hmem⟩ := hkey c (colRefs_mem hgi c hc')
      simp [he', hmem]
    simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mapM_nil,
      pure, Except.pure, List.map_nil, List.append_nil] at hraw
    split at hraw
    · cases hraw
    rename_i out hout
    split at hraw
    · cases hraw
    rename_i its hits
    obtain ⟨keys', hk', rfl⟩ := finishSelect_nondistinct N.fold _ orderBy lim off hraw
    have hX : ∀ y ∈ ((items.map itemExpr).filter aggFragment ++
        orderBy.map SqlEquiv.OrderByItem.expr).eraseDups, aggFragment y = true := by
      intro y hy
      rcases List.mem_append.mp (List.mem_eraseDups.mp hy) with hy | hy
      · exact (List.mem_filter.mp hy).2
      · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hy; exact hob o ho
    refine ⟨keyList, _, fun j => aggList[j], its, keys', hk, ?_, ?_, ?keys, rfl⟩
    case keys =>
      refine forall₂_imp_mem (mapM_forall₂ hk') fun o ho k hok => ?_
      obtain ⟨oe, dir, nulls⟩ := o
      have hfr : aggFragment oe = true := hob _ ho
      have hmem : oe ∈ ((items.map itemExpr).filter aggFragment ++
          orderBy.map SqlEquiv.OrderByItem.expr).eraseDups :=
        List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨_, ho, rfl⟩))
      obtain ⟨j, hj⟩ : ∃ j, ((items.map itemExpr).filter aggFragment ++
          orderBy.map SqlEquiv.OrderByItem.expr).eraseDups.findIdx? (· == oe) = some j :=
        Option.isSome_iff_exists.mp (by
          rw [List.findIdx?_isSome, List.any_eq_true]; exact ⟨oe, hmem, by simp⟩)
      obtain ⟨hjl, hje, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
      simp only [beq_iff_eq] at hje
      have hjv : j < aggList.length := hV.length_eq ▸ hjl
      have hja : j < (aggList ++ []).length := by simpa using hjv
      have hel := (List.forall₂_iff_get.mp hV).2 j hjl hjv
      simp only [List.get_eq_getElem, hje] at hel
      unfold elabOrderKey at hok
      cases oe
      all_goals try simp [aggFragment] at hfr
      all_goals
        simp only [bind, Except.bind] at hok
        rw [elab_of_hook _ _ _ (hook_agg _ _ _ _ hj hja)] at hok
        simp only [pure, Except.pure, Except.ok.injEq] at hok
        subst hok
        exact ⟨⟨j, hja⟩, hel, rfl, rfl, rfl⟩
    · intro ⟨j, hj⟩
      have hjv : j < aggList.length := by simpa using hj
      have hjl := hV.length_eq ▸ hjv
      have hx := (List.forall₂_iff_get.mp hV).2 j hjl hjv
      simp only [List.get_eq_getElem] at hx
      exact ⟨_, hX _ (List.getElem_mem hjl), hx⟩
    · refine forall₂_imp_mem (mapM_forall₂ hits) fun it hit x hx => ?_
      obtain ⟨e, al, rfl, hcase⟩ := groupItems_mem hgi it hit
      dsimp only at hx
      rcases hcase with hfr | ⟨c, rfl, hc⟩
      · -- an aggregate: its column among the aggregates
        have hmem : e ∈ ((items.map itemExpr).filter aggFragment ++
            orderBy.map SqlEquiv.OrderByItem.expr).eraseDups :=
          List.mem_eraseDups.mpr (List.mem_append_left _
            (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_, hit, rfl⟩, hfr⟩))
        obtain ⟨j, hj⟩ : ∃ j, ((items.map itemExpr).filter aggFragment ++
            orderBy.map SqlEquiv.OrderByItem.expr).eraseDups.findIdx?
            (· == e) = some j :=
          Option.isSome_iff_exists.mp (by
            rw [List.findIdx?_isSome, List.any_eq_true]; exact ⟨e, hmem, by simp⟩)
        obtain ⟨hjl, hje, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
        simp only [beq_iff_eq] at hje
        have hjv : j < aggList.length := hV.length_eq ▸ hjl
        have hja : j < (aggList ++ []).length := by simpa using hjv
        rw [elab_of_hook _ _ _ (hook_agg _ _ _ _ hj hja)] at hx
        simp only at hx
        split at hx
        · simp only [Except.ok.injEq] at hx
          subst hx
          refine .inl ⟨⟨j, hja⟩, ?_, rfl⟩
          have := (List.forall₂_iff_get.mp hV).2 j hjl hjv
          simp only [List.get_eq_getElem, hje] at this
          simpa [itemExpr] using this
        · simp [throw, throwThe, MonadExceptOf.throw] at hx
      · -- a key column: its column among the keys
        have hnone : ((items.map itemExpr).filter aggFragment ++
            orderBy.map SqlEquiv.OrderByItem.expr).eraseDups.findIdx?
            (· == SqlEquiv.Expr.col c) = none := by
          rw [List.findIdx?_eq_none_iff]
          intro y hy
          have := hX y hy
          have hne : y ≠ .col c := by rintro rfl; simp [aggFragment] at this
          simpa using hne
        obtain ⟨e', he', hmem⟩ := hkey c hc
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
        obtain ⟨i₀, hi₀⟩ : ∃ i₀, (List.finRange keyList.length).find?
            (fun k : Fin keyList.length => keyList[k] == keyList[i]'hi) = some i₀ :=
          Option.isSome_iff_exists.mp
            ((List.find?_isSome (p := fun k : Fin keyList.length => keyList[k] == keyList[i]'hi)).mpr ⟨⟨i, hi⟩, List.mem_finRange _, beq_self_eq_true (keyList[i]'hi)⟩)
        have hk₀ : keyList[i₀] = keyList[i]'hi := by
          simpa using List.find?_some hi₀
        rw [elab_key keyList out cf N.fold _ hnone he' hi₀] at hx
        simp only at hx
        split at hx
        · simp only [Except.ok.injEq] at hx
          subst hx
          exact .inr ⟨c, i₀, rfl, by rw [he', hk₀], rfl⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at hx


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

/-- Combine the typed groups (through the aggregate and the sort keys) with `SqlEquiv`'s groups. -/
theorem tri_rel {G G' A B : Type _} {GR : G → G' → Prop} {P1 : G → A → Prop} {P2 : A → B → Prop}
    {OR : B → G' → Prop} (gs₀ : List G)
    (H : ∀ g ∈ gs₀, ∀ g' a b, GR g g' → P1 g a → P2 a b → OR b g') :
    ∀ {gs : List G} {gs' : List G'} {as : List A} {bs : List B}, (∀ g ∈ gs, g ∈ gs₀) →
      List.Forall₂ GR gs gs' → List.Forall₂ P1 gs as → List.Forall₂ P2 as bs →
      List.Forall₂ OR bs gs'
  | _, _, _, _, _, .nil, .nil, .nil => .nil
  | g :: _, _ :: _, _ :: _, _ :: _, hsub, .cons hg hgs, .cons h1 h1s, .cons h2 h2s =>
    .cons (H g (hsub g List.mem_cons_self) _ _ _ hg h1 h2)
      (tri_rel gs₀ H (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hgs h1s h2s)

/-- Groups whose projected row and key row both exist: the zipped rows relate. -/
theorem zip_filterMap_rel {X G P K : Type _} {Φ : G → Option P} {Ψ : G → Option K}
    {PR : X → P × K → Prop} : ∀ {xs : List X} {gs : List G},
      List.Forall₂ (fun x g => ∃ p k, Φ g = some p ∧ Ψ g = some k ∧ PR x (p, k)) xs gs →
      List.Forall₂ PR xs ((gs.filterMap Φ).zip (gs.filterMap Ψ))
  | _, _, .nil => .nil
  | _, _, .cons ⟨_, _, hp, hk, h⟩ hs => by
    rw [List.filterMap_cons_some hp, List.filterMap_cons_some hk, List.zip_cons_cons]
    exact .cons h (zip_filterMap_rel hs)

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

set_option maxHeartbeats 4000000 in
/-- **Elaborator correctness for `GROUP BY … ORDER BY` aggregates (#352, roadmap step 3b-3).** For
    `SELECT … FROM f [WHERE p] GROUP BY c₁, …, cₘ ORDER BY a₁, … [LIMIT n] [OFFSET m]`, the items
    and keys as in `elabStmt_correct_group`, every sort key an aggregate of step 3a, and no output
    name able to capture `SqlEquiv`'s sort-key columns: when the statement elaborates, the typed
    query's rows relate, in order, to `SqlEquiv`'s. -/
theorem elabStmt_correct_group_ordered (N : NamedSchema)
    (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hgi : groupItems groupBy items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hw : ∀ w ∈ wh, isFragment w = true) (hobne : orderBy ≠ [])
    (hob : ∀ o ∈ orderBy, aggFragment o.expr = true)
    (hnm : ∀ it ∈ items, '.' ∉ (outName it).toList ∧
      ∀ k, (outName it).toLower ≠ SqlEquiv.groupOrderKeyName k)
    {e : Elaborated N.S}
    (h : elabStmt N (groupOrderStmt items fr wh groupBy orderBy lim off) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupOrderStmt items fr wh groupBy orderBy lim off)).2 =
        some out ∧ List.Forall₂ OutRel rs out := by
  obtain ⟨hty, sub, n, qf, cf, hf, q₀, hq₀, keyList, a, aggs, its, sk, hk, haggs, hits, hsk, rfl⟩ :=
    elab_group_order_shape N hgi hgb hw hob h
  have hlo : orderBy.length = sk.length := hsk.length_eq
  have hsk0 : sk.length ≠ 0 := by
    intro h0; apply hobne; exact List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨hnames, hfrom⟩ := from_rel N hfold hfoldCI hwn hfix hD hrel sub fr hff hf
  simp only [hsk0, ↓reduceIte] at hnames hfrom hty hnb ⊢
  rw [typeOf_limitWrap] at hty
  rw [qnb_limitWrap] at hnb
  -- the sort keys: each the column of an aggregate
  have hskget : ∀ i : Fin sk.length, ∃ j : Fin a,
      elabAgg cf N.fold (orderBy[i.1]'(by omega)).expr = .ok (aggs j) ∧
      (sk[i]).e = .col (Fin.natAdd _ j) ∧ (sk[i]).desc = ((orderBy[i.1]'(by omega)).dir == .desc) ∧
      (sk[i]).nullsFirst = ((orderBy[i.1]'(by omega)).nulls == .first) := by
    intro i
    have := (List.forall₂_iff_get.mp hsk).2 i.1 (by omega) i.2
    simpa using this
  choose kj hkj using hskget
  -- typing
  obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
  obtain ⟨Γa, hΓo, -⟩ := Query.typeOf_project_eq_some.mp hΔ
  obtain ⟨hΓa, -⟩ := Query.typeOf_orderBy_eq_some hΓo
  obtain ⟨Γ₀, Δk, Δa, hq₀ty, hks, has, hΓeq⟩ := Query.typeOf_aggregate_eq_some hΓa
  obtain ⟨-, hnbO, hnbA, hnbq₀⟩ := hnb
  have hnbK := (hnbA Γ₀ hq₀ty).1
  have hnbAgg := (hnbA Γ₀ hq₀ty).2
  have hτb : ∀ i : Fin sk.length, Δa (kj i) ≠ .bool := by
    intro i hb
    apply hnbO Γa hΓa i
    rw [(hkj i).2.1, ← hΓeq]
    simp [Expr.typeOf, hb]
  have hsrc : qf.typeOf = some Γ₀ := by
    rcases hq₀ with ⟨-, rfl⟩ | ⟨w, p, -, -, rfl⟩
    · exact hq₀ty
    · exact (Query.typeOf_select_eq_some.mp hq₀ty).1
  have hnbsrc : QNoBoolOrder qf := by
    rcases hq₀ with ⟨-, rfl⟩ | ⟨w, p, -, -, rfl⟩
    · exact hnbq₀
    · exact hnbq₀.2
  obtain ⟨hdivf, Rf, hRf, hrelf⟩ := hfrom hsrc hnbsrc
  have hrows : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) Rf
      (SqlEquiv.evalFrom db fr) := hrelf.imp fun r u h =>
    ⟨rowRel_of_keyed N.fold hfold hfoldCI (fun j => (hnames j).1) (fun j => (hnames j).2) h.1, h.2⟩
  have hdivq₀ : q₀.divSafe = true := by
    rcases hq₀ with ⟨-, rfl⟩ | ⟨w, p, hwp, hp, rfl⟩
    · exact hdivf
    · simp only [Query.divSafe, hdivf, Bool.and_true]
      exact Translates.divSafe _ _ (translates_of_elab _ _ w (hw w hwp) hp)
  obtain ⟨R, hR⟩ := Query.IsSafe.exists_eval_eq_ok (q := q₀) ⟨by simp [hq₀ty], hdivq₀⟩ hD
  -- the keys translate the `GROUP BY` columns
  have hK := mapM_forall₂ hk
  have hlen : groupBy.length = keyList.length := hK.length_eq
  have htk : ∀ i : Fin keyList.length, Translates cf N.fold (groupBy[i.1]'(by omega)) keyList[i] := by
    intro i
    have h1 := (List.forall₂_iff_get.mp hK).2 i.1 (by omega) i.2
    simp only [List.get_eq_getElem] at h1
    obtain ⟨c, hc⟩ := hgc _ (List.getElem_mem (by omega : i.1 < groupBy.length))
    rw [hc] at h1 ⊢
    exact translates_of_elab cf N.fold _ rfl h1
  -- the typed query evaluates
  have hdivK : ∀ i : Fin keyList.length, (keyList[i]).divSafe = true :=
    fun i => Translates.divSafe _ _ (htk i)
  have hsafe : (limitWrap lim off (Query.project (fun i : Fin its.length => (its[i]).1)
      (Query.orderBy (fun i : Fin sk.length => sk[i])
        (Query.aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀)))).IsSafe := by
    refine ⟨by rw [typeOf_limitWrap]; exact hty, ?_⟩
    rw [divSafe_limitWrap]
    have hcols : ∀ i : Fin its.length, ((its[i]).1).divSafe = true := by
      intro i
      rcases (List.forall₂_iff_get.mp hits).2 i.1 (by have := hits.length_eq; omega) i.2 with
        ⟨j, -, hj⟩ | ⟨c, i', -, -, hj⟩ <;>
        (simp only [List.get_eq_getElem] at hj; show ((its[i.1]).1).divSafe = true; rw [hj]; rfl)
    have hda : ∀ j, (aggs j).divSafe = true := fun j => by
      obtain ⟨x, hx, hel⟩ := haggs j; exact agg_divSafe cf N.fold x hx hel
    have hdsk : ∀ i : Fin sk.length, (sk[i]).e.divSafe = true := fun i => by rw [(hkj i).2.1]; rfl
    simp only [Query.divSafe, hda, hdivq₀, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun i => hcols i, fun i => hdsk i, fun i => hdivK i, fun _ => trivial⟩
  obtain ⟨rs, hrs⟩ := Query.IsSafe.exists_eval_eq_ok hsafe hD
  refine ⟨rs, hrs, _, rfl, ?_⟩
  -- the typed evaluation, step by step
  obtain ⟨base, hbase, rfl⟩ := eval_limitWrap D lim off _ hrs
  rw [Query.eval_project] at hbase
  obtain ⟨sorted, hsorted, hout⟩ := bind_ok hbase
  rw [Query.eval_orderBy] at hsorted
  obtain ⟨rowsA, hA, hsorted⟩ := bind_ok hsorted
  obtain ⟨keyedS, hkeyedS, hpure⟩ := bind_ok hsorted
  cases hpure
  have hAconf := Query.conforms_of_eval_eq_ok hD hΓa hA
  rw [Query.eval_aggregate, hR] at hA
  obtain ⟨R', hR', hA⟩ := bind_ok hA
  cases hR'
  obtain ⟨keyed, hkeyed, hgrp⟩ := bind_ok hA
  have hg0 : keyList.length ≠ 0 := by
    intro h0; apply hgb; exact List.eq_nil_of_length_eq_zero (by omega)
  have hgroups : Row.groups keyed = Row.groupAux [] keyed := by simp [Row.groups, hg0]
  -- the keyed rows
  have hKeyed : List.Forall₂ (fun r p => ∃ k, Expr.evalRow (fun i : Fin keyList.length => keyList[i]) r
      = .ok k ∧ p = (k, r)) R keyed :=
    (mapM_forall₂ hkeyed).imp fun r p h => bind_pure_ok h
  -- the sorted rows: an aggregate row, keyed by its sort-key columns
  have hKS : List.Forall₂ (fun A x => A.Conforms Γa ∧ ∃ kk,
      Expr.evalRow (fun i : Fin sk.length => (sk[i]).e) A = .ok kk ∧ x = (kk, A)) rowsA keyedS :=
    forall₂_imp_mem (mapM_forall₂ hkeyedS) fun A hAm x hx => ⟨hAconf A hAm, bind_pure_ok hx⟩
  -- `SqlEquiv`'s side
  simp only [SqlEquiv.evalQuery]
  rw [SqlEquiv.evalSelect_eq_evalSelectCore]
  obtain ⟨F, F', Φ, Ψ, hF, hF', hΦ, hΨ, heq⟩ :=
    evalSelectCore_grouped_ordered _ _ _ _ _ _ _ _ _ _ items fr wh groupBy orderBy lim off hgb
  rw [heq, applyOrder_eq]
  apply limit_rel
  have hgob : (SqlEquiv.groupOrderByItems orderBy).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff, ← List.length_pos_iff, length_groupOrderByItems]; omega
  simp only [hgob, Bool.false_eq_true, ↓reduceIte]
  -- over any source rows related to the typed input
  have final : ∀ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U →
      List.Forall₂ OutRel base (((((U.foldl F []).filterMap Φ).zip
        ((U.foldl F' []).filterMap Ψ)).mergeSort (fun p₁ p₂ =>
          SqlEquiv.compareByOrderItemsParam (fun db' r e => SqlEquiv.evalExprWithDb db' r e) db
            (p₁.1 ++ p₁.2) (p₂.1 ++ p₂.2) (SqlEquiv.groupOrderByItems orderBy))).map Prod.fst) := by
    intro U hRU
    let kf : SqlEquiv.Row → List (Option SqlEquiv.Value) := fun u =>
      groupBy.map fun e => (SqlEquiv.evalExprWithDb db u e).map SqlEquiv.Value.setKey
    let E : Row keyList.length × Row n → SqlEquiv.Row → Prop := fun p u =>
      (RowRel cf N.fold p.2 u ∧ p.2.Conforms Γ₀) ∧
        Expr.evalRow (fun i : Fin keyList.length => keyList[i]) p.2 = .ok p.1 ∧ KRel Δk p.1 (kf u)
    -- each keyed row relates to its untyped row, keys included
    have hE : List.Forall₂ E keyed U := by
      refine zip_rel (fun r pk u hpk hq => ?_) hKeyed hRU
      obtain ⟨k, hk, rfl⟩ := hpk
      refine ⟨hq, hk, ?_⟩
      have hval : ∀ i : Fin keyList.length, ∃ v,
          SqlEquiv.evalExprWithDb db u (groupBy[i.1]'(by omega)) = some v ∧
            TRel (Δk i) (k i) v := by
        intro i
        have hki : (keyList[i]).eval r = .ok (k i) := Expr.evalRow_eq_ok_iff.mp hk i
        obtain ⟨v, hv, hrel⟩ := Translates.eval_rel cf N.fold db hq.1 hq.2 (htk i) (hnbK i) hki
        exact ⟨v, hv, hrel, Expr.hasType_of_eval_eq_ok hq.2 (hks i) hki⟩
      choose w hw using hval
      refine ⟨w, ?_, fun i => (hw i).2⟩
      apply List.ext_getElem (by simp [kf, hlen])
      intro i h1 h2
      simp only [kf, List.getElem_map, List.getElem_ofFn]
      rw [(hw ⟨i, by simpa using h2⟩).1]; rfl
    have hgrel := groupAux_rel (E := E) (kf := kf) (KRel := KRel Δk) (fun _ _ _ h => h.2.2)
      (fun _ _ _ _ h₁ h₂ => krel_iff h₁ h₂) hE (acc := []) (acc' := []) .nil
    rw [foldl_insU kf F hF U [] List.nodup_nil, foldl_insU kf F' hF' U [] List.nodup_nil]
    have hsub : ∀ grp ∈ Row.groupAux [] keyed, grp ∈ Row.groups keyed := by
      rw [hgroups]; exact fun _ h => h
    have hGO : Row.GroupsOf keyed (Row.groups keyed) := by
      rw [hgroups]; exact Row.groupsOf_groupAux (fun _ h => by simp at h) (fun x hx => hx)
    -- a sorted pair: the typed (sort keys, aggregate row) against `SqlEquiv`'s
    -- (projected row, key row)
    let τ : Fin sk.length → SqlType := fun i => Δa (kj i)
    let PR : Row sk.length × Row (keyList.length + a) → SqlEquiv.Row × SqlEquiv.Row → Prop :=
      fun x y => (∀ o, Expr.evalRow (fun i : Fin its.length => (its[i]).1) x.2 = .ok o →
          OutRel o y.1) ∧
        (∀ i : Fin sk.length, ∃ v, SqlEquiv.evalExprWithDb db (y.1 ++ y.2)
          ((SqlEquiv.groupOrderByItems orderBy)[i.1]'(by
            rw [length_groupOrderByItems]; omega)).expr = some v ∧ DatumRel (x.1 i) v) ∧
        ∀ i, (x.1 i).HasType (τ i)
    have hPR : List.Forall₂ (fun x g => ∃ p k, Φ g = some p ∧ Ψ g = some k ∧ PR x (p, k))
        keyedS (U.foldl (fun gs u => insU (kf u) u gs) []) := by
      refine tri_rel (Row.groups keyed) ?_ hsub hgrel
        (by rw [← hgroups]; exact mapM_forall₂ hgrp) hKS
      rintro ⟨k, rs'⟩ hgm ⟨key, us⟩ rowA x ⟨hkk, hrs'⟩ h1 ⟨hAc, kk, hkk', rfl⟩
      obtain ⟨hne, -⟩ := hGO _ hgm
      simp only at hne hrs' hkk
      have hus : us ≠ [] := by
        rintro rfl; cases hrs'; exact hne rfl
      obtain ⟨s, hs⟩ : ∃ s, SqlEquiv.bareSampleRow (fun r e => SqlEquiv.evalExprWithDb db r e)
          (SqlEquiv.selectMinMaxCalls items none) us = some s :=
        Option.ne_none_iff_exists'.mp ((SqlEquiv.bareSampleRow_eq_none_iff _ _ _).not.mpr hus)
      have hsm := bareSampleRow_mem _ _ hs
      obtain ⟨A, hAe, rfl⟩ := bind_pure_ok h1
      have hrows' : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) rs' us :=
        hrs'.imp fun _ _ h => h.1
      have hitems : ∀ it ∈ items, ∃ e al, it = .exprItem e al := fun it hit => by
        obtain ⟨e, al, h, -⟩ := groupItems_mem hgi it hit; exact ⟨e, al, h⟩
      -- the sort-key values
      have hkv : ∀ i : Fin sk.length, kk i = Fin.append k A (Fin.natAdd _ (kj i)) := by
        intro i
        have h3 := Expr.evalRow_eq_ok_iff.mp hkk' i
        rw [(hkj i).2.1] at h3
        exact (Except.ok.inj h3).symm
      let p := items.flatMap (SqlEquiv.evalSelectItemWithAggParam ee db us s)
      have hval : ∀ i : Fin orderBy.length, ∃ v,
          SqlEquiv.evalExprWithAggParam ee db us (p ++ s) (orderBy[i]).expr = some v ∧
            DatumRel (A (kj ⟨i, by omega⟩)) v := fun i =>
        agg_rel cf N.fold db hrows' (p ++ s) _ (hob _ (List.getElem_mem _)) (hkj ⟨i, by omega⟩).1
          (hnbAgg _) (has _) (evalAll_get hAe _)
      choose vs hvs using hval
      have hkr := groupOrderKeyRow_eq db _ orderBy us s p vs (fun i => (hvs i).1)
      have hfree : KeyNameFree p := by
        intro kv hkv
        obtain ⟨it, hit, hname⟩ := names_of_items db us s hitems kv hkv
        rw [hname]; exact hnm it hit
      refine ⟨_, _, hΦ key us s hs, hΨ key us s hs, ?_, ?_, ?_⟩
      · intro r h2
        have hr := Expr.evalRow_eq_ok_iff.mp h2
        unfold OutRel
        rw [items_vals_group db us s hitems]
        apply List.forall₂_iff_get.mpr
        refine ⟨by simp [hits.length_eq], fun i h1' h2' => ?_⟩
        simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
        have hi : i < its.length := by simpa using h1'
        have hi' : i < items.length := by simpa using h2'
        have hcase := (List.forall₂_iff_get.mp hits).2 i hi' hi
        simp only [List.get_eq_getElem] at hcase
        rcases hcase with ⟨j, hel, hj⟩ | ⟨c, i', hc, hel, hj⟩
        · -- an aggregate
          have hri : r ⟨i, hi⟩ = A j := by
            have h3 := hr ⟨i, hi⟩
            have h4 : ((its[i]).1).eval (Fin.append k A) = .ok (A j) := by
              rw [hj]; show Except.ok _ = _; rw [Fin.append_right]
            exact Except.ok.inj (h3.symm.trans h4)
          obtain ⟨x, al, hx, hcase'⟩ := groupItems_mem hgi _ (List.getElem_mem hi')
          have hfr : aggFragment (itemExpr items[i]) = true := by
            rw [hx]; simp only [itemExpr]
            rcases hcase' with h | ⟨c, rfl, -⟩
            · exact h
            · rw [hx] at hel; simp [itemExpr, elabAgg, throw, throwThe, MonadExceptOf.throw] at hel
          obtain ⟨v, hv, hvr⟩ := agg_rel cf N.fold db hrows' s _ hfr hel (hnbAgg j) (has j)
            (evalAll_get hAe j)
          rw [hri, hv]; exact hvr
        · -- a key column, read on the sample row
          have hri : r ⟨i, hi⟩ = k i' := by
            have h3 := hr ⟨i, hi⟩
            have h4 : ((its[i]).1).eval (Fin.append k A) = .ok (k i') := by
              rw [hj]; show Except.ok _ = _; rw [Fin.append_left]
            exact Except.ok.inj (h3.symm.trans h4)
          obtain ⟨rs_, -, hE_⟩ := forall₂_mem_right hrs' hsm
          have hki : (keyList[i']).eval rs_ = .ok (k i') := Expr.evalRow_eq_ok_iff.mp hE_.2.1 i'
          have htr := translates_of_elab cf N.fold (.col c) rfl hel
          obtain ⟨v, hv, hvr⟩ := Translates.eval_rel cf N.fold db hE_.1.1 hE_.1.2 htr (hnbK i') hki
          rw [hri, hc]
          simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
          exact hvr
      · intro i
        refine ⟨vs ⟨i, by omega⟩, ?_, ?_⟩
        · rw [getElem_groupOrderByItems]
          show SqlEquiv.evalExprWithDb db (p ++ SqlEquiv.groupOrderKeyRow db _ orderBy us s p)
            (.col ⟨none, SqlEquiv.groupOrderKeyName i⟩) = _
          rw [SqlEquiv.evalExprWithDb_col, hkr]
          exact keyRow_lookup p hfree vs ⟨i, by omega⟩
        · show DatumRel (kk i) _
          rw [hkv i, Fin.append_right]; exact (hvs ⟨i, by omega⟩).2
      · intro i
        show (kk i).HasType (Δa (kj i))
        have := hAc (Fin.natAdd _ (kj i))
        simp only [← hΓeq, Fin.append_right] at this
        rw [hkv i, Fin.append_right]; exact this
    have hPRz := zip_filterMap_rel hPR
    obtain ⟨W, hW1, hW2, hW⟩ := sorted_gen (fun i : Fin sk.length => sk[i]) τ
      (fun p₁ p₂ => SqlEquiv.compareByOrderItemsParam
        (fun db' r e => SqlEquiv.evalExprWithDb db' r e) db (p₁.1 ++ p₁.2) (p₂.1 ++ p₂.2)
        (SqlEquiv.groupOrderByItems orderBy)) PR
      (fun x y hxy i => hxy.2.2 i) (fun x₁ y₁ x₂ y₂ h₁ h₂ => by
        apply compareBy_agree' _ db _ _ _ (by rw [length_groupOrderByItems]; exact hlo)
        intro i
        obtain ⟨v₁, hv₁, hr₁⟩ := h₁.2.1 i
        obtain ⟨v₂, hv₂, hr₂⟩ := h₂.2.1 i
        rw [hv₁, hv₂]
        refine cmpDatum_agree (sk[i]) _ ?_ ?_ hr₁ hr₂ ?_
        · rw [getElem_groupOrderByItems]; exact (hkj i).2.2.1
        · rw [getElem_groupOrderByItems]; exact (hkj i).2.2.2
        · rintro x y ⟨hx, -⟩
          have := h₁.2.2 i
          rw [hx] at this
          exact hτb i (by simpa [Datum.HasType] using this.symm)) hPRz
    rw [hW1, List.map_map] at hout
    rw [hW2, List.map_map]
    exact mapM_rel_of (fun w hw d hd => (hW w hw).1 d hd) hout
  apply final
  rcases hq₀ with ⟨rfl, rfl⟩ | ⟨w, p, rfl, hp, rfl⟩
  · rw [hRf, Except.ok.injEq] at hR; subst hR; exact hrows
  · have hR' := hR
    simp only [Query.eval_select, hRf, bind, Except.bind] at hR'
    exact filter_rel _ _ db (translates_of_elab _ _ w (hw w rfl) hp) (hnbq₀.1 _ hsrc) hrows hR'

end SqlBridge.CorrectGroupOrder
