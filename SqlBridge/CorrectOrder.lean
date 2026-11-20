/-
  Elaborator correctness with `ORDER BY` / `LIMIT` / `OFFSET` (#352, roadmap step 1).

  `SqlEquiv` sorts with `List.mergeSort` and a Boolean comparator that re-evaluates the `ORDER BY`
  expressions on `projected ++ source` rows; the typed core sorts keyed rows with a stable
  insertion sort (`sortKeyed`). This file connects the two:

  * Sorting: merge sort and insertion sort agree for a comparator that is a total preorder on the
    list's elements, ties included (`SortBridge.mergeSort_eq_insertionSort_of_mem`).
  * Comparators: on related rows, `SqlEquiv`'s comparator decides as the typed lexicographic
    comparison does (`cmpDatum_agree`, `compareBy_agree`), except on two booleans, which
    `SqlEquiv` does not order.
  * The typed comparator is a total preorder on well-typed key rows (`transCmp_cmpKeyRows`,
    `keyed_total_trans`).
  * Keys: an elaborated column key has the value `SqlEquiv` finds for it on `projected ++ source`
    (`orderKey_rel`, `keysRel_of_elab`).
  * The statement: `elabStmt_correct_ordered`, for
    `SELECT e₁, …, eₖ FROM t [AS a] [WHERE p] [ORDER BY c₁, …] [LIMIT n] [OFFSET m]`; the
    result rows relate in order, as in `elabStmt_correct`. Roadmap and coverage in
    `docs/TYPED_CORE_PLAN.md`; examples in `SqlCoreTest/CorrectExamples.lean`.
-/
import SqlBridge.Correct

namespace SortBridge
open List

variable {α : Type _}

/-- Inserting `a` past a prefix it does not precede, in front of a suffix whose head it precedes. -/
theorem orderedInsert_append (r : α → α → Prop) [DecidableRel r] (a : α) :
    ∀ (l₁ l₂ : List α), (∀ b ∈ l₁, ¬ r a b) → (∀ b ∈ l₂.head?, r a b) →
      orderedInsert r a (l₁ ++ l₂) = l₁ ++ a :: l₂
  | [], [], _, _ => rfl
  | [], b :: l₂, _, h2 => orderedInsert_cons_of_le r l₂ (h2 b rfl)
  | b :: l₁, l₂, h1, h2 => by
    rw [List.cons_append, orderedInsert_of_not_le r _ (h1 b mem_cons_self),
      orderedInsert_append r a l₁ l₂ (fun c hc => h1 c (mem_cons_of_mem _ hc)) h2, List.cons_append]

/-- Merge sort and insertion sort agree for a comparator that is a total preorder, ties included:
both are stable. -/
theorem mergeSort_eq_insertionSort_total (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a) :
    ∀ l : List α, l.mergeSort le = l.insertionSort (fun a b => le a b = true)
  | [] => by simp
  | a :: l => by
    obtain ⟨l₁, l₂, h1, h2, h3⟩ := mergeSort_cons trans total a l
    rw [insertionSort_cons, ← mergeSort_eq_insertionSort_total le trans total l, h2, h1]
    symm
    apply orderedInsert_append
    · intro b hb; simpa using h3 b hb
    · intro b hb
      have hp := pairwise_mergeSort trans total (a :: l)
      rw [h1, pairwise_append] at hp
      have hb' : b ∈ l₂ := mem_of_mem_head? hb
      exact (pairwise_cons.mp hp.2.1).1 b hb'

/-- The same, for a comparator that is a total preorder on the list's elements only. -/
theorem mergeSort_eq_insertionSort_of_mem (le : α → α → Bool) (l : List α)
    (trans : ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, le a b → le b c → le a c)
    (total : ∀ a ∈ l, ∀ b ∈ l, le a b || le b a) :
    l.mergeSort le = l.insertionSort (fun a b => le a b = true) := by
  let le' : {x // x ∈ l} → {x // x ∈ l} → Bool := fun a b => le a.1 b.1
  have e := mergeSort_eq_insertionSort_total le'
    (fun a b c => trans a.1 a.2 b.1 b.2 c.1 c.2) (fun a b => total a.1 a.2 b.1 b.2) l.attach
  have := congrArg (List.map Subtype.val) e
  rw [map_mergeSort (s := le) (fun _ _ _ _ => rfl), attach_map_subtype_val,
    map_insertionSort (fun a b => le' a b = true) (fun a b => le a b = true) Subtype.val _
      (fun _ _ _ _ => Iff.rfl), attach_map_subtype_val] at this
  exact this

end SortBridge

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge.Correct Std

/-- An ordering as `SqlEquiv`'s one-key comparison reports it: `some true` when the first row
sorts first, `some false` when the second does, `none` on a tie. -/
def toB : Ordering → Option Bool
  | .lt => some true
  | .gt => some false
  | .eq => none

/-- Related values of incomparable types are incomparable on both sides. -/
theorem compare_none_of_cmp_error {a b : SqlCore.Value} {a' b' : SqlEquiv.Value} (ha : ValRel a a')
    (hb : ValRel b b') {e : EvalError} (h : Value.cmp a b = .error e) : a'.compare b' = none := by
  cases ha <;> cases hb <;> simp_all [Value.cmp, SqlEquiv.Value.compare]

/-- One `ORDER BY` key: the typed comparison of two related datums decides as `SqlEquiv`'s does,
    when the key's direction and `NULL` placement are the item's and the datums are not two
    booleans (`SqlEquiv` does not order booleans). -/
theorem cmpDatum_agree {n : ℕ} (k : SortKey n) (item : SqlEquiv.OrderByItem)
    (hd : k.desc = (item.dir == .desc)) (hn : k.nullsFirst = (item.nulls == .first))
    {d₁ d₂ : Datum} {v₁ v₂ : SqlEquiv.Value} (h₁ : DatumRel d₁ v₁) (h₂ : DatumRel d₂ v₂)
    (hnb : ∀ x y, ¬ (d₁ = some (.bool x) ∧ d₂ = some (.bool y))) :
    SqlEquiv.orderKeyCmp item (some v₁) (some v₂) = toB (k.cmpDatum d₁ d₂) := by
  obtain ⟨e, dir, nulls⟩ := item
  cases d₁ with
  | none =>
    obtain ⟨t₁, rfl⟩ := h₁
    cases d₂ with
    | none =>
      obtain ⟨t₂, rfl⟩ := h₂
      simp [SqlEquiv.orderKeyCmp, SqlEquiv.orderKeyIsNull, SortKey.cmpDatum, toB]
    | some b =>
      have hb := h₂.ne_null
      cases v₂ <;> simp_all [SqlEquiv.orderKeyCmp, SqlEquiv.orderKeyIsNull, SortKey.cmpDatum,
        SqlEquiv.OrderByItem.nulls] <;> cases nulls <;> rfl
  | some a =>
    have ha := h₁.ne_null
    cases d₂ with
    | none =>
      obtain ⟨t₂, rfl⟩ := h₂
      cases v₁ <;> simp_all [SqlEquiv.orderKeyCmp, SqlEquiv.orderKeyIsNull, SortKey.cmpDatum,
        SqlEquiv.OrderByItem.nulls] <;> cases nulls <;> rfl
    | some b =>
      have hb := h₂.ne_null
      have hnull : ∀ v : SqlEquiv.Value, (∀ t, v ≠ .null t) → SqlEquiv.orderKeyIsNull (some v) = false :=
        fun v hv => by cases v <;> simp_all [SqlEquiv.orderKeyIsNull]
      simp only [SqlEquiv.orderKeyCmp, hnull v₁ ha, hnull v₂ hb, SortKey.cmpDatum, hd]
      rcases hc : Value.cmp a b with err | o
      · rw [compare_none_of_cmp_error h₁ h₂ hc]
        simp [Except.toOption, toB]
      · rw [compare_of_cmp h₁ h₂ (fun x y hxy => hnb x y ⟨by rw [hxy.1], by rw [hxy.2]⟩) hc]
        simp only [Except.toOption, Option.getD_some, SqlEquiv.OrderByItem.dir]
        cases o <;> cases dir <;> rfl

/-- The first decision in a list of one-key comparisons; all ties mean "in order". -/
def lexB : List (Option Bool) → Bool
  | [] => true
  | some b :: _ => b
  | none :: rest => lexB rest

theorem compareByOrderItems_eq_lexB (exprEval : SqlEquiv.Database → SqlEquiv.Row → SqlEquiv.Expr →
    Option SqlEquiv.Value) (db : SqlEquiv.Database) (r₁ r₂ : SqlEquiv.Row) :
    ∀ items : List SqlEquiv.OrderByItem, SqlEquiv.compareByOrderItemsParam exprEval db r₁ r₂ items =
      lexB (items.map fun it =>
        SqlEquiv.orderKeyCmp it (exprEval db r₁ it.expr) (exprEval db r₂ it.expr))
  | [] => rfl
  | it :: rest => by
    simp only [SqlEquiv.compareByOrderItemsParam, List.map_cons]
    split <;> rename_i h <;> simp only [h, lexB, compareByOrderItems_eq_lexB exprEval db r₁ r₂ rest]

theorem foldr_then_ne_gt : ∀ os : List Ordering,
    decide (os.foldr Ordering.then .eq ≠ .gt) = lexB (os.map toB)
  | [] => rfl
  | .eq :: os => by
    have ih := foldr_then_ne_gt os
    simp only [List.foldr_cons, Ordering.then, List.map_cons, toB, lexB]
    exact ih
  | .lt :: os => by simp [Ordering.then, toB, lexB]
  | .gt :: os => by simp [Ordering.then, toB, lexB]

/-- All keys: `SqlEquiv`'s comparator (the first row sorts first or ties) is the typed lexicographic
    comparison not being `gt`, when every key decides alike. -/
theorem compareBy_agree (exprEval : SqlEquiv.Database → SqlEquiv.Row → SqlEquiv.Expr →
    Option SqlEquiv.Value) (db : SqlEquiv.Database) (r₁ r₂ : SqlEquiv.Row)
    (items : List SqlEquiv.OrderByItem) {m : ℕ} (keys : Fin items.length → SortKey m)
    (a b : Row items.length)
    (h : ∀ i : Fin items.length, SqlEquiv.orderKeyCmp items[i] (exprEval db r₁ items[i].expr)
      (exprEval db r₂ items[i].expr) = toB ((keys i).cmpDatum (a i) (b i))) :
    SqlEquiv.compareByOrderItemsParam exprEval db r₁ r₂ items = decide (cmpKeyRows keys a b ≠ .gt) := by
  rw [compareByOrderItems_eq_lexB, cmpKeyRows,
    ← List.foldr_map (f := fun i => (keys i).cmpDatum (a i) (b i)), foldr_then_ne_gt, List.map_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_finRange, Function.comp_apply]
  exact h ⟨i, by simpa using h₁⟩



/-! ### The typed sort comparator is a total preorder on well-typed rows -/

section Generic
variable {α β : Type _}

theorem transCmp_comap (c : β → β → Ordering) [TransCmp c] (f : α → β) :
    TransCmp (fun a b => c (f a) (f b)) where
  eq_swap := OrientedCmp.eq_swap (cmp := c)
  isLE_trans h₁ h₂ := TransCmp.isLE_trans (cmp := c) h₁ h₂

theorem transCmp_eq : TransCmp (fun _ _ : α => Ordering.eq) where
  eq_swap := rfl
  isLE_trans _ _ := rfl

theorem transCmp_then (c₁ c₂ : α → α → Ordering) [TransCmp c₁] [TransCmp c₂] :
    TransCmp (fun a b => (c₁ a b).then (c₂ a b)) :=
  inferInstanceAs (TransCmp (compareLex c₁ c₂))

/-- `NULL` first or last (absolute), values compared by `c`, ascending or descending. -/
def optCmp (nf desc : Bool) (c : β → β → Ordering) : Option β → Option β → Ordering
  | none, none => .eq
  | none, some _ => if nf then .lt else .gt
  | some _, none => if nf then .gt else .lt
  | some a, some b => if desc then c b a else c a b

theorem transCmp_optCmp (nf desc : Bool) (c : β → β → Ordering) [TransCmp c] :
    TransCmp (optCmp nf desc c) where
  eq_swap {a b} := by
    cases a <;> cases b <;> cases nf <;> cases desc <;>
      simp only [optCmp, ↓reduceIte, Bool.false_eq_true] <;>
      first
        | rfl
        | exact OrientedCmp.eq_swap (cmp := c)
  isLE_trans {a b d} h₁ h₂ := by
    cases a <;> cases b <;> cases d <;> cases nf <;> cases desc <;>
      simp_all [optCmp] <;>
      first
        | exact TransCmp.isLE_trans (cmp := c) h₁ h₂
        | exact TransCmp.isLE_trans (cmp := fun x y => c y x) h₁ h₂

end Generic

/-- The datums of one type, compared by a sort key. -/
def keyCmp {n : ℕ} (k : SortKey n) (τ : SqlType) :
    {d : Datum // d.HasType τ} → {d : Datum // d.HasType τ} → Ordering :=
  fun a b => k.cmpDatum a.1 b.1

/-- On datums of one type, a key's comparison is `optCmp` over a linear order: integers,
    rationals, strings or booleans. -/
theorem cmpDatum_eq_optCmp {β : Type _} [Ord β] [OrientedCmp (compare : β → β → Ordering)]
    {n : ℕ} (k : SortKey n) (τ : SqlType)
    (f : Value → β) (hf : ∀ a b : Value, a.type = τ → b.type = τ →
      Value.cmp a b = .ok (compare (f a) (f b))) (a b : {d : Datum // d.HasType τ}) :
    keyCmp k τ a b = optCmp k.nullsFirst k.desc compare (a.1.map f) (b.1.map f) := by
  obtain ⟨_ | x, hx⟩ := a <;> obtain ⟨_ | y, hy⟩ := b <;>
    simp only [keyCmp, SortKey.cmpDatum, optCmp, Option.map]
  rw [hf x y hx hy]
  simp only [Except.toOption, Option.getD_some]
  cases k.desc
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte]
    exact (OrientedCmp.eq_swap (cmp := (compare : β → β → Ordering))).symm

theorem transCmp_keyCmp_of {β : Type _} [Ord β] [TransCmp (compare : β → β → Ordering)]
    {n : ℕ} (k : SortKey n) (τ : SqlType) (f : Value → β)
    (hf : ∀ a b : Value, a.type = τ → b.type = τ → Value.cmp a b = .ok (compare (f a) (f b))) :
    TransCmp (keyCmp k τ) := by
  have h : keyCmp k τ = fun a b => optCmp k.nullsFirst k.desc compare (a.1.map f) (b.1.map f) :=
    funext fun a => funext fun b => cmpDatum_eq_optCmp k τ f hf a b
  rw [h]
  have := transCmp_optCmp (β := β) k.nullsFirst k.desc compare
  exact transCmp_comap (optCmp k.nullsFirst k.desc compare)
    (fun a : {d : Datum // d.HasType τ} => a.1.map f)

/-- A sort key compares the datums of any one type as a total preorder. -/
theorem transCmp_keyCmp {n : ℕ} (k : SortKey n) (τ : SqlType) : TransCmp (keyCmp k τ) := by
  cases τ with
  | int =>
    exact transCmp_keyCmp_of k .int (fun | .int z => z | _ => 0) (fun a b ha hb => by
      cases a <;> cases b <;> simp_all [Value.type, Value.cmp, compareInt])
  | text =>
    exact transCmp_keyCmp_of k .text (fun | .text s => s | _ => "") (fun a b ha hb => by
      cases a <;> cases b <;> simp_all [Value.type, Value.cmp, compareText])
  | bool =>
    exact transCmp_keyCmp_of k .bool (fun | .bool x => x | _ => false) (fun a b ha hb => by
      cases a <;> cases b <;> simp_all [Value.type, Value.cmp, compareBool])
  | decimal =>
    exact transCmp_keyCmp_of k .decimal (fun | .decimal q => q | _ => 0) (fun a b ha hb => by
      cases a <;> cases b <;> simp_all [Value.type, Value.cmp, compareDec])

/-- Key rows whose `i`-th datum has type `Γ i`. -/
abbrev KeyRow (Γ : Fin k → SqlType) := {r : Row k // ∀ i, (r i).HasType (Γ i)}

theorem transCmp_foldr {n k : ℕ} (keys : Fin k → SortKey n) (Γ : Fin k → SqlType) :
    ∀ l : List (Fin k), TransCmp (fun a b : KeyRow Γ =>
      l.foldr (fun i acc => ((keys i).cmpDatum (a.1 i) (b.1 i)).then acc) .eq)
  | [] => transCmp_eq
  | i :: l => by
    have := transCmp_foldr keys Γ l
    have := transCmp_keyCmp (keys i) (Γ i)
    have := transCmp_comap (keyCmp (keys i) (Γ i)) (fun a : KeyRow Γ => ⟨a.1 i, a.2 i⟩)
    exact transCmp_then (fun a b : KeyRow Γ => keyCmp (keys i) (Γ i) ⟨a.1 i, a.2 i⟩ ⟨b.1 i, b.2 i⟩)
      (fun a b : KeyRow Γ => l.foldr (fun i acc => ((keys i).cmpDatum (a.1 i) (b.1 i)).then acc) .eq)

/-- On well-typed key rows, `cmpKeyRows` is a total preorder. -/
theorem transCmp_cmpKeyRows {n k : ℕ} (keys : Fin k → SortKey n) (Γ : Fin k → SqlType) :
    TransCmp (fun a b : KeyRow Γ => cmpKeyRows keys a.1 b.1) :=
  transCmp_foldr keys Γ (List.finRange k)

/-- The comparator the typed sort uses (`sortKeyed`) is total and transitive on keyed rows whose
    keys are well typed: the hypotheses of `SortBridge.mergeSort_eq_insertionSort_of_mem`. -/
theorem keyed_total_trans {n k : ℕ} {β : Type _} (keys : Fin k → SortKey n) (Γ : Fin k → SqlType)
    (L : List (Row k × β)) (hL : ∀ x ∈ L, ∀ i, (x.1 i).HasType (Γ i)) :
    (∀ x ∈ L, ∀ y ∈ L, decide (cmpKeyRows keys x.1 y.1 ≠ .gt) ||
      decide (cmpKeyRows keys y.1 x.1 ≠ .gt)) ∧
    (∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L, decide (cmpKeyRows keys x.1 y.1 ≠ .gt) = true →
      decide (cmpKeyRows keys y.1 z.1 ≠ .gt) = true → decide (cmpKeyRows keys x.1 z.1 ≠ .gt) = true) := by
  have := transCmp_cmpKeyRows keys Γ
  let c := fun a b : KeyRow Γ => cmpKeyRows keys a.1 b.1
  refine ⟨fun x hx y hy => ?_, fun x hx y hy z hz h₁ h₂ => ?_⟩
  · have hs := OrientedCmp.eq_swap (cmp := c) (a := ⟨x.1, hL x hx⟩) (b := ⟨y.1, hL y hy⟩)
    simp only [c] at hs
    rw [hs]
    cases cmpKeyRows keys y.1 x.1 <;> simp [Ordering.swap]
  · have := TransCmp.le_trans (cmp := c) (x := ⟨x.1, hL x hx⟩) (y := ⟨y.1, hL y hy⟩)
      (z := ⟨z.1, hL z hz⟩) (by simpa [c] using h₁) (by simpa [c] using h₂)
    simpa [c] using this

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge SqlBridge.Correct

/-! ### `ORDER BY` keys: output names, then the input -/

/-- An item's output column name in `SqlEquiv` (`evalSelectItem`). -/
def outName : SqlEquiv.SelectItem → String
  | .exprItem e al => al.getD (SqlEquiv.exprToName e)
  | .star _ => ""

/-- SELECT items whose output names are the same in both evaluators and contain no dot: a column
    without an alias, or any expression with an alias. (Unaliased non-column items are named
    `expr` by `SqlEquiv` and `?column?` by the elaborator.) -/
def itemsNamed : List SqlEquiv.SelectItem → Bool
  | [] => true
  | .exprItem (.col c) none :: rest => decide ('.' ∉ c.column.toList) && itemsNamed rest
  | .exprItem _ (some a) :: rest => decide ('.' ∉ a.toList) && itemsNamed rest
  | _ :: _ => false

theorem outName_noDot : ∀ items : List SqlEquiv.SelectItem, itemsNamed items = true →
    ∀ it ∈ items, '.' ∉ (outName it).toList
  | [], _ => by simp
  | .exprItem (.col c) none :: rest, h => by
    simp only [itemsNamed, Bool.and_eq_true, decide_eq_true_eq] at h
    intro it hit
    rcases List.mem_cons.mp hit with rfl | hit
    · simpa [outName, SqlEquiv.exprToName] using h.1
    · exact outName_noDot rest h.2 it hit
  | .exprItem (.lit _) none :: _, h | .exprItem (.binOp ..) none :: _, h
  | .exprItem (.unaryOp ..) none :: _, h | .exprItem (.func ..) none :: _, h
  | .exprItem (.agg ..) none :: _, h | .exprItem .countStar none :: _, h
  | .exprItem (.case ..) none :: _, h | .exprItem (.inList ..) none :: _, h
  | .exprItem (.inSubquery ..) none :: _, h | .exprItem (.exists ..) none :: _, h
  | .exprItem (.subquery ..) none :: _, h | .exprItem (.between ..) none :: _, h
  | .exprItem (.windowFn ..) none :: _, h | .star _ :: _, h => by simp [itemsNamed] at h
  | .exprItem e (some a) :: rest, h => by
    have h' : decide ('.' ∉ a.toList) && itemsNamed rest = true := by
      cases e <;> simpa [itemsNamed] using h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    intro it hit
    rcases List.mem_cons.mp hit with rfl | hit
    · simpa [outName] using h'.1
    · exact outName_noDot rest h'.2 it hit

/-- Fragment items project to one `(name, value)` entry each. -/
theorem flatMap_items (db : SqlEquiv.Database) (u : SqlEquiv.Row) :
    ∀ items : List SqlEquiv.SelectItem, itemsFragment items = true →
      items.flatMap (SqlEquiv.evalSelectItem db u) = items.map fun it => (outName it, itemValue db u it)
  | [], _ => rfl
  | .exprItem e al :: rest, h => by
    simp only [itemsFragment, Bool.and_eq_true] at h
    simp only [List.flatMap_cons, List.map_cons, flatMap_items db u rest h.2, SqlEquiv.evalSelectItem,
      outName, itemValue]
    split <;> simp_all
  | .star _ :: _, h => by simp [itemsFragment] at h

theorem find?_congr' {α : Type _} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.find?_cons, h x List.mem_cons_self,
      find?_congr' (l := l) (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- A dot-free key does not end in `.c`. -/
theorem not_endsWith_dot {k c : String} (hk : '.' ∉ k.toList) :
    k.toLower.endsWith s!".{c.toLower}" = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [endsWith_iff_suffix] at h
  have hd : '.' ∈ k.toLower.toList := by
    apply h.subset
    simp [toString, String.toList_append, toList_dot]
  exact dot_not_mem_map_toLower hk (by simpa [toList_toLower] using hd)

/-- Lookup in `projected ++ source` falls through to the source when no output name matches:
    output names have no dot, so a qualified reference never matches one. -/
theorem getQualified_append_noMatch (p u : SqlEquiv.Row) (q : Option String) (c : String)
    (hdot : ∀ kv ∈ p, '.' ∉ kv.1.toList) (hne : q = none → ∀ kv ∈ p, kv.1.toLower ≠ c.toLower) :
    (p ++ u).getQualified q c = u.getQualified q c := by
  cases q with
  | some t =>
    simp only [SqlEquiv.Row.getQualified, lookupCI_eq_find?, List.find?_append]
    have : p.find? (fun kv => kv.1.toLower == (s!"{t}.{c}").toLower) = none := by
      rw [List.find?_eq_none]
      intro kv hkv h
      have h' := congrArg String.toList (beq_iff_eq.mp h)
      simp only [toList_toLower, toList_qualified, List.map_append, List.map_cons, toLower_dot] at h'
      exact dot_not_mem_map_toLower (hdot kv hkv) (h' ▸ List.mem_append_right _ List.mem_cons_self)
    rw [this, Option.none_or]
  | none =>
    simp only [SqlEquiv.Row.getQualified, List.find?_append]
    have : p.find? (fun kv : String × SqlEquiv.Value =>
        kv.1.toLower == c.toLower || kv.1.toLower.endsWith s!".{c.toLower}") = none := by
      rw [List.find?_eq_none]
      intro kv hkv
      simp [hne rfl kv hkv, not_endsWith_dot (c := c) (hdot kv hkv)]
    rw [this, Option.none_or]

/-- Lookup of a bare name in `projected ++ source` finds the first output column with that name
    (ignoring case). -/
theorem getQualified_none_append_match (p u : SqlEquiv.Row) (c : String)
    (hdot : ∀ kv ∈ p, '.' ∉ kv.1.toList) {kv : String × SqlEquiv.Value}
    (hp : p.find? (fun kv => kv.1.toLower == c.toLower) = some kv) :
    (p ++ u).getQualified none c = some kv.2 := by
  simp only [SqlEquiv.Row.getQualified, List.find?_append]
  rw [find?_congr' (l := p) (q := fun kv => kv.1.toLower == c.toLower)
    (fun x hx => by simp [not_endsWith_dot (c := c) (hdot x hx)]), hp]
  rfl

/-- The elaborated items carry `SqlEquiv`'s output names, for named fragment items. -/
theorem itemsNames_of_elab (N : NamedSchema) {n : ℕ} (cols : Fin n → Column) :
    ∀ (items : List SqlEquiv.SelectItem) {its : List (Expr n × Column)},
      itemsFragment items = true → itemsNamed items = true → elabItems N cols items = .ok its →
      List.Forall₂ (fun it x => x.2.name = outName it) items its
  | [], its, _, _, h => by
    simp only [elabItems, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | .exprItem e al :: rest, its, hf, hn, h => by
    simp only [itemsFragment, Bool.and_eq_true] at hf
    have hn' : itemsNamed rest = true ∧ (al = none → ∃ c, e = .col c) := by
      cases al <;> cases e <;> simp_all [itemsNamed]
    simp only [elabItems] at h
    rcases he : elabExpr cols N.fold noHook e with _ | e'
    · simp [he, bind, Except.bind] at h
    rcases hτ : e'.typeOf (ctx cols) with _ | τ
    · simp [he, hτ, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    rcases hr : elabItems N cols rest with _ | its'
    · simp [he, hτ, hr, bind, Except.bind] at h
    simp only [he, hτ, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine .cons ?_ (itemsNames_of_elab N cols rest hf.2 hn'.1 hr)
    cases al with
    | some a => rfl
    | none =>
      obtain ⟨c, rfl⟩ := hn'.2 rfl
      rfl
  | .star _ :: _, _, hf, _, _ => by simp [itemsFragment] at hf

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String)

/-- A bare `ORDER BY` name that matches output columns: `SqlEquiv` reads the first match's value,
    which relates to the typed key (every match elaborates to the same expression). -/
theorem first_match_rel (hfoldCI : ∀ x y, fold x = fold y ↔ x.toLower = y.toLower)
    (db : SqlEquiv.Database) {Γ : Fin n → SqlType} {r : Row n} {u : SqlEquiv.Row}
    (hrow : RowRel cols fold r u) (hr : r.Conforms Γ) (c : String) {e' : Expr n} {d : Datum}
    (hd : e'.eval r = .ok d) :
    ∀ {items : List SqlEquiv.SelectItem} {its : List (Expr n × Column)},
      ItemsRel cols fold items its → List.Forall₂ (fun it x => x.2.name = outName it) items its →
      (∀ x ∈ its, NoBoolOrder Γ x.1) →
      (∀ x ∈ its.filter (fun x => fold x.2.name == fold c), x.1 = e') →
      its.filter (fun x => fold x.2.name == fold c) ≠ [] →
      ∃ kv, (items.map fun it => (outName it, itemValue db u it)).find?
        (fun kv => kv.1.toLower == c.toLower) = some kv ∧ DatumRel d kv.2
  | _, _, .nil, _, _, _, hne => absurd rfl hne
  | it :: items, x :: its, .cons ⟨e, al, hit, ht⟩ hrest, .cons hnx hnrest, hnb, hall, hne => by
    by_cases hp : fold x.2.name = fold c
    · have hlow : (outName it).toLower = c.toLower := by rw [← hnx]; exact (hfoldCI _ _).mp hp
      have hx : x.1 = e' := hall x (by simp [hp])
      subst hx
      obtain ⟨v, hv, hrel⟩ := Translates.eval_rel cols fold db hrow hr ht
        (hnb x List.mem_cons_self) hd
      refine ⟨(outName it, itemValue db u it), ?_, ?_⟩
      · simp [hlow]
      · subst hit; simpa [itemValue, hv] using hrel
    · have hlow : (outName it).toLower ≠ c.toLower := by
        rw [← hnx]; exact fun h => hp ((hfoldCI _ _).mpr h)
      have hf : (x :: its).filter (fun x => fold x.2.name == fold c) =
          its.filter (fun x => fold x.2.name == fold c) := by simp [hp]
      rw [hf] at hall hne
      obtain ⟨kv, hkv, hrel⟩ := first_match_rel hfoldCI db hrow hr c hd hrest hnrest
        (fun y hy => hnb y (List.mem_cons_of_mem _ hy)) hall hne
      exact ⟨kv, by simp [hlow, hkv], hrel⟩

/-- No output column matches a bare name: no `SqlEquiv` output name matches it either. -/
theorem no_match_names (hfoldCI : ∀ x y, fold x = fold y ↔ x.toLower = y.toLower)
    (db : SqlEquiv.Database) (u : SqlEquiv.Row) (c : String) :
    ∀ {items : List SqlEquiv.SelectItem} {its : List (Expr n × Column)},
      List.Forall₂ (fun it x => x.2.name = outName it) items its →
      its.filter (fun x => fold x.2.name == fold c) = [] →
      ∀ kv ∈ items.map (fun it => (outName it, itemValue db u it)), kv.1.toLower ≠ c.toLower
  | _, _, .nil, _ => by simp
  | it :: items, x :: its, .cons hnx hrest, h => by
    have hp : ¬ fold x.2.name = fold c := by
      intro hp; simp [hp] at h
    have h' : its.filter (fun x => fold x.2.name == fold c) = [] := by simpa [hp] using h
    intro kv hkv
    rcases List.mem_cons.mp hkv with rfl | hkv
    · show (outName it).toLower ≠ c.toLower
      rw [← hnx]; exact fun hl => hp ((hfoldCI _ _).mpr hl)
    · exact no_match_names hfoldCI db u c hrest h' kv hkv

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge SqlBridge.Correct

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String)

/-- A column reference evaluated on the source row and on `projected ++ source` agree when no
    output name matches it. -/
theorem col_rel_of_noMatch (db : SqlEquiv.Database) {Γ : Fin n → SqlType} {r : Row n}
    {u p : SqlEquiv.Row} (hrow : RowRel cols fold r u) (hr : r.Conforms Γ)
    (hdotp : ∀ kv ∈ p, '.' ∉ kv.1.toList) (cr : SqlEquiv.ColumnRef)
    (hne : cr.table = none → ∀ kv ∈ p, kv.1.toLower ≠ cr.column.toLower)
    {e' : Expr n} (he : elabExpr cols fold noHook (.col cr) = .ok e') {d : Datum}
    (hd : e'.eval r = .ok d) :
    ∃ v, SqlEquiv.evalExprWithDb db (p ++ u) (.col cr) = some v ∧ DatumRel d v := by
  have ht := translates_of_elab cols fold (.col cr) rfl he
  obtain ⟨v, hv, hrel⟩ := Translates.eval_rel cols fold db hrow hr ht (by cases ht; trivial) hd
  refine ⟨v, ?_, hrel⟩
  rw [SqlEquiv.evalExprWithDb_col] at hv ⊢
  rw [getQualified_append_noMatch p u cr.table cr.column hdotp hne, hv]

/-- An `ORDER BY` key that is a column reference: the typed key's value on a row relates to the
    value `SqlEquiv` reads on `projected ++ source`, and the key keeps the item's direction and
    `NULL` placement. Output names are looked up first, as in both evaluators. -/
theorem orderKey_rel (hfoldCI : ∀ x y, fold x = fold y ↔ x.toLower = y.toLower)
    (db : SqlEquiv.Database) {Γ : Fin n → SqlType} {r : Row n} {u : SqlEquiv.Row}
    (hrow : RowRel cols fold r u) (hr : r.Conforms Γ)
    {items : List SqlEquiv.SelectItem} {its : List (Expr n × Column)}
    (hif : itemsFragment items = true) (hin : itemsNamed items = true)
    (hir : ItemsRel cols fold items its)
    (hnm : List.Forall₂ (fun it x => x.2.name = outName it) items its)
    (hnb : ∀ x ∈ its, NoBoolOrder Γ x.1) (cr : SqlEquiv.ColumnRef) (dir : SqlEquiv.OrderDir)
    (nulls : SqlEquiv.NullsOrder) {key : SortKey n}
    (hk : elabOrderKey fold (elabExpr cols fold noHook) its ⟨.col cr, dir, nulls⟩ = .ok key)
    {d : Datum} (hd : key.e.eval r = .ok d) :
    (∃ v, SqlEquiv.evalExprWithDb db (items.flatMap (SqlEquiv.evalSelectItem db u) ++ u)
      (.col cr) = some v ∧ DatumRel d v) ∧
    key.desc = (dir == .desc) ∧ key.nullsFirst = (nulls == .first) := by
  rw [flatMap_items db u items hif]
  have hdotp : ∀ kv ∈ items.map (fun it => (outName it, itemValue db u it)), '.' ∉ kv.1.toList := by
    intro kv hkv
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hkv
    exact outName_noDot items hin it hit
  obtain ⟨q, c⟩ := cr
  cases q with
  | some t =>
    simp only [elabOrderKey, bind, Except.bind] at hk
    rcases he : elabExpr cols fold noHook (.col ⟨some t, c⟩) with _ | e'
    · simp [he] at hk
    simp only [he, pure, Except.pure, Except.ok.injEq] at hk
    subst hk
    exact ⟨col_rel_of_noMatch cols fold db hrow hr hdotp _ (by simp) he hd, rfl, rfl⟩
  | none =>
    simp only [elabOrderKey, bind, Except.bind] at hk
    rcases hm : ((its.filter fun it => fold it.2.name == fold c).map (·.1)).eraseDups with
      _ | ⟨e', _ | ⟨e'', l⟩⟩
    · -- no output column: the input
      simp only [hm] at hk
      rcases he : elabExpr cols fold noHook (.col ⟨none, c⟩) with _ | e'
      · simp [he] at hk
      simp only [he, pure, Except.pure, Except.ok.injEq] at hk
      subst hk
      have hf : its.filter (fun it => fold it.2.name == fold c) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro x hx
        have : x.1 ∈ ((its.filter fun it => fold it.2.name == fold c).map (·.1)).eraseDups :=
          List.mem_eraseDups.mpr (List.mem_map_of_mem hx)
        rw [hm] at this; cases this
      exact ⟨col_rel_of_noMatch cols fold db hrow hr hdotp _
        (fun _ => no_match_names fold hfoldCI db u c hnm hf) he hd, rfl, rfl⟩
    · -- one output expression: the first matching output column
      simp only [hm, pure, Except.pure, Except.ok.injEq] at hk
      subst hk
      have hall : ∀ x ∈ its.filter (fun x => fold x.2.name == fold c), x.1 = e' := by
        intro x hx
        have : x.1 ∈ ((its.filter fun it => fold it.2.name == fold c).map (·.1)).eraseDups :=
          List.mem_eraseDups.mpr (List.mem_map_of_mem hx)
        rw [hm] at this; simpa using this
      have hne : its.filter (fun x => fold x.2.name == fold c) ≠ [] := by
        intro h0; rw [h0] at hm; cases hm
      obtain ⟨kv, hkv, hrel⟩ := first_match_rel cols fold hfoldCI db hrow hr c hd hir hnm hnb hall hne
      refine ⟨⟨kv.2, ?_, hrel⟩, rfl, rfl⟩
      rw [SqlEquiv.evalExprWithDb_col]
      exact getQualified_none_append_match _ u c hdotp hkv
    · -- several output expressions: ambiguous, not elaborated
      simp [hm, throw, throwThe, MonadExceptOf.throw] at hk

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlEquiv

theorem evalSelectCore_project_ordered (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool) (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause) (wh : Option Expr)
    (orderBy : List OrderByItem) (lim off : Option Nat)
    (hNoAgg : hasAgg items = false) (hNoWin : hasWindowFn items = false) :
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk false items (some from_) wh [] none orderBy lim off) =
    let src := match wh with
      | some c => (fromEval db from_).filter fun row => exprEval db row c == some (Value.bool true)
      | none => fromEval db from_
    applyOrderByLimitOffsetAligned compareEval db orderBy lim off true src
      (src.map fun row => items.flatMap (selectItemEval db row)) := by
  rw [evalSelectCore_eq_afterFilter]
  cases wh <;>
  simp [evalSelectAfterFilter, evalSelectProjectDistinct, hNoAgg, hNoWin]

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge SqlBridge.Correct

/-! ### Sorting related rows -/

/-- `SqlEquiv`'s projection of a source row. -/
def projRow (db : SqlEquiv.Database) (items : List SqlEquiv.SelectItem) (u : SqlEquiv.Row) :
    SqlEquiv.Row :=
  items.flatMap (SqlEquiv.evalSelectItem db u)

/-- `SqlEquiv`'s `ORDER BY` comparator on `(projected, source)` pairs. -/
def cmpU (db : SqlEquiv.Database) (orderBy : List SqlEquiv.OrderByItem)
    (p₁ p₂ : SqlEquiv.Row × SqlEquiv.Row) : Bool :=
  SqlEquiv.compareByOrderItemsParam (fun db' r e => SqlEquiv.evalExprWithDb db' r e) db
    (p₁.1 ++ p₁.2) (p₂.1 ++ p₂.2) orderBy

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String) (db : SqlEquiv.Database)
  (Γ : Fin n → SqlType) (items : List SqlEquiv.SelectItem) (orderBy : List SqlEquiv.OrderByItem)
  {o : ℕ} (hlen : orderBy.length = o) (keys : Fin o → SortKey n)

/-- A typed keyed row and `SqlEquiv`'s `(projected, source)` pair for the same input row. -/
def PairRel (x : Row o × Row n) (y : SqlEquiv.Row × SqlEquiv.Row) : Prop :=
  RowRel cols fold x.2 y.2 ∧ x.2.Conforms Γ ∧ y.1 = projRow db items y.2 ∧
    Expr.evalRow (fun i => (keys i).e) x.2 = .ok x.1

theorem keyed_rel_of {F : Row n → Except EvalError (Row o × Row n)}
    (hF : ∀ r x, F r = .ok x → Expr.evalRow (fun i => (keys i).e) r = .ok x.1 ∧ x.2 = r) :
    ∀ {R : List (Row n)} {U : List SqlEquiv.Row},
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U →
      ∀ {K}, R.mapM F = .ok K →
      List.Forall₂ (PairRel cols fold db Γ items keys) K ((U.map (projRow db items)).zip U)
  | _, _, .nil, K, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | r :: R, u :: U, .cons hru hrest, K, h => by
    rw [List.mapM_cons] at h
    rcases hk : F r with _ | x
    · simp [hk, bind, Except.bind] at h
    rcases hK : R.mapM F with _ | K'
    · simp [hk, hK, bind, Except.bind] at h
    simp only [hk, hK, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hx1, hx2⟩ := hF r x hk
    obtain ⟨kr, r'⟩ := x
    simp only at hx1 hx2
    subst hx2
    exact .cons ⟨hru.1, hru.2, rfl, hx1⟩ (keyed_rel_of hF hrest hK)

theorem keyed_rel {R : List (Row n)} {U : List SqlEquiv.Row}
    (hRU : List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U) {K}
    (h : R.mapM (fun r => do return (← Expr.evalRow (fun i => (keys i).e) r, r)) = .ok K) :
    List.Forall₂ (PairRel cols fold db Γ items keys) K ((U.map (projRow db items)).zip U) :=
  keyed_rel_of cols fold db Γ items keys (fun r x hx => by
    rcases hk : Expr.evalRow (fun i => (keys i).e) r with _ | kr
    · simp [hk, bind, Except.bind] at hx
    · simp only [hk, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hx
      subst hx; exact ⟨rfl, rfl⟩) hRU h

/-- What each `ORDER BY` key must satisfy: its typed value relates to the value `SqlEquiv` reads on
    `projected ++ source` (`orderKey_rel`), it keeps the item's direction and `NULL` placement,
    and its type is not boolean (`SqlEquiv` does not order booleans). -/
structure KeysRel : Prop where
  val : ∀ r u, RowRel cols fold r u → r.Conforms Γ → ∀ (i : Fin o) d,
    (keys i).e.eval r = .ok d →
      ∃ v, SqlEquiv.evalExprWithDb db (projRow db items u ++ u) (orderBy[i.1]'(hlen ▸ i.2)).expr = some v ∧
        DatumRel d v
  dir : ∀ i : Fin o, (keys i).desc = ((orderBy[i.1]'(hlen ▸ i.2)).dir == .desc)
  nulls : ∀ i : Fin o, (keys i).nullsFirst = ((orderBy[i.1]'(hlen ▸ i.2)).nulls == .first)
  ty : ∀ i : Fin o, ∃ τ, (keys i).e.typeOf Γ = some τ ∧ τ ≠ .bool

/-- A key datum of a conforming row has its key's type. -/
theorem key_hasType {r : Row n} (hr : r.Conforms Γ) {e : Expr n} {τ : SqlType}
    (hτ : e.typeOf Γ = some τ) {d : Datum} (hd : e.eval r = .ok d) : d.HasType τ := by
  rcases Expr.eval_ok_or_divisionByZero hr hτ with ⟨d', hd', ht⟩ | ⟨hdz, _⟩
  · rw [hd] at hd'; cases hd'; exact ht
  · rw [hd] at hdz; cases hdz

/-- On related pairs, `SqlEquiv`'s comparator is the typed one. -/
theorem cmpU_agree (hk : KeysRel cols fold db Γ items orderBy hlen keys)
    {x₁ x₂ : Row o × Row n} {y₁ y₂ : SqlEquiv.Row × SqlEquiv.Row}
    (h₁ : PairRel cols fold db Γ items keys x₁ y₁)
    (h₂ : PairRel cols fold db Γ items keys x₂ y₂) :
    cmpU db orderBy y₁ y₂ = decide (cmpKeyRows keys x₁.1 x₂.1 ≠ .gt) := by
  obtain ⟨hrow₁, hr₁, hp₁, hk₁⟩ := h₁
  obtain ⟨hrow₂, hr₂, hp₂, hk₂⟩ := h₂
  subst hlen
  unfold cmpU
  apply compareBy_agree
  intro i
  have he₁ := (Expr.evalRow_eq_ok_iff.mp hk₁) i
  have he₂ := (Expr.evalRow_eq_ok_iff.mp hk₂) i
  obtain ⟨v₁, hv₁, hrel₁⟩ := hk.val _ _ hrow₁ hr₁ i _ he₁
  obtain ⟨v₂, hv₂, hrel₂⟩ := hk.val _ _ hrow₂ hr₂ i _ he₂
  rw [hp₁, hp₂]
  try simp only [Fin.getElem_fin]
  rw [hv₁, hv₂]
  obtain ⟨τ, hτ, hτb⟩ := hk.ty i
  refine cmpDatum_agree (keys i) _ (hk.dir i) (hk.nulls i) hrel₁ hrel₂ ?_
  rintro x y ⟨hx, -⟩
  have := key_hasType Γ hr₁ hτ he₁
  rw [hx] at this
  exact hτb (by simpa [Datum.HasType] using this.symm)

theorem insertionSort_congr {α : Type _} {r s : α → α → Prop} [DecidableRel r] [DecidableRel s]
    (h : ∀ a b, r a b ↔ s a b) (l : List α) : l.insertionSort r = l.insertionSort s := by
  have : r = s := funext fun a => funext fun b => propext (h a b)
  subst this
  congr

/-- Both sorts are images of one sorted list of related pairs: the typed sort's keyed rows are its
    first components and `SqlEquiv`'s sorted `(projected, source)` pairs its second. -/
theorem sorted_rel (hk : KeysRel cols fold db Γ items orderBy hlen keys)
    {K : List (Row o × Row n)} {Y : List (SqlEquiv.Row × SqlEquiv.Row)}
    (hKY : List.Forall₂ (PairRel cols fold db Γ items keys) K Y) :
    ∃ W : List ((Row o × Row n) × (SqlEquiv.Row × SqlEquiv.Row)),
      sortKeyed keys K = W.map Prod.fst ∧ Y.mergeSort (cmpU db orderBy) = W.map Prod.snd ∧
        ∀ w ∈ W, PairRel cols fold db Γ items keys w.1 w.2 := by
  obtain ⟨hlenKY, hzip⟩ := List.forall₂_iff_zip.mp hKY
  let Z := K.zip Y
  have hZ1 : Z.map Prod.fst = K := List.map_fst_zip (by omega)
  have hZ2 : Z.map Prod.snd = Y := List.map_snd_zip (by omega)
  have hmem : ∀ z ∈ Z, PairRel cols fold db Γ items keys z.1 z.2 := fun z hz => hzip hz
  let le : Row o × Row n → Row o × Row n → Bool :=
    fun x y => decide (cmpKeyRows keys x.1 y.1 ≠ .gt)
  let W := Z.mergeSort fun a b => le a.1 b.1
  refine ⟨W, ?_, ?_, fun w hw => hmem w (List.mem_mergeSort.mp hw)⟩
  · -- the typed insertion sort is the merge sort, a total preorder on these key rows
    choose τ hτ using hk.ty
    have htyped : ∀ x ∈ K, ∀ i, (x.1 i).HasType (τ i) := by
      intro x hx i
      rw [← hZ1] at hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      obtain ⟨-, hr, -, hkr⟩ := hmem z hz
      exact key_hasType Γ hr (hτ i).1 ((Expr.evalRow_eq_ok_iff.mp hkr) i)
    obtain ⟨htot, htrans⟩ := keyed_total_trans keys τ K htyped
    rw [sortKeyed, insertionSort_congr (s := fun x y => le x y = true) (fun a b => by simp [le]),
      ← SortBridge.mergeSort_eq_insertionSort_of_mem le K htrans htot]
    conv_lhs => rw [← hZ1]
    exact (List.map_mergeSort (r := fun a b => le a.1 b.1) (s := le) (f := Prod.fst) (l := Z)
      (fun _ _ _ _ => rfl)).symm
  · rw [← hZ2]
    exact (List.map_mergeSort (fun a ha b hb =>
      (cmpU_agree cols fold db Γ items orderBy hlen keys hk (hmem a ha) (hmem b hb)).symm)).symm

theorem mapM_rel_of {α β γ ε : Type _} {f : α → Except ε β} {g : γ → α} {h : γ → SqlEquiv.Row}
    {P : β → SqlEquiv.Row → Prop} :
    ∀ {W : List γ}, (∀ w ∈ W, ∀ d, f (g w) = .ok d → P d (h w)) →
      ∀ {out}, (W.map g).mapM f = .ok out → List.Forall₂ P out (W.map h)
  | [], _, out, e => by
    simp only [List.map_nil, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at e
    subst e; exact .nil
  | w :: W, hW, out, e => by
    rw [List.map_cons, List.mapM_cons] at e
    rcases hd : f (g w) with _ | d
    · simp [hd, bind, Except.bind] at e
    rcases hR : (W.map g).mapM f with _ | out'
    · simp [hd, hR, bind, Except.bind] at e
    simp only [hd, hR, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at e
    subst e
    exact .cons (hW w List.mem_cons_self d hd)
      (mapM_rel_of (fun v hv => hW v (List.mem_cons_of_mem _ hv)) hR)

theorem project_pairs_rel {its : List (Expr n × Column)} (hits : ItemsRel cols fold items its)
    (hnb : ∀ i : Fin its.length, NoBoolOrder Γ (its[i]).1)
    {W : List ((Row o × Row n) × (SqlEquiv.Row × SqlEquiv.Row))}
    (hW : ∀ w ∈ W, PairRel cols fold db Γ items keys w.1 w.2) {out}
    (h : (W.map fun w => w.1.2).mapM (Expr.evalRow fun i : Fin its.length => (its[i]).1) = .ok out) :
    List.Forall₂ OutRel out (W.map fun w => w.2.1) :=
  mapM_rel_of (fun w hw d hd => by
    obtain ⟨hrow, hr, hp, -⟩ := hW w hw
    rw [hp]
    exact row_rel cols fold db hrow hr hits hnb hd) h

/-- `ORDER BY`, then the projection: the typed result relates, in order, to `SqlEquiv`'s sorted
    projected rows. -/
theorem ordered_out_rel (hk : KeysRel cols fold db Γ items orderBy hlen keys)
    {its : List (Expr n × Column)} (hits : ItemsRel cols fold items its)
    (hnb : ∀ i : Fin its.length, NoBoolOrder Γ (its[i]).1) {R : List (Row n)}
    {U : List SqlEquiv.Row} (hRU : List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U)
    {K} (hK : R.mapM (fun r => do return (← Expr.evalRow (fun i => (keys i).e) r, r)) = .ok K)
    {out} (hout : ((sortKeyed keys K).map Prod.snd).mapM
      (Expr.evalRow fun i : Fin its.length => (its[i]).1) = .ok out) :
    List.Forall₂ OutRel out
      ((((U.map (projRow db items)).zip U).mergeSort (cmpU db orderBy)).map Prod.fst) := by
  obtain ⟨W, hW1, hW2, hW⟩ := sorted_rel cols fold db Γ items orderBy hlen keys hk
    (keyed_rel cols fold db Γ items keys hRU hK)
  rw [hW1, List.map_map] at hout
  rw [hW2, List.map_map]
  exact project_pairs_rel cols fold db Γ items orderBy keys hits hnb hW hout

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge SqlBridge.Correct

/-- `LIMIT` / `OFFSET` as `finishSelect` adds them. -/
def limitWrap {S : DbSchema} {k : ℕ} (lim off : Option ℕ) (q : Query S k) : Query S k :=
  match lim, off with
  | none, none => q
  | some l, o => .limit (some l) (o.getD 0) q
  | none, some o => .limit none o q

/-- The query `finishSelect` builds without `DISTINCT`: the projection, sorted below it when there
    are keys, then `LIMIT` / `OFFSET`. -/
theorem finishSelect_nondistinct {S : DbSchema} (fold : String → String) (sc : Scoped S)
    (orderBy : List SqlEquiv.OrderByItem) (lim off : Option ℕ) {e : Elaborated S}
    (h : finishSelect fold sc false orderBy lim off = .ok e) :
    ∃ keyList, orderBy.mapM (elabOrderKey fold sc.scope sc.items) = .ok keyList ∧
      e = ⟨sc.items.length, limitWrap lim off
        (if keyList.length = 0 then .project (fun i => (sc.items[i]).1) sc.q
         else .project (fun i => (sc.items[i]).1)
           (.orderBy (fun i : Fin keyList.length => keyList[i]) sc.q)),
        fun i => (sc.items[i]).2⟩ := by
  unfold finishSelect at h
  rcases hk : orderBy.mapM (elabOrderKey fold sc.scope sc.items) with _ | keyList
  · simp [hk, bind, Except.bind] at h
  refine ⟨keyList, rfl, ?_⟩
  simp only [hk, bind, Except.bind] at h
  split at h
  · split at h
    · cases h
    · simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      cases lim <;> cases off <;> rfl
  · simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases lim <;> cases off <;> rfl

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge SqlBridge.Correct

theorem mapM_forall₂ {α β ε : Type _} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → List.Forall₂ (fun a b => f a = .ok b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    rcases ha : f a with _ | b
    · simp [ha, bind, Except.bind] at h
    rcases hl : l.mapM f with _ | l''
    · simp [ha, hl, bind, Except.bind] at h
    simp only [ha, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .cons ha (mapM_forall₂ hl)

theorem bind_pure_ok {α β ε : Type _} {x : Except ε α} {f : α → β} {b : β}
    (h : (x >>= fun a => pure (f a)) = .ok b) : ∃ a, x = .ok a ∧ b = f a := by
  cases x <;> simp_all [bind, Except.bind, pure, Except.pure]

/-- An elaborated `ORDER BY` key keeps the item's direction and `NULL` placement. -/
theorem orderKey_dir {m : ℕ} (fold : String → String) (sc : SqlEquiv.Expr → ElabM (Expr m))
    (its : List (Expr m × Column)) (e : SqlEquiv.Expr) (dir : SqlEquiv.OrderDir)
    (nulls : SqlEquiv.NullsOrder) {key : SortKey m}
    (h : elabOrderKey fold sc its ⟨e, dir, nulls⟩ = .ok key) :
    key.desc = (dir == .desc) ∧ key.nullsFirst = (nulls == .first) := by
  unfold elabOrderKey at h
  dsimp only at h
  repeat' split at h
  all_goals
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  all_goals
    first
      | (cases h; exact ⟨rfl, rfl⟩)
      | cases h
      | (split at h <;> first | (cases h; exact ⟨rfl, rfl⟩) | cases h)

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String)

/-- The elaborated `ORDER BY` keys of column references satisfy `KeysRel`. -/
theorem keysRel_of_elab (hfoldCI : ∀ x y, fold x = fold y ↔ x.toLower = y.toLower)
    (db : SqlEquiv.Database) {Γ : Fin n → SqlType}
    {items : List SqlEquiv.SelectItem} {its : List (Expr n × Column)}
    (hif : itemsFragment items = true) (hin : itemsNamed items = true)
    (hir : ItemsRel cols fold items its)
    (hnm : List.Forall₂ (fun it x => x.2.name = outName it) items its)
    (hnbIt : ∀ x ∈ its, NoBoolOrder Γ x.1)
    {orderBy : List SqlEquiv.OrderByItem} {keyList : List (SortKey n)}
    (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c)
    (hk : orderBy.mapM (elabOrderKey fold (elabExpr cols fold noHook) its) = .ok keyList)
    (hty : ∀ k ∈ keyList, ∃ τ, k.e.typeOf Γ = some τ ∧ τ ≠ .bool) :
    ∃ hlen : orderBy.length = keyList.length,
      KeysRel cols fold db Γ items orderBy hlen (fun i => keyList[i]) := by
  have hF := mapM_forall₂ hk
  have hlen := hF.length_eq
  have hget : ∀ i : Fin keyList.length,
      elabOrderKey fold (elabExpr cols fold noHook) its (orderBy[i.1]'(by rw [hlen]; exact i.2)) = .ok keyList[i] :=
    fun i => (List.forall₂_iff_get.mp hF).2 i.1 (by rw [hlen]; exact i.2) i.2
  have hitem : ∀ i : Fin keyList.length, ∃ cr dir nulls,
      orderBy[i.1]'(by rw [hlen]; exact i.2) = ⟨.col cr, dir, nulls⟩ := by
    intro i
    obtain ⟨c, hc⟩ := hcols _ (List.getElem_mem (by rw [hlen]; exact i.2))
    generalize orderBy[i.1]'(by rw [hlen]; exact i.2) = it at hc ⊢
    obtain ⟨e, dir, nulls⟩ := it
    simp only [SqlEquiv.OrderByItem.expr] at hc
    subst hc
    exact ⟨c, dir, nulls, rfl⟩
  refine ⟨hlen, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro r u hrow hr i d hd
    obtain ⟨cr, dir, nulls, hi⟩ := hitem i
    have hki := hget i
    rw [hi] at hki ⊢
    exact (orderKey_rel cols fold hfoldCI db hrow hr hif hin hir hnm hnbIt cr dir nulls hki hd).1
  · intro i
    obtain ⟨cr, dir, nulls, hi⟩ := hitem i
    have hki := hget i
    rw [hi] at hki ⊢
    exact (orderKey_dir fold _ its _ dir nulls hki).1
  · intro i
    obtain ⟨cr, dir, nulls, hi⟩ := hitem i
    have hki := hget i
    rw [hi] at hki ⊢
    exact (orderKey_dir fold _ its _ dir nulls hki).2
  · intro i
    exact hty _ (List.getElem_mem i.2)

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge SqlBridge.Correct

/-- The typed core's `OFFSET` / `LIMIT` on a list (`Query.eval_limit`, offset default 0). -/
def typedLimit {α : Type _} (lim off : Option ℕ) (l : List α) : List α :=
  match lim with
  | some c => (l.drop (off.getD 0)).take c
  | none => l.drop (off.getD 0)

/-- `SqlEquiv`'s `OFFSET` / `LIMIT` on a list (`applyOrderByLimitOffsetAligned`). -/
def untypedLimit {α : Type _} (lim off : Option ℕ) (l : List α) : List α :=
  let o := match off with
    | some m => l.drop m
    | none => l
  match lim with
  | some n => o.take n
  | none => o

theorem eval_limitWrap {S : DbSchema} {k : ℕ} (D : Database S) (lim off : Option ℕ)
    (q : Query S k) {rs : List (Row k)} (h : (limitWrap lim off q).eval D = .ok rs) :
    ∃ base, q.eval D = .ok base ∧ rs = typedLimit lim off base := by
  cases lim <;> cases off <;> simp only [limitWrap] at h
  all_goals first
    | exact ⟨rs, h, by simp [typedLimit]⟩
    | (simp only [Query.eval_limit, bind, Except.bind] at h
       split at h
       · cases h
       · rename_i base hb
         simp only [pure, Except.pure, Except.ok.injEq] at h
         exact ⟨base, hb, by rw [← h]; simp [typedLimit]⟩)

/-- `OFFSET` then `LIMIT` keep related lists related. -/
theorem limit_rel {α β : Type _} {P : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ P as bs) (lim off : Option ℕ) :
    List.Forall₂ P (typedLimit lim off as) (untypedLimit lim off bs) := by
  have hd : List.Forall₂ P (as.drop (off.getD 0))
      (match off with | some m => bs.drop m | none => bs) := by
    cases off with
    | some m => exact List.forall₂_drop m h
    | none => simpa using h
  cases lim with
  | some c => exact List.forall₂_take c hd
  | none => exact hd

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge SqlBridge.Correct

theorem bind_ok {α β ε : Type _} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem applyOrder_eq (compareEval : SqlEquiv.Database → SqlEquiv.Row → SqlEquiv.Row →
    List SqlEquiv.OrderByItem → Bool) (db : SqlEquiv.Database)
    (orderBy : List SqlEquiv.OrderByItem) (lim off : Option ℕ) (sources rows : SqlEquiv.Table) :
    SqlEquiv.applyOrderByLimitOffsetAligned compareEval db orderBy lim off true sources rows =
      untypedLimit lim off (if orderBy.isEmpty then rows else
        ((rows.zip sources).mergeSort fun p₁ p₂ =>
          compareEval db (p₁.1 ++ p₁.2) (p₂.1 ++ p₂.2) orderBy).map (·.1)) := by
  cases lim <;> cases off <;> rfl

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String) (db : SqlEquiv.Database)
  (Γ : Fin n → SqlType) (items : List SqlEquiv.SelectItem) (orderBy : List SqlEquiv.OrderByItem)

/-- Projection, `ORDER BY`, `OFFSET` and `LIMIT` over related input rows: the typed result relates,
    in order, to `SqlEquiv`'s. -/
theorem finish_rel {S : DbSchema} {D : Database S} {q₀ : Query S n} {R : List (Row n)}
    {U : List SqlEquiv.Row} (hR : q₀.eval D = .ok R)
    (hRU : List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U)
    {its : List (Expr n × Column)} (hits : ItemsRel cols fold items its)
    (hnb : ∀ i : Fin its.length, NoBoolOrder Γ (its[i]).1)
    {keyList : List (SortKey n)} (hlen : orderBy.length = keyList.length)
    (hk : keyList.length ≠ 0 → KeysRel cols fold db Γ items orderBy hlen (fun i => keyList[i]))
    (lim off : Option ℕ) {rs : List (Row its.length)}
    (hrs : (limitWrap lim off (if keyList.length = 0 then .project (fun i => (its[i]).1) q₀
      else .project (fun i => (its[i]).1)
        (.orderBy (fun i : Fin keyList.length => keyList[i]) q₀))).eval D = .ok rs) :
    List.Forall₂ OutRel rs
      (SqlEquiv.applyOrderByLimitOffsetAligned
        (SqlEquiv.compareByOrderItemsParam fun db' r e => SqlEquiv.evalExprWithDb db' r e)
        db orderBy lim off true U (U.map (projRow db items))) := by
  obtain ⟨base, hbase, rfl⟩ := eval_limitWrap D lim off _ hrs
  rw [applyOrder_eq]
  apply limit_rel
  by_cases hk0 : keyList.length = 0
  · have ho : orderBy = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ho
    simp only [hk0, ↓reduceIte, Query.eval_project, hR, bind, Except.bind] at hbase
    simp only [List.isEmpty_nil, ↓reduceIte]
    exact project_rel cols fold db hits hnb hRU hbase
  · have hne : orderBy.isEmpty = false := by
      cases orderBy with
      | nil => simp at hlen; omega
      | cons _ _ => rfl
    simp only [hk0, ↓reduceIte] at hbase
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [Query.eval_project] at hbase
    obtain ⟨sorted, hsorted, hout⟩ := bind_ok hbase
    rw [Query.eval_orderBy, hR] at hsorted
    obtain ⟨R', hR', hK'⟩ := bind_ok hsorted
    cases hR'
    obtain ⟨K, hK, hpure⟩ := bind_ok hK'
    cases hpure
    exact ordered_out_rel cols fold db Γ items orderBy hlen _ (hk hk0) hits hnb hRU hK hout

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge SqlBridge.Correct

/-- The statements of roadmap step 1: `SELECT e₁, …, eₖ FROM t [AS a] [WHERE p]
    [ORDER BY c₁, …] [LIMIT n] [OFFSET m]`. -/
def orderedStmt (items : List SqlEquiv.SelectItem) (name : String) (al : Option String)
    (wh : Option SqlEquiv.Expr) (orderBy : List SqlEquiv.OrderByItem) (lim off : Option ℕ) :
    SqlEquiv.Stmt :=
  .query (.simple (.mk false items (some (.table ⟨name, al⟩)) wh [] none orderBy lim off))

theorem aggsOfList_cols : ∀ es : List SqlEquiv.Expr, (∀ e ∈ es, ∃ c, e = .col c) → aggsOfList es = []
  | [], _ => rfl
  | e :: es, h => by
    obtain ⟨c, rfl⟩ := h e List.mem_cons_self
    simp [aggsOfList, aggsOf, aggsOfList_cols es (fun e he => h e (List.mem_cons_of_mem _ he))]

theorem aggsOfList_map_cols {α : Type _} (f : α → SqlEquiv.Expr) (l : List α)
    (h : ∀ o ∈ l, ∃ c, f o = .col c) : aggsOfList (l.map f) = [] :=
  aggsOfList_cols _ (fun e he => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp he
    exact h o ho)

theorem elab_ordered_shape (N : NamedSchema) {items : List SqlEquiv.SelectItem} {name : String}
    {al : Option String} {wh : Option SqlEquiv.Expr} {orderBy : List SqlEquiv.OrderByItem}
    {lim off : Option ℕ} (hit : itemsFragment items = true) (hw : ∀ w ∈ wh, isFragment w = true)
    (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c) {e : Elaborated N.S}
    (h : elabStmt N (orderedStmt items name al wh orderBy lim off) = .ok e) :
    e.q.typeOf.isSome ∧ ∃ T, (N.fold name, T) ∈ N.tables ∧
      ∃ q₀ : Query N.S (N.S.arity T),
        ((wh = none ∧ q₀ = .table T) ∨ ∃ w p, wh = some w ∧
          elabExpr (requalify (N.fold (al.getD name)) (N.S.columns T)) N.fold noHook w = .ok p ∧
          q₀ = .select p (.table T)) ∧
      ∃ its, elabItems N (requalify (N.fold (al.getD name)) (N.S.columns T)) items = .ok its ∧
      ∃ keyList, orderBy.mapM (elabOrderKey N.fold
          (elabExpr (requalify (N.fold (al.getD name)) (N.S.columns T)) N.fold noHook) its) =
          .ok keyList ∧
        e = ⟨its.length, limitWrap lim off
          (if keyList.length = 0 then .project (fun i => (its[i]).1) q₀
           else .project (fun i => (its[i]).1)
             (.orderBy (fun i : Fin keyList.length => keyList[i]) q₀)),
          fun i => (its[i]).2⟩ := by
  simp only [orderedStmt, elabStmt, elabQuery, bind, Except.bind] at h
  rcases hraw : elabQueryRaw N (.simple (.mk false items (some (.table ⟨name, al⟩)) wh [] none
    orderBy lim off)) with _ | e₀
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
  have hcols' : ∀ o ∈ orderBy, ∃ c, (match o with | .mk e _ _ => e) = SqlEquiv.Expr.col c :=
    fun o ho => (hcols o ho).elim fun c hc => ⟨c, by cases o; simpa [SqlEquiv.OrderByItem.expr] using hc⟩
  rcases hT : N.tables.find? (fun x => x.1 == N.fold name) with _ | ⟨nm, T⟩
  · simp [elabFrom, lookupTable, hT, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hraw
  have hmem : (N.fold name, T) ∈ N.tables := by
    have h1 := List.mem_of_find?_eq_some hT
    have h2 := List.find?_some hT
    simp only [beq_iff_eq] at h2; subst h2; exact h1
  refine ⟨T, hmem, ?_⟩
  simp only [elabFrom, lookupTable, hT, bind, Except.bind, pure, Except.pure] at hraw
  cases wh with
  | none =>
    simp only [] at hraw
    rw [aggsOfList_map_cols _ _ ?hm, aggsOfList_items ?hf items hit] at hraw
    case hm => exact hcols'
    case hf => intros; rfl
    simp only [List.isEmpty_nil, aggsOfOpt, List.append_nil, List.eraseDups_nil, Option.isNone_none,
      Bool.and_self, ↓reduceIte] at hraw
    rcases hits : elabItems N (requalify (N.fold (al.getD name)) (N.S.columns T)) items with _ | its
    · simp [hits] at hraw
    simp only [hits] at hraw
    obtain ⟨keyList, hk, he⟩ := finishSelect_nondistinct N.fold _ orderBy lim off hraw
    exact ⟨.table T, .inl ⟨rfl, rfl⟩, its, rfl, keyList, hk, he⟩
  | some w =>
    simp only [subsOf_frag w (hw w rfl), List.foldl_nil, List.isEmpty_nil, ↓reduceIte] at hraw
    rcases hp : elabExpr (requalify (N.fold (al.getD name)) (N.S.columns T)) N.fold noHook w with
      _ | p
    · simp [hp] at hraw
    simp only [hp] at hraw
    rw [aggsOfList_map_cols _ _ ?hm, aggsOfList_items ?hf items hit] at hraw
    case hm => exact hcols'
    case hf => intros; rfl
    simp only [List.isEmpty_nil, aggsOfOpt, List.append_nil, List.eraseDups_nil, Option.isNone_none,
      Bool.and_self, ↓reduceIte] at hraw
    rcases hits : elabItems N (requalify (N.fold (al.getD name)) (N.S.columns T)) items with _ | its
    · simp [hits] at hraw
    simp only [hits] at hraw
    obtain ⟨keyList, hk, he⟩ := finishSelect_nondistinct N.fold _ orderBy lim off hraw
    exact ⟨.select p (.table T), .inr ⟨w, p, rfl, hp, rfl⟩, its, rfl, keyList, hk, he⟩

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge SqlBridge.Correct

theorem typeOf_limitWrap {S : DbSchema} {k : ℕ} (lim off : Option ℕ) (q : Query S k) :
    (limitWrap lim off q).typeOf = q.typeOf := by
  cases lim <;> cases off <;> rfl

theorem divSafe_limitWrap {S : DbSchema} {k : ℕ} (lim off : Option ℕ) (q : Query S k) :
    (limitWrap lim off q).divSafe = q.divSafe := by
  cases lim <;> cases off <;> rfl

theorem qnb_limitWrap {S : DbSchema} {k : ℕ} (lim off : Option ℕ) (q : Query S k) :
    QNoBoolOrder (limitWrap lim off q) ↔ QNoBoolOrder q := by
  cases lim <;> cases off <;> simp [limitWrap, QNoBoolOrder]

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String)

/-- An elaborated `ORDER BY` key of a column reference cannot divide by zero. -/
theorem orderKey_divSafe {its : List (Expr n × Column)} (hits : ∀ x ∈ its, x.1.divSafe = true)
    (cr : SqlEquiv.ColumnRef) (dir : SqlEquiv.OrderDir) (nulls : SqlEquiv.NullsOrder)
    {key : SortKey n}
    (hk : elabOrderKey fold (elabExpr cols fold noHook) its ⟨.col cr, dir, nulls⟩ = .ok key) :
    key.e.divSafe = true := by
  obtain ⟨q, c⟩ := cr
  have hcol : ∀ {e' : Expr n}, elabExpr cols fold noHook (.col ⟨q, c⟩) = .ok e' →
      e'.divSafe = true :=
    fun he => Translates.divSafe cols fold (translates_of_elab cols fold (.col _) rfl he)
  cases q with
  | some t =>
    simp only [elabOrderKey, bind, Except.bind] at hk
    rcases he : elabExpr cols fold noHook (.col ⟨some t, c⟩) with _ | e'
    · simp [he] at hk
    simp only [he, pure, Except.pure, Except.ok.injEq] at hk
    subst hk; exact hcol he
  | none =>
    simp only [elabOrderKey, bind, Except.bind] at hk
    rcases hm : ((its.filter fun it => fold it.2.name == fold c).map (·.1)).eraseDups with
      _ | ⟨e', _ | ⟨e'', l⟩⟩
    · simp only [hm] at hk
      rcases he : elabExpr cols fold noHook (.col ⟨none, c⟩) with _ | e'
      · simp [he] at hk
      simp only [he, pure, Except.pure, Except.ok.injEq] at hk
      subst hk; exact hcol he
    · simp only [hm, pure, Except.pure, Except.ok.injEq] at hk
      subst hk
      have : e' ∈ ((its.filter fun it => fold it.2.name == fold c).map (·.1)).eraseDups := by
        rw [hm]; exact List.mem_cons_self
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp this)
      exact hits x (List.mem_of_mem_filter hx)
    · simp [hm, throw, throwThe, MonadExceptOf.throw] at hk

end SqlBridge.CorrectOrder

namespace SqlBridge.CorrectOrder
open SqlCore SqlBridge SqlBridge.Correct

/-- **Elaborator correctness with `ORDER BY` / `LIMIT` / `OFFSET`** (#352, roadmap step 1). For
    `SELECT e₁, …, eₖ FROM t [AS a] [WHERE p] [ORDER BY c₁, …] [LIMIT n] [OFFSET m]` with fragment
    expressions and column-reference sort keys: when the statement elaborates, the typed query
    evaluates, and its rows relate, in order, to `SqlEquiv`'s.

    Beyond `elabStmt_correct`'s hypotheses, with `ORDER BY`: unaliased SELECT items are columns
    and output names have no dot (`itemsNamed`, so both evaluators name output columns alike), the
    fold identifies names that differ only in case (as `String.toLower` does; with `id` an `ORDER BY`
    name could pick an output column on one side and an input column on the other), and no sort
    key is boolean (`QNoBoolOrder`). -/
theorem elabStmt_correct_ordered (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hwn : WellNamed N) {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms)
    (hrel : DbRel N db D) {items : List SqlEquiv.SelectItem} {name : String}
    {al : Option String} {wh : Option SqlEquiv.Expr} {orderBy : List SqlEquiv.OrderByItem}
    {lim off : Option ℕ} (hit : itemsFragment items = true) (hw : ∀ w ∈ wh, isFragment w = true)
    (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c)
    (hnamed : orderBy ≠ [] → itemsNamed items = true)
    (hfoldCI : orderBy ≠ [] → ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower)
    {e : Elaborated N.S} (h : elabStmt N (orderedStmt items name al wh orderBy lim off) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (orderedStmt items name al wh orderBy lim off)).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  obtain ⟨hty, T, hmem, q₀, hq₀, its, hits, keyList, hk, rfl⟩ := elab_ordered_shape N hit hw hcols h
  have hir := itemsRel_of_elab (requalify (N.fold (al.getD name)) (N.S.columns T)) N items hit hits
  have hlen : orderBy.length = keyList.length := (mapM_forall₂ hk).length_eq
  simp only at hty hnb ⊢
  rw [typeOf_limitWrap] at hty
  rw [qnb_limitWrap] at hnb
  -- the input query: its type, and its predicate (if any) is boolean
  have hq₀ty : ∀ Γ, q₀.typeOf = some Γ → Γ = N.S.ctx T := by
    intro Γ hΓ
    rcases hq₀ with ⟨-, rfl⟩ | ⟨w, p, -, -, rfl⟩
    · simpa using hΓ.symm
    · obtain ⟨h1, -⟩ := Query.typeOf_select_eq_some.mp hΓ
      simpa using h1.symm
  -- typing and the boolean side conditions, with and without keys
  have hfacts : q₀.typeOf = some (N.S.ctx T) ∧
      (∀ i : Fin its.length, NoBoolOrder (N.S.ctx T) (its[i]).1) ∧ QNoBoolOrder q₀ ∧
      (keyList.length ≠ 0 → ∀ k ∈ keyList, ∃ τ, k.e.typeOf (N.S.ctx T) = some τ ∧ τ ≠ .bool) := by
    by_cases hk0 : keyList.length = 0
    · simp only [hk0, ↓reduceIte] at hty hnb
      obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
      obtain ⟨Γ, hΓ, -⟩ := Query.typeOf_project_eq_some.mp hΔ
      have := hq₀ty Γ hΓ; subst this
      exact ⟨hΓ, fun i => hnb.1 _ hΓ i, hnb.2, fun h => absurd hk0 h⟩
    · simp only [hk0, ↓reduceIte] at hty hnb
      obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
      obtain ⟨Γ, hΓ, -⟩ := Query.typeOf_project_eq_some.mp hΔ
      obtain ⟨hq, Δk, hΔk⟩ := Query.typeOf_orderBy_eq_some hΓ
      have := hq₀ty Γ hq; subst this
      refine ⟨hq, fun i => hnb.1 _ hΓ i, hnb.2.2, fun _ k hk => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
      exact ⟨Δk ⟨i, hi⟩, hΔk ⟨i, hi⟩, fun hb => hnb.2.1 _ hq ⟨i, hi⟩ (by rw [hΔk ⟨i, hi⟩, hb])⟩
  obtain ⟨hq₀T, hnbIt, hnbq₀, hkty⟩ := hfacts
  -- division safety, so the typed query evaluates
  have hdivIt : ∀ x ∈ its, x.1.divSafe = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨_, _, _, htr⟩ := (List.forall₂_iff_get.mp hir).2 i (by have := hir.length_eq; omega) hi
    exact Translates.divSafe _ _ htr
  have hdivKeys : ∀ k ∈ keyList, k.e.divSafe = true := by
    intro k hkm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hkm
    have hf := (List.forall₂_iff_get.mp (mapM_forall₂ hk)).2 i (by omega) hi
    simp only [List.get_eq_getElem] at hf
    obtain ⟨c, hc⟩ := hcols _ (List.getElem_mem (by omega : i < orderBy.length))
    generalize orderBy[i]'(by omega) = it at hf hc
    obtain ⟨e, dir, nulls⟩ := it
    simp only [SqlEquiv.OrderByItem.expr] at hc
    subst hc
    exact orderKey_divSafe _ N.fold hdivIt c dir nulls hf
  have hdivq₀ : q₀.divSafe = true := by
    rcases hq₀ with ⟨-, rfl⟩ | ⟨w, p, hwp, hp, rfl⟩
    · rfl
    · simp only [Query.divSafe, Bool.and_true]
      exact Translates.divSafe _ _ (translates_of_elab _ _ w (hw w hwp) hp)
  have hsafe : (limitWrap lim off (if keyList.length = 0 then .project (fun i => (its[i]).1) q₀
      else .project (fun i => (its[i]).1)
        (.orderBy (fun i : Fin keyList.length => keyList[i]) q₀))).IsSafe := by
    refine ⟨by rw [typeOf_limitWrap]; exact hty, ?_⟩
    rw [divSafe_limitWrap]
    have hdi : decide (∀ i : Fin its.length, (its[i]).1.divSafe = true) = true :=
      decide_eq_true fun i => hdivIt _ (List.getElem_mem i.2)
    by_cases hk0 : keyList.length = 0
    · simp only [hk0, ↓reduceIte, Query.divSafe, hdi, hdivq₀, Bool.and_true]
    · have hdk : decide (∀ i : Fin keyList.length, (keyList[i]).e.divSafe = true) = true :=
        decide_eq_true fun i => hdivKeys _ (List.getElem_mem i.2)
      simp only [hk0, ↓reduceIte, Query.divSafe, hdi, hdk, hdivq₀, Bool.and_true]
  obtain ⟨rs, hrs⟩ := Query.IsSafe.exists_eval_eq_ok hsafe hD
  obtain ⟨R, hR⟩ := Query.IsSafe.exists_eval_eq_ok (q := q₀) ⟨by simp [hq₀T], hdivq₀⟩ hD
  refine ⟨rs, hrs, _, rfl, ?_⟩
  -- `SqlEquiv`'s side, in closed form
  simp only [SqlEquiv.evalQuery]
  rw [SqlEquiv.evalSelect_eq_evalSelectCore, evalSelectCore_project_ordered _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ (selectHasAggregate_frag items hit) (selectHasWindowFn_frag items hit)]
  -- the keys
  have hkr : keyList.length ≠ 0 → KeysRel (requalify (N.fold (al.getD name)) (N.S.columns T))
      N.fold db (N.S.ctx T) items orderBy hlen (fun i => keyList[i]) := fun hk0 => by
    have hne : orderBy ≠ [] := by intro h0; subst h0; simp at hlen; omega
    obtain ⟨_, hkr⟩ := keysRel_of_elab _ N.fold (hfoldCI hne) db hit (hnamed hne) hir
      (itemsNames_of_elab N _ items hit (hnamed hne) hits)
      (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        exact hnbIt ⟨i, hi⟩) hcols hk (hkty hk0)
    exact hkr
  -- the input rows
  have hrows := fragment_rows N hfold hwn hD hrel hmem al
  rcases hq₀ with ⟨rfl, rfl⟩ | ⟨w, p, rfl, hp, rfl⟩
  · simp only [Query.eval_table, Except.ok.injEq] at hR
    subst hR
    exact finish_rel _ N.fold db (N.S.ctx T) items orderBy (Query.eval_table _ _) hrows hir hnbIt
      hlen hkr lim off hrs
  · have hR' := hR
    simp only [Query.eval_select, Query.eval_table, bind, Except.bind] at hR'
    have htp := translates_of_elab _ _ w (hw w rfl) hp
    have hfr := filter_rel _ _ db htp (hnbq₀.1 _ rfl) hrows hR'
    exact finish_rel _ N.fold db (N.S.ctx T) items orderBy hR hfr hir hnbIt hlen hkr lim off hrs

end SqlBridge.CorrectOrder
