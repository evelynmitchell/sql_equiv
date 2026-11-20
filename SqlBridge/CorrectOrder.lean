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
