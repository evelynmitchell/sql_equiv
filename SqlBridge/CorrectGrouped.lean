/-
  Elaborator correctness for grouped queries (#352, roadmap steps 3b-4 to 3b-6): one statement for
  `SELECT … FROM f [WHERE p] GROUP BY c₁, … [HAVING h] [ORDER BY a₁, …] [LIMIT n] [OFFSET m]`,
  items aggregates of step 3a, key columns, or bare columns (registry T9), read on the group's
  first row or, next to one `MIN`/`MAX`, on the row where its argument is extreme; sort keys
  aggregates or `GROUP BY` columns that no other item's name captures (`OrderKeyOk`). `AVG` items
  (step 3c) relate up to `SqlEquiv`'s rounding (`ItemRel`, `CorrectAvg.AvgRel`).

  * `evalSelectCore_grouped_full`: `SqlEquiv`'s grouped path in closed form, `HAVING` and the
    per-group sort keys included.
  * `elab_grouped_shape`: the elaborator's query. A bare column becomes the aggregate
    `AggCall.first` when no `MIN`/`MAX` is written, so both evaluators read the group's first row,
    and `AggCall.atExtreme` next to exactly one (not DISTINCT, in a mode that picks the row), which
    `SqlBridge.CorrectExtreme.atExtreme_rel` relates to `SqlEquiv`'s `bareSampleRow` (`BareOk`).
    Item columns resolve in the `FROM` scope (the elaborator checks it).
-/
import SqlBridge.CorrectGroupOrder
import SqlBridge.CorrectExtreme
import SqlBridge.CorrectAvg

namespace SqlBridge.CorrectGrouped
open SqlEquiv SqlBridge.CorrectGroup

/-- `SqlEquiv`'s grouped path in closed form: an optional `HAVING`, any `ORDER BY` (rewritten onto
    the per-group key rows), `LIMIT`/`OFFSET`. Under an outer row (a subquery body, #409) the source
    rows carry it at the end; the statement itself is `outerRow = []`. A group whose `HAVING` is not `TRUE` on its sample
    row gives neither a row nor a key row. -/
theorem evalSelectCore_grouped_full (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool) (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause) (wh : Option Expr) (groupBy : List Expr)
    (having : Option Expr) (orderBy : List OrderByItem) (lim off : Option Nat)
    (hg : groupBy ≠ []) (hNoWin : hasWindowFn items = false) :
    ∃ (F F' : List (List (Option Value) × Table) → Row → List (List (Option Value) × Table))
      (Φ Ψ : List (Option Value) × Table → Option Row),
      (∀ gs u, (gs.map Prod.fst).Nodup →
        F gs u = insU (groupBy.map fun e => (exprEval db u e).map Value.setKey) u gs) ∧
      (∀ gs u, (gs.map Prod.fst).Nodup →
        F' gs u = insU (groupBy.map fun e => (exprEval db u e).map Value.setKey) u gs) ∧
      (∀ key rows s, bareSampleRow (exprEval db) (selectMinMaxCalls items having) rows = some s →
        Φ (key, rows) = if (having.all fun c => exprWithAggEval db rows s c == some (Value.bool true))
          then some (items.flatMap (selectItemWithAggEval db rows s)) else none) ∧
      (∀ key rows s, bareSampleRow (exprEval db) (selectMinMaxCalls items having) rows = some s →
        Ψ (key, rows) = if (having.all fun c => exprWithAggEval db rows s c == some (Value.bool true))
          then some (groupOrderKeyRow db exprWithAggEval orderBy rows s
            (items.flatMap (selectItemWithAggEval db rows s))) else none) ∧
      evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
        (SelectStmt.mk false items (some from_) wh groupBy having orderBy lim off) =
      applyOrderByLimitOffsetAligned compareEval db (groupOrderByItems orderBy) lim off true
        (((match wh with
          | some c => ((fromEval db from_).map fun row => row ++ outerRow).filter
              fun row => exprEval db row c == some (Value.bool true)
          | none => (fromEval db from_).map fun row => row ++ outerRow).foldl F' []).filterMap Ψ)
        (((match wh with
          | some c => ((fromEval db from_).map fun row => row ++ outerRow).filter
              fun row => exprEval db row c == some (Value.bool true)
          | none => (fromEval db from_).map fun row => row ++ outerRow).foldl F []).filterMap Φ) := by
  have hne : groupBy.isEmpty = false := by cases groupBy <;> simp_all
  refine ⟨?F, ?F', ?Φ, ?Ψ, ?h1, ?h1', ?h2, ?h2', ?h3⟩
  case h3 =>
    rw [evalSelectCore_eq_afterFilter]
    cases wh <;> simp [evalSelectAfterFilter, evalSelectProjectDistinct, evalSelectGroupOrderKeys,
      hne, hNoWin] <;> rfl
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
    cases having <;> simp [h]
  case h2' =>
    intro key rows s h
    cases having <;> simp [h]

end SqlBridge.CorrectGrouped

namespace SqlBridge.CorrectGrouped
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGroup SqlBridge.CorrectGroupOrder

/-- An aggregate item: of step 3a, or `AVG` (step 3c, as an item only: its value is related up to
    rounding, `CorrectAvg.AvgRel`). -/
def itemAggFragment (e : SqlEquiv.Expr) : Bool := aggFragment e || CorrectAvg.avgFragment e

/-- Items of steps 3b-4 and 3c: aggregates of step 3a, `AVG`, and columns (keys or bare). -/
def groupedItems : List SqlEquiv.SelectItem → Bool
  | [] => true
  | .exprItem e _ :: rest =>
    (itemAggFragment e || match e with | .col _ => true | _ => false) && groupedItems rest
  | _ :: _ => false

/-- Grouped items (aggregates, `AVG`, columns) have no window function (#429). -/
theorem selectHasWindowFn_groupedItems : ∀ {items : List SqlEquiv.SelectItem},
    groupedItems items = true → SqlEquiv.selectHasWindowFn items = false
  | [], _ => rfl
  | .exprItem e _ :: rest, h => by
    simp only [groupedItems, Bool.and_eq_true] at h
    have he : SqlEquiv.exprHasWindowFn e = false := by
      cases e <;> simp_all [itemAggFragment, aggFragment, CorrectAvg.avgFragment,
        SqlEquiv.exprHasWindowFn]
    have := selectHasWindowFn_groupedItems h.2
    simp only [SqlEquiv.selectHasWindowFn, List.any_cons, he, Bool.false_or] at this ⊢
    exact this
  | .star _ :: _, h => by simp [groupedItems] at h

/-- An item's output value against `SqlEquiv`'s: an `AVG` item up to rounding
    (`CorrectAvg.AvgRel`, registry rows 7 and T10), every other column exactly. -/
def ItemRel (it : SqlEquiv.SelectItem) (d : Datum) (v : SqlEquiv.Value) : Prop :=
  if CorrectAvg.avgFragment (itemExpr it) then CorrectAvg.AvgRel d v else DatumRel d v

/-- A typed output row against `SqlEquiv`'s, column by column (`ItemRel`). -/
def OutRelI {k : ℕ} (items : List SqlEquiv.SelectItem) (r : Row k) (o : SqlEquiv.Row) : Prop :=
  items.length = k ∧ List.Forall₂ (fun (x : SqlEquiv.SelectItem × Datum) v => ItemRel x.1 x.2 v)
    (items.zip (List.ofFn r)) (o.map (·.2))

/-- Without `AVG` items the relation is exact. -/
theorem outRel_of_outRelI {k : ℕ} {items : List SqlEquiv.SelectItem}
    (hna : ∀ it ∈ items, CorrectAvg.avgFragment (itemExpr it) = false) {r : Row k}
    {o : SqlEquiv.Row} (h : OutRelI items r o) : OutRel r o := by
  obtain ⟨hlen, h⟩ := h
  have hl := h.length_eq
  simp only [List.length_zip, List.length_ofFn, List.length_map, hlen, min_self] at hl
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
  simp only [List.length_ofFn] at h1
  have h3 := (List.forall₂_iff_get.mp h).2 i (by simp [hlen]; omega) (by simpa using h2)
  simp only [List.get_eq_getElem, List.getElem_zip, List.getElem_ofFn, ItemRel] at h3 ⊢
  rw [if_neg (by simp [hna _ (List.getElem_mem (by omega : i < items.length))])] at h3
  exact h3

theorem avgFragment_false_of_agg {e : SqlEquiv.Expr} (h : aggFragment e = true) :
    CorrectAvg.avgFragment e = false := by
  cases e <;> simp_all [aggFragment, CorrectAvg.avgFragment]
  rename_i fn _ _
  cases fn <;> simp_all

/-- The statements of step 3b-4. -/
def groupedStmt (items : List SqlEquiv.SelectItem) (f : SqlEquiv.FromClause)
    (wh : Option SqlEquiv.Expr) (groupBy : List SqlEquiv.Expr) (having : Option SqlEquiv.Expr)
    (orderBy : List SqlEquiv.OrderByItem) (lim off : Option ℕ) : SqlEquiv.Stmt :=
  .query (.simple (.mk false items (some f) wh groupBy having orderBy lim off))

/-- An item's output name in the elaborator (`?column?` for an unaliased expression). -/
def itemColName : SqlEquiv.SelectItem → String
  | .exprItem e al => al.getD (match e with | .col c => c.column | _ => "?column?")
  | .star _ => ""

/-- An `ORDER BY` key of the grouped fragment: an aggregate of step 3a, or a `GROUP BY` column
    (step 3b-6) that no other item's output name captures: every item named like it, in either
    evaluator, is that column. Both evaluators then read the group's key. -/
def OrderKeyOk (items : List SqlEquiv.SelectItem) (groupBy : List SqlEquiv.Expr)
    (o : SqlEquiv.Expr) : Prop :=
  aggFragment o = true ∨ ∃ c, o = .col c ∧ SqlEquiv.Expr.col c ∈ groupBy ∧
    ∀ it ∈ items, ((outName it).toLower = c.column.toLower ∨
      (itemColName it).toLower = c.column.toLower) → itemExpr it = .col c

/-- The `MIN`/`MAX` aggregates. -/
def isMinMax : SqlEquiv.Expr → Bool
  | .agg (.min _) _ _ | .agg (.max _) _ _ => true
  | _ => false

/-- Where bare columns read (registry T9): every item column is a key; or the dialect takes bare
    columns and no `MIN`/`MAX` is written anywhere (the group's first row); or it takes them and
    one `MIN`/`MAX`, not `DISTINCT`, is written, as `SqlEquiv` and the elaborator both count it (the
    row where its argument is extreme). (Every item column resolves in the `FROM` scope: the
    elaborator checks it, #384.) -/
def BareOk (N : NamedSchema) (items : List SqlEquiv.SelectItem)
    (groupBy : List SqlEquiv.Expr) (having : Option SqlEquiv.Expr)
    (orderBy : List SqlEquiv.OrderByItem) : Prop :=
  (∀ c ∈ colRefs items, SqlEquiv.Expr.col c ∈ groupBy) ∨
  (N.config.bareColumns = .sqlite ∧ (∀ it ∈ items, SqlEquiv.minMaxCalls (itemExpr it) = []) ∧
    (∀ h ∈ having, SqlEquiv.minMaxCalls h = []) ∧ ∀ o ∈ orderBy, SqlEquiv.minMaxCalls o.expr = []) ∨
  (N.config.bareColumns = .sqlite ∧ ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode)
    (arg : SqlEquiv.Expr), mode.bareRow = true ∧
    SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
    (((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
      (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups.filter isMinMax) =
      [.agg (if wantMax then .max mode else .min mode) (some arg) false])

section
variable {f : SqlEquiv.SelectItem → Option SqlEquiv.Expr} (hf : ∀ e al, f (.exprItem e al) = some e)
include hf

theorem aggsOfList_groupedItems : ∀ items, groupedItems items = true →
    aggsOfList (items.filterMap f) = (items.map itemExpr).filter itemAggFragment
  | [], _ => by simp [aggsOfList]
  | .exprItem e al :: rest, h => by
    simp only [groupedItems, Bool.and_eq_true, Bool.or_eq_true] at h
    have hae : aggsOf e = if itemAggFragment e then [e] else [] := by
      rcases h.1 with h1 | h1
      · rw [if_pos h1]
        simp only [itemAggFragment, Bool.or_eq_true] at h1
        rcases h1 with h1 | h1
        · exact aggsOf_aggFragment e h1
        · cases e <;> simp_all [CorrectAvg.avgFragment, aggsOf]
      · cases e <;> simp_all [itemAggFragment, aggFragment, CorrectAvg.avgFragment, aggsOf]
    simp only [List.filterMap_cons, hf, aggsOfList, hae,
      aggsOfList_groupedItems rest h.2, List.map_cons, itemExpr, List.filter_cons]
    split <;> simp
  | .star _ :: _, h => by simp [groupedItems] at h

theorem colsOutsideAggsList_groupedItems : ∀ items, groupedItems items = true →
    colsOutsideAggsList (items.filterMap f) = colRefs items
  | [], _ => by simp [colsOutsideAggsList, colRefs]
  | .exprItem e al :: rest, h => by
    simp only [groupedItems, Bool.and_eq_true, Bool.or_eq_true] at h
    have ih := colsOutsideAggsList_groupedItems rest h.2
    rcases h.1 with h1 | h1
    · cases e <;> simp_all [colsOutsideAggsList, colsOutsideAggs, colRefs, itemAggFragment,
        aggFragment, CorrectAvg.avgFragment]
    · cases e <;> simp_all [colsOutsideAggsList, colsOutsideAggs, colRefs]
  | .star _ :: _, h => by simp [groupedItems] at h

end

theorem mapM_eq_map {α β ε : Type _} {f : α → Except ε β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = .ok (g x)) → l.mapM f = .ok (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self, mapM_eq_map (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

/-- No `MIN`/`MAX` call in an expression: none among its aggregates. -/
theorem minMaxCalls_of_aggsOf_having {groupBy : List SqlEquiv.Expr} : ∀ (h : SqlEquiv.Expr),
    havingFragment groupBy h = true → SqlEquiv.minMaxCalls h = [] →
      ∀ x ∈ aggsOf h, SqlEquiv.minMaxCalls x = []
  | .lit _, _, _, x, hx | .col _, _, _, x, hx => by simp [aggsOf] at hx
  | .binOp op p q, hf, hm, x, hx => by
    simp only [havingFragment, Bool.or_eq_true, Bool.and_eq_true] at hf
    simp only [SqlEquiv.minMaxCalls, List.append_eq_nil_iff] at hm
    rcases hf with hca | hf
    · obtain ⟨z, c, rfl, -, hxa⟩ := cmpAvgForm_spec hca
      have hp : aggsOf p = [p] := by
        cases p <;> simp [avgColFragment] at hxa
        simp [aggsOf]
      simp only [aggsOf, hp, List.append_nil, List.mem_singleton] at hx
      subst hx
      exact hm.1
    simp only [aggsOf, List.mem_append] at hx
    rcases hx with hx | hx
    · exact minMaxCalls_of_aggsOf_having p hf.1.2 hm.1 x hx
    · exact minMaxCalls_of_aggsOf_having q hf.2 hm.2 x hx
  | .unaryOp op p, hf, hm, x, hx => by
    cases op <;> simp only [havingFragment] at hf
    · exact minMaxCalls_of_aggsOf_having p hf (by simpa [SqlEquiv.minMaxCalls] using hm) x
        (by simpa [aggsOf] using hx)
    all_goals simp [aggFragment] at hf
  | .countStar, _, hm, x, hx => by simp [aggsOf] at hx; subst hx; exact hm
  | .agg fn a d, _, hm, x, hx => by simp [aggsOf] at hx; subst hx; exact hm
  | .between p lo hi, hf, hm, x, hx => by
    simp only [havingFragment, Bool.and_eq_true] at hf
    simp only [SqlEquiv.minMaxCalls, List.append_eq_nil_iff] at hm
    simp only [aggsOf, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact minMaxCalls_of_aggsOf_having p hf.1.1 hm.1.1 x hx
    · exact minMaxCalls_of_aggsOf_having lo hf.1.2 hm.1.2 x hx
    · exact minMaxCalls_of_aggsOf_having hi hf.2 hm.2 x hx
  | .func _ _, hf, _, _, _ | .case _ _, hf, _, _, _ | .inList _ _ _, hf, _, _, _
  | .inSubquery _ _ _, hf, _, _, _ | .exists _ _, hf, _, _, _
  | .subquery _, hf, _, _, _ | .windowFn _ _ _, hf, _, _, _ => by
    simp [havingFragment, aggFragment] at hf

/-- No `MIN`/`MAX` call: the elaborator's filter for `MIN`/`MAX` aggregates is empty. -/
theorem filter_nil_of_noMinMax {l : List SqlEquiv.Expr} (hl : ∀ x ∈ l, SqlEquiv.minMaxCalls x = [])
    {p : SqlEquiv.Expr → Bool} (hp : ∀ x, SqlEquiv.minMaxCalls x = [] → p x = false) :
    l.filter p = [] :=
  List.filter_eq_nil_iff.mpr fun x hx => by simp [hp x (hl x hx)]

theorem groupedItems_mem : ∀ {items : List SqlEquiv.SelectItem},
    groupedItems items = true → ∀ it ∈ items, ∃ e al, it = .exprItem e al ∧
      (itemAggFragment e = true ∨ ∃ c, e = .col c)
  | [], _, _, h => by simp at h
  | .exprItem e al :: rest, h, it, hit => by
    simp only [groupedItems, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases List.mem_cons.mp hit with rfl | hit
    · refine ⟨e, al, rfl, ?_⟩
      rcases h.1 with h1 | h1
      · exact .inl h1
      · cases e <;> simp_all
    · exact groupedItems_mem h.2 it hit
  | .star _ :: _, h, _, _ => by simp [groupedItems] at h

/-- `ColumnRef`'s derived `BEq` compares fields. -/
instance : LawfulBEq SqlEquiv.ColumnRef where
  eq_of_beq {a b} h := by
    obtain ⟨t, c⟩ := a; obtain ⟨t', c'⟩ := b
    change (t == t' && c == c') = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]
  rfl {a} := by
    obtain ⟨t, c⟩ := a
    change (t == t && c == c) = true
    simp

theorem colRefs_of_mem {items : List SqlEquiv.SelectItem} {it : SqlEquiv.SelectItem} (hit : it ∈ items)
    {c : SqlEquiv.ColumnRef} {al : Option String} (h : it = .exprItem (.col c) al) : c ∈ colRefs items := by
  induction items with
  | nil => simp at hit
  | cons x rest ih =>
    rcases List.mem_cons.mp hit with rfl | hit
    · subst h; simp [colRefs]
    · have := ih hit
      cases x with
      | exprItem e al' => cases e <;> simp [colRefs, this]
      | star t => simpa [colRefs] using this

theorem exists_item_of_colRefs {c : SqlEquiv.ColumnRef} :
    ∀ {items : List SqlEquiv.SelectItem}, c ∈ colRefs items →
      ∃ it ∈ items, itemExpr it = .col c
  | [], h => by simp [colRefs] at h
  | .exprItem e al :: rest, h => by
    cases e
    case col c' =>
      simp only [colRefs, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨it, hit, he⟩ := exists_item_of_colRefs h
        exact ⟨it, List.mem_cons_of_mem _ hit, he⟩
    all_goals
      obtain ⟨it, hit, he⟩ := exists_item_of_colRefs (by simpa [colRefs] using h)
      exact ⟨it, List.mem_cons_of_mem _ hit, he⟩
  | .star _ :: rest, h => by
    obtain ⟨it, hit, he⟩ := exists_item_of_colRefs (by simpa [colRefs] using h)
    exact ⟨it, List.mem_cons_of_mem _ hit, he⟩

/-- `findIdx?` in `X ++ Y`: an element of `X` is found where it is in `X`. -/
theorem findIdx_append_left {α : Type _} {X Y : List α} {p : α → Bool} {j : ℕ}
    (h : X.findIdx? p = some j) : (X ++ Y).findIdx? p = some j := by
  rw [List.findIdx?_append, h]; rfl

theorem findIdx_append_right {α : Type _} {X Y : List α} {p : α → Bool} {j : ℕ}
    (hX : X.findIdx? p = none) (h : Y.findIdx? p = some j) :
    (X ++ Y).findIdx? p = some (j + X.length) := by
  rw [List.findIdx?_append, hX, h]; rfl

/-- With no `MIN`/`MAX` call, the sample row is the group's first row. -/
theorem bareSampleRow_nil_calls (argEval : SqlEquiv.Row → SqlEquiv.Expr → Option SqlEquiv.Value)
    (rows : SqlEquiv.Table) : SqlEquiv.bareSampleRow argEval [] rows = rows.head? := rfl

theorem selectMinMaxCalls_nil {items : List SqlEquiv.SelectItem} {having : Option SqlEquiv.Expr}
    (hi : ∀ it ∈ items, ∃ e al, it = .exprItem e al ∧ SqlEquiv.minMaxCalls e = [])
    (hh : ∀ h ∈ having, SqlEquiv.minMaxCalls h = []) :
    SqlEquiv.selectMinMaxCalls items having = [] := by
  have h2 : SqlEquiv.minMaxCalls.minMaxCallsOpt having = [] := by
    cases having with
    | none => rfl
    | some h => exact hh h rfl
  unfold SqlEquiv.selectMinMaxCalls
  rw [List.flatMap_eq_nil_iff.mpr ?h1, h2]
  · rfl
  case h1 =>
    intro it hit
    obtain ⟨e, al, rfl, he⟩ := hi it hit
    exact he

/-- `AggCall.first` reads its expression on the group's first row. -/
theorem first_eval {m : ℕ} {e : Expr m} {r₀ : Row m} {rs : List (Row m)} {d : Datum}
    (h : (AggCall.first e).eval (r₀ :: rs) = .ok d) : e.eval r₀ = .ok d := by
  simp only [AggCall.eval, List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
  rcases h0 : e.eval r₀ with _ | d₀
  · simp [h0] at h
  rcases h1 : rs.mapM e.eval with _ | ds
  · simp [h0, h1] at h
  simp only [h0, h1, Except.ok.injEq, List.head?_cons, Option.getD_some] at h
  rw [h]

/-- A relation through `mapM`: each output relates to the image of its partner. -/
theorem forall₂_mapM_rel {α β γ δ ε : Type _} {P : α → β → Prop} {f : α → Except ε γ}
    {Q : γ → δ → Prop} {g : β → δ} (hq : ∀ a b, P a b → ∀ c, f a = .ok c → Q c (g b)) :
    ∀ {as : List α} {bs : List β} {cs : List γ}, List.Forall₂ P as bs → as.mapM f = .ok cs →
      List.Forall₂ Q cs (bs.map g)
  | _, _, cs, .nil, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | a :: as, b :: bs, cs, .cons hab hs, h => by
    rw [List.mapM_cons] at h
    rcases hd : f a with _ | c
    · simp [hd, bind, Except.bind] at h
    rcases hr : as.mapM f with _ | cs'
    · simp [hd, hr, bind, Except.bind] at h
    simp only [hd, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .cons (hq a b hab c hd) (forall₂_mapM_rel hq hs hr)

theorem aggsOfList_orderKeys {f : SqlEquiv.OrderByItem → SqlEquiv.Expr} (hf : ∀ o, f o = o.expr) :
    ∀ orderBy : List SqlEquiv.OrderByItem,
      (∀ o ∈ orderBy, aggFragment o.expr = true ∨ ∃ c, o.expr = .col c) →
      aggsOfList (orderBy.map f) = (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment
  | [], _ => rfl
  | o :: os, h => by
    have ih := aggsOfList_orderKeys hf os (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rcases h o List.mem_cons_self with ho | ⟨c, hc⟩
    · simp only [List.map_cons, aggsOfList, hf, aggsOf_aggFragment _ ho, ih, List.filter_cons, ho,
        ↓reduceIte, List.singleton_append]
    · simp only [List.map_cons, aggsOfList, hf, hc, ih, List.filter_cons]
      simp [aggsOf, aggFragment]

theorem colsOutsideAggsList_orderKeys {f : SqlEquiv.OrderByItem → SqlEquiv.Expr}
    (hf : ∀ o, f o = o.expr) : ∀ orderBy : List SqlEquiv.OrderByItem,
      (∀ o ∈ orderBy, aggFragment o.expr = true ∨ ∃ c, o.expr = .col c) →
      ∀ c ∈ colsOutsideAggsList (orderBy.map f), ∃ o ∈ orderBy, o.expr = .col c
  | [], _, c, hc => by simp [colsOutsideAggsList] at hc
  | o :: os, h, c, hc => by
    simp only [List.map_cons, colsOutsideAggsList, hf, List.mem_append] at hc
    rcases hc with hc | hc
    · rcases h o List.mem_cons_self with ho | ⟨c', hc'⟩
      · rw [colsOutsideAggs_aggFragment _ ho] at hc; cases hc
      · rw [hc'] at hc; simp only [colsOutsideAggs, List.mem_singleton] at hc; subst hc
        exact ⟨o, List.mem_cons_self, hc'⟩
    · obtain ⟨o', ho', h'⟩ := colsOutsideAggsList_orderKeys hf os
        (fun x hx => h x (List.mem_cons_of_mem _ hx)) c hc
      exact ⟨o', List.mem_cons_of_mem _ ho', h'⟩

/-- A list whose elements are all `v` deduplicates to `[]` or `[v]`. -/
theorem eraseDups_of_all_eq {α : Type _} [BEq α] [LawfulBEq α] {l : List α} {v : α}
    (h : ∀ y ∈ l, y = v) : l.eraseDups = [] ∨ l.eraseDups = [v] := by
  cases l with
  | nil => left; rfl
  | cons y ys =>
    right
    have hy := h y List.mem_cons_self
    subst hy
    rw [List.eraseDups_cons]
    have : ys.filter (fun b => !b == y) = [] :=
      List.filter_eq_nil_iff.mpr (fun b hb => by simp [h b (List.mem_cons_of_mem _ hb)])
    rw [this]; rfl

theorem filter_isMinMax {p : SqlEquiv.Expr → Bool} (hp : ∀ x, p x = isMinMax x)
    (l : List SqlEquiv.Expr) : l.filter p = l.filter isMinMax :=
  List.filter_congr fun x _ => hp x

set_option maxHeartbeats 12000000 in
theorem elab_grouped_shape (N : NamedSchema)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) {items : List SqlEquiv.SelectItem}
    {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} {groupBy : List SqlEquiv.Expr}
    {having : Option SqlEquiv.Expr} {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hgi : groupedItems items = true)
    (hgb : groupBy ≠ [] ∨ ∃ it ∈ items, itemAggFragment (itemExpr it) = true)
    (hob : ∀ o ∈ orderBy, OrderKeyOk items groupBy o.expr)
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hhv : ∀ h ∈ having, havingFragment groupBy h = true)
    (hbf : BareOk N items groupBy having orderBy) {e : Elaborated N.S}
    (h : elabStmt N (groupedStmt items fr wh groupBy having orderBy lim off) = .ok e) :
    e.q.typeOf.isSome ∧ ∃ n, ∃ qf : Query N.S n, ∃ cf,
      elabFrom N (fun sq => elabSubQuery N 15 sq) fr = .ok ⟨n, qf, cf⟩ ∧
      ∃ q₀ : Query N.S n, elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf wh = .ok q₀ ∧
      ∃ (keyList : List (Expr n)) (a : ℕ) (aggs : Fin a → AggCall n)
        (its : List (Expr (keyList.length + a) × Column)) (sk : List (SortKey (keyList.length + a)))
        (mk : Expr n → AggCall n),
        groupBy.mapM (elabExpr cf N.fold noHook) = .ok keyList ∧
        -- with a bare column: `first` and no `MIN`/`MAX` call, or `atExtreme` at the one call
        ((∃ it ∈ items, ∃ c e', itemExpr it = .col c ∧ elabExpr cf N.fold noHook (.col c) = .ok e' ∧
            e' ∉ keyList) →
          ((∀ e, mk e = .first e) ∧ SqlEquiv.selectMinMaxCalls items having = []) ∨
          ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
            mode.bareRow = true ∧
            SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
            isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
            ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e) ∧
        (∀ j, (∃ x, itemAggFragment x = true ∧ elabAgg cf N.fold x = .ok (aggs j)) ∨
          ∃ c e', c ∈ colRefs items ∧ elabExpr cf N.fold noHook (.col c) = .ok e' ∧ e' ∉ keyList ∧
            aggs j = mk e') ∧
        List.Forall₂ (fun it x =>
          (∃ j : Fin a, elabAgg cf N.fold (itemExpr it) = .ok (aggs j) ∧
            x.1 = .col (Fin.natAdd _ j)) ∨
          (∃ c, ∃ i : Fin keyList.length, itemExpr it = .col c ∧
            elabExpr cf N.fold noHook (.col c) = .ok keyList[i] ∧ x.1 = .col (Fin.castAdd a i)) ∨
          (∃ c, ∃ j : Fin a, ∃ e', itemExpr it = .col c ∧ elabExpr cf N.fold noHook (.col c) = .ok e' ∧
            e' ∉ keyList ∧ aggs j = mk e' ∧ x.1 = .col (Fin.natAdd _ j)))
          items its ∧
        List.Forall₂ (fun o k =>
          ((∃ j : Fin a, elabAgg cf N.fold o.expr = .ok (aggs j) ∧ k.e = .col (Fin.natAdd _ j)) ∨
            ∃ c, ∃ i : Fin keyList.length, o.expr = .col c ∧
              elabExpr cf N.fold noHook (.col c) = .ok keyList[i] ∧ k.e = .col (Fin.castAdd a i)) ∧
          k.desc = (o.dir == .desc) ∧ k.nullsFirst = (o.nulls == .first)) orderBy sk ∧
        ∃ qh : Query N.S (keyList.length + a),
          ((having = none ∧ qh = .aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀) ∨
            ∃ hv p out, having = some hv ∧
              TranslatesH cf out N.fold (fun i : Fin keyList.length => keyList[i]) aggs hv p ∧
              qh = .select p (.aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀)) ∧
        e = ⟨its.length, limitWrap lim off
          (if sk.length = 0 then .project (fun i => (its[i]).1) qh
           else .project (fun i => (its[i]).1) (.orderBy (fun i : Fin sk.length => sk[i]) qh)),
          fun i => (its[i]).2⟩ := by
  simp only [groupedStmt, elabStmt, elabQuery, bind, Except.bind] at h
  rcases hraw : elabQueryRaw N (.simple (.mk false items (some fr) wh groupBy having orderBy lim off))
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
  obtain ⟨q₀, hq₀, hraw'⟩ := bind_ok hraw
  clear hraw
  rename' hraw' => hraw
  -- not the elaborator's branch without aggregates: a key, or an aggregate item
  have hcond : (groupBy.isEmpty && ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
      (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups.isEmpty && having.isNone) = false := by
    rcases hgb with hgb | ⟨it, hit, hag⟩
    · cases groupBy with
      | nil => exact absurd rfl hgb
      | cons _ _ => rfl
    · have hmem : itemExpr it ∈ ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
          (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups :=
        List.mem_eraseDups.mpr (by simp only [List.mem_append, List.mem_filter, List.mem_map]
                                   exact .inl (.inl ⟨⟨it, hit, rfl⟩, hag⟩))
      have : ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
          (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups.isEmpty = false := by
        cases hl : ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
          (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups with
        | nil => rw [hl] at hmem; simp at hmem
        | cons _ _ => rfl
      rw [this, Bool.and_false, Bool.false_and]
  simp only [pure, Except.pure, bind, Except.bind] at hraw
  refine ⟨n, qf, cf, hf, q₀, hq₀, ?_⟩
  all_goals
    have hob' : ∀ o ∈ orderBy, aggFragment o.expr = true ∨ ∃ c, o.expr = .col c := fun o ho =>
      (hob o ho).imp id fun ⟨c, hc, _⟩ => ⟨c, hc⟩
    -- the `ORDER BY` columns are keys
    have hoK : ∀ c ∈ colsOutsideAggsList (orderBy.map fun | .mk e _ _ => e),
        SqlEquiv.Expr.col c ∈ groupBy := fun c hc => by
      obtain ⟨o, ho, hoc⟩ := colsOutsideAggsList_orderKeys (fun o => by cases o; rfl) orderBy hob' c hc
      rcases hob o ho with h | ⟨c', hc', hg, -⟩
      · rw [hoc] at h; simp [aggFragment] at h
      · rw [hoc] at hc'; cases hc'; exact hg
    rw [aggsOfList_groupedItems ?hf items hgi, colsOutsideAggsList_groupedItems ?hf2 items hgi,
      aggsOfList_orderKeys ?hf3 orderBy hob'] at hraw
    case hf => intros; rfl
    case hf2 => intros; rfl
    case hf3 => intro o; cases o; rfl
    simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hraw
    split at hraw
    · cases hraw
    rename_i keyList hk
    split at hraw
    · cases hraw
    rename_i colsE hcolsE
    split at hraw
    · cases hraw
    rename_i aggList hv
    generalize hB : List.filterMap _
      (if (N.config.bareColumns == SqlEquiv.BareColumns.sqlite) = true then _ else []) = B at hraw
    have hK := mapM_forall₂ hk
    have hV := mapM_forall₂ hv
    have hkey : ∀ c, SqlEquiv.Expr.col c ∈ groupBy → ∃ e', elabExpr cf N.fold noHook (.col c) = .ok e' ∧
        e' ∈ keyList := fun c hc => by
      obtain ⟨e', he', h⟩ := forall₂_mem_left hK hc
      exact ⟨e', h, he'⟩
    -- every item column resolves in the `FROM` scope: the elaborator checks it (#384)
    have hres' : ∀ c ∈ colRefs items, ∃ e', elabExpr cf N.fold noHook (.col c) = .ok e' := by
      intro c hc
      obtain ⟨e', -, he'⟩ := forall₂_mem_left (mapM_forall₂ hcolsE) (List.mem_append_left _ hc)
      exact ⟨e', he'⟩
    -- the bare columns: item columns that are no key
    have hBmem : ∀ p ∈ B, elabExpr cf N.fold noHook (.col p.1) = .ok p.2 ∧ p.2 ∉ keyList ∧
        p.1 ∈ colRefs items := by
      intro p hp
      rw [← hB, List.mem_filterMap] at hp
      obtain ⟨c, hcm, hc⟩ := hp
      split at hc
      · rename_i e' he'
        split at hc
        · cases hc
        · cases hc; rename_i hn
          refine ⟨he', by simpa using hn, ?_⟩
          -- a `HAVING` column is a key, so a bare column is an item column
          split at hcm
          · rcases List.mem_append.mp (mem_of_mem_eraseDups' _ le_rfl hcm) with hcm | hcm
            · rcases List.mem_append.mp hcm with hcm | hcm
              · exact hcm
              · exfalso
                cases having with
                | none => simp [colsOutsideAggsOpt] at hcm
                | some hv' =>
                  obtain ⟨e'', he'', hmem⟩ := hkey c (having_cols hv' (hhv hv' rfl) c hcm)
                  rw [he'] at he''; cases he''; simp at hn; exact hn hmem
            · -- an `ORDER BY` column is a key
              exfalso
              obtain ⟨e'', he'', hmem⟩ := hkey c (hoK c hcm)
              rw [he'] at he''; cases he''; simp at hn; exact hn hmem
          · simp at hcm
      · cases hc
    -- no bare column; or no MIN/MAX (the first row); or one MIN/MAX (the extreme row)
    have hBX : B = [] ∨ ((∀ x ∈ ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
        (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups, SqlEquiv.minMaxCalls x = []) ∧
        SqlEquiv.selectMinMaxCalls items having = []) ∨
        ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr), mode.bareRow = true ∧
          SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
          (((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
        (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups).filter isMinMax =
            [.agg (if wantMax then .max mode else .min mode) (some arg) false] := by
      rcases hbf with hall | ⟨-, hmi, hmh, hmo⟩ | ⟨-, w, m, a', hm, hcalls, hext⟩
      · left
        rw [← hB, List.filterMap_eq_nil_iff]
        intro c hc
        have hcg : SqlEquiv.Expr.col c ∈ groupBy := by
          split at hc
          · rcases List.mem_append.mp (mem_of_mem_eraseDups' _ le_rfl hc) with hc | hc
            · rcases List.mem_append.mp hc with hc | hc
              · exact hall c hc
              · cases having with
                | none => simp [colsOutsideAggsOpt] at hc
                | some hv' => exact having_cols hv' (hhv hv' rfl) c hc
            · exact hoK c hc
          · simp at hc
        obtain ⟨e', he', hmem⟩ := hkey c hcg
        simp [he', hmem]
      · have hc0 : SqlEquiv.selectMinMaxCalls items having = [] := by
          refine selectMinMaxCalls_nil (fun it hit => ?_) hmh
          obtain ⟨e, al, rfl, -⟩ := groupedItems_mem hgi it hit
          exact ⟨e, al, rfl, hmi _ hit⟩
        refine .inr (.inl ⟨fun x hx => ?_, hc0⟩)
        rcases List.mem_append.mp (List.mem_eraseDups.mp hx) with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨hx, -⟩ := List.mem_filter.mp hx
            obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hx
            exact hmi it hit
          · cases having with
            | none => simp [aggsOfOpt] at hx
            | some hv' => exact minMaxCalls_of_aggsOf_having hv' (hhv hv' rfl) (hmh hv' rfl) x hx
        · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hx).1
          exact hmo o ho
      · exact .inr (.inr ⟨w, m, a', hm, hcalls, hext⟩)
    split at hraw
    case' isTrue hBne =>
      rcases hBX.resolve_left (by intro h0; simp [h0] at hBne) with ⟨hX, hcalls⟩ |
        ⟨wantMax, mode, arg, hm, hcalls, hext⟩
      case' inl =>
        rw [filter_nil_of_noMinMax hX ?hp] at hraw
        case hp =>
          intro x hx
          cases x
          case agg fn _ _ => cases fn <;> first | rfl | simp [SqlEquiv.minMaxCalls] at hx
          all_goals rfl
        simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, List.length_nil,
          show ¬ ((0 : ℕ) > 1) by omega] at hraw
        rw [mapM_eq_map (l := B) (g := fun x => AggCall.first x.2) (fun _ _ => rfl)] at hraw
        obtain ⟨mk, hmk⟩ : ∃ mk : Expr n → AggCall n, (AggCall.first : Expr n → AggCall n) = mk := ⟨_, rfl⟩
        rw [hmk] at hraw
        have hmkS : ((∀ e, mk e = .first e) ∧ (B = [] ∨ SqlEquiv.selectMinMaxCalls items having = [])) ∨
            ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
              mode.bareRow = true ∧
              SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
              isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
              ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e :=
          .inl ⟨fun e => by rw [← hmk], .inr hcalls⟩
      case' inr =>
        -- the one `MIN`/`MAX`: its argument is a fragment, and elaborates
        have hmemx : SqlEquiv.Expr.agg (if wantMax then .max mode else .min mode) (some arg) false ∈
            ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
        (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups := by
          have : SqlEquiv.Expr.agg (if wantMax then .max mode else .min mode) (some arg) false ∈
              (((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
        (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups).filter isMinMax := by rw [hext]; simp
          exact (List.mem_filter.mp this).1
        have hfrag : isFragment arg = true := by
          have hx : itemAggFragment
              (.agg (if wantMax then .max mode else .min mode) (some arg) false) := by
            rcases List.mem_append.mp (List.mem_eraseDups.mp hmemx) with hx | hx
            · rcases List.mem_append.mp hx with hx | hx
              · exact (List.mem_filter.mp hx).2
              · cases having with
                | none => simp [aggsOfOpt] at hx
                | some hv' =>
                  simp [itemAggFragment, having_aggs hv' (hhv hv' rfl) _ hx]
            · simp [itemAggFragment, (List.mem_filter.mp hx).2]
          cases wantMax <;> simpa [itemAggFragment, aggFragment, CorrectAvg.avgFragment] using hx
        rw [filter_isMinMax (fun x => by
          cases x
          case agg fn _ _ => cases fn <;> rfl
          all_goals rfl) _, hext] at hraw
        rcases hk' : elabExpr cf N.fold noHook arg with err | k'
        · exfalso
          obtain ⟨p₀, B', rfl⟩ : ∃ p₀ B', B = p₀ :: B' := by
            cases B with
            | nil => simp at hBne
            | cons p₀ B' => exact ⟨p₀, B', rfl⟩
          cases wantMax <;> simp [hk', List.mapM_cons, bind, Except.bind] at hraw
        cases wantMax
        case' false =>
          simp only [Bool.false_eq_true, ↓reduceIte, List.any_cons, List.any_nil, Bool.or_false,
            List.length_singleton, gt_iff_lt, lt_self_iff_false, hk'] at hraw
          rw [mapM_eq_map (l := B) (g := fun x => AggCall.atExtreme .lt k' x.2) (fun _ _ => rfl)] at hraw
          obtain ⟨mk, hmk⟩ : ∃ mk : Expr n → AggCall n, AggCall.atExtreme Ordering.lt k' = mk := ⟨_, rfl⟩
          rw [hmk] at hraw
          have hmkS : ((∀ e, mk e = .first e) ∧
              (B = [] ∨ SqlEquiv.selectMinMaxCalls items having = [])) ∨
              ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
                mode.bareRow = true ∧
                SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
                isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
                ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e :=
            .inr ⟨false, mode, arg, k', hm, hcalls, hfrag, hk', fun e => by rw [← hmk]; rfl⟩
        case' true =>
          simp only [↓reduceIte, eq_self_iff_true, Bool.false_eq_true, List.any_cons, List.any_nil,
            Bool.or_false,
            List.length_singleton, gt_iff_lt, lt_self_iff_false, hk'] at hraw
          rw [mapM_eq_map (l := B) (g := fun x => AggCall.atExtreme .gt k' x.2) (fun _ _ => rfl)] at hraw
          obtain ⟨mk, hmk⟩ : ∃ mk : Expr n → AggCall n, AggCall.atExtreme Ordering.gt k' = mk := ⟨_, rfl⟩
          rw [hmk] at hraw
          have hmkS : ((∀ e, mk e = .first e) ∧
              (B = [] ∨ SqlEquiv.selectMinMaxCalls items having = [])) ∨
              ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
                mode.bareRow = true ∧
                SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
                isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
                ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e :=
            .inr ⟨true, mode, arg, k', hm, hcalls, hfrag, hk', fun e => by rw [← hmk]; rfl⟩
    case' isFalse hBe =>
      have hB0 : B = [] := by simpa using hBe
      rw [mapM_eq_map (l := B) (g := fun x => AggCall.first x.2) (by simp [hB0])] at hraw
      obtain ⟨mk, hmk⟩ : ∃ mk : Expr n → AggCall n, (AggCall.first : Expr n → AggCall n) = mk := ⟨_, rfl⟩
      rw [hmk] at hraw
      have hmkS : ((∀ e, mk e = .first e) ∧ (B = [] ∨ SqlEquiv.selectMinMaxCalls items having = [])) ∨
          ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
            mode.bareRow = true ∧
            SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
            isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
            ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e :=
        .inl ⟨fun e => by rw [← hmk], .inl hB0⟩
    all_goals
      simp only at hraw
      split at hraw
      · cases hraw
      rename_i out hout
      -- the aggregates' list `X`: aggregates of the items, of `HAVING` and of `ORDER BY`
      have hXf' : ∀ x ∈ ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
          (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups,
          itemAggFragment x = true := by
        intro x hx
        rcases List.mem_append.mp (List.mem_eraseDups.mp hx) with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact (List.mem_filter.mp hx).2
          · cases having with
            | none => simp [aggsOfOpt] at hx
            | some hv' => simp [itemAggFragment, having_aggs hv' (hhv hv' rfl) x hx]
        · simp [itemAggFragment, (List.mem_filter.mp hx).2]
      have hXi : ∀ it ∈ items, itemAggFragment (itemExpr it) = true →
          itemExpr it ∈ ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
            (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups := fun it hit hfr =>
        List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_left _
          (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_, hit, rfl⟩, hfr⟩)))
      have hXh : ∀ hv ∈ having, ∀ x ∈ aggsOf hv,
          x ∈ ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
            (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups := by
        intro hv hhv' x hx
        cases hhv'
        exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_right _ hx))
      have hXo : ∀ o ∈ orderBy, aggFragment o.expr = true → o.expr ∈ ((items.map itemExpr).filter
          itemAggFragment ++ aggsOfOpt having ++
            (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups := fun o ho hfr =>
        List.mem_eraseDups.mpr (List.mem_append_right _
          (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨o, ho, rfl⟩, hfr⟩))
      generalize ((items.map itemExpr).filter itemAggFragment ++ aggsOfOpt having ++
        (orderBy.map SqlEquiv.OrderByItem.expr).filter aggFragment).eraseDups = X at hXf' hXi hXh hXo hV hraw hout
      clear hv hBX
      have hlenX : X.length = aggList.length := hV.length_eq
      -- the hook's list: `X`, then the bare columns
      have hXf : ∀ x ∈ X ++ B.map (fun x => SqlEquiv.Expr.col x.1),
          aggFragment x = true ∨ CorrectAvg.avgFragment x = true ∨
            ∃ c, x = .col c ∧ SqlEquiv.Expr.col c ∉ groupBy := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have h := hXf' x hx
          simp only [itemAggFragment, Bool.or_eq_true] at h
          rcases h with h | h
          · exact .inl h
          · exact .inr (.inl h)
        · obtain ⟨⟨c, e'⟩, hcB, rfl⟩ := List.mem_map.mp hx
          refine .inr (.inr ⟨c, rfl, fun hcg => ?_⟩)
          obtain ⟨e'', he'', hmem⟩ := hkey c hcg
          obtain ⟨he', hn, -⟩ := hBmem _ hcB
          rw [he''] at he'; cases he'; exact hn hmem
      have hfindX : ∀ x ∈ X, ∃ j, (X ++ B.map (fun x => SqlEquiv.Expr.col x.1)).findIdx? (· == x) =
          some j ∧ ∃ hj : j < X.length, X[j] = x := by
        intro x hx
        obtain ⟨j, hj⟩ : ∃ j, X.findIdx? (· == x) = some j :=
          Option.isSome_iff_exists.mp (by
            rw [List.findIdx?_isSome, List.any_eq_true]; exact ⟨x, hx, by simp⟩)
        obtain ⟨hjl, hje, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
        exact ⟨j, findIdx_append_left hj, hjl, by simpa using hje⟩
      have hagg : ∀ j (hj : j < X.length), ∃ hja : j < (aggList ++ B.map (fun x => mk x.2)).length,
          elabAgg cf N.fold X[j] = .ok ((aggList ++ B.map (fun x => mk x.2))[j]) := by
        intro j hj
        have hjv : j < aggList.length := hlenX ▸ hj
        refine ⟨by simp; omega, ?_⟩
        rw [List.getElem_append_left hjv]
        have := (List.forall₂_iff_get.mp hV).2 j hj hjv
        simpa using this
      have hkc : ∀ i : Fin keyList.length, ∃ idx, keyList[i] = .col idx := by
        intro i
        have h1 := (List.forall₂_iff_get.mp hK).2 i.1 (by have := hK.length_eq; omega) i.2
        simp only [List.get_eq_getElem] at h1
        obtain ⟨c, hc⟩ := hgc _ (List.getElem_mem (by have := hK.length_eq; omega : i.1 < groupBy.length))
        rw [hc] at h1
        exact elab_col_is_col cf N.fold c h1
      -- a non-key item column is a bare column
      have hbareB : ∀ c e', c ∈ colRefs items → elabExpr cf N.fold noHook (.col c) = .ok e' →
          e' ∉ keyList → (c, e') ∈ B := by
        intro c e' hc he' hkm
        rw [← hB, List.mem_filterMap]
        refine ⟨c, ?_, by simp [he', hkm]⟩
        rcases hbf with hall | ⟨hsq, -⟩ | ⟨hsq, -⟩
        · obtain ⟨e'', he'', hm⟩ := hkey c (hall c hc)
          rw [he'] at he''; cases he''; exact absurd hm hkm
        all_goals
          simp only [hsq]
          exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_left _ hc))
      rcases having with _ | hv
      case' some =>
        simp only at hraw
        split at hraw
        · cases hraw
        rename_i p hp
        have hp' : elabExpr out N.fold (aggHook (a := (aggList ++ B.map (fun x => mk x.2)).length)
            cf N.fold (fun i : Fin keyList.length => keyList[i])
            (X ++ B.map (fun x => SqlEquiv.Expr.col x.1))) hv = .ok p := by
          split at hp
          · simp only [Except.ok.injEq] at hp; subst hp; assumption
          · split at hp <;> simp [throw, throwThe, MonadExceptOf.throw] at hp
          · simp [throw, throwThe, MonadExceptOf.throw] at hp
      all_goals
        try simp only at hraw
        split at hraw
        · cases hraw
        rename_i its hits
        obtain ⟨keys', hk', rfl⟩ := finishSelect_nondistinct N.fold _ orderBy lim off hraw
        refine ⟨keyList, _, fun j => (aggList ++ B.map (fun x => mk x.2))[j], its, keys', mk, hk,
          ?gMk, ?gAggs, ?gItems, ?gKeys, ?gQh⟩
        case gMk =>
          rintro ⟨it, hit, c, e', hc, he', hkn⟩
          have hcr : c ∈ colRefs items := by
            obtain ⟨x, al, hx, -⟩ := groupedItems_mem hgi _ hit
            rw [hx] at hc; simp only [itemExpr] at hc; subst hc
            exact colRefs_of_mem hit hx
          rcases hmkS with ⟨hf, hB0 | hcalls⟩ | hat
          · have := hbareB c e' hcr he' hkn; rw [hB0] at this; simp at this
          · exact .inl ⟨hf, hcalls⟩
          · exact .inr hat
        case gAggs =>
          intro ⟨j, hj⟩
          by_cases hjv : j < aggList.length
          · left
            obtain ⟨_, hel⟩ := hagg j (hlenX ▸ hjv)
            exact ⟨_, hXf' _ (List.getElem_mem _), hel⟩
          · right
            have hjB : j - aggList.length < B.length := by simp at hj; omega
            refine ⟨B[j - aggList.length].1, B[j - aggList.length].2,
              (hBmem _ (List.getElem_mem hjB)).2.2, (hBmem _ (List.getElem_mem hjB)).1,
              (hBmem _ (List.getElem_mem hjB)).2.1, ?_⟩
            show (aggList ++ B.map (fun x => mk x.2))[j] = _
            rw [List.getElem_append_right (by omega)]
            simp
        case gKeys =>
          refine forall₂_imp_mem (mapM_forall₂ hk') fun o ho k hok => ?_
          obtain ⟨oe, dir, nulls⟩ := o
          rcases hob _ ho with hfr | ⟨c, hce, hcg, hcap⟩
          · -- an aggregate: its column among the aggregates
            replace hfr : aggFragment oe = true := hfr
            obtain ⟨j, hj, hjl, hje⟩ := hfindX oe (hXo _ ho hfr)
            obtain ⟨hja, hel⟩ := hagg j hjl
            unfold elabOrderKey at hok
            cases oe
            all_goals try simp [aggFragment] at hfr
            all_goals
              simp only [bind, Except.bind] at hok
              rw [elab_of_hook _ _ _ (hook_agg _ _ _ _ hj hja)] at hok
              simp only [pure, Except.pure, Except.ok.injEq] at hok
              subst hok
              exact ⟨.inl ⟨⟨j, hja⟩, hje ▸ hel, rfl⟩, rfl, rfl⟩
          · -- a `GROUP BY` column: the key's column, whether or not an output name matches
            change oe = .col c at hce
            subst hce
            obtain ⟨e', he', hkm⟩ := hkey c hcg
            have hnX : ∀ y ∈ X, y ≠ .col c := fun y hy h => by
              have := hXf' y hy; rw [h] at this; simp [itemAggFragment, aggFragment, CorrectAvg.avgFragment] at this
            have hnone : (X ++ B.map (fun x => SqlEquiv.Expr.col x.1)).findIdx?
                (· == SqlEquiv.Expr.col c) = none := by
              rw [List.findIdx?_eq_none_iff]
              intro y hy
              rcases List.mem_append.mp hy with hy | hy
              · simpa using hnX y hy
              · obtain ⟨⟨c', e''⟩, hcB, rfl⟩ := List.mem_map.mp hy
                rw [beq_eq_false_iff_ne, ne_eq, SqlEquiv.Expr.col.injEq]
                rintro rfl
                obtain ⟨he'', hn, -⟩ := hBmem _ hcB
                rw [he'] at he''; cases he''; exact hn hkm
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hkm
            obtain ⟨i₀, hi₀⟩ : ∃ i₀, (List.finRange keyList.length).find?
                (fun k : Fin keyList.length => keyList[k] == keyList[i]'hi) = some i₀ :=
              Option.isSome_iff_exists.mp
                ((List.find?_isSome (p := fun k : Fin keyList.length => keyList[k] == keyList[i]'hi)).mpr
                  ⟨⟨i, hi⟩, List.mem_finRange _, beq_self_eq_true (keyList[i]'hi)⟩)
            have hk₀ : keyList[i₀] = keyList[i]'hi := by
              simpa using List.find?_some hi₀
            have hE := elab_key keyList out cf N.fold _ hnone he' hi₀
            -- every output column named like the key is the key's column
            have hF : ∀ x ∈ its, N.fold x.2.name = N.fold c.column →
                x.1 = .col (Fin.castAdd _ i₀) := by
              intro x hx hfn
              obtain ⟨it, hit, hix⟩ := forall₂_mem_right (mapM_forall₂ hits) hx
              obtain ⟨e, al, rfl, -⟩ := groupedItems_mem hgi _ hit
              dsimp only at hix
              have hnm : x.2.name = itemColName (.exprItem e al) := by
                split at hix
                · cases hix
                · split at hix
                  · cases hix; rfl
                  · simp [throw, throwThe, MonadExceptOf.throw] at hix
              have hec : e = .col c := by
                have := hcap _ hit (.inr (by rw [← hnm]; exact (hfoldCI _ _).mp hfn))
                simpa [itemExpr] using this
              subst hec
              rw [hE] at hix
              simp only at hix
              split at hix
              · simp only [Except.ok.injEq] at hix; subst hix; rfl
              · simp [throw, throwThe, MonadExceptOf.throw] at hix
            unfold elabOrderKey at hok
            obtain ⟨q, cn⟩ := c
            cases q with
            | some t =>
              simp only [bind, Except.bind] at hok
              rw [hE] at hok
              simp only [pure, Except.pure, Except.ok.injEq] at hok
              subst hok
              exact ⟨.inr ⟨_, i₀, rfl, by rw [he', hk₀], rfl⟩, rfl, rfl⟩
            | none =>
              have hall : ∀ y ∈ (its.filter fun it => N.fold it.2.name == N.fold cn).map (·.1),
                  y = .col (Fin.castAdd _ i₀) := by
                intro y hy
                obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
                obtain ⟨hx, hfn⟩ := List.mem_filter.mp hx
                exact hF x hx (by simpa using hfn)
              rcases eraseDups_of_all_eq hall with h0 | h1
              · simp only [bind, Except.bind, h0] at hok
                rw [hE] at hok
                simp only [pure, Except.pure, Except.ok.injEq] at hok
                subst hok
                exact ⟨.inr ⟨_, i₀, rfl, by rw [he', hk₀], rfl⟩, rfl, rfl⟩
              · simp only [bind, Except.bind, h1, pure, Except.pure, Except.ok.injEq] at hok
                subst hok
                exact ⟨.inr ⟨_, i₀, rfl, by rw [he', hk₀], rfl⟩, rfl, rfl⟩
        case gItems =>
          refine forall₂_imp_mem (mapM_forall₂ hits) fun it hit x hx => ?_
          obtain ⟨e, al, rfl, hcase⟩ := groupedItems_mem hgi _ hit
          dsimp only at hx
          rcases hcase with hfr | ⟨c, rfl⟩
          · -- an aggregate: its column among the aggregates
            obtain ⟨j, hj, hjl, hje⟩ := hfindX e (hXi _ hit hfr)
            obtain ⟨hja, hel⟩ := hagg j hjl
            rw [elab_of_hook _ _ _ (hook_agg _ _ _ _ hj hja)] at hx
            simp only at hx
            split at hx
            · simp only [Except.ok.injEq] at hx
              subst hx
              exact .inl ⟨⟨j, hja⟩, hje ▸ hel, rfl⟩
            · simp [throw, throwThe, MonadExceptOf.throw] at hx
          · have hc : c ∈ colRefs items := colRefs_of_mem hit rfl
            obtain ⟨e', he'⟩ := hres' c hc
            have hnX : ∀ y ∈ X, y ≠ .col c := fun y hy h => by
              have := hXf' y hy; rw [h] at this; simp [itemAggFragment, aggFragment, CorrectAvg.avgFragment] at this
            by_cases hkm : e' ∈ keyList
            · -- a key column: its column among the keys
              have hnone : (X ++ B.map (fun x => SqlEquiv.Expr.col x.1)).findIdx?
                  (· == SqlEquiv.Expr.col c) = none := by
                rw [List.findIdx?_eq_none_iff]
                intro y hy
                rcases List.mem_append.mp hy with hy | hy
                · simpa using hnX y hy
                · obtain ⟨⟨c', e''⟩, hcB, rfl⟩ := List.mem_map.mp hy
                  rw [beq_eq_false_iff_ne, ne_eq, SqlEquiv.Expr.col.injEq]
                  rintro rfl
                  obtain ⟨he'', hn, -⟩ := hBmem _ hcB
                  rw [he'] at he''; cases he''; exact hn hkm
              obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hkm
              obtain ⟨i₀, hi₀⟩ : ∃ i₀, (List.finRange keyList.length).find?
                  (fun k : Fin keyList.length => keyList[k] == keyList[i]'hi) = some i₀ :=
                Option.isSome_iff_exists.mp
                  ((List.find?_isSome (p := fun k : Fin keyList.length => keyList[k] == keyList[i]'hi)).mpr
                    ⟨⟨i, hi⟩, List.mem_finRange _, beq_self_eq_true (keyList[i]'hi)⟩)
              have hk₀ : keyList[i₀] = keyList[i]'hi := by
                simpa using List.find?_some hi₀
              rw [elab_key keyList out cf N.fold _ hnone he' hi₀] at hx
              simp only at hx
              split at hx
              · simp only [Except.ok.injEq] at hx
                subst hx
                exact .inr (.inl ⟨c, i₀, rfl, by rw [he', hk₀], rfl⟩)
              · simp [throw, throwThe, MonadExceptOf.throw] at hx
            · -- a bare column: its `first` aggregate
              have hcB : (c, e') ∈ B := hbareB c e' hc he' hkm
              obtain ⟨k, hk⟩ : ∃ k, (B.map (fun x => SqlEquiv.Expr.col x.1)).findIdx?
                  (· == SqlEquiv.Expr.col c) = some k :=
                Option.isSome_iff_exists.mp (by
                  rw [List.findIdx?_isSome, List.any_eq_true]
                  exact ⟨_, List.mem_map.mpr ⟨_, hcB, rfl⟩, by simp⟩)
              obtain ⟨hkl, hke, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
              have hkB : k < B.length := by simpa using hkl
              have hkc : B[k].1 = c := by simpa using hke
              have hnoneX : X.findIdx? (· == SqlEquiv.Expr.col c) = none := by
                rw [List.findIdx?_eq_none_iff]; intro y hy; simpa using hnX y hy
              have hja : k + X.length < (aggList ++ B.map (fun x => mk x.2)).length := by
                simp; omega
              rw [elab_of_hook _ _ _ (hook_agg _ _ _ _ (findIdx_append_right hnoneX hk) hja)] at hx
              simp only at hx
              split at hx
              · simp only [Except.ok.injEq] at hx
                subst hx
                have hBk := (hBmem _ (List.getElem_mem hkB)).1
                rw [hkc, he'] at hBk
                cases hBk
                refine .inr (.inr ⟨c, ⟨k + X.length, hja⟩, _, rfl, he', hkm, ?_, rfl⟩)
                show (aggList ++ B.map (fun x => mk x.2))[k + X.length] = _
                rw [List.getElem_append_right (by omega)]
                simp [hlenX]
              · simp [throw, throwThe, MonadExceptOf.throw] at hx
        case gQh =>
          first
            | exact ⟨_, .inl ⟨rfl, rfl⟩, rfl⟩
            | (refine ⟨_, .inr ⟨hv, p, out, rfl, ?_, rfl⟩, rfl⟩
               refine translatesH_of_elab cf N.fold keyList out _ _ groupBy hXf ?_ hkc hkey
                 hv (hhv hv rfl) (fun x hx => List.mem_append_left _ (hXh hv rfl x hx)) hp'
               intro j hj hfr
               have hjX : j < X.length := by
                 by_contra hn
                 rw [List.getElem_append_right (by omega)] at hfr
                 rcases hfr with hfr | hfr <;> simp [aggFragment, CorrectAvg.avgFragment] at hfr
               obtain ⟨hja, hel⟩ := hagg j hjX
               refine ⟨hja, ?_⟩
               rw [List.getElem_append_left hjX]
               exact hel)

end SqlBridge.CorrectGrouped


namespace SqlBridge.CorrectGrouped
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGroup SqlBridge.CorrectGroupOrder

/-- The truth of a predicate on a row, `false` on an error. -/
def keepRow {m : ℕ} (p : Expr m) (r : Row m) : Bool :=
  match p.evalTruth r with
  | .ok t => t.isTrue
  | .error _ => false

/-- A predicate that filters the rows: each row's truth evaluates, and the rows kept are those
    whose truth is `TRUE`. -/
theorem filterRows_eq_filter {m : ℕ} (p : Expr m) : ∀ {as as' : List (Row m)},
    p.filterRows as = .ok as' →
      (∀ A ∈ as, ∃ t, p.evalTruth A = .ok t) ∧ as' = as.filter (keepRow p)
  | [], as', h => by
    simp only [Expr.filterRows, List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | A :: as, as', h => by
    obtain ⟨t, R'', hte, hrs, rfl⟩ := filterRows_cons_ok h
    obtain ⟨hall, rfl⟩ := filterRows_eq_filter p hrs
    refine ⟨fun B hB => ?_, ?_⟩
    · rcases List.mem_cons.mp hB with rfl | hB
      · exact ⟨t, hte⟩
      · exact hall B hB
    · simp only [List.filter_cons, keepRow, hte]

/-- Groups kept by both evaluators relate, and groups dropped by both give nothing: the typed rows
    kept relate, in order, to `SqlEquiv`'s rows zipped with their key rows. -/
theorem grouped_rel {X G : Type _} {Φ Ψ : G → Option SqlEquiv.Row}
    {PR : X → SqlEquiv.Row × SqlEquiv.Row → Prop} (keep : X → Bool) :
    ∀ {as : List X} {gs : List G}, List.Forall₂ (fun A g =>
        (keep A = true ∧ ∃ p k, Φ g = some p ∧ Ψ g = some k ∧ PR A (p, k)) ∨
        (keep A = false ∧ Φ g = none ∧ Ψ g = none)) as gs →
      List.Forall₂ PR (as.filter keep) ((gs.filterMap Φ).zip (gs.filterMap Ψ)) ∧
        ((gs.filterMap Φ).zip (gs.filterMap Ψ)).map Prod.fst = gs.filterMap Φ
  | _, _, .nil => ⟨.nil, rfl⟩
  | A :: _, _ :: _, .cons h hs => by
    obtain ⟨ih1, ih2⟩ := grouped_rel keep hs
    rcases h with ⟨hk, p, k, hp, hq, hpr⟩ | ⟨hk, hp, hq⟩
    · rw [List.filter_cons_of_pos hk, List.filterMap_cons_some hp, List.filterMap_cons_some hq,
        List.zip_cons_cons, List.map_cons, ih2]
      exact ⟨.cons hpr ih1, rfl⟩
    · rw [List.filter_cons_of_neg (by simp [hk]), List.filterMap_cons_none hp,
        List.filterMap_cons_none hq]
      exact ⟨ih1, ih2⟩

/-- `zip_rel` with the elements' memberships. -/
theorem zip_rel_mem {α β γ : Type _} {P : α → β → Prop} {Q : α → γ → Prop} {E : β → γ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ},
      (∀ a ∈ as, ∀ b ∈ bs, ∀ c, P a b → Q a c → E b c) →
      List.Forall₂ P as bs → List.Forall₂ Q as cs → List.Forall₂ E bs cs
  | _, _, _, _, .nil, .nil => .nil
  | _, _, _, h, .cons hp hps, .cons hq hqs =>
    .cons (h _ List.mem_cons_self _ List.mem_cons_self _ hp hq)
      (zip_rel_mem (fun a ha b hb c => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) c)
        hps hqs)

/-- Each projected entry is an item's output name and value. -/
theorem kv_of_items (db : SqlEquiv.Database) (U : List SqlEquiv.Row) (row : SqlEquiv.Row) :
    ∀ {items : List SqlEquiv.SelectItem}, (∀ it ∈ items, ∃ e al, it = .exprItem e al) →
      ∀ kv ∈ items.flatMap (SqlEquiv.evalSelectItemWithAggParam ee db U row),
        ∃ it ∈ items, kv.1 = outName it ∧
          kv.2 = (SqlEquiv.evalExprWithAggParam ee db U row (itemExpr it)).getD (.null none)
  | [], _, kv, h => by simp at h
  | it :: rest, h, kv, hkv => by
    obtain ⟨e, al, rfl⟩ := h it List.mem_cons_self
    rw [List.flatMap_cons, List.mem_append] at hkv
    rcases hkv with hkv | hkv
    · refine ⟨_, List.mem_cons_self, ?_⟩
      simp only [SqlEquiv.evalSelectItemWithAggParam] at hkv
      split at hkv <;> simp_all [outName, itemExpr]
    · obtain ⟨it', hit', h'⟩ :=
        kv_of_items db U row (fun x hx => h x (List.mem_cons_of_mem _ hx)) kv hkv
      exact ⟨it', List.mem_cons_of_mem _ hit', h'⟩

/-- An `ORDER BY` key column read on `projected ++ sample`: when every output column named like it
    is that column, the value is the sample row's (output names have no dot). -/
theorem keyCol_lookup (db : SqlEquiv.Database) (U : List SqlEquiv.Row) (s : SqlEquiv.Row)
    {items : List SqlEquiv.SelectItem} (hitems : ∀ it ∈ items, ∃ e al, it = .exprItem e al)
    (hdot : ∀ it ∈ items, '.' ∉ (outName it).toList) (c : SqlEquiv.ColumnRef)
    (hcap : ∀ it ∈ items, (outName it).toLower = c.column.toLower → itemExpr it = .col c)
    {v : SqlEquiv.Value} (hv : SqlEquiv.evalExprWithDb db s (.col c) = some v) :
    SqlEquiv.evalExprWithDb db
      (items.flatMap (SqlEquiv.evalSelectItemWithAggParam ee db U s) ++ s) (.col c) = some v := by
  have hv' := hv
  have hmem := kv_of_items db U s hitems
  have hdotp : ∀ kv ∈ items.flatMap (SqlEquiv.evalSelectItemWithAggParam ee db U s),
      '.' ∉ kv.1.toList := fun kv hkv => by
    obtain ⟨it, hit, hn, -⟩ := hmem kv hkv
    rw [hn]; exact hdot it hit
  rw [SqlEquiv.evalExprWithDb_col] at hv ⊢
  obtain ⟨q, cn⟩ := c
  cases q with
  | some t =>
    rw [getQualified_append_noMatch _ s (some t) cn hdotp (by simp)]; exact hv
  | none =>
    rcases hf : (items.flatMap (SqlEquiv.evalSelectItemWithAggParam ee db U s)).find?
        (fun kv => kv.1.toLower == cn.toLower) with _ | kv
    · rw [getQualified_append_noMatch _ s none cn hdotp (fun _ kv hkv h => by
        have := List.find?_eq_none.mp hf kv hkv; simp [h] at this)]
      exact hv
    · rw [getQualified_none_append_match _ s cn hdotp hf]
      obtain ⟨it, hit, hn, hval⟩ := hmem kv (List.mem_of_find?_eq_some hf)
      have hlow : (outName it).toLower = cn.toLower := by
        rw [← hn]; simpa using List.find?_some hf
      rw [hval, hcap it hit hlow]
      simp [SqlEquiv.evalExprWithAggParam, ee, hv']

/-- An aggregate item elaborates to a division-safe call. -/
theorem itemAgg_divSafe {m : ℕ} (cols : Fin m → Column) (fold : String → String)
    (x : SqlEquiv.Expr) (hx : itemAggFragment x = true) {c : AggCall m}
    (hel : elabAgg cols fold x = .ok c) : c.divSafe = true := by
  simp only [itemAggFragment, Bool.or_eq_true] at hx
  rcases hx with hx | hx
  · exact agg_divSafe cols fold x hx hel
  · match x, hx with
    | .agg (.avg _) (some w) false, hx =>
      simp only [elabAgg] at hel
      obtain ⟨e, he, rfl⟩ := bind_pure_ok hel
      exact Translates.divSafe cols fold (translates_of_elab cols fold w hx he)

/-- What a `HAVING` with a comparison `AVG(c) op k` (`cmpAvgForm`) asks for, as the scalar
    subqueries over an `AVG` do (`SqlBridge.CorrectSub.AvgWhere`): no column of the schema is a
    decimal, so the average is one of integers, and `FROM` has at most `10¹⁶` rows, so its
    denominator, at most a group's size, is within `SqlEquiv`'s 16 places. Nothing is asked of
    a `HAVING` without such a comparison. -/
def HavingAvgOk (N : NamedSchema) (D : Database N.S) (fr : SqlEquiv.FromClause)
    (having : Option SqlEquiv.Expr) : Prop :=
  (∃ h ∈ having, hasCmpAvg h = true) →
    (∀ T j, (N.S.columns T j).type ≠ .decimal) ∧
    ∀ {n : ℕ} (qf : Query N.S n) (cf : Fin n → Column) (Rf : List (Row n)),
      elabFrom N (fun sq => elabSubQuery N 15 sq) fr = .ok ⟨n, qf, cf⟩ → qf.eval D = .ok Rf →
      Rf.length ≤ 10 ^ SqlEquiv.avgPlaces

theorem havingAvgOk_of_noAvg {N : NamedSchema} {D : Database N.S} {fr : SqlEquiv.FromClause}
    {having : Option SqlEquiv.Expr} (h : ∀ hv ∈ having, hasCmpAvg hv = false) :
    HavingAvgOk N D fr having := by
  rintro ⟨hv, hmem, hc⟩
  rw [h hv hmem] at hc; cases hc

set_option maxHeartbeats 8000000 in
/-- **Elaborator correctness for grouped queries (#352, roadmap steps 3b-4 to 3b-6).** For
    `SELECT … FROM f [WHERE p] GROUP BY c₁, … [HAVING h] [ORDER BY a₁, …] [LIMIT n] [OFFSET m]`,
    column keys, every item an aggregate of step 3a, a key column or a bare column, `h` in
    `havingFragment`, every sort key an aggregate or an uncaptured key column (`OrderKeyOk`): when
    the statement elaborates, the typed query's rows relate, in order, to `SqlEquiv`'s, an `AVG`
    item (step 3c) up to `SqlEquiv`'s rounding (`OutRelI`). Bare columns read the group's first row, or the row
    where the one `MIN`/`MAX` argument is extreme (`BareOk`), and with sort keys no output
    name captures `SqlEquiv`'s key columns (`hnm`).

    The conclusion is under every outer row `ctx` (#409): as a subquery body `SqlEquiv` evaluates
    the statement on source rows `row ++ ctx`, and the typed result is the same one. -/
theorem elabStmt_correct_grouped_ctx (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} {having : Option SqlEquiv.Expr}
    {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hgi : groupedItems items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hwo : ∀ {n : ℕ} (qf q₀ : Query N.S n) (cf : Fin n → Column),
      elabFrom N (fun sq => elabSubQuery N 15 sq) fr = .ok ⟨n, qf, cf⟩ →
      elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf wh = .ok q₀ →
      WhereOk cf N.fold db D wh qf q₀) (hhv : ∀ h ∈ having, havingFragment groupBy h = true)
    (hav : HavingAvgOk N D fr having)
    (hob : ∀ o ∈ orderBy, OrderKeyOk items groupBy o.expr) (hbf : BareOk N items groupBy having orderBy)
    (hnm : orderBy ≠ [] → ∀ it ∈ items, '.' ∉ (outName it).toList ∧
      ∀ k, (outName it).toLower ≠ SqlEquiv.groupOrderKeyName k)
    {e : Elaborated N.S}
    (h : elabStmt N (groupedStmt items fr wh groupBy having orderBy lim off) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    e.q.IsSafe ∧ ∃ rs, e.q.eval D = .ok rs ∧
      ∀ ctx, List.Forall₂ (OutRelI items) rs (SqlEquiv.evalSelectWithContext db ctx
        (.mk false items (some fr) wh groupBy having orderBy lim off)) := by
  obtain ⟨hty, n, qf, cf, hf, q₀, hq₀, keyList, a, aggs, its, sk, mk, hk, hmk, haggs, hits, hsk,
    qh, hqh, rfl⟩ := elab_grouped_shape N hfoldCI hgi (.inl hgb) hob hgc hhv hbf h
  have hwo' := hwo qf q₀ cf hf hq₀
  -- what a bare column's aggregate is: `first` with no `MIN`/`MAX`, or `atExtreme` at the one
  have hmkC : ∀ c e', c ∈ colRefs items → elabExpr cf N.fold noHook (.col c) = .ok e' →
      e' ∉ keyList → ((∀ e, mk e = .first e) ∧ SqlEquiv.selectMinMaxCalls items having = []) ∨
        ∃ (wantMax : Bool) (mode : SqlEquiv.MinMaxMode) (arg : SqlEquiv.Expr) (k' : Expr n),
          mode.bareRow = true ∧
          SqlEquiv.selectMinMaxCalls items having = [(wantMax, mode, some arg, false)] ∧
          isFragment arg = true ∧ elabExpr cf N.fold noHook arg = .ok k' ∧
          ∀ e, mk e = .atExtreme (if wantMax then .gt else .lt) k' e := by
    intro c e' hc he' hkn
    obtain ⟨it, hit, hite⟩ := exists_item_of_colRefs hc
    exact hmk ⟨it, hit, c, e', hite, he', hkn⟩
  have hlo : orderBy.length = sk.length := hsk.length_eq
  obtain ⟨hnames, hfrom⟩ := from_rel N hfold hfoldCI hwn hfix hD hrel _ fr hff hf
  simp only at hnames hfrom hty hnb ⊢
  rw [typeOf_limitWrap] at hty
  rw [qnb_limitWrap] at hnb
  -- the sort keys: each the column of an aggregate
  have hskget : ∀ i : Fin sk.length, ∃ idx : Fin (keyList.length + a),
      (sk[i]).e = .col idx ∧ (sk[i]).desc = ((orderBy[i.1]'(by omega)).dir == .desc) ∧
      (sk[i]).nullsFirst = ((orderBy[i.1]'(by omega)).nulls == .first) ∧
      ((∃ j : Fin a, idx = Fin.natAdd _ j ∧
          elabAgg cf N.fold (orderBy[i.1]'(by omega)).expr = .ok (aggs j)) ∨
        ∃ c, ∃ i' : Fin keyList.length, idx = Fin.castAdd a i' ∧
          (orderBy[i.1]'(by omega)).expr = .col c ∧
          elabExpr cf N.fold noHook (.col c) = .ok keyList[i']) := by
    intro i
    have := (List.forall₂_iff_get.mp hsk).2 i.1 (by omega) i.2
    simp only [List.get_eq_getElem] at this
    obtain ⟨hcase, hd, hn⟩ := this
    rcases hcase with ⟨j, hel, he⟩ | ⟨c, i', hc, hel, he⟩
    · exact ⟨_, he, hd, hn, .inl ⟨j, rfl, hel⟩⟩
    · exact ⟨_, he, hd, hn, .inr ⟨c, i', rfl, hc, hel⟩⟩
  choose idx hidx using hskget
  set aggQ : Query N.S (keyList.length + a) :=
    .aggregate (fun i : Fin keyList.length => keyList[i]) aggs q₀ with haggQ
  -- typing and the boolean side conditions, through the optional `ORDER BY`
  obtain ⟨Γa, hΓqh, hnbqh, hnbO⟩ : ∃ Γa, qh.typeOf = some Γa ∧ QNoBoolOrder qh ∧
      (sk.length ≠ 0 → ∀ i : Fin sk.length, (sk[i]).e.typeOf Γa ≠ some .bool) := by
    obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
    by_cases h0 : sk.length = 0
    · simp only [h0, ↓reduceIte] at hΔ hnb
      obtain ⟨Γa, hΓa, -⟩ := Query.typeOf_project_eq_some.mp hΔ
      exact ⟨Γa, hΓa, hnb.2, fun h => absurd h0 h⟩
    · simp only [h0, ↓reduceIte] at hΔ hnb
      obtain ⟨Γa, hΓo, -⟩ := Query.typeOf_project_eq_some.mp hΔ
      obtain ⟨hΓa, -⟩ := Query.typeOf_orderBy_eq_some hΓo
      exact ⟨Γa, hΓa, hnb.2.2, fun _ => hnb.2.1 Γa hΓa⟩
  -- the `HAVING` predicate, if any: which aggregate rows it keeps
  obtain ⟨P, hP, hΓa, hnbA, hnbP, hdivP⟩ : ∃ P : Option (Expr (keyList.length + a)),
      ((having = none ∧ P = none ∧ qh = aggQ) ∨ ∃ hv p out, having = some hv ∧ P = some p ∧
        TranslatesH cf out N.fold (fun i : Fin keyList.length => keyList[i]) aggs hv p ∧
        qh = .select p aggQ) ∧
      aggQ.typeOf = some Γa ∧ QNoBoolOrder aggQ ∧ (∀ p ∈ P, NoBoolOrder Γa p) ∧
      (∀ p ∈ P, p.divSafe = true) := by
    rcases hqh with ⟨hhn, rfl⟩ | ⟨hv, p, out, hhs, htrH, rfl⟩
    · exact ⟨none, .inl ⟨hhn, rfl, rfl⟩, hΓqh, hnbqh, by simp, by simp⟩
    · refine ⟨some p, .inr ⟨hv, p, out, hhs, rfl, htrH, rfl⟩,
        (Query.typeOf_select_eq_some.mp hΓqh).1, hnbqh.2, ?_, ?_⟩
      · intro p' hp'; cases hp'; exact hnbqh.1 Γa (Query.typeOf_select_eq_some.mp hΓqh).1
      · intro p' hp'; cases hp'
        exact TranslatesH.divSafe htrH
  obtain ⟨Γ₀, Δk, Δa, hq₀ty, hks, has, hΓeq⟩ := Query.typeOf_aggregate_eq_some hΓa
  obtain ⟨hnbA', hnbq₀⟩ := hnbA
  have hnbK := (hnbA' Γ₀ hq₀ty).1
  have hnbAgg := (hnbA' Γ₀ hq₀ty).2
  have hτb : sk.length ≠ 0 → ∀ i : Fin sk.length, Γa (idx i) ≠ .bool := by
    intro h0 i hb
    apply hnbO h0 i
    rw [(hidx i).1]
    simp [Expr.typeOf, hb]
  have hsrc : qf.typeOf = some Γ₀ := hwo'.src _ hq₀ty
  have hnbsrc : QNoBoolOrder qf := hwo'.nb hnbq₀
  obtain ⟨hdivf, Rf, hRf, hrelf⟩ := hfrom hsrc hnbsrc
  have hrows : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) Rf
      (SqlEquiv.evalFrom db fr) := hrelf.imp fun r u h =>
    ⟨rowRel_of_keyed N.fold hfold hfoldCI (fun j => (hnames j).1) (fun j => (hnames j).2) h.1, h.2⟩
  have hdivq₀ : q₀.divSafe = true := hwo'.div _ hq₀ty hnbq₀ hdivf
  obtain ⟨R, hR⟩ := Query.IsSafe.exists_eval_eq_ok (q := q₀) ⟨by simp [hq₀ty], hdivq₀⟩ hD
  -- the keys translate the `GROUP BY` columns
  have hK := mapM_forall₂ hk
  have hlen : groupBy.length = keyList.length := hK.length_eq
  have hkey : ∀ c, SqlEquiv.Expr.col c ∈ groupBy → ∃ e', elabExpr cf N.fold noHook (.col c) = .ok e' ∧
      e' ∈ keyList := fun c hc => by
    obtain ⟨e', he', h⟩ := forall₂_mem_left hK hc
    exact ⟨e', h, he'⟩
  have htk : ∀ i : Fin keyList.length, Translates cf N.fold (groupBy[i.1]'(by omega)) keyList[i] := by
    intro i
    have h1 := (List.forall₂_iff_get.mp hK).2 i.1 (by omega) i.2
    simp only [List.get_eq_getElem] at h1
    obtain ⟨c, hc⟩ := hgc _ (List.getElem_mem (by omega : i.1 < groupBy.length))
    rw [hc] at h1 ⊢
    exact translates_of_elab cf N.fold _ rfl h1
  have hdivK : ∀ i : Fin keyList.length, (keyList[i]).divSafe = true :=
    fun i => Translates.divSafe _ _ (htk i)
  -- every aggregate is safe: aggregates of step 3a, and `first` of a column
  have hda : ∀ j, (aggs j).divSafe = true := fun j => by
    rcases haggs j with ⟨x, hx, hel⟩ | ⟨c, e', hc, he', hkn, hj⟩
    · exact itemAgg_divSafe cf N.fold x hx hel
    · obtain ⟨idx, rfl⟩ := elab_col_is_col cf N.fold c he'
      rcases hmkC c _ hc he' hkn with ⟨hfst, -⟩ | ⟨w, m, arg, k', -, -, hfrag, hk', hat⟩
      · rw [hj, hfst]; rfl
      · rw [hj, hat]
        simp only [AggCall.divSafe, Bool.and_eq_true]
        exact ⟨Translates.divSafe _ _ (translates_of_elab cf N.fold arg hfrag hk'), rfl⟩
  have hdivA : aggQ.divSafe = true := by
    simp only [haggQ, Query.divSafe, hda, hdivq₀, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun i => hdivK i, fun _ => trivial⟩
  -- the typed query evaluates
  have hsafe : (limitWrap lim off (if sk.length = 0 then .project (fun i : Fin its.length => (its[i]).1) qh
      else .project (fun i : Fin its.length => (its[i]).1)
        (.orderBy (fun i : Fin sk.length => sk[i]) qh))).IsSafe := by
    refine ⟨by rw [typeOf_limitWrap]; exact hty, ?_⟩
    rw [divSafe_limitWrap]
    have hcols : ∀ i : Fin its.length, ((its[i]).1).divSafe = true := by
      intro i
      rcases (List.forall₂_iff_get.mp hits).2 i.1 (by have := hits.length_eq; omega) i.2 with
        ⟨j, -, hj⟩ | ⟨c, i', -, -, hj⟩ | ⟨c, j, e', -, -, -, -, hj⟩ <;>
        (simp only [List.get_eq_getElem] at hj; show ((its[i.1]).1).divSafe = true; rw [hj]; rfl)
    have hqd : qh.divSafe = true := by
      rcases hP with ⟨-, rfl, rfl⟩ | ⟨hv, p, out, -, rfl, -, rfl⟩
      · exact hdivA
      · simp only [Query.divSafe, hdivA, Bool.and_true]; exact hdivP p rfl
    by_cases h0 : sk.length = 0
    · simp only [h0, ↓reduceIte, Query.divSafe, hqd, Bool.and_true, decide_eq_true_eq]
      exact fun i => hcols i
    · simp only [h0, ↓reduceIte, Query.divSafe, hqd, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨fun i => hcols i, fun i => by rw [(hidx i).1]; rfl⟩
  obtain ⟨rs, hrs⟩ := Query.IsSafe.exists_eval_eq_ok hsafe hD
  refine ⟨hsafe, rs, hrs, fun ctx => ?_⟩
  -- the typed evaluation, step by step
  obtain ⟨base, hbase, rfl⟩ := eval_limitWrap D lim off _ hrs
  obtain ⟨rowsH, hH, hbase'⟩ : ∃ rowsH, qh.eval D = .ok rowsH ∧
      (if sk.length = 0 then rowsH.mapM (Expr.evalRow fun i : Fin its.length => (its[i]).1) = .ok base
       else ∃ keyedS, rowsH.mapM (fun r : Row (keyList.length + a) =>
          (do return (← Expr.evalRow (fun i : Fin sk.length => (sk[i]).e) r, r) :
            Except EvalError (Row sk.length × Row (keyList.length + a)))) = .ok keyedS ∧
        ((sortKeyed (fun i : Fin sk.length => sk[i]) keyedS).map Prod.snd).mapM
          (Expr.evalRow fun i : Fin its.length => (its[i]).1) = .ok base) := by
    by_cases h0 : sk.length = 0
    · simp only [h0, ↓reduceIte] at hbase ⊢
      rw [Query.eval_project] at hbase
      obtain ⟨rowsH, hH, hout⟩ := bind_ok hbase
      exact ⟨rowsH, hH, hout⟩
    · simp only [h0, ↓reduceIte] at hbase ⊢
      rw [Query.eval_project] at hbase
      obtain ⟨sorted, hsorted, hout⟩ := bind_ok hbase
      rw [Query.eval_orderBy] at hsorted
      obtain ⟨rowsH, hH, hsorted⟩ := bind_ok hsorted
      obtain ⟨keyedS, hkeyedS, hpure⟩ := bind_ok hsorted
      cases hpure
      exact ⟨rowsH, hH, keyedS, hkeyedS, hout⟩
  -- the aggregate's rows, filtered by `HAVING`
  let keep : Row (keyList.length + a) → Bool := fun A => P.all fun p => keepRow p A
  obtain ⟨rowsA, hA, rfl, hPt⟩ : ∃ rowsA, aggQ.eval D = .ok rowsA ∧ rowsH = rowsA.filter keep ∧
      ∀ A ∈ rowsA, ∀ p ∈ P, ∃ t, p.evalTruth A = .ok t := by
    rcases hP with ⟨-, rfl, rfl⟩ | ⟨hv, p, out, -, rfl, -, rfl⟩
    · exact ⟨rowsH, hH, by simp [keep], by simp⟩
    · rw [Query.eval_select] at hH
      obtain ⟨rowsA, hA, hfilt⟩ := bind_ok hH
      obtain ⟨hall, rfl⟩ := filterRows_eq_filter p hfilt
      exact ⟨rowsA, hA, by simp [keep], fun A hA p' hp' => by cases hp'; exact hall A hA⟩
  have hAeval := hA
  rw [haggQ, Query.eval_aggregate, hR] at hA
  obtain ⟨R', hR', hA⟩ := bind_ok hA
  cases hR'
  obtain ⟨keyed, hkeyed, hgrp⟩ := bind_ok hA
  have hg0 : keyList.length ≠ 0 := by
    intro h0; apply hgb; exact List.eq_nil_of_length_eq_zero (by omega)
  have hgroups : Row.groups keyed = Row.groupAux [] keyed := by simp [Row.groups, hg0]
  have hKeyed : List.Forall₂ (fun r p => ∃ k, Expr.evalRow (fun i : Fin keyList.length => keyList[i]) r
      = .ok k ∧ p = (k, r)) R keyed :=
    (mapM_forall₂ hkeyed).imp fun r p h => bind_pure_ok h
  have hitems : ∀ it ∈ items, ∃ e al, it = .exprItem e al := fun it hit => by
    obtain ⟨e, al, h, -⟩ := groupedItems_mem hgi it hit; exact ⟨e, al, h⟩
  -- `SqlEquiv`'s side
  rw [SqlEquiv.evalSelectWithContext_eq_evalSelectCore]
  obtain ⟨F, F', Φ, Ψ, hF, hF', hΦ, hΨ, heq⟩ :=
    evalSelectCore_grouped_full db ctx _ _ _ _ _ _ _ _ _ items fr wh groupBy having orderBy lim off hgb
      (selectHasWindowFn_groupedItems hgi)
  rw [heq, applyOrder_eq]
  apply limit_rel
  -- a typed aggregate row against `SqlEquiv`'s (projected row, key row)
  let PRA : Row (keyList.length + a) → SqlEquiv.Row × SqlEquiv.Row → Prop := fun A y =>
    (∀ o, Expr.evalRow (fun i : Fin its.length => (its[i]).1) A = .ok o → OutRelI items o y.1) ∧
    (∀ i : Fin sk.length, ∃ v, SqlEquiv.evalExprWithDb db (y.1 ++ y.2)
      ((SqlEquiv.groupOrderByItems orderBy)[i.1]'(by
        rw [length_groupOrderByItems]; omega)).expr = some v ∧
        DatumRel (A (idx i)) v) ∧
    A.Conforms Γa
  have core : ∀ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U →
      List.Forall₂ PRA (rowsA.filter keep) (((U.foldl F []).filterMap Φ).zip
        ((U.foldl F' []).filterMap Ψ)) ∧
      (((U.foldl F []).filterMap Φ).zip ((U.foldl F' []).filterMap Ψ)).map Prod.fst =
        (U.foldl F []).filterMap Φ := by
    intro U hRU
    let kf : SqlEquiv.Row → List (Option SqlEquiv.Value) := fun u =>
      groupBy.map fun e => (SqlEquiv.evalExprWithDb db u e).map SqlEquiv.Value.setKey
    let E : Row keyList.length × Row n → SqlEquiv.Row → Prop := fun p u =>
      (RowRel cf N.fold p.2 u ∧ p.2.Conforms Γ₀) ∧
        Expr.evalRow (fun i : Fin keyList.length => keyList[i]) p.2 = .ok p.1 ∧ KRel Δk p.1 (kf u)
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
    have hP1 : List.Forall₂ (fun g A => (do return Fin.append g.1 (← AggCall.evalAll aggs g.2) :
        Except EvalError (Row (keyList.length + a))) = .ok A) (Row.groupAux [] keyed) rowsA := by
      rw [← hgroups]; exact mapM_forall₂ hgrp
    apply grouped_rel keep
    refine zip_rel_mem ?_ hP1 hgrel
    rintro ⟨k, rs'⟩ hgm A hAm ⟨key, us⟩ h1 ⟨hkk, hrs'⟩
    obtain ⟨hne, -⟩ := hGO _ (hsub _ hgm)
    simp only at hne hrs' hkk
    have hus : us ≠ [] := by
      rintro rfl; cases hrs'; exact hne rfl
    obtain ⟨s, hs⟩ : ∃ s, SqlEquiv.bareSampleRow (fun r e => SqlEquiv.evalExprWithDb db r e)
        (SqlEquiv.selectMinMaxCalls items having) us = some s :=
      Option.ne_none_iff_exists'.mp ((SqlEquiv.bareSampleRow_eq_none_iff _ _ _).not.mpr hus)
    have hsm := bareSampleRow_mem _ _ hs
    obtain ⟨Ag, hAe, rfl⟩ := bind_pure_ok h1
    have hrows' : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) rs' us :=
      hrs'.imp fun _ _ h => h.1
    obtain ⟨rs_, -, hE_⟩ := forall₂_mem_right hrs' hsm
    -- the aggregate row conforms
    have hrsc : ∀ r ∈ rs', r.Conforms Γ₀ := fun r hr => by
      obtain ⟨u, -, h⟩ := forall₂_mem_left hrows' hr; exact h.2
    have hAc : Row.Conforms Δa Ag := by
      rcases AggCall.evalAll_ok_or_divisionByZero hrsc has with ⟨A', hA', hc⟩ | ⟨hdz, -⟩
      · rw [hAe, Except.ok.injEq] at hA'; subst hA'; exact hc
      · rw [hAe] at hdz; cases hdz
    have hkc : Row.Conforms Δk k := fun i =>
      Expr.hasType_of_eval_eq_ok hE_.1.2 (hks i) (Expr.evalRow_eq_ok_iff.mp hE_.2.1 i)
    have hconf : Row.Conforms Γa (Fin.append k Ag : Row (keyList.length + a)) := by
      rw [← hΓeq]; exact Row.conforms_append_iff.mpr ⟨hkc, hAc⟩
    -- the `HAVING` decision agrees
    have hdec : keep (Fin.append k Ag) = having.all (fun c =>
        SqlEquiv.evalExprWithAggParam ee db us s c == some (.bool true)) := by
      rcases hP with ⟨hhn, hPn, -⟩ | ⟨hv, p, out, hhs, hPs, htrH, -⟩
      · simp [keep, hhn, hPn]
      · obtain ⟨t, ht⟩ := hPt _ hAm p (by simp [hPs])
        obtain ⟨d, hd, hdt⟩ : ∃ d, p.eval (Fin.append k Ag) = .ok d ∧ d.toTruth = .ok t := by
          unfold Expr.evalTruth at ht
          rcases he : p.eval (Fin.append k Ag) with _ | d
          · simp [he, bind, Except.bind] at ht
          · simp only [he, bind, Except.bind] at ht
            exact ⟨d, rfl, ht⟩
        obtain ⟨v, hv', hrel⟩ := TranslatesH.eval_rel cf out N.fold _ aggs db hrows' hAe hconf
          ⟨rs_, hE_.1.1, hE_.1.2, hE_.2.1⟩ hnbK hnbAgg (fun j => ⟨_, has j⟩) htrH
          (fun hca x j q hxa hel hq => by
            -- the average of an integer column over a group of at most `10¹⁶` rows
            obtain ⟨hnd, hrowsB⟩ := hav ⟨hv, by simp [hhs], hca⟩
            have hgl : rs'.length ≤ 10 ^ SqlEquiv.avgPlaces := by
              have h1 := Row.length_le_of_mem_groups (hsub _ hgm)
              have h2 := hKeyed.length_eq
              have h3 := (hwo'.rel hq₀ty hnbq₀ hRf hR hrows).length_eq
              have h4 := hrows.length_eq
              have h5 := hrowsB qf cf Rf hf hRf
              cases wh with
              | none => simp only at h1 h3; omega
              | some c =>
                have h6 := List.length_filter_le
                  (fun u => SqlEquiv.evalExprWithDb db u c == some (.bool true))
                  (SqlEquiv.evalFrom db fr)
                simp only at h1 h3; omega
            match x, hxa with
            | .agg (.avg b) (some (.col c)) false, _ =>
              simp only [elabAgg, bind, Except.bind] at hel
              rcases he₀ : elabExpr cf N.fold noHook (.col c) with err | e₀
              · simp [he₀] at hel
              simp only [he₀, pure, Except.pure, Except.ok.injEq] at hel
              obtain ⟨ix, rfl⟩ := elab_col_is_col cf N.fold c he₀
              have hτ : Γ₀ ix ≠ .decimal := from_noDecimal N _ hnd fr hff hf hsrc ix
              have hint : (Expr.col ix : Expr _).typeOf Γ₀ = some .int := by
                have h1 := has j
                rw [← hel] at h1
                simp only [AggCall.typeOf, Expr.typeOf] at h1 ⊢
                cases hΓ : Γ₀ ix <;> simp_all
              have hev := evalAll_get hAe j
              rw [← hel, hq] at hev
              exact (CorrectAvg.avg_den_le (fun r hr d hd' => by
                rcases Expr.eval_ok_or_divisionByZero (hrsc r hr) hint with ⟨d', hd'', hty⟩ | ⟨hdz, _⟩
                · rw [hd'] at hd''; cases hd''; exact hty
                · rw [hd'] at hdz; cases hdz) hev).trans hgl)
          (hnbP p (by simp [hPs])) hd
        simp only [keep, hPs, hhs, Option.all_some, keepRow, ht, hv']
        exact isTrue_iff_where hrel hdt
    rw [hΦ key us s hs, hΨ key us s hs, ← hdec]
    cases hkp : keep (Fin.append k Ag)
    · exact .inr ⟨rfl, by simp, by simp⟩
    simp only [↓reduceIte]
    refine .inl ⟨by simp, _, _, rfl, rfl, ?_, ?_, hconf⟩
    · -- the items
      intro r h2
      have hr := Expr.evalRow_eq_ok_iff.mp h2
      unfold OutRelI
      refine ⟨hits.length_eq, ?_⟩
      rw [items_vals_group db us s hitems]
      apply List.forall₂_iff_get.mpr
      refine ⟨by simp [hits.length_eq], fun i h1' h2' => ?_⟩
      simp only [List.get_eq_getElem, List.getElem_zip, List.getElem_ofFn, List.getElem_map]
      have hi : i < its.length := by simp at h1'; omega
      have hi' : i < items.length := by simpa using h2'
      have hcase := (List.forall₂_iff_get.mp hits).2 i hi' hi
      simp only [List.get_eq_getElem] at hcase
      rcases hcase with ⟨j, hel, hj⟩ | ⟨c, i', hc, hel, hj⟩ | ⟨c, j, e', hc, hel, hkn, hjf, hj⟩
      · -- an aggregate: exact, or `AVG` up to rounding
        have hri : r ⟨i, hi⟩ = Ag j := by
          have h3 := hr ⟨i, hi⟩
          have h4 : ((its[i]).1).eval (Fin.append k Ag) = .ok (Ag j) := by
            rw [hj]; show Except.ok _ = _; rw [Fin.append_right]
          exact Except.ok.inj (h3.symm.trans h4)
        obtain ⟨x, al, hx, hcase'⟩ := groupedItems_mem hgi _ (List.getElem_mem hi')
        have hfr' : itemAggFragment (itemExpr items[i]) = true := by
          rw [hx]; simp only [itemExpr]
          rcases hcase' with h | ⟨c, rfl⟩
          · exact h
          · rw [hx] at hel; simp [itemExpr, elabAgg, throw, throwThe, MonadExceptOf.throw] at hel
        simp only [itemAggFragment, Bool.or_eq_true] at hfr'
        rcases hfr' with hfr | hfr
        · rw [ItemRel, if_neg (by simp [avgFragment_false_of_agg hfr])]
          obtain ⟨v, hv, hvr⟩ := agg_rel cf N.fold db hrows' s _ hfr hel (hnbAgg j) (has j)
            (evalAll_get hAe j)
          rw [hri, hv]; exact hvr
        · rw [ItemRel, if_pos hfr]
          obtain ⟨v, hv, hvr⟩ := CorrectAvg.avg_rel cf N.fold db hrows' s _ hfr hel (hnbAgg j)
            (has j) (evalAll_get hAe j)
          rw [hri, hv]; exact hvr
      · -- a key column, read on the sample row
        have hri : r ⟨i, hi⟩ = k i' := by
          have h3 := hr ⟨i, hi⟩
          have h4 : ((its[i]).1).eval (Fin.append k Ag) = .ok (k i') := by
            rw [hj]; show Except.ok _ = _; rw [Fin.append_left]
          exact Except.ok.inj (h3.symm.trans h4)
        have hki : (keyList[i']).eval rs_ = .ok (k i') := Expr.evalRow_eq_ok_iff.mp hE_.2.1 i'
        have htr := translates_of_elab cf N.fold (.col c) rfl hel
        obtain ⟨v, hv, hvr⟩ := Translates.eval_rel cf N.fold db hE_.1.1 hE_.1.2 htr (hnbK i') hki
        rw [ItemRel, hc, if_neg (by simp [CorrectAvg.avgFragment]), hri]
        simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
        exact hvr
      · -- a bare column, read on the group's first row
        have hri : r ⟨i, hi⟩ = Ag j := by
          have h3 := hr ⟨i, hi⟩
          have h4 : ((its[i]).1).eval (Fin.append k Ag) = .ok (Ag j) := by
            rw [hj]; show Except.ok _ = _; rw [Fin.append_right]
          exact Except.ok.inj (h3.symm.trans h4)
        have hcr : c ∈ colRefs items := by
          obtain ⟨x, al, hx, -⟩ := groupedItems_mem hgi _ (List.getElem_mem hi')
          rw [hx] at hc; simp only [itemExpr] at hc; subst hc
          exact colRefs_of_mem (List.getElem_mem hi') hx
        have htr := translates_of_elab cf N.fold (.col c) rfl hel
        have hnbe : NoBoolOrder Γ₀ e' := by
          obtain ⟨idx, rfl⟩ := elab_col_is_col cf N.fold c hel; trivial
        have hfe := evalAll_get hAe j
        rw [hjf] at hfe
        rcases hmkC c e' hcr hel hkn with ⟨hfst, hcalls⟩ |
          ⟨wantMax, mode, arg, k', hm, hcalls, hfrag, hk', hat⟩
        · -- no `MIN`/`MAX`: `first`, on the group's first row
          rw [hfst] at hfe
          rw [hcalls, bareSampleRow_nil_calls] at hs
          obtain ⟨r₀, rs₁, rfl⟩ : ∃ r₀ rs₁, rs' = r₀ :: rs₁ := by
            cases rs' with
            | nil => cases hrows'; simp at hs
            | cons r₀ rs₁ => exact ⟨r₀, rs₁, rfl⟩
          obtain ⟨u₀, us₁, rfl⟩ : ∃ u₀ us₁, us = u₀ :: us₁ := by
            cases us with
            | nil => simp at hs
            | cons u₀ us₁ => exact ⟨u₀, us₁, rfl⟩
          simp only [List.head?_cons, Option.some.injEq] at hs
          subst hs
          have hrow₀ := (List.forall₂_cons.mp hrows').1
          have hd₀ := first_eval hfe
          obtain ⟨v, hv, hvr⟩ := Translates.eval_rel cf N.fold db hrow₀.1 hrow₀.2 htr hnbe hd₀
          rw [ItemRel, hc, if_neg (by simp [CorrectAvg.avgFragment]), hri]
          simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
          exact hvr
        · -- one `MIN`/`MAX`: `atExtreme`, on the row where its argument is extreme
          rw [hat] at hfe
          rw [hcalls] at hs
          have hagj := hnbAgg j
          rw [hjf, hat] at hagj
          obtain ⟨hnbk, -⟩ := hagj
          obtain ⟨τ, hkty, hτ⟩ : ∃ τ, k'.typeOf Γ₀ = some τ ∧ τ ≠ .bool := by
            have hty' := has j
            rw [hjf, hat] at hty'
            simp only [AggCall.typeOf] at hty'
            split at hty'
            all_goals first
              | (rename_i hk; exact ⟨_, hk, by simp⟩)
              | cases hty'
          obtain ⟨s', hs', v, hv, hvr⟩ := CorrectExtreme.atExtreme_rel cf N.fold db hτ hm
            (translates_of_elab cf N.fold arg hfrag hk') hnbk hkty htr hnbe hrows' hus hfe
          rw [hs'] at hs
          cases hs
          rw [ItemRel, hc, if_neg (by simp [CorrectAvg.avgFragment]), hri]
          simp only [SqlEquiv.evalExprWithAggParam, ee, hv, Option.getD_some]
          exact hvr
    · -- the sort-key values, read back from the key row
      intro i
      have hob0 : orderBy ≠ [] := by
        intro h0
        have hi2 := i.2
        have : sk.length = 0 := by rw [← hlo, h0]; rfl
        omega
      let p := items.flatMap (SqlEquiv.evalSelectItemWithAggParam ee db us s)
      have hval : ∀ i' : Fin orderBy.length, ∃ v,
          SqlEquiv.evalExprWithAggParam ee db us (p ++ s) (orderBy[i']).expr = some v ∧
            DatumRel (Fin.append k Ag (idx ⟨i', by omega⟩)) v := fun i' => by
        show ∃ v, SqlEquiv.evalExprWithAggParam ee db us (p ++ s) (orderBy[i'.1]).expr = some v ∧ _
        rcases (hidx ⟨i', by omega⟩).2.2.2 with ⟨j, hj, hel⟩ | ⟨c, i'', hi'', hc, hel⟩
        · -- an aggregate, over the group
          rw [hj, Fin.append_right]
          have hfr : aggFragment (orderBy[i'.1]).expr = true := by
            rcases hob _ (List.getElem_mem i'.2) with hfr | ⟨c', hc', -, -⟩
            · exact hfr
            · exfalso
              have hel' : elabAgg cf N.fold (orderBy[i'.1]).expr = .ok (aggs j) := hel
              rw [hc'] at hel'
              simp [elabAgg, throw, throwThe, MonadExceptOf.throw] at hel'
          exact agg_rel cf N.fold db hrows' (p ++ s) _ hfr hel (hnbAgg _) (has _) (evalAll_get hAe _)
        · -- a key column, read on the sample row (no output column captures it)
          rw [hi'', Fin.append_left]
          have hc' : (orderBy[i'.1]).expr = .col c := hc
          rw [hc']
          have hki : (keyList[i'']).eval rs_ = .ok (k i'') := Expr.evalRow_eq_ok_iff.mp hE_.2.1 i''
          have htr := translates_of_elab cf N.fold (.col c) rfl hel
          obtain ⟨v, hv, hvr⟩ := Translates.eval_rel cf N.fold db hE_.1.1 hE_.1.2 htr (hnbK i'') hki
          refine ⟨v, ?_, hvr⟩
          have hcap : ∀ it ∈ items, (outName it).toLower = c.column.toLower → itemExpr it = .col c := by
            rcases hob _ (List.getElem_mem i'.2) with hfr | ⟨c', hc'', -, hcap⟩
            · rw [hc'] at hfr; simp [aggFragment] at hfr
            · rw [hc'] at hc''; cases hc''
              exact fun it hit h => hcap it hit (.inl h)
          simp only [SqlEquiv.evalExprWithAggParam, ee]
          exact keyCol_lookup db us s hitems (fun it hit => (hnm hob0 it hit).1) c hcap hv
      choose vs hvs using hval
      have hkr := groupOrderKeyRow_eq db _ orderBy us s p vs (fun i => (hvs i).1)
      have hfree : KeyNameFree p := by
        intro kv hkv
        obtain ⟨it, hit, hname⟩ := names_of_items db us s hitems kv hkv
        rw [hname]; exact hnm hob0 it hit
      refine ⟨vs ⟨i, by omega⟩, ?_, ?_⟩
      · rw [getElem_groupOrderByItems]
        show SqlEquiv.evalExprWithDb db (p ++ SqlEquiv.groupOrderKeyRow db _ orderBy us s p)
          (.col ⟨none, SqlEquiv.groupOrderKeyName i⟩) = _
        rw [SqlEquiv.evalExprWithDb_col, hkr]
        exact keyRow_lookup p hfree vs ⟨i, by omega⟩
      · exact (hvs ⟨i, by omega⟩).2
  suffices hfin : ∀ U, List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ₀) R U →
      List.Forall₂ (OutRelI items) base (if (SqlEquiv.groupOrderByItems orderBy).isEmpty then
        (U.foldl F []).filterMap Φ
      else ((((U.foldl F []).filterMap Φ).zip ((U.foldl F' []).filterMap Ψ)).mergeSort
        fun p₁ p₂ => SqlEquiv.compareByOrderItemsParam
          (fun db' r e => SqlEquiv.evalExprWithDb db' r e) db (p₁.1 ++ p₁.2) (p₂.1 ++ p₂.2)
          (SqlEquiv.groupOrderByItems orderBy)).map Prod.fst) by
    apply hfin
    refine hwo'.rel hq₀ty hnbq₀ hRf hR ?_
    rw [List.forall₂_map_right_iff]
    exact hrows.imp fun r u h => ⟨rowRel_append ctx h.1, h.2⟩
  intro U hRU
  obtain ⟨hPR, hfst⟩ := core U hRU
  by_cases h0 : sk.length = 0
  · have hob0 : orderBy = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hgob : (SqlEquiv.groupOrderByItems orderBy).isEmpty = true := by
      simp [hob0, SqlEquiv.groupOrderByItems]
    simp only [h0, ↓reduceIte] at hbase'
    simp only [hgob, ↓reduceIte]
    rw [← hfst]
    exact forall₂_mapM_rel (fun A y hpra c hc => hpra.1 c hc) hPR hbase'
  · have hgob : (SqlEquiv.groupOrderByItems orderBy).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff, ← List.length_pos_iff, length_groupOrderByItems]; omega
    simp only [h0, ↓reduceIte] at hbase'
    obtain ⟨keyedS, hkeyedS, hout⟩ := hbase'
    simp only [hgob, Bool.false_eq_true, ↓reduceIte]
    have hKS : List.Forall₂ (fun A x => ∃ kk, Expr.evalRow (fun i : Fin sk.length => (sk[i]).e) A =
        .ok kk ∧ x = (kk, A)) (rowsA.filter keep) keyedS :=
      (mapM_forall₂ hkeyedS).imp fun _ _ h => bind_pure_ok h
    let τ : Fin sk.length → SqlType := fun i => Γa (idx i)
    let PR : Row sk.length × Row (keyList.length + a) → SqlEquiv.Row × SqlEquiv.Row → Prop :=
      fun x y => PRA x.2 y ∧ ∀ i, x.1 i = x.2 (idx i)
    have hPRz : List.Forall₂ PR keyedS (((U.foldl F []).filterMap Φ).zip
        ((U.foldl F' []).filterMap Ψ)) := zip_rel (fun A x y hx hpra => by
          obtain ⟨kk, hkk, rfl⟩ := hx
          refine ⟨hpra, fun i => ?_⟩
          have h3 := Expr.evalRow_eq_ok_iff.mp hkk i
          rw [(hidx i).1] at h3
          exact (Except.ok.inj h3).symm) hKS hPR
    obtain ⟨W, hW1, hW2, hW⟩ := sorted_gen (fun i : Fin sk.length => sk[i]) τ
      (fun p₁ p₂ => SqlEquiv.compareByOrderItemsParam
        (fun db' r e => SqlEquiv.evalExprWithDb db' r e) db (p₁.1 ++ p₁.2) (p₂.1 ++ p₂.2)
        (SqlEquiv.groupOrderByItems orderBy)) PR
      (fun x y hxy i => by
        show (x.1 i).HasType (Γa (idx i))
        rw [hxy.2 i]; exact hxy.1.2.2 (idx i))
      (fun x₁ y₁ x₂ y₂ h₁ h₂ => by
        apply compareBy_agree' _ db _ _ _ (by rw [length_groupOrderByItems]; exact hlo)
        intro i
        obtain ⟨v₁, hv₁, hr₁⟩ := h₁.1.2.1 i
        obtain ⟨v₂, hv₂, hr₂⟩ := h₂.1.2.1 i
        rw [hv₁, hv₂, h₁.2 i, h₂.2 i]
        refine cmpDatum_agree (sk[i]) _ ?_ ?_ hr₁ hr₂ ?_
        · rw [getElem_groupOrderByItems]; exact (hidx i).2.1
        · rw [getElem_groupOrderByItems]; exact (hidx i).2.2.1
        · rintro x y ⟨hx, -⟩
          have := h₁.1.2.2 (idx i)
          rw [hx] at this
          exact hτb h0 i (by simpa [Datum.HasType] using this.symm)) hPRz
    rw [hW1, List.map_map] at hout
    rw [hW2, List.map_map]
    exact mapM_rel_of (fun w hw d hd => (hW w hw).1.1 d hd) hout

/-- `elabStmt_correct_grouped_ctx` for the statement itself: no outer row. -/
theorem elabStmt_correct_grouped_w (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} {having : Option SqlEquiv.Expr}
    {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hgi : groupedItems items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hwo : ∀ {n : ℕ} (qf q₀ : Query N.S n) (cf : Fin n → Column),
      elabFrom N (fun sq => elabSubQuery N 15 sq) fr = .ok ⟨n, qf, cf⟩ →
      elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf wh = .ok q₀ →
      WhereOk cf N.fold db D wh qf q₀) (hhv : ∀ h ∈ having, havingFragment groupBy h = true)
    (hav : HavingAvgOk N D fr having)
    (hob : ∀ o ∈ orderBy, OrderKeyOk items groupBy o.expr) (hbf : BareOk N items groupBy having orderBy)
    (hnm : orderBy ≠ [] → ∀ it ∈ items, '.' ∉ (outName it).toList ∧
      ∀ k, (outName it).toLower ≠ SqlEquiv.groupOrderKeyName k)
    {e : Elaborated N.S}
    (h : elabStmt N (groupedStmt items fr wh groupBy having orderBy lim off) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupedStmt items fr wh groupBy having orderBy lim off)).2 =
        some out ∧ List.Forall₂ (OutRelI items) rs out := by
  obtain ⟨-, rs, hrs, hctx⟩ := elabStmt_correct_grouped_ctx N hfold hfoldCI hwn hfix hD hrel hgi hgb
    hgc hff hwo hhv hav hob hbf hnm h hnb
  refine ⟨rs, hrs, _, rfl, ?_⟩
  have := hctx []
  rw [SqlEquiv.evalSelectWithContext_eq_evalSelectCore] at this
  simp only [SqlEquiv.evalQuery]
  rw [SqlEquiv.evalSelect_eq_evalSelectCore]
  exact this

end SqlBridge.CorrectGrouped

/-! ### Steps 3b-1 to 3b-3 as instances of the unified statement -/

namespace SqlBridge.CorrectGroup
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGrouped

theorem groupedItems_of_groupItems {groupBy : List SqlEquiv.Expr} :
    ∀ {items : List SqlEquiv.SelectItem}, groupItems groupBy items = true → groupedItems items = true
  | [], _ => rfl
  | .exprItem e al :: rest, h => by
    simp only [groupItems, groupedItems, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    refine ⟨?_, groupedItems_of_groupItems h.2⟩
    rcases h.1 with h1 | h1
    · exact .inl (by simp [itemAggFragment, h1])
    · right; cases e <;> simp_all
  | .star _ :: _, h => by simp [groupItems] at h

/-- Items of steps 3b-1 to 3b-3 hold no `AVG`. -/
theorem noAvg_of_groupItems {groupBy : List SqlEquiv.Expr} :
    ∀ {items : List SqlEquiv.SelectItem}, groupItems groupBy items = true →
      ∀ it ∈ items, CorrectAvg.avgFragment (itemExpr it) = false
  | [], _, _, hit => by simp at hit
  | .exprItem e al :: rest, h, it, hit => by
    simp only [groupItems, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases List.mem_cons.mp hit with rfl | hit
    · rcases h.1 with h1 | h1
      · exact avgFragment_false_of_agg h1
      · cases e <;> simp_all [itemExpr, CorrectAvg.avgFragment]
    · exact noAvg_of_groupItems h.2 it hit
  | .star _ :: _, h, _, _ => by simp [groupItems] at h

/-- `elabStmt_correct_grouped_w` with a `WHERE` in the expression fragment. -/
theorem elabStmt_correct_grouped (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} {having : Option SqlEquiv.Expr}
    {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hgi : groupedItems items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hw : ∀ w ∈ wh, isFragment w = true) (hhv : ∀ h ∈ having, havingFragment groupBy h = true)
    (hav : HavingAvgOk N D fr having)
    (hob : ∀ o ∈ orderBy, OrderKeyOk items groupBy o.expr) (hbf : BareOk N items groupBy having orderBy)
    (hnm : orderBy ≠ [] → ∀ it ∈ items, '.' ∉ (outName it).toList ∧
      ∀ k, (outName it).toLower ≠ SqlEquiv.groupOrderKeyName k)
    {e : Elaborated N.S}
    (h : elabStmt N (groupedStmt items fr wh groupBy having orderBy lim off) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupedStmt items fr wh groupBy having orderBy lim off)).2 =
        some out ∧ List.Forall₂ (OutRelI items) rs out :=
  elabStmt_correct_grouped_w N hfold hfoldCI hwn hfix hD hrel hgi hgb hgc hff
    (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq) hhv hav hob hbf hnm h hnb

/-- **Elaborator correctness for `GROUP BY` (#352, roadmap step 3b-1).** For
    `SELECT … FROM f [WHERE p] GROUP BY c₁, …, cₘ`, with column keys and every item either a key
    column or an aggregate of step 3a, and `f` a `FROM` tree of step 2: when the statement
    elaborates, the typed query's groups relate, in order, to `SqlEquiv`'s. An instance of
    `elabStmt_correct_grouped`. -/
theorem elabStmt_correct_group (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} (hgi : groupItems groupBy items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hw : ∀ w ∈ wh, isFragment w = true)
    {e : Elaborated N.S} (h : elabStmt N (groupStmt items fr wh groupBy) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupStmt items fr wh groupBy)).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  obtain ⟨rs, hrs, out, hout, hr⟩ :=
      elabStmt_correct_grouped N hfold hfoldCI hwn hfix hD hrel (groupedItems_of_groupItems hgi) hgb hgc
      hff hw (by simp) (havingAvgOk_of_noAvg (by simp)) (by simp) (.inl (colRefs_mem hgi)) (by simp) h hnb
  exact ⟨rs, hrs, out, hout, hr.imp fun _ _ h => outRel_of_outRelI (noAvg_of_groupItems hgi) h⟩

/-- **Elaborator correctness for `GROUP BY … HAVING` (#352, roadmap step 3b-2).** As
    `elabStmt_correct_group`, with a `HAVING` predicate of literals, key columns, aggregates of
    step 3a, comparisons, `AND`, `OR` and `NOT` (`havingFragment`): the groups it keeps relate, in
    order. An instance of `elabStmt_correct_grouped`. -/
theorem elabStmt_correct_having (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} (hgi : groupItems groupBy items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hw : ∀ w ∈ wh, isFragment w = true) {hav : SqlEquiv.Expr}
    (hhv : havingFragment groupBy hav = true) (havg : HavingAvgOk N D fr (some hav))
    {e : Elaborated N.S} (h : elabStmt N (groupStmt items fr wh groupBy (some hav)) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupStmt items fr wh groupBy (some hav))).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  obtain ⟨rs, hrs, out, hout, hr⟩ :=
      elabStmt_correct_grouped N hfold hfoldCI hwn hfix hD hrel (groupedItems_of_groupItems hgi) hgb hgc
      hff hw (fun h hh => by cases hh; exact hhv) havg (by simp) (.inl (colRefs_mem hgi)) (by simp) h hnb
  exact ⟨rs, hrs, out, hout, hr.imp fun _ _ h => outRel_of_outRelI (noAvg_of_groupItems hgi) h⟩

end SqlBridge.CorrectGroup

namespace SqlBridge.CorrectGroupOrder
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg SqlBridge.CorrectGroup SqlBridge.CorrectGrouped

/-- **Elaborator correctness for `GROUP BY … ORDER BY` aggregates (#352, roadmap step 3b-3).** For
    `SELECT … FROM f [WHERE p] GROUP BY c₁, …, cₘ ORDER BY a₁, … [LIMIT n] [OFFSET m]`, the items
    and keys as in `elabStmt_correct_group`, every sort key an aggregate of step 3a, and no output
    name able to capture `SqlEquiv`'s sort-key columns: when the statement elaborates, the typed
    query's rows relate, in order, to `SqlEquiv`'s. An instance of `elabStmt_correct_grouped`. -/
theorem elabStmt_correct_group_ordered (N : NamedSchema)
    (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {fr : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hgi : groupItems groupBy items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment fr = true)
    (hw : ∀ w ∈ wh, isFragment w = true)
    (hob : ∀ o ∈ orderBy, aggFragment o.expr = true)
    (hnm : ∀ it ∈ items, '.' ∉ (outName it).toList ∧
      ∀ k, (outName it).toLower ≠ SqlEquiv.groupOrderKeyName k)
    {e : Elaborated N.S}
    (h : elabStmt N (groupOrderStmt items fr wh groupBy orderBy lim off) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (groupOrderStmt items fr wh groupBy orderBy lim off)).2 =
        some out ∧ List.Forall₂ OutRel rs out := by
  obtain ⟨rs, hrs, out, hout, hr⟩ :=
    elabStmt_correct_grouped N hfold hfoldCI hwn hfix hD hrel (groupedItems_of_groupItems hgi) hgb
      hgc hff hw (by simp) (havingAvgOk_of_noAvg (by simp)) (fun o ho => .inl (hob o ho)) (.inl (colRefs_mem hgi)) (fun _ => hnm) h hnb
  exact ⟨rs, hrs, out, hout, hr.imp fun _ _ h => outRel_of_outRelI (noAvg_of_groupItems hgi) h⟩

end SqlBridge.CorrectGroupOrder
