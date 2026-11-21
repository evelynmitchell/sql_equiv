/-
  Elaborator correctness with joins (#352, roadmap step 2).

  Extends `elabStmt_correct_ordered` from one table to a `FROM` tree of tables under inner joins
  (with or without a fragment `ON`) and cross joins without `ON`:

  * Rows: `KeyedRow` records how `SqlEquiv`'s `FROM` keys a row (`Q.name` per column, `Q` the
    table name or alias as written); unlike `RowRel` it composes under `++` (`KeyedRow.append`),
    and it implies `RowRel` when the fold identifies exactly the names equal ignoring case and
    column names are their own folds (`rowRel_of_keyed`).
  * Joins: `SqlEquiv`'s inner join is the cross product, left row outermost, filtered by `ON`
    (`evalFrom_join_filter`), as is the typed `Query.join` (`product_rel`, `filter_rel_of`).
  * The `FROM` tree (`fromFragment`, `from_rel`) and the statement (`elabStmt_correct_join`),
    whose projection, `WHERE`, `ORDER BY` and `LIMIT`/`OFFSET` reuse `SqlBridge.CorrectOrder`.
    Roadmap and coverage in `docs/TYPED_CORE_PLAN.md`; examples in
    `SqlCoreTest/CorrectExamples.lean`.
-/
import SqlBridge.CorrectOrder

namespace SqlBridge.CorrectJoin
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder

section Keyed

variable {n : ℕ} (fold : String → String)

/-- A source row as `SqlEquiv`'s `FROM` builds it: column `j` is keyed `Q j.name_j`, with `Q j` the
    table name or alias as written, and the typed column is qualified by `fold (Q j)`. Unlike
    `RowRel`, this composes under joins (`KeyedRow.append`). -/
def KeyedRow (cols : Fin n → Column) (r : Row n) (u : SqlEquiv.Row) : Prop :=
  ∃ (Q : Fin n → String) (w : Fin n → SqlEquiv.Value),
    u = List.ofFn (fun j => (s!"{Q j}.{(cols j).name}", w j)) ∧
    (∀ j, (cols j).qualifier = some (fold (Q j))) ∧ ∀ j, DatumRel (r j) (w j)

theorem KeyedRow.append {m : ℕ} {c₁ : Fin n → Column} {c₂ : Fin m → Column} {r₁ : Row n}
    {r₂ : Row m} {u₁ u₂ : SqlEquiv.Row} (h₁ : KeyedRow fold c₁ r₁ u₁) (h₂ : KeyedRow fold c₂ r₂ u₂) :
    KeyedRow fold (Fin.append c₁ c₂) (Fin.append r₁ r₂) (u₁ ++ u₂) := by
  obtain ⟨Q₁, w₁, rfl, hq₁, hw₁⟩ := h₁
  obtain ⟨Q₂, w₂, rfl, hq₂, hw₂⟩ := h₂
  refine ⟨Fin.append Q₁ Q₂, Fin.append w₁ w₂, ?_, ?_, ?_⟩
  · rw [← List.ofFn_fin_append]
    congr 1
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hq₁, hq₂]
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hw₁, hw₂]

theorem keyed_table {m : ℕ} (Q : String) (base : Fin m → Column) (r : Row m)
    (w : Fin m → SqlEquiv.Value) (hw : ∀ j, DatumRel (r j) (w j)) :
    KeyedRow fold (requalify (fold Q) base) r
      (List.ofFn fun j => (s!"{Q}.{(base j).name}", w j)) :=
  ⟨fun _ => Q, w, rfl, fun _ => rfl, hw⟩

/-- On keyed rows, a reference the elaborator resolves finds the related value through
    `SqlEquiv`'s lookup, provided the fold identifies exactly the names equal ignoring case, and
    column names have no dots and are their own folds (Spider's lowercased names under
    `String.toLower`). Several tables may share column names: the elaborator then rejects an
    unqualified reference as ambiguous, and `SqlEquiv` would find two keys. -/
theorem rowRel_of_keyed (hfold : ∀ s, (fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, fold x = fold y ↔ x.toLower = y.toLower) {cols : Fin n → Column}
    (hfix : ∀ j, fold (cols j).name = (cols j).name) (hdot : ∀ j, '.' ∉ (cols j).name.toList)
    {r : Row n} {u : SqlEquiv.Row} (h : KeyedRow fold cols r u) : RowRel cols fold r u := by
  obtain ⟨Q, w, rfl, hq, hw⟩ := h
  intro q name i hres
  obtain ⟨hm, huniq⟩ := resolveColumn_eq_ok_iff.mp hres
  have hname : (cols i).name = fold name := hm.1
  have hnl : name.toLower = (cols i).name.toLower := by rw [hname, hfold]
  -- a column whose name equals `name` ignoring case is named `fold name`
  have hnm : ∀ j, (cols j).name.toList.map Char.toLower = name.toList.map Char.toLower →
      (cols j).name = fold name := by
    intro j hj
    have : (cols j).name.toLower = name.toLower :=
      String.toList_inj.mp (by simpa [toList_toLower] using hj)
    rw [← hfix j]; exact (hfoldCI _ _).mpr this
  have hd := dot_not_mem_map_toLower (hdot i)
  refine ⟨w i, ?_, hw i⟩
  cases q with
  | some q' =>
    have hqi : (Q i).toLower = q'.toLower := by
      have h1 := hm.2 (fold q') rfl
      rw [hq i] at h1
      exact (hfoldCI _ _).mp (Option.some.inj h1)
    have hkey : (s!"{q'}.{name}").toLower = (s!"{Q i}.{(cols i).name}").toLower := by
      apply String.toList_inj.mp
      have h1 := congrArg String.toList hqi
      have h2 := congrArg String.toList hnl
      simp only [toList_toLower] at h1 h2
      simp only [toList_toLower, toList_qualified, List.map_append, List.map_cons, toLower_dot,
        h1, h2]
    simp only [SqlEquiv.Row.getQualified, lookupCI_eq_find?]
    rw [hkey, find?_ofFn_of_unique _ _ i]
    · rfl
    · simp
    · intro j hj
      have := String.toList_inj.mpr (beq_iff_eq.mp hj)
      simp only [toList_toLower, toList_qualified, List.map_append, List.map_cons, toLower_dot] at this
      have hn := eq_of_append_dot (dot_not_mem_map_toLower (hdot j)) hd this
      have hnj : (cols j).name = fold name := hnm j (by
        rw [hn]; have := congrArg String.toList hnl; simpa [toList_toLower] using this.symm)
      rw [hn] at this
      have hQ := List.append_cancel_right this
      have hQl : (Q j).toLower = (Q i).toLower := String.toList_inj.mp (by simpa [toList_toLower] using hQ)
      apply huniq j
      refine ⟨hnj, fun q'' hq'' => ?_⟩
      simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hq''
      subst hq''
      rw [hq j, (hfoldCI _ _).mpr hQl, ← hq i]
      exact hm.2 _ rfl
  | none =>
    simp only [SqlEquiv.Row.getQualified]
    rw [hnl]
    rw [find?_ofFn_of_unique _ _ i]
    · simp only [Bool.or_eq_true, endsWith_iff_suffix]
      right
      simp only [toString, String.toList_append, toList_toLower, List.map_append, toList_dot,
        List.map_cons, toLower_dot, List.append_assoc, List.singleton_append]
      exact List.suffix_append _ _
    · intro j hj
      simp only [Bool.or_eq_true, beq_iff_eq, endsWith_iff_suffix] at hj
      rcases hj with h | ⟨t, ht⟩
      · have := congrArg String.toList h
        simp only [toString, String.toList_append, toList_toLower, List.map_append,
          toList_dot, List.map_cons, toLower_dot, List.append_assoc, List.singleton_append] at this
        exact absurd (this ▸ List.mem_append_right _ List.mem_cons_self) hd
      · simp only [toString, String.toList_append, toList_toLower, List.map_append,
          toList_dot, List.map_cons, toLower_dot, List.append_assoc, List.singleton_append] at ht
        have hn := eq_of_append_dot (dot_not_mem_map_toLower (hdot j)) hd ht.symm
        apply huniq j
        refine ⟨hnm j (by
          rw [hn]; have := congrArg String.toList hnl; simpa [toList_toLower] using this.symm), ?_⟩
        simp

end Keyed

end SqlBridge.CorrectJoin

namespace SqlBridge.CorrectJoin
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder

/-- `SqlEquiv`'s inner join (or cross join without `ON`): the cross product, left row outermost,
    filtered by the `ON` condition. -/
theorem evalFrom_join_filter (db : SqlEquiv.Database) (l r : SqlEquiv.FromClause)
    (kind : SqlEquiv.JoinType) (on : Option SqlEquiv.Expr)
    (hk : kind = .inner ∨ (kind = .cross ∧ on = none)) :
    SqlEquiv.evalFrom db (.join l kind r on) =
      ((SqlEquiv.evalFrom db l).flatMap fun lr => (SqlEquiv.evalFrom db r).map (lr ++ ·)).filter
        fun u => on.all fun e => SqlEquiv.evalExprWithDb db u e == some (.bool true) := by
  rcases hk with rfl | ⟨rfl, rfl⟩
  · rw [SqlEquiv.evalFrom_inner_join, List.filter_flatMap]
    dsimp only
    congr 1; funext lr
    cases on with
    | none => simp
    | some c =>
      induction SqlEquiv.evalFrom db r with
      | nil => rfl
      | cons rr rest ih =>
        simp only [List.filterMap_cons, List.map_cons, List.filter_cons, Option.all_some] at ih ⊢
        rw [ih]
        rcases hv : SqlEquiv.evalExprWithDb db (lr ++ rr) c with _ | v
        · simp
        · cases v with
          | bool b => cases b <;> simp
          | _ => simp
  · rw [SqlEquiv.evalFrom_cross_join]
    simp

section Rows
variable (fold : String → String)

/-- Related inputs give related cross products, in the same order. -/
theorem product_rel {n m : ℕ} {c₁ : Fin n → Column} {c₂ : Fin m → Column} {Γ : Fin n → SqlType}
    {Δ : Fin m → SqlType} {R₂ : List (Row m)} {U₂ : List SqlEquiv.Row}
    (h₂ : List.Forall₂ (fun r u => KeyedRow fold c₂ r u ∧ r.Conforms Δ) R₂ U₂) :
    ∀ {R₁ : List (Row n)} {U₁ : List SqlEquiv.Row},
      List.Forall₂ (fun r u => KeyedRow fold c₁ r u ∧ r.Conforms Γ) R₁ U₁ →
      List.Forall₂ (fun r u => KeyedRow fold (Fin.append c₁ c₂) r u ∧ r.Conforms (Fin.append Γ Δ))
        (Row.product R₁ R₂) (U₁.flatMap fun lr => U₂.map (lr ++ ·))
  | _, _, .nil => by simp [Row.product]
  | r :: R₁, u :: U₁, .cons hru hrest => by
    have ih := product_rel h₂ hrest
    simp only [Row.product, List.product_cons, List.map_append, List.map_map, List.flatMap_cons] at ih ⊢
    refine List.rel_append ?_ ih
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine h₂.imp fun r₂ u₂ h => ⟨hru.1.append fold h.1, ?_⟩
    exact Row.conforms_append_iff.mpr ⟨hru.2, h.2⟩

variable {n : ℕ} (cols : Fin n → Column)

/-- `filter_rel` for any relation that implies `RowRel` and conformance (here, keyed rows). -/
theorem filter_rel_of (db : SqlEquiv.Database) {Γ : Fin n → SqlType} {w : SqlEquiv.Expr}
    {p : Expr n} (ht : Translates cols fold w p) (hnb : NoBoolOrder Γ p)
    {P : Row n → SqlEquiv.Row → Prop} (hP : ∀ r u, P r u → RowRel cols fold r u ∧ r.Conforms Γ) :
    ∀ {R : List (Row n)} {U : List SqlEquiv.Row}, List.Forall₂ P R U →
      ∀ {R' : List (Row n)}, p.filterRows R = .ok R' →
      List.Forall₂ P R' (U.filter fun u => SqlEquiv.evalExprWithDb db u w == some (.bool true))
  | _, _, .nil, R', h => by
    simp only [Expr.filterRows, List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | r :: R, u :: U, .cons hru hrest, R', h => by
    obtain ⟨t, R'', hte, hrs, rfl⟩ := filterRows_cons_ok h
    have ih := filter_rel_of db ht hnb hP hrest hrs
    have hev : ∃ d, p.eval r = .ok d ∧ d.toTruth = .ok t := by
      unfold Expr.evalTruth at hte
      rcases he : p.eval r with _ | d
      · simp [he, bind, Except.bind] at hte
      · simp only [he, bind, Except.bind] at hte
        exact ⟨d, rfl, hte⟩
    obtain ⟨d, hd, hdt⟩ := hev
    obtain ⟨v, hv, hrel⟩ :=
      Translates.eval_rel cols fold db (hP _ _ hru).1 (hP _ _ hru).2 ht hnb hd
    have key := isTrue_iff_where hrel hdt
    rw [← hv] at key
    simp only [List.filter_cons, ← key]
    cases t.isTrue
    · exact ih
    · exact .cons hru ih

end Rows

end SqlBridge.CorrectJoin

namespace SqlBridge.CorrectJoin
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder

/-- `FROM` clauses of roadmap step 2: base tables, inner joins (`ON` a fragment condition, or none)
    and cross joins, nested. -/
def fromFragment : SqlEquiv.FromClause → Bool
  | .table _ => true
  | .join l .inner r on => fromFragment l && fromFragment r && on.all isFragment
  | .join l .cross r none => fromFragment l && fromFragment r
  | _ => false

theorem join_kind {l r : SqlEquiv.FromClause} {kind : SqlEquiv.JoinType} {on : Option SqlEquiv.Expr}
    (h : fromFragment (.join l kind r on) = true) :
    fromFragment l = true ∧ fromFragment r = true ∧ (∀ e ∈ on, isFragment e = true) ∧
      (kind = .inner ∨ (kind = .cross ∧ on = none)) := by
  cases kind <;> cases on <;> simp_all [fromFragment]

variable (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
  (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
  (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
  {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
  (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S))

include hfold hfoldCI hwn hfix hD hrel in
/-- A `FROM` tree of tables, inner and cross joins: its elaboration evaluates to rows keyed as
    `SqlEquiv`'s `FROM` builds them, in the same order. -/
theorem from_rel : ∀ (f : SqlEquiv.FromClause), fromFragment f = true →
    ∀ {e : Elaborated N.S}, elabFrom N sub f = .ok e →
    (∀ j, N.fold (e.cols j).name = (e.cols j).name ∧ '.' ∉ (e.cols j).name.toList) ∧
    ∀ {Γ}, e.q.typeOf = some Γ → QNoBoolOrder e.q →
      e.q.divSafe = true ∧ ∃ R, e.q.eval D = .ok R ∧
        List.Forall₂ (fun r u => KeyedRow N.fold e.cols r u ∧ r.Conforms Γ) R
          (SqlEquiv.evalFrom db f)
  | .table ⟨name, al⟩, _, e, h => by
    rcases hT : N.tables.find? (fun x => x.1 == N.fold name) with _ | ⟨nm, T⟩
    · simp [elabFrom, lookupTable, hT, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    have hmem : (N.fold name, T) ∈ N.tables := by
      have h1 := List.mem_of_find?_eq_some hT
      have h2 := List.find?_some hT
      simp only [beq_iff_eq] at h2; subst h2; exact h1
    simp only [elabFrom, lookupTable, hT, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨fun j => ⟨hfix T j, hwn.noDot T j⟩, fun {Γ} hΓ _ => ⟨rfl, D T, rfl, ?_⟩⟩
    simp only [Query.typeOf_table, Option.some.injEq] at hΓ
    subst hΓ
    rw [SqlEquiv.evalFrom_table]
    refine forall₂_and_left ?_ (fun r hr => hD T r hr)
    rw [List.forall₂_map_right_iff]
    refine (hrel name T hmem).imp ?_
    rintro r u ⟨w, rfl, hw⟩
    simp only [List.map_ofFn]
    exact keyed_table N.fold _ _ r w hw
  | .join l kind r on, hf, e, h => by
    obtain ⟨hl, hr, hon, hk⟩ := join_kind hf
    rw [elabFrom] at h
    obtain ⟨⟨n, ql, cl⟩, hel, h⟩ := bind_ok h
    obtain ⟨⟨m, qr, cr⟩, her, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hnl, ihl⟩ := from_rel l hl hel
    obtain ⟨hnr, ihr⟩ := from_rel r hr her
    have hnames : ∀ j, N.fold ((Fin.append cl cr) j).name = ((Fin.append cl cr) j).name ∧
        '.' ∉ ((Fin.append cl cr) j).name.toList := fun j =>
      Fin.addCases (fun i => by simpa using hnl i) (fun i => by simpa using hnr i) j
    -- the join condition translates, and filters as `SqlEquiv`'s `ON` does
    have hθw : ∃ θ w, e = ⟨n + m, .join θ ql qr, Fin.append cl cr⟩ ∧
        Translates (Fin.append cl cr) N.fold w θ ∧ ∀ u,
        (on.all fun e => SqlEquiv.evalExprWithDb db u e == some (.bool true)) =
          (SqlEquiv.evalExprWithDb db u w == some (.bool true)) := by
      rcases hk with rfl | ⟨rfl, rfl⟩
      · cases on with
        | none =>
          simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
          exact ⟨_, .lit (.bool true), h.symm, .lit rfl, fun u => by simp [SqlEquiv.evalExprWithDb_lit]⟩
        | some c =>
          obtain ⟨θ, hθ, h⟩ := bind_ok h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          exact ⟨θ, c, h.symm, translates_of_elab _ _ c (hon c rfl) hθ, fun u => by simp⟩
      · simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
        exact ⟨_, .lit (.bool true), h.symm, .lit rfl, fun u => by simp [SqlEquiv.evalExprWithDb_lit]⟩
    obtain ⟨θ, w, rfl, htr, hfil⟩ := hθw
    refine ⟨hnames, fun {Γ} hΓ hnb => ?_⟩
    obtain ⟨Γ₁, Δ, h₁, h₂, hθty, rfl⟩ := Query.typeOf_join_eq_some.mp hΓ
    obtain ⟨hθnb, hnb₁, hnb₂⟩ := hnb
    obtain ⟨hd₁, R₁, hR₁, hrel₁⟩ := ihl h₁ hnb₁
    obtain ⟨hd₂, R₂, hR₂, hrel₂⟩ := ihr h₂ hnb₂
    have hdiv : (Query.join θ ql qr).divSafe = true := by
      simp [Query.divSafe, Translates.divSafe _ _ htr, hd₁, hd₂]
    obtain ⟨R, hR⟩ := Query.IsSafe.exists_eval_eq_ok (q := Query.join θ ql qr) ⟨by simp [hΓ], hdiv⟩ hD
    refine ⟨hdiv, R, hR, ?_⟩
    rw [Query.eval_join, hR₁, hR₂] at hR
    simp only [bind, Except.bind] at hR
    rw [evalFrom_join_filter db l r kind on hk]
    simp only [hfil]
    refine filter_rel_of N.fold (Fin.append cl cr) db htr (hθnb Γ₁ Δ h₁ h₂) ?_
      (product_rel N.fold hrel₂ hrel₁) hR
    intro r u hru
    exact ⟨rowRel_of_keyed N.fold hfold hfoldCI (fun j => (hnames j).1) (fun j => (hnames j).2) hru.1,
      hru.2⟩
  | .subquery _ _, hf, _, _ => by simp [fromFragment] at hf

end SqlBridge.CorrectJoin

namespace SqlBridge.CorrectJoin
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder

/-- The statements of roadmap steps 1 and 2:
    `SELECT e₁, …, eₖ FROM f [WHERE p] [ORDER BY …] [LIMIT n] [OFFSET m]`. -/
def joinStmt (items : List SqlEquiv.SelectItem) (f : SqlEquiv.FromClause)
    (wh : Option SqlEquiv.Expr) (orderBy : List SqlEquiv.OrderByItem) (lim off : Option ℕ) :
    SqlEquiv.Stmt :=
  .query (.simple (.mk false items (some f) wh [] none orderBy lim off))

theorem elab_join_shape (N : NamedSchema) {items : List SqlEquiv.SelectItem}
    {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} {orderBy : List SqlEquiv.OrderByItem}
    {lim off : Option ℕ} (hit : itemsFragment items = true) (hw : ∀ w ∈ wh, isFragment w = true)
    (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c) {e : Elaborated N.S}
    (h : elabStmt N (joinStmt items f wh orderBy lim off) = .ok e) :
    e.q.typeOf.isSome ∧ ∃ sub n, ∃ qf : Query N.S n, ∃ cf, elabFrom N sub f = .ok ⟨n, qf, cf⟩ ∧
      ∃ q₀ : Query N.S n,
        ((wh = none ∧ q₀ = qf) ∨ ∃ w p, wh = some w ∧
          elabExpr cf N.fold noHook w = .ok p ∧ q₀ = .select p qf) ∧
      ∃ its, elabItems N cf items = .ok its ∧
      ∃ keyList, orderBy.mapM (elabOrderKey N.fold (elabExpr cf N.fold noHook) its) = .ok keyList ∧
        e = ⟨its.length, limitWrap lim off
          (if keyList.length = 0 then .project (fun i => (its[i]).1) q₀
           else .project (fun i => (its[i]).1)
             (.orderBy (fun i : Fin keyList.length => keyList[i]) q₀)),
          fun i => (its[i]).2⟩ := by
  simp only [joinStmt, elabStmt, elabQuery, bind, Except.bind] at h
  rcases hraw : elabQueryRaw N (.simple (.mk false items (some f) wh [] none
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
  obtain ⟨⟨n, qf, cf⟩, hf, hraw⟩ := bind_ok hraw
  refine ⟨_, n, qf, cf, hf, ?_⟩
  dsimp only at hraw
  cases wh with
  | none =>
    simp only [pure, Except.pure, bind, Except.bind] at hraw
    rw [aggsOfList_map_cols _ _ ?hm, aggsOfList_items ?hf items hit] at hraw
    case hm => exact hcols'
    case hf => intros; rfl
    simp only [List.isEmpty_nil, aggsOfOpt, List.append_nil, List.eraseDups_nil, Option.isNone_none,
      Bool.and_self, ↓reduceIte] at hraw
    rcases hits : elabItems N cf items with _ | its
    · simp [hits] at hraw
    simp only [hits] at hraw
    obtain ⟨keyList, hk, he⟩ := finishSelect_nondistinct N.fold _ orderBy lim off hraw
    exact ⟨qf, .inl ⟨rfl, rfl⟩, its, rfl, keyList, hk, he⟩
  | some w =>
    simp only [subsOf_frag w (hw w rfl), List.foldl_nil, List.isEmpty_nil, ↓reduceIte] at hraw
    rcases hp : elabExpr cf N.fold noHook w with _ | p
    · simp [hp, bind, Except.bind] at hraw
    simp only [hp, bind, Except.bind, pure, Except.pure] at hraw
    rw [aggsOfList_map_cols _ _ ?hm, aggsOfList_items ?hf items hit] at hraw
    case hm => exact hcols'
    case hf => intros; rfl
    simp only [List.isEmpty_nil, aggsOfOpt, List.append_nil, List.eraseDups_nil, Option.isNone_none,
      Bool.and_self, ↓reduceIte] at hraw
    rcases hits : elabItems N cf items with _ | its
    · simp [hits] at hraw
    simp only [hits] at hraw
    obtain ⟨keyList, hk, he⟩ := finishSelect_nondistinct N.fold _ orderBy lim off hraw
    exact ⟨.select p qf, .inr ⟨w, p, rfl, hp, rfl⟩, its, rfl, keyList, hk, he⟩

/-- **Elaborator correctness with joins (#352, roadmap step 2).** For
    `SELECT e₁, …, eₖ FROM f [WHERE p] [ORDER BY c₁, …] [LIMIT n] [OFFSET m]`, where `f` nests
    base tables (optionally aliased), inner joins (`ON` a fragment condition, or none) and cross
    joins: when the statement elaborates, the typed query evaluates, and its rows relate, in order,
    to `SqlEquiv`'s.

    Beyond `elabStmt_correct_ordered`'s hypotheses: the fold identifies exactly the names equal
    ignoring case (`hfoldCI`, now also for `ON`, `WHERE` and the items, since two tables may spell
    a qualifier alike up to case) and the schema's column names are their own folds (`hfix`), so a
    reference the elaborator finds unambiguously in the joined columns is the one `SqlEquiv`'s
    lookup finds first. Spider's schemas satisfy both (`String.toLower`, lowercased names). -/
theorem elabStmt_correct_join_ctx (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hit : itemsFragment items = true) (hff : fromFragment f = true)
    (hw : ∀ w ∈ wh, isFragment w = true) (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c)
    (hnamed : orderBy ≠ [] → itemsNamed items = true)
    {e : Elaborated N.S} (h : elabStmt N (joinStmt items f wh orderBy lim off) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (joinStmt items f wh orderBy lim off)).2 = some out ∧
        List.Forall₂ OutRel rs out ∧
        (orderBy = [] → ∀ ctx, List.Forall₂ OutRel rs
          (SqlEquiv.evalSelectWithContext db ctx (.mk false items (some f) wh [] none [] lim off))) := by
  obtain ⟨hty, sub, n, qf, cf, hf, q₀, hq₀, its, hits, keyList, hk, rfl⟩ :=
    elab_join_shape N hit hw hcols h
  obtain ⟨hnames, hfrom⟩ := from_rel N hfold hfoldCI hwn hfix hD hrel sub f hff hf
  simp only at hnames hfrom
  have hir := itemsRel_of_elab cf N items hit hits
  have hlen : orderBy.length = keyList.length := (mapM_forall₂ hk).length_eq
  simp only at hty hnb ⊢
  rw [typeOf_limitWrap] at hty
  rw [qnb_limitWrap] at hnb
  -- the source query below the `WHERE`
  have hsrc : ∀ Γ, q₀.typeOf = some Γ → qf.typeOf = some Γ := by
    intro Γ hΓ
    rcases hq₀ with ⟨-, rfl⟩ | ⟨w, p, -, -, rfl⟩
    · exact hΓ
    · exact (Query.typeOf_select_eq_some.mp hΓ).1
  have hnbsrc : QNoBoolOrder q₀ → QNoBoolOrder qf := by
    rcases hq₀ with ⟨-, rfl⟩ | ⟨w, p, -, -, rfl⟩
    · exact id
    · exact fun h => h.2
  -- typing and the boolean side conditions, with and without keys
  have hfacts : ∃ Γ, q₀.typeOf = some Γ ∧
      (∀ i : Fin its.length, NoBoolOrder Γ (its[i]).1) ∧ QNoBoolOrder q₀ ∧
      (keyList.length ≠ 0 → ∀ k ∈ keyList, ∃ τ, k.e.typeOf Γ = some τ ∧ τ ≠ .bool) := by
    by_cases hk0 : keyList.length = 0
    · simp only [hk0, ↓reduceIte] at hty hnb
      obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
      obtain ⟨Γ, hΓ, -⟩ := Query.typeOf_project_eq_some.mp hΔ
      exact ⟨Γ, hΓ, fun i => hnb.1 _ hΓ i, hnb.2, fun h => absurd hk0 h⟩
    · simp only [hk0, ↓reduceIte] at hty hnb
      obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
      obtain ⟨Γ, hΓ, -⟩ := Query.typeOf_project_eq_some.mp hΔ
      obtain ⟨hq, Δk, hΔk⟩ := Query.typeOf_orderBy_eq_some hΓ
      refine ⟨Γ, hq, fun i => hnb.1 _ hΓ i, hnb.2.2, fun _ k hk => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
      exact ⟨Δk ⟨i, hi⟩, hΔk ⟨i, hi⟩, fun hb => hnb.2.1 _ hq ⟨i, hi⟩ (by rw [hΔk ⟨i, hi⟩, hb])⟩
  obtain ⟨Γ, hq₀T, hnbIt, hnbq₀, hkty⟩ := hfacts
  obtain ⟨hdivf, Rf, hRf, hrelf⟩ := hfrom (hsrc Γ hq₀T) (hnbsrc hnbq₀)
  have hrows : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ) Rf
      (SqlEquiv.evalFrom db f) := hrelf.imp fun r u h =>
    ⟨rowRel_of_keyed N.fold hfold hfoldCI (fun j => (hnames j).1) (fun j => (hnames j).2) h.1, h.2⟩
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
    · exact hdivf
    · simp only [Query.divSafe, hdivf, Bool.and_true]
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
  -- the keys
  -- the keys
  have hkr : keyList.length ≠ 0 → KeysRel cf N.fold db Γ items orderBy hlen
      (fun i => keyList[i]) := fun hk0 => by
    have hne : orderBy ≠ [] := by intro h0; subst h0; simp at hlen; omega
    obtain ⟨_, hkr⟩ := keysRel_of_elab _ N.fold hfoldCI db hit (hnamed hne) hir
      (itemsNames_of_elab N _ items hit (hnamed hne) hits)
      (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        exact hnbIt ⟨i, hi⟩) hcols hk (hkty hk0)
    exact hkr
  refine ⟨rs, hrs, _, rfl, ?_, ?_⟩
  · -- `SqlEquiv`'s side, in closed form
    simp only [SqlEquiv.evalQuery]
    rw [SqlEquiv.evalSelect_eq_evalSelectCore, evalSelectCore_project_ordered _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ (selectHasAggregate_frag items hit) (selectHasWindowFn_frag items hit)]
    rcases hq₀ with ⟨rfl, rfl⟩ | ⟨w, p, rfl, hp, rfl⟩
    · exact finish_rel cf N.fold db Γ items orderBy hRf hrows hir hnbIt hlen hkr lim off hrs
    · have hR' := hR
      simp only [Query.eval_select, hRf, bind, Except.bind] at hR'
      have htp := translates_of_elab _ _ w (hw w rfl) hp
      have hfr := filter_rel _ _ db htp (hnbq₀.1 _ (hsrc Γ hq₀T)) hrows hR'
      exact finish_rel cf N.fold db Γ items orderBy hR hfr hir hnbIt hlen hkr lim off hrs
  · -- under an outer row (a subquery body): the `FROM` rows carry it at the end, where no lookup
    -- the elaborator resolved reaches it
    rintro rfl ctx
    rw [SqlEquiv.evalSelectWithContext_eq_evalSelectCore, evalSelectCore_project_ctx _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ (selectHasAggregate_frag items hit) (selectHasWindowFn_frag items hit)]
    have hrows' : List.Forall₂ (fun r u => RowRel cf N.fold r u ∧ r.Conforms Γ) Rf
        ((SqlEquiv.evalFrom db f).map fun row => row ++ ctx) := by
      rw [List.forall₂_map_right_iff]
      exact hrows.imp fun r u h => ⟨rowRel_append ctx h.1, h.2⟩
    rcases hq₀ with ⟨rfl, rfl⟩ | ⟨w, p, rfl, hp, rfl⟩
    · exact finish_rel cf N.fold db Γ items [] hRf hrows' hir hnbIt hlen hkr lim off hrs
    · have hR' := hR
      simp only [Query.eval_select, hRf, bind, Except.bind] at hR'
      have htp := translates_of_elab _ _ w (hw w rfl) hp
      have hfr := filter_rel _ _ db htp (hnbq₀.1 _ (hsrc Γ hq₀T)) hrows' hR'
      exact finish_rel cf N.fold db Γ items [] hR hfr hir hnbIt hlen hkr lim off hrs

/-- `elabStmt_correct_join_ctx` without the outer row. -/
theorem elabStmt_correct_join (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hit : itemsFragment items = true) (hff : fromFragment f = true)
    (hw : ∀ w ∈ wh, isFragment w = true) (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c)
    (hnamed : orderBy ≠ [] → itemsNamed items = true)
    {e : Elaborated N.S} (h : elabStmt N (joinStmt items f wh orderBy lim off) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (joinStmt items f wh orderBy lim off)).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  obtain ⟨rs, hrs, out, hout, hr, -⟩ := elabStmt_correct_join_ctx N hfold hfoldCI hwn hfix hD hrel
    hit hff hw hcols hnamed h hnb
  exact ⟨rs, hrs, out, hout, hr⟩

end SqlBridge.CorrectJoin
