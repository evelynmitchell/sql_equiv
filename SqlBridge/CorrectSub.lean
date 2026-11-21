/-
  Elaborator correctness for uncorrelated `IN` / `NOT IN` subqueries (#352, step 6b):
  `SELECT … FROM f WHERE e [NOT] IN (SELECT e' FROM f' [WHERE p']) …`.

  `SqlEquiv` re-evaluates the subquery body for every outer row, on rows `inner ++ outer`; the
  typed core evaluates it once and attaches the membership test to the input as a last column
  (`Query.attach`), filters on it and projects it away. The pieces:

  * the value: `eq_agree`, `inList_agree`, `inSub_agree` (the typed three-valued membership
    against `SqlEquiv`'s `inSubqueryResult`, `NULL`s included, whatever the order of the rows);
  * one row: `inExpr_eval_rel`; a filter by any predicate that relates row by row:
    `filter_rel_of`;
  * the elaborated clause: `elabWhere_inSub` (its shape), `attachFilter_rel` (the
    attach–filter–project pipeline keeps the rows `SqlEquiv` keeps);
  * the body: it elaborates the same with any fuel (`elabSelectF_fuel`) and gives the same
    result under every outer row (`elabStmt_correct_join_ctx`);
  * `whereOk_inSub`: the clause provides `WhereOk`, the hypothesis the statement theorems take
    for their `WHERE`; `elabStmt_correct_inSub`: the statement theorem for a plain outer query.
-/
import SqlBridge.CorrectSetOp

namespace SqlBridge.CorrectSub
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin

/-- The untyped value of a truth value. -/
def truthValue : Truth → SqlEquiv.Value
  | .true => .bool true
  | .false => .bool false
  | .unknown => .null none

theorem datumRel_truthValue (t : Truth) : DatumRel t.toDatum (truthValue t) := by
  cases t <;> first | exact ValRel.bool _ | exact ⟨none, rfl⟩

/-- One comparison `a = b` on related values: TRUE exactly when `SqlEquiv`'s `Value.eq` says so,
    unknown exactly when one side is `NULL`. -/
theorem eq_agree {a b : Datum} {a' b' : SqlEquiv.Value} (ha : DatumRel a a') (hb : DatumRel b b')
    {t : Truth} (h : CmpOp.eq.eval a b = .ok t) :
    (t = .true ↔ a'.eq b' = some true) ∧ (t = .unknown ↔ (a'.isNull || b'.isNull) = true) := by
  have h' : SqlCore.evalBinOp (.cmp .eq) a b = .ok t.toDatum := by
    simp [SqlCore.evalBinOp, h]
  obtain ⟨v, hv, hd⟩ := cmp_agree (op := .eq) rfl ha hb (fun h => absurd rfl h) h'
  cases a' <;> cases b' <;> cases t <;>
    simp_all [SqlEquiv.evalBinOp, SqlEquiv.Value.isNull, SqlEquiv.Value.eq, DatumRel,
      Truth.toDatum] <;>
    first
      | done
      | (cases hd; simp_all)

/-- A subquery's rows as `SqlEquiv` reads them under `IN`: one column each, its value related
    to the typed row's. (`OutRel` on one-column rows.) -/
def SubRowRel (s : Datum) (row : SqlEquiv.Row) : Prop :=
  ∃ nm val, row = [(nm, val)] ∧ DatumRel s val

theorem subRowRel_of_outRel {r : Row 1} {u : SqlEquiv.Row} (h : OutRel r u) :
    SubRowRel (r 0) u := by
  unfold OutRel at h
  match u, h with
  | [(nm, val)], h =>
    simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
      List.forall₂_cons, List.Forall₂.nil, and_true] at h
    exact ⟨nm, val, rfl, h⟩

/-- **`IN` over a subquery's values.** With the probe and the values related, the typed
    three-valued membership is TRUE exactly when `SqlEquiv` finds a match, and unknown exactly
    when it finds none and a `NULL` takes part. -/
theorem inList_agree {d : Datum} {v : SqlEquiv.Value} (hd : DatumRel d v) :
    ∀ {ss : List Datum} {rows : List SqlEquiv.Row}, List.Forall₂ SubRowRel ss rows →
      ∀ {t : Truth}, d.inList ss = .ok t →
        (t = .true ↔ SqlEquiv.inSubqueryMatch v rows = true) ∧
        (t = .unknown ↔ SqlEquiv.inSubqueryMatch v rows = false ∧
          SqlEquiv.inSubqueryHasNull v rows = true)
  | [], [], .nil, t, h => by
    simp only [Datum.inList_nil, Except.ok.injEq] at h
    subst h
    simp [SqlEquiv.inSubqueryMatch, SqlEquiv.inSubqueryHasNull]
  | s :: ss, row :: rows, .cons hrow hrest, t, h => by
    obtain ⟨nm, val, rfl, hsv⟩ := hrow
    rw [Datum.inList_cons] at h
    obtain ⟨t₁, ht₁, h⟩ := SqlBridge.CorrectOrder.bind_ok h
    obtain ⟨t₂, ht₂, h⟩ := SqlBridge.CorrectOrder.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hm₁, hn₁⟩ := eq_agree hd hsv ht₁
    obtain ⟨hm₂, hn₂⟩ := inList_agree hd hrest ht₂
    have hM : SqlEquiv.inSubqueryMatch v ([(nm, val)] :: rows) =
        (v.eq val == some true || SqlEquiv.inSubqueryMatch v rows) := by
      simp [SqlEquiv.inSubqueryMatch]
    have hH : SqlEquiv.inSubqueryHasNull v ([(nm, val)] :: rows) = true ↔
        (v.isNull || val.isNull) = true ∨ SqlEquiv.inSubqueryHasNull v rows = true := by
      simp only [SqlEquiv.inSubqueryHasNull, List.isEmpty_cons, Bool.not_false, Bool.and_true,
        List.any_cons, List.head?_cons, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
      tauto
    rw [hM]
    constructor
    · rw [Truth.sup_eq_true_iff, hm₁, hm₂]
      simp
    · have hu : t₁ ⊔ t₂ = .unknown ↔ t₁ ≠ .true ∧ t₂ ≠ .true ∧ (t₁ = .unknown ∨ t₂ = .unknown) := by
        cases t₁ <;> cases t₂ <;> decide
      rw [hu, hH, hn₁, hn₂, Ne, hm₁, Ne, hm₂]
      cases hveq : v.eq val == some true <;>
        cases hmr : SqlEquiv.inSubqueryMatch v rows <;> simp_all

/-- So the typed result is the datum of `SqlEquiv`'s `inSubqueryResult`, for `IN` and `NOT IN`. -/
theorem inSub_agree {d : Datum} {v : SqlEquiv.Value} (hd : DatumRel d v) {ss : List Datum}
    {rows : List SqlEquiv.Row} (hss : List.Forall₂ SubRowRel ss rows) {t : Truth}
    (h : d.inList ss = .ok t) (neg : Bool) :
    DatumRel (if neg then t.not.toDatum else t.toDatum) (SqlEquiv.inSubqueryResult neg v rows) := by
  obtain ⟨hm, hu⟩ := inList_agree hd hss h
  unfold SqlEquiv.inSubqueryResult
  cases t <;> cases neg <;>
    cases hM : SqlEquiv.inSubqueryMatch v rows <;>
    cases hH : SqlEquiv.inSubqueryHasNull v rows <;>
    simp_all [Truth.not, Truth.toDatum, DatumRel] <;>
    exact ValRel.bool _

/-! ### Part 3: the predicate, row by row -/

section Pred
variable {n : ℕ} (cols : Fin n → Column) (fold : String → String)

/-- The typed expression of `e [NOT] IN (vals)`, as `SubKind.extra` builds it. -/
def inExpr (neg : Bool) (e' : Expr n) (vals : List Datum) : Expr n :=
  if neg then .unary .not (.inList e' vals) else .inList e' vals

/-- **`e [NOT] IN (subquery)` on one row.** With the row related, the probe translated and the
    subquery's values related to the rows `SqlEquiv` computes for this outer row, the typed
    value relates to `SqlEquiv`'s. -/
theorem inExpr_eval_rel (db : SqlEquiv.Database) {Γ : Fin n → SqlType} {r : Row n}
    {u : SqlEquiv.Row} (hrow : RowRel cols fold r u) (hr : r.Conforms Γ)
    {e : SqlEquiv.Expr} {e' : Expr n} (ht : Translates cols fold e e') (hnb : NoBoolOrder Γ e')
    {neg : Bool} {sq : SqlEquiv.SubQuery} {vals : List Datum}
    (hsub : List.Forall₂ SubRowRel vals (SqlEquiv.evalSubQueryWithContext db u sq))
    {d : Datum} (h : (inExpr neg e' vals).eval r = .ok d) :
    ∃ v, SqlEquiv.evalExprWithDb db u (.inSubquery e neg sq) = some v ∧ DatumRel d v := by
  have key : ∃ de t, e'.eval r = .ok de ∧ de.inList vals = .ok t ∧
      d = if neg then t.not.toDatum else t.toDatum := by
    unfold inExpr at h
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, Expr.eval_inList] at h
      obtain ⟨de, hde, h⟩ := SqlBridge.CorrectOrder.bind_ok h
      obtain ⟨t, ht', h⟩ := SqlBridge.CorrectOrder.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨de, t, hde, ht', by simp [h]⟩
    · simp only [↓reduceIte, Expr.eval] at h
      obtain ⟨dl, hdl, h⟩ := SqlBridge.CorrectOrder.bind_ok h
      obtain ⟨de, hde, hdl⟩ := SqlBridge.CorrectOrder.bind_ok hdl
      obtain ⟨t, ht', hdl⟩ := SqlBridge.CorrectOrder.bind_ok hdl
      simp only [pure, Except.pure, Except.ok.injEq] at hdl
      subst hdl
      simp [SqlCore.evalUnOp, Except.map, Functor.map] at h
      exact ⟨de, t, hde, ht', by simp [h]⟩
  obtain ⟨de, t, hde, ht', rfl⟩ := key
  obtain ⟨v, hv, hd⟩ := Translates.eval_rel cols fold db hrow hr ht hnb hde
  refine ⟨SqlEquiv.inSubqueryResult neg v (SqlEquiv.evalSubQueryWithContext db u sq), ?_,
    inSub_agree hd hsub ht' neg⟩
  rw [SqlEquiv.evalExprWithDb_inSubquery, hv]

/-- `filter_rel` for any typed predicate that relates, row by row, to an untyped one. -/
theorem filter_rel_of {Γ : Fin n → SqlType} {x : Expr n}
    (pred : SqlEquiv.Row → Option SqlEquiv.Value)
    (hpt : ∀ r u, RowRel cols fold r u → r.Conforms Γ → ∀ d, x.eval r = .ok d →
      ∃ v, pred u = some v ∧ DatumRel d v) :
    ∀ {R : List (Row n)} {U : List SqlEquiv.Row},
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U →
      ∀ {R' : List (Row n)}, x.filterRows R = .ok R' →
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R'
        (U.filter fun u => pred u == some (.bool true))
  | _, _, .nil, R', h => by
    simp only [Expr.filterRows, List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | r :: R, u :: U, .cons hru hrest, R', h => by
    obtain ⟨t, R'', hte, hrs, rfl⟩ := filterRows_cons_ok h
    have ih := filter_rel_of pred hpt hrest hrs
    have hev : ∃ d, x.eval r = .ok d ∧ d.toTruth = .ok t := by
      unfold Expr.evalTruth at hte
      rcases he : x.eval r with _ | d
      · simp [he, bind, Except.bind] at hte
      · simp only [he, bind, Except.bind] at hte
        exact ⟨d, rfl, hte⟩
    obtain ⟨d, hd, hdt⟩ := hev
    obtain ⟨v, hv, hrel⟩ := hpt r u hru.1 hru.2 d hd
    have key := isTrue_iff_where hrel hdt
    rw [← hv] at key
    simp only [List.filter_cons, ← key]
    cases t.isTrue
    · exact ih
    · exact .cons hru ih

end Pred

/-! ### Part 3: the elaborated `WHERE e [NOT] IN (…)` -/

/-- The elaborated `WHERE e [NOT] IN (sq)`: the subquery body elaborates to a one-column query,
    the probe elaborates over the `FROM` columns, and the result attaches the membership test as
    a last column, filters on it and projects it away. -/
theorem elabWhere_inSub (N : NamedSchema) (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S))
    {n : ℕ} (cols : Fin n → Column) (q : Query N.S n) {e : SqlEquiv.Expr} {neg : Bool}
    {sq : SqlEquiv.SubQuery} {q₀ : Query N.S n}
    (h : elabWhere N sub cols q (some (.inSubquery e neg sq)) = .ok q₀) :
    ∃ (r : Elaborated N.S) (h1 : r.n = 1) (e' : Expr n), sub sq = .ok r ∧
      elabExpr cols N.fold noHook e = .ok e' ∧
      q₀ = .project (fun i : Fin n => .col (Fin.castLE (Nat.le_succ n) i))
        (.select (.col (Fin.last n)) (.attach (.inSub neg e') (h1 ▸ r.q) q)) := by
  simp only [elabWhere, subsOf, List.foldl_cons, List.foldl_nil, List.any_nil, Bool.false_eq_true,
    ↓reduceIte, List.nil_append, List.isEmpty_cons, List.mapM_cons, List.mapM_nil] at h
  rcases hs : sub sq with err | r
  · rw [hs] at h
    cases err <;> first
      | (simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h; done)
      | (dsimp only at h; split at h <;>
          simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h)
  rw [hs] at h
  by_cases h1 : r.n = 1
  swap
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at h
  simp only [h1, ↓reduceDIte, pure, Except.pure, bind, Except.bind, List.foldlM_cons,
    List.foldlM_nil] at h
  rcases he : elabExpr cols N.fold noHook e with err | e'
  · simp [he] at h
  simp only [he] at h
  rw [elabExpr] at h
  simp only [List.findIdx?_cons, beq_self_eq_true, ↓reduceIte, Nat.add_zero, Nat.lt_add_one,
    ↓reduceDIte, pure, Except.pure, Nat.le_add_right] at h
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨r, h1, e', rfl, rfl, rfl⟩

/-- **The attach–filter–project pipeline keeps the rows `SqlEquiv` keeps.** The input rows get
    the value of `x` as a last column, the rows where it is TRUE are kept, and the column is
    dropped; when `x` relates row by row to an untyped predicate, the result relates to the
    untyped rows filtered by it. -/
theorem attachFilter_rel {n : ℕ} (cols : Fin n → Column) (fold : String → String)
    {Γ : Fin n → SqlType} {x : Expr n}
    (pred : SqlEquiv.Row → Option SqlEquiv.Value)
    (hpt : ∀ r u, RowRel cols fold r u → r.Conforms Γ → ∀ d, x.eval r = .ok d →
      ∃ v, pred u = some v ∧ DatumRel d v) :
    ∀ {R : List (Row n)} {U : List SqlEquiv.Row},
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U →
      ∀ {E F : List (Row (n + 1))} {R' : List (Row n)},
      R.mapM (Expr.evalRow (Fin.append (fun i => Expr.col i) ![x])) = .ok E →
      (Expr.col (Fin.last n)).filterRows E = .ok F →
      F.mapM (Expr.evalRow (fun i : Fin n => Expr.col (Fin.castLE (Nat.le_succ n) i))) = .ok R' →
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R'
        (U.filter fun u => pred u == some (.bool true))
  | _, _, .nil, E, F, R', hE, hF, hR' => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hE
    subst hE
    simp only [Expr.filterRows, List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at hF
    subst hF
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hR'
    subst hR'
    exact .nil
  | r :: R, u :: U, .cons hru hrest, E, F, R', hE, hF, hR' => by
    rw [List.mapM_cons] at hE
    obtain ⟨e₁, he₁, hE⟩ := bind_ok hE
    obtain ⟨E', hE', hE⟩ := bind_ok hE
    simp only [pure, Except.pure, Except.ok.injEq] at hE
    subst hE
    obtain ⟨t, F'', hte, hF'', rfl⟩ := filterRows_cons_ok hF
    have hcells := Expr.evalRow_eq_ok_iff.mp he₁
    have hL : Fin.last n = Fin.natAdd n (0 : Fin 1) := by ext; simp
    have hlast : x.eval r = .ok (e₁ (Fin.last n)) := by
      have := hcells (Fin.last n)
      rw [hL, Fin.append_right] at this
      rw [hL]; simpa using this
    have hinit : ∀ j : Fin n, e₁ (Fin.castLE (Nat.le_succ n) j) = r j := by
      intro j
      have hC : Fin.castLE (Nat.le_succ n) j = Fin.castAdd 1 j := by ext; simp
      have := hcells (Fin.castAdd 1 j)
      rw [Fin.append_left] at this
      rw [hC]
      simpa using this.symm
    have hdt : (e₁ (Fin.last n)).toTruth = .ok t := by
      simpa [Expr.evalTruth, bind, Except.bind] using hte
    obtain ⟨v, hv, hrel⟩ := hpt r u hru.1 hru.2 _ hlast
    have key := isTrue_iff_where hrel hdt
    rw [← hv] at key
    simp only [List.filter_cons, ← key]
    cases htt : t.isTrue
    · simp only [htt, Bool.false_eq_true, ↓reduceIte] at hR' ⊢
      exact attachFilter_rel cols fold pred hpt hrest hE' hF'' hR'
    · simp only [htt, ↓reduceIte] at hR' ⊢
      rw [List.mapM_cons] at hR'
      obtain ⟨r₁, hr₁, hR'⟩ := bind_ok hR'
      obtain ⟨R'', hR'', hR'⟩ := bind_ok hR'
      simp only [pure, Except.pure, Except.ok.injEq] at hR'
      subst hR'
      have hr₁' : r₁ = r := by
        funext j
        have := Expr.evalRow_eq_ok_iff.mp hr₁ j
        simp only [Expr.eval_col, Except.ok.injEq] at this
        rw [← this, hinit]
      subst hr₁'
      exact .cons hru (attachFilter_rel cols fold pred hpt hrest hE' hF'' hR'')

/-! ### The subquery body, and the statement -/

/-- A `FROM` clause of the fragment has no derived table, so the subquery elaborator is not used. -/
theorem elabFrom_congr (N : NamedSchema) (sub sub' : SqlEquiv.SubQuery → ElabM (Elaborated N.S)) :
    ∀ f, fromFragment f = true → elabFrom N sub f = elabFrom N sub' f
  | .table _, _ => by simp [elabFrom]
  | .join l kind r on, h => by
    obtain ⟨hl, hr, -, -⟩ := join_kind h
    simp only [elabFrom, elabFrom_congr N sub sub' l hl, elabFrom_congr N sub sub' r hr]
  | .subquery _ _, h => by simp [fromFragment] at h

/-- So a plain statement of the fragment elaborates the same with any fuel. -/
theorem elabSelectF_fuel (N : NamedSchema) (a b : ℕ) {items : List SqlEquiv.SelectItem}
    {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} (hff : fromFragment f = true)
    (hw : ∀ w ∈ wh, isFragment w = true) :
    elabSelectF N a (.mk false items (some f) wh [] none [] none none) =
      elabSelectF N b (.mk false items (some f) wh [] none [] none none) := by
  rw [elabSelectF, elabSelectF]
  conv_lhs => rw [elabFrom_congr N _ (fun sq => elabSubQuery N 15 sq) f hff]
  conv_rhs => rw [elabFrom_congr N _ (fun sq => elabSubQuery N 15 sq) f hff]
  cases wh with
  | none => simp only [elabWhere]
  | some w => simp only [elabWhere, subsOf_frag w (hw w rfl), List.foldl_nil, List.isEmpty_nil, ↓reduceIte]

theorem typeOf_attach_inSub {S : DbSchema} {n : ℕ} {neg : Bool} {e : Expr n} {sub : Query S 1}
    {q : Query S n} {Γ' : Fin (n + 1) → SqlType} (h : (Query.attach (.inSub neg e) sub q).typeOf = some Γ') :
    ∃ Δ Γ, sub.typeOf = some Δ ∧ q.typeOf = some Γ ∧ Γ' = Fin.append Γ ![.bool] := by
  simp only [Query.typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨Δ, hΔ, Γ, hΓ, h⟩ := h
  split at h
  · simp only [Option.some.injEq] at h
    exact ⟨Δ, Γ, hΔ, hΓ, h.symm⟩
  · cases h

/-- The type of the elaborated `WHERE e [NOT] IN (…)` is the `FROM` query's. -/
theorem typeOf_inSubWhere {S : DbSchema} {n : ℕ} {neg : Bool} {e : Expr n} {sub : Query S 1}
    {q : Query S n} {Γ : Fin n → SqlType}
    (h : (Query.project (fun i : Fin n => Expr.col (Fin.castLE (Nat.le_succ n) i))
      (.select (.col (Fin.last n)) (.attach (.inSub neg e) sub q))).typeOf = some Γ) :
    q.typeOf = some Γ ∧ sub.typeOf.isSome := by
  obtain ⟨Γ', hsel, hproj⟩ := Query.typeOf_project_eq_some.mp h
  obtain ⟨hatt, -⟩ := Query.typeOf_select_eq_some.mp hsel
  obtain ⟨Δ, Γq, hΔ, hΓq, rfl⟩ := typeOf_attach_inSub hatt
  refine ⟨?_, by simp [hΔ]⟩
  rw [hΓq]
  congr 1
  funext i
  have := hproj i
  have hC : Fin.castLE (Nat.le_succ n) i = Fin.castAdd 1 i := by ext; simp
  simp only [Expr.typeOf, hC, Fin.append_left, Option.some.injEq] at this
  exact this

/-- **`e [NOT] IN (plain subquery)` provides `WhereOk`.** The body is a statement of
    `elabStmt_correct_join` without `ORDER BY`; its result is the same under every outer row
    (`elabStmt_correct_join_ctx`), so the attached membership test relates row by row. -/
theorem whereOk_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {n : ℕ} {cf : Fin n → Column} {qf q₀ : Query N.S n}
    {e : SqlEquiv.Expr} {neg : Bool} {items : List SqlEquiv.SelectItem}
    {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (he : isFragment e = true) (hit : itemsFragment items = true) (hff : fromFragment f = true)
    (hw : ∀ w ∈ wh, isFragment w = true)
    (h : elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf
      (some (.inSubquery e neg (.simple (.mk false items (some f) wh [] none [] none none)))) =
        .ok q₀) :
    WhereOk cf N.fold db D
      (some (.inSubquery e neg (.simple (.mk false items (some f) wh [] none [] none none))))
      qf q₀ := by
  obtain ⟨r, h1, e', hsub, he', rfl⟩ := elabWhere_inSub N _ cf qf h
  obtain ⟨m, rq, rc⟩ := r
  dsimp only at h1
  subst h1
  have htp := translates_of_elab cf N.fold e he he'
  have hleaf : rq.typeOf.isSome → QNoBoolOrder rq → rq.IsSafe ∧ ∃ ss, rq.eval D = .ok ss ∧
      ∀ ctx, List.Forall₂ OutRel ss (SqlEquiv.evalSelectWithContext db ctx
        (.mk false items (some f) wh [] none [] none none)) := by
    intro hty hnbq
    have hst : elabStmt N (joinStmt items f wh [] none none) = .ok ⟨1, rq, rc⟩ := by
      rw [elabSubQuery] at hsub
      simp only [joinStmt, elabStmt, elabQuery, elabQueryRaw, elabSelect]
      rw [elabSelectF_fuel N 16 14 hff hw, hsub]
      simp [hty, bind, Except.bind, pure, Except.pure]
    obtain ⟨hs, ss, hss, -, -, -, hctx⟩ := elabStmt_correct_join_ctx N hfold hfoldCI hwn hfix hD
      hrel hit hff (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq) (by simp) (by simp) hst hnbq
    exact ⟨hs, ss, hss, hctx rfl⟩
  refine ⟨fun Γ hΓ => (typeOf_inSubWhere hΓ).1, fun h => h.2.2.2.2, ?_, ?_⟩
  · intro Γ hΓ hnb hd
    obtain ⟨hs, -⟩ := hleaf (typeOf_inSubWhere hΓ).2 hnb.2.2.2.1
    simp [Query.divSafe, SubKind.divSafe, Expr.divSafe, hd, hs.2, Translates.divSafe _ _ htp]
  · intro Γ Rf R U hΓ hnb hRf hR hrows
    obtain ⟨hqfT, hsubT⟩ := typeOf_inSubWhere hΓ
    obtain ⟨-, ss, hss, hctx⟩ := hleaf hsubT hnb.2.2.2.1
    rw [Query.eval_project, Query.eval_select, Query.eval_attach] at hR
    obtain ⟨F, hF, hR⟩ := bind_ok hR
    obtain ⟨E, hE, hF⟩ := bind_ok hF
    obtain ⟨ss', hss', hE⟩ := bind_ok hE
    rw [hss] at hss'
    cases hss'
    obtain ⟨x, hx, hE⟩ := bind_ok hE
    simp only [SubKind.extra, Except.ok.injEq] at hx
    subst hx
    obtain ⟨Rf', hRf', hE⟩ := bind_ok hE
    rw [hRf] at hRf'
    cases hRf'
    have hsubrows : ∀ u, List.Forall₂ SubRowRel (ss.map (· 0))
        (SqlEquiv.evalSubQueryWithContext db u
          (.simple (.mk false items (some f) wh [] none [] none none))) := by
      intro u
      rw [SqlEquiv.evalSubQuery_simple, List.forall₂_map_left_iff]
      exact (hctx u).imp fun _ _ h => subRowRel_of_outRel h
    exact attachFilter_rel cf N.fold
      (fun u => SqlEquiv.evalExprWithDb db u
        (.inSubquery e neg (.simple (.mk false items (some f) wh [] none [] none none))))
      (fun r u hru hc d hd => inExpr_eval_rel cf N.fold db hru hc htp (hnb.2.2.1 Γ hqfT)
        (hsubrows u) hd) hrows hE hF hR

/-- **Elaborator correctness for `WHERE e [NOT] IN (SELECT …)` (#352, step 6b).** For
    `SELECT e₁, …, eₖ FROM f WHERE e [NOT] IN (SELECT e' FROM f' [WHERE p']) [ORDER BY …]
    [LIMIT n] [OFFSET m]`, the outer statement and the subquery body as in
    `elabStmt_correct_join`, the subquery uncorrelated (the elaborator rejects a correlated
    one): when the statement elaborates, the typed query evaluates, and its rows relate, in
    order, to `SqlEquiv`'s. `SqlEquiv` re-evaluates the body for every outer row, on rows that
    carry the outer row; the typed core evaluates it once. The three-valued result agrees,
    `NULL`s included (`inSub_agree`). -/
theorem elabStmt_correct_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
    {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    {e : SqlEquiv.Expr} {neg : Bool} {items' : List SqlEquiv.SelectItem}
    {f' : SqlEquiv.FromClause} {wh' : Option SqlEquiv.Expr}
    (hit : itemsFragment items = true) (hff : fromFragment f = true)
    (he : isFragment e = true) (hit' : itemsFragment items' = true)
    (hff' : fromFragment f' = true) (hw' : ∀ w ∈ wh', isFragment w = true)
    (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c)
    (hnamed : orderBy ≠ [] → itemsNamed items = true)
    {el : Elaborated N.S}
    (h : elabStmt N (joinStmt items f (some (.inSubquery e neg
      (.simple (.mk false items' (some f') wh' [] none [] none none)))) orderBy lim off) = .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (joinStmt items f (some (.inSubquery e neg
        (.simple (.mk false items' (some f') wh' [] none [] none none)))) orderBy lim off)).2 =
          some out ∧ List.Forall₂ OutRel rs out := by
  obtain ⟨-, rs, hrs, out, hout, hr, -⟩ := elabStmt_correct_join_ctx N hfold hfoldCI hwn hfix hD
    hrel hit hff (fun _ _ _ _ hq => whereOk_inSub N hfold hfoldCI hwn hfix hD hrel he hit' hff'
      hw' hq) hcols hnamed h hnb
  exact ⟨rs, hrs, out, hout, hr⟩

end SqlBridge.CorrectSub
