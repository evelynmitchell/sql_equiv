/-
  Elaborator correctness for uncorrelated subqueries in `WHERE` (#352, steps 6b and 6c):
  `e [NOT] IN (SELECT …)` and the scalar `(SELECT …)` under a comparison.

  `SqlEquiv` re-evaluates the subquery body for every outer row, on rows `inner ++ outer`; the
  typed core evaluates it once and attaches the membership test to the input as a last column
  (`Query.attach`), filters on it and projects it away. The pieces:

  * the value: `eq_agree`, `inList_agree`, `inSub_agree` (the typed three-valued membership
    against `SqlEquiv`'s `inSubqueryResult`, `NULL`s included, whatever the order of the rows);
  * one row: `inExpr_eval_rel`; a filter by any predicate that relates row by row:
    `filter_rel_of`;
  * the attach–filter–project pipeline keeps the rows `SqlEquiv` keeps: `attachFilter_rel`;
  * the body: it elaborates the same with any fuel (`elabSelectF_fuel`) and gives the same
    result under every outer row (`body_ctx`, from `elabStmt_correct_join_ctx` and
    `elabStmt_correct_agg_w`);
  * the predicate (step 6c): `HoleCtx`, a clause with one subquery node, `IN` or scalar, under a
    comparison and conjunctions; `holeCtx_elab` relates the elaborated clause to the untyped
    one given the node's value; `elabWhere_one_inSub` / `elabWhere_one_scalar` give the shape
    of the elaborated `WHERE`;
  * `whereOk_attach`, `whereOk_of_subWhere`: the clause provides `WhereOk`, the hypothesis the
    statement theorems take for their `WHERE`; `elabStmt_correct_inSub` and the three after it:
    the statement theorems for plain, `DISTINCT` and aggregate outer queries.
-/
import SqlBridge.CorrectSetOp
import SqlBridge.CorrectAggBare
import SqlBridge.CorrectDistinct

namespace SqlBridge.CorrectSub
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg (itemExpr)

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

/-! ### Weakening, the pipeline for any predicate, and `WhereOk` -/

/-- No column reference of the expression answers to the name `nm` (after folding). -/
def noRefTo (fold : String → String) (nm : String) : SqlEquiv.Expr → Bool
  | .col c => fold c.column != nm
  | .binOp _ a b => noRefTo fold nm a && noRefTo fold nm b
  | .unaryOp _ a => noRefTo fold nm a
  | .between e lo hi => noRefTo fold nm e && noRefTo fold nm lo && noRefTo fold nm hi
  | _ => true

/-- A reference that does not answer to the appended column resolves, among the columns with one
    more appended, where it resolves among the original ones. -/
theorem resolveColumn_append_one {n : ℕ} (cols : Fin n → Column) (c : Column) {q : Option String}
    {name : String} (hc : c.name ≠ name) {j : Fin (n + 1)}
    (h : resolveColumn (Fin.append cols ![c]) q name = .ok j) :
    ∃ i, resolveColumn cols q name = .ok i ∧ j = Fin.castAdd 1 i := by
  obtain ⟨hm, hu⟩ := resolveColumn_eq_ok_iff.mp h
  induction j using Fin.addCases with
  | left i =>
    rw [Fin.append_left] at hm
    refine ⟨i, resolveColumn_eq_ok_iff.mpr ⟨hm, fun k hk => ?_⟩, rfl⟩
    exact Fin.castAdd_injective _ _ (hu (Fin.castAdd 1 k) (by rw [Fin.append_left]; exact hk))
  | right i =>
    rw [Fin.append_right] at hm
    have : (![c] : Fin 1 → Column) i = c := by
      have : i = 0 := Subsingleton.elim _ _
      subst this; rfl
    rw [this] at hm
    exact absurd hm.1 hc

theorem retypeNull_rename {n : ℕ} (cols : Fin n → Column) (c : Column) (a b : Expr n) :
    retypeNull (Fin.append cols ![c]) (a.rename (Fin.castAdd 1)) (b.rename (Fin.castAdd 1)) =
      (retypeNull cols a b).rename (Fin.castAdd 1) := by
  have hctx : ctx (Fin.append cols ![c]) ∘ Fin.castAdd 1 = ctx cols := by
    funext i; simp [ctx, Fin.append_left]
  unfold retypeNull
  rw [Expr.typeOf_rename, hctx]
  cases a <;> cases hb : b.typeOf (ctx cols) <;> simp [Expr.rename]

/-- **Weakening.** A fragment expression elaborated among the columns with one more appended,
    under a hook that leaves fragment expressions alone, is its elaboration among the original
    columns, re-indexed; provided no column reference answers to the appended column's name. -/
theorem elabExpr_weaken {n : ℕ} (cols : Fin n → Column) (fold : String → String) (c : Column)
    (hook : SqlEquiv.Expr → Option (Expr (n + 1)))
    (hhook : ∀ x, isFragment x = true → hook x = none) :
    ∀ (a : SqlEquiv.Expr) {p : Expr (n + 1)}, isFragment a = true → noRefTo fold c.name a = true →
      elabExpr (Fin.append cols ![c]) fold hook a = .ok p →
      ∃ p₀, elabExpr cols fold noHook a = .ok p₀ ∧ p = p₀.rename (Fin.castAdd 1)
  | .lit v, p, hf, _, h => by
    unfold elabExpr at h ⊢
    simp only [hhook _ hf, noHook] at h ⊢
    cases v <;> simp only [elabValue, pure, Except.pure, Except.ok.injEq] at h ⊢ <;> subst h <;>
      exact ⟨_, rfl, rfl⟩
  | .col cr, p, hf, hn, h => by
    simp only [noRefTo, bne_iff_ne, ne_eq] at hn
    simp only [elabExpr, hhook _ hf, noHook, resolve] at h ⊢
    rcases hr : resolveColumn (Fin.append cols ![c]) (cr.table.map fold) (fold cr.column) with _ | j
    · rename_i err
      cases err <;> simp [hr, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · rw [hr] at h
      simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
      subst h
      obtain ⟨i, hi, rfl⟩ := resolveColumn_append_one cols c (fun hc => hn hc.symm) hr
      exact ⟨.col i, by simp [hi, pure, Except.pure, bind, Except.bind], rfl⟩
  | .binOp op a b, p, hf, hn, h => by
    have hf' := hf
    simp only [isFragment, Bool.and_eq_true] at hf
    obtain ⟨⟨hop, ha⟩, hb⟩ := hf
    simp only [noRefTo, Bool.and_eq_true] at hn
    simp only [elabExpr, hhook _ hf', noHook] at h ⊢
    rcases hea : elabExpr (Fin.append cols ![c]) fold hook a with _ | a'
    · cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure]
    rcases heb : elabExpr (Fin.append cols ![c]) fold hook b with _ | b'
    · cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure]
    obtain ⟨a₀, ha₀, rfl⟩ := elabExpr_weaken cols fold c hook hhook a ha hn.1 hea
    obtain ⟨b₀, hb₀, rfl⟩ := elabExpr_weaken cols fold c hook hhook b hb hn.2 heb
    simp only [hea, heb, ha₀, hb₀] at h ⊢
    cases op <;> simp_all [elabBinOp, bind, Except.bind, pure, Except.pure, retypeNull_rename,
      Expr.rename]
  | .unaryOp op a, p, hf, hn, h => by
    have hf' := hf
    cases op <;> simp only [isFragment, Bool.false_eq_true] at hf
    simp only [noRefTo] at hn
    simp only [elabExpr, hhook _ hf', noHook] at h ⊢
    rcases hea : elabExpr (Fin.append cols ![c]) fold hook a with _ | a'
    · simp [hea, bind, Except.bind] at h
    obtain ⟨a₀, ha₀, rfl⟩ := elabExpr_weaken cols fold c hook hhook a hf hn hea
    simp only [hea, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨.unary (elabUnOp .not) a₀, by simp [ha₀, bind, Except.bind, pure, Except.pure],
      by simp [Expr.rename]⟩
  | .func _ _, _, hf, _, _ | .agg _ _ _, _, hf, _, _ | .countStar, _, hf, _, _
  | .«case» _ _, _, hf, _, _ | .inList _ _ _, _, hf, _, _ | .inSubquery _ _ _, _, hf, _, _
  | .exists _ _, _, hf, _, _ | .subquery _, _, hf, _, _
  | .windowFn _ _ _, _, hf, _, _ => by simp [isFragment] at hf
  | .between x lo hi, p, hf, hn, h => by
    have hf' := hf
    simp only [isFragment, Bool.and_eq_true] at hf
    obtain ⟨⟨hx, hlo⟩, hhi⟩ := hf
    simp only [noRefTo, Bool.and_eq_true] at hn
    simp only [elabExpr, hhook _ hf', noHook] at h ⊢
    rcases hex : elabExpr (Fin.append cols ![c]) fold hook x with _ | x'
    · simp [hex, bind, Except.bind] at h
    rcases helo : elabExpr (Fin.append cols ![c]) fold hook lo with _ | lo'
    · simp [hex, helo, bind, Except.bind] at h
    rcases hehi : elabExpr (Fin.append cols ![c]) fold hook hi with _ | hi'
    · simp [hex, helo, hehi, bind, Except.bind] at h
    obtain ⟨x₀, hx₀, rfl⟩ := elabExpr_weaken cols fold c hook hhook x hx hn.1.1 hex
    obtain ⟨lo₀, hlo₀, rfl⟩ := elabExpr_weaken cols fold c hook hhook lo hlo hn.1.2 helo
    obtain ⟨hi₀, hhi₀, rfl⟩ := elabExpr_weaken cols fold c hook hhook hi hhi hn.2 hehi
    simp only [hex, helo, hehi, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨.binary .and (.binary (.cmp .ge) x₀ (retypeNull cols lo₀ x₀))
      (.binary (.cmp .le) x₀ (retypeNull cols hi₀ x₀)),
      by simp [hx₀, hlo₀, hhi₀, bind, Except.bind, pure, Except.pure],
      by simp [Expr.rename, retypeNull_rename]⟩

theorem append_single_eq {n : ℕ} {e₁ : Row (n + 1)} {r : Row n}
    (hinit : ∀ j : Fin n, e₁ (Fin.castAdd 1 j) = r j) :
    e₁ = Fin.append r ![e₁ (Fin.last n)] := by
  funext j
  induction j using Fin.addCases with
  | left i => rw [Fin.append_left, hinit]
  | right i =>
    have : i = 0 := Subsingleton.elim _ _
    subst this
    rw [Fin.append_right]
    have hL : Fin.natAdd n (0 : Fin 1) = Fin.last n := by ext; simp
    rw [hL]; rfl

/-- **The attach–filter–project pipeline, for any predicate over the extended row.** -/
theorem attachFilter_rel {n : ℕ} (cols : Fin n → Column) (fold : String → String)
    {Γ : Fin n → SqlType} {x : Expr n} {P : Expr (n + 1)}
    (pred : SqlEquiv.Row → Option SqlEquiv.Value)
    (hpt : ∀ r u, RowRel cols fold r u → r.Conforms Γ → ∀ d, x.eval r = .ok d →
      ∀ dp, P.eval (Fin.append r ![d]) = .ok dp → ∃ v, pred u = some v ∧ DatumRel dp v) :
    ∀ {R : List (Row n)} {U : List SqlEquiv.Row},
      List.Forall₂ (fun r u => RowRel cols fold r u ∧ r.Conforms Γ) R U →
      ∀ {E F : List (Row (n + 1))} {R' : List (Row n)},
      R.mapM (Expr.evalRow (Fin.append (fun i => Expr.col i) ![x])) = .ok E →
      P.filterRows E = .ok F →
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
    have hinit : ∀ j : Fin n, e₁ (Fin.castAdd 1 j) = r j := by
      intro j
      have := hcells (Fin.castAdd 1 j)
      rw [Fin.append_left] at this
      simpa using this.symm
    have he₁eq := append_single_eq hinit
    have hev : ∃ dp, P.eval e₁ = .ok dp ∧ dp.toTruth = .ok t := by
      unfold Expr.evalTruth at hte
      rcases he : P.eval e₁ with _ | dp
      · simp [he, bind, Except.bind] at hte
      · simp only [he, bind, Except.bind] at hte
        exact ⟨dp, rfl, hte⟩
    obtain ⟨dp, hdp, hdt⟩ := hev
    rw [he₁eq] at hdp
    obtain ⟨v, hv, hrel⟩ := hpt r u hru.1 hru.2 _ hlast dp hdp
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
        have hC : Fin.castLE (Nat.le_succ n) j = Fin.castAdd 1 j := by ext; simp
        rw [← this, hC, hinit]
      subst hr₁'
      exact .cons hru (attachFilter_rel cols fold pred hpt hrest hE' hF'' hR'')


/-- The hidden column the elaborator appends for an attached subquery. -/
def subCol (ty : SqlType) : Column := { qualifier := none, name := "?subquery?", type := ty }

theorem noBoolOrder_rename {n m : ℕ} (ρ : Fin n → Fin m) (Γ : Fin m → SqlType) :
    ∀ e : Expr n, NoBoolOrder Γ (e.rename ρ) → NoBoolOrder (Γ ∘ ρ) e := by
  intro e
  induction e with
  | binary op a b iha ihb =>
    intro h
    cases op <;> simp only [Expr.rename, NoBoolOrder, Expr.typeOf_rename] at h ⊢ <;>
      first
        | exact ⟨iha h.1, ihb h.2⟩
        | exact ⟨h.1, iha h.2.1, ihb h.2.2⟩
  | unary op a iha => intro h; exact iha h
  | _ => intro _; trivial

theorem eval_col_last_append {n : ℕ} (r : Row n) (d : Datum) :
    (Expr.col (Fin.last n) : Expr (n + 1)).eval (Fin.append r ![d]) = .ok d := by
  have hL : Fin.last n = Fin.natAdd n (0 : Fin 1) := by ext; simp
  rw [Expr.eval_col, hL, Fin.append_right]; rfl

/-! ### Predicates with one subquery node (step 6c) -/

/-- A predicate with one subquery node `node` and otherwise in the expression fragment:
    `node`, `a op node` for a comparison `op`, `C AND b`, `a AND C`. -/
inductive HoleCtx (fold : String → String) (node : SqlEquiv.Expr) : SqlEquiv.Expr → Prop
  | hole : HoleCtx fold node node
  | cmpR {op : SqlEquiv.BinOp} {a : SqlEquiv.Expr} {c : CmpOp} (hop : elabBinOp op = .ok (.cmp c))
      (ha : isFragment a = true) (hna : noRefTo fold "?subquery?" a = true) :
      HoleCtx fold node (.binOp op a node)
  | andL {w b : SqlEquiv.Expr} (hw : HoleCtx fold node w) (hb : isFragment b = true)
      (hnb : noRefTo fold "?subquery?" b = true) : HoleCtx fold node (.binOp .and w b)
  | andR {a w : SqlEquiv.Expr} (ha : isFragment a = true)
      (hna : noRefTo fold "?subquery?" a = true) (hw : HoleCtx fold node w) :
      HoleCtx fold node (.binOp .and a w)

theorem elabExpr_hook_some {n : ℕ} (cols : Fin n → Column) (fold : String → String)
    (hook : SqlEquiv.Expr → Option (Expr n)) {e : SqlEquiv.Expr} {e' : Expr n}
    (h : hook e = some e') : elabExpr cols fold hook e = .ok e' := by
  cases e <;> (unfold elabExpr; simp [h, pure, Except.pure])

section Hole
variable {n : ℕ} (cols : Fin n → Column) (fold : String → String) (τc τ : SqlType)
  (hook : SqlEquiv.Expr → Option (Expr (n + 1))) (node : SqlEquiv.Expr)
  (hhookN : hook node = some (.col (Fin.last n)))
  (hhook : ∀ x, x ≠ node → hook x = none) (hnf : isFragment node = false)
  (hnbin : ∀ op a b, node ≠ .binOp op a b)
include hhookN hhook hnf hnbin

/-- What the elaboration `P` of a `HoleCtx` predicate `w` gives: it is safe, and it relates to
    `w` row by row, given that the attached column relates to the node's value. -/
theorem holeCtx_elab (db : SqlEquiv.Database) :
    ∀ {w : SqlEquiv.Expr}, HoleCtx fold node w → ∀ {P : Expr (n + 1)},
      elabExpr (Fin.append cols ![subCol τc]) fold hook w = .ok P →
      P.divSafe = true ∧
      ∀ (Γ : Fin n → SqlType), NoBoolOrder (Fin.append Γ ![τ]) P →
        ∀ (r : Row n) (u : SqlEquiv.Row), RowRel cols fold r u → r.Conforms Γ →
        ∀ (d : Datum) (vn : SqlEquiv.Value), SqlEquiv.evalExprWithDb db u node = some vn →
          DatumRel d vn → Row.Conforms (Fin.append Γ ![τ]) (Fin.append r ![d] : Row (n + 1)) →
        ∀ dp, P.eval (Fin.append r ![d]) = .ok dp →
          ∃ v, SqlEquiv.evalExprWithDb db u w = some v ∧ DatumRel dp v := by
  have hfragHook : ∀ x, isFragment x = true → hook x = none := fun x hx =>
    hhook x (fun h => by rw [h, hnf] at hx; cases hx)
  have hΓ' : ∀ Γ : Fin n → SqlType, (Fin.append Γ ![τ]) ∘ Fin.castAdd 1 = Γ := fun Γ => by
    funext i; simp [Fin.append_left]
  intro w hw
  induction hw with
  | hole =>
    intro P h
    rw [elabExpr_hook_some _ _ _ hhookN, Except.ok.injEq] at h
    subst h
    refine ⟨rfl, fun Γ _ r u _ _ d vn hvn hrn _ dp hdp => ?_⟩
    rw [eval_col_last_append, Except.ok.injEq] at hdp
    exact ⟨vn, hvn, hdp ▸ hrn⟩
  | @cmpR op a c hop ha hna =>
    intro P h
    simp only [elabExpr, hhook _ (Ne.symm (hnbin op a node)), hop, pure, Except.pure, bind,
      Except.bind] at h
    rcases hea : elabExpr (Fin.append cols ![subCol τc]) fold hook a with err | a'
    · simp [hea] at h
    obtain ⟨a₀, ha₀, rfl⟩ := elabExpr_weaken cols fold (subCol τc) hook hfragHook a ha hna hea
    simp only [hea, elabExpr_hook_some _ _ _ hhookN, Except.ok.injEq] at h
    subst h
    have hta := translates_of_elab cols fold a ha ha₀
    refine ⟨by simp [Expr.divSafe, divSafe_retypeNull, Translates.divSafe _ _ hta,
      BinOp.isDivision], fun Γ hnbP r u hru hc d vn hvn hrn hcx dp hdp => ?_⟩
    obtain ⟨hcc, hna', -⟩ := hnbP
    obtain ⟨da, db', hea1, heb1, hd⟩ := eval_binary_ok hdp
    have hea' := hea1
    rw [eval_retypeNull, Expr.eval_rename_castAdd] at hea'
    rw [eval_retypeNull, eval_col_last_append, Except.ok.injEq] at heb1
    subst heb1
    have hnba : NoBoolOrder Γ a₀ := by
      have h2 := noBoolOrder_rename _ _ _ (noBoolOrder_of_retypeNull _ _ hna')
      rwa [hΓ'] at h2
    obtain ⟨va, hva, hra⟩ := Translates.eval_rel cols fold db hru hc hta hnba hea'
    obtain ⟨v, hv, hrel⟩ := cmp_agree hop hra hrn (fun h1 h2 x y hxy => by
      rcases hcc with hcc | hcc | ⟨τa, hτ, hτb⟩
      · exact h1 hcc
      · exact h2 hcc
      · rcases Expr.eval_ok_or_divisionByZero hcx hτ with ⟨d', hd', hty⟩ | ⟨hdz, _⟩
        · rw [hea1] at hd'; cases hd'
          rw [hxy.1] at hty
          exact hτb (by simpa [Datum.HasType, Value.type] using hty.symm)
        · rw [hea1] at hdz; cases hdz) hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_binOp, hva, hvn, hv], hrel⟩
  | @andL w b hw hb hnb ih =>
    intro P h
    simp only [elabExpr, hhook _ (Ne.symm (hnbin .and w b)), elabBinOp, pure, Except.pure, bind,
      Except.bind] at h
    rcases hew : elabExpr (Fin.append cols ![subCol τc]) fold hook w with err | Pw
    · simp [hew] at h
    rcases heb : elabExpr (Fin.append cols ![subCol τc]) fold hook b with err | b'
    · simp [hew, heb] at h
    obtain ⟨b₀, hb₀, rfl⟩ := elabExpr_weaken cols fold (subCol τc) hook hfragHook b hb hnb heb
    simp only [hew, heb, Except.ok.injEq] at h
    subst h
    obtain ⟨hdivw, hrelw⟩ := ih hew
    have htb := translates_of_elab cols fold b hb hb₀
    refine ⟨by simp [Expr.divSafe, divSafe_retypeNull, Translates.divSafe _ _ htb, hdivw,
      BinOp.isDivision], fun Γ hnbP r u hru hc d vn hvn hrn hcx dp hdp => ?_⟩
    obtain ⟨hnw, hnb'⟩ := hnbP
    obtain ⟨dw, db', hew1, heb1, hd⟩ := eval_binary_ok hdp
    rw [eval_retypeNull] at hew1 heb1
    rw [Expr.eval_rename_castAdd] at heb1
    obtain ⟨vw, hvw, hrw⟩ := hrelw Γ (noBoolOrder_of_retypeNull _ _ hnw) r u hru hc d vn hvn hrn
      hcx dw hew1
    have hnbb : NoBoolOrder Γ b₀ := by
      have h2 := noBoolOrder_rename _ _ _ (noBoolOrder_of_retypeNull _ _ hnb')
      rwa [hΓ'] at h2
    obtain ⟨vb, hvb, hrb⟩ := Translates.eval_rel cols fold db hru hc htb hnbb heb1
    obtain ⟨v, hv, hrel⟩ := and_agree hrw hrb hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_binOp, hvw, hvb, hv], hrel⟩
  | @andR a w ha hna hw ih =>
    intro P h
    simp only [elabExpr, hhook _ (Ne.symm (hnbin .and a w)), elabBinOp, pure, Except.pure, bind,
      Except.bind] at h
    rcases hea : elabExpr (Fin.append cols ![subCol τc]) fold hook a with err | a'
    · simp [hea] at h
    rcases hew : elabExpr (Fin.append cols ![subCol τc]) fold hook w with err | Pw
    · simp [hea, hew] at h
    obtain ⟨a₀, ha₀, rfl⟩ := elabExpr_weaken cols fold (subCol τc) hook hfragHook a ha hna hea
    simp only [hea, hew, Except.ok.injEq] at h
    subst h
    obtain ⟨hdivw, hrelw⟩ := ih hew
    have hta := translates_of_elab cols fold a ha ha₀
    refine ⟨by simp [Expr.divSafe, divSafe_retypeNull, Translates.divSafe _ _ hta, hdivw,
      BinOp.isDivision], fun Γ hnbP r u hru hc d vn hvn hrn hcx dp hdp => ?_⟩
    obtain ⟨hna', hnw⟩ := hnbP
    obtain ⟨da, dw, hea1, hew1, hd⟩ := eval_binary_ok hdp
    rw [eval_retypeNull] at hea1 hew1
    rw [Expr.eval_rename_castAdd] at hea1
    obtain ⟨vw, hvw, hrw⟩ := hrelw Γ (noBoolOrder_of_retypeNull _ _ hnw) r u hru hc d vn hvn hrn
      hcx dw hew1
    have hnba : NoBoolOrder Γ a₀ := by
      have h2 := noBoolOrder_rename _ _ _ (noBoolOrder_of_retypeNull _ _ hna')
      rwa [hΓ'] at h2
    obtain ⟨va, hva, hra⟩ := Translates.eval_rel cols fold db hru hc hta hnba hea1
    obtain ⟨v, hv, hrel⟩ := and_agree hra hrw hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_binOp, hva, hvw, hv], hrel⟩

end Hole

/-- The hook the elaborator uses for a `WHERE` with the single subquery node `node`: the node
    reads the attached last column. -/
def hookOf (n : ℕ) (node : SqlEquiv.Expr) (sq : SqlEquiv.SubQuery) :
    SqlEquiv.Expr → Option (Expr (n + 1)) := fun e₁ =>
  match List.findIdx? (fun x => x.1 == e₁) [(node, sq)] with
  | some j => if h : n + j < n + 1 then some (.col ⟨n + j, h⟩) else none
  | none => none

theorem hookOf_node (n : ℕ) (node : SqlEquiv.Expr) (sq : SqlEquiv.SubQuery) :
    hookOf n node sq node = some (.col (Fin.last n)) := by
  simp [hookOf, List.findIdx?_cons, Fin.last]

theorem hookOf_ne (n : ℕ) (node : SqlEquiv.Expr) (sq : SqlEquiv.SubQuery) {x : SqlEquiv.Expr}
    (hx : x ≠ node) : hookOf n node sq x = none := by
  have : (node == x) = false := by rw [beq_eq_false_iff_ne]; exact fun h => hx h.symm
  simp [hookOf, List.findIdx?_cons, this]

/-- The subqueries of a `HoleCtx` predicate: its node. -/
theorem holeCtx_subs {fold : String → String} {node : SqlEquiv.Expr} {sq : SqlEquiv.SubQuery}
    (hn : subsOf node = [(node, sq)]) :
    ∀ {w : SqlEquiv.Expr}, HoleCtx fold node w → subsOf w = [(node, sq)] := by
  intro w hw
  induction hw with
  | hole => exact hn
  | cmpR _ ha _ => simp [subsOf, subsOf_frag _ ha, hn]
  | andL _ hb _ ih => simp [subsOf, subsOf_frag _ hb, ih]
  | andR ha _ _ ih => simp [subsOf, subsOf_frag _ ha, ih]

/-- The elaborated `WHERE w` when `w`'s one subquery is the `IN` node. -/
theorem elabWhere_one_inSub (N : NamedSchema) (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S))
    {n : ℕ} (cols : Fin n → Column) (q : Query N.S n) {w e : SqlEquiv.Expr} {neg : Bool}
    {sq : SqlEquiv.SubQuery} {q₀ : Query N.S n}
    (hs : subsOf w = [(.inSubquery e neg sq, sq)])
    (h : elabWhere N sub cols q (some w) = .ok q₀) :
    ∃ (r : Elaborated N.S) (h1 : r.n = 1) (e' : Expr n) (P : Expr (n + 1)), sub sq = .ok r ∧
      elabExpr cols N.fold noHook e = .ok e' ∧
      elabExpr (Fin.append cols ![subCol .bool]) N.fold (hookOf n (.inSubquery e neg sq) sq) w =
        .ok P ∧
      q₀ = .project (fun i : Fin n => .col (Fin.castLE (Nat.le_succ n) i))
        (.select P (.attach (.inSub neg e') (h1 ▸ r.q) q)) := by
  simp only [elabWhere, hs, List.foldl_cons, List.foldl_nil, List.any_nil, Bool.false_eq_true,
    ↓reduceIte, List.nil_append, List.isEmpty_cons, List.mapM_cons, List.mapM_nil] at h
  rcases hsb : sub sq with err | r
  · rw [hsb] at h
    cases err <;> first
      | (simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h; done)
      | (dsimp only at h; split at h <;>
          simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h)
  rw [hsb] at h
  by_cases h1 : r.n = 1
  swap
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at h
  simp only [h1, ↓reduceDIte, pure, Except.pure, bind, Except.bind, List.foldlM_cons,
    List.foldlM_nil] at h
  rcases he : elabExpr cols N.fold noHook e with err | e'
  · simp [he] at h
  simp only [he] at h
  have hsc : ({ qualifier := none, name := "?subquery?", type := SqlType.bool } : Column) =
      subCol .bool := rfl
  simp only [hsc] at h
  generalize hH : (fun e_1 : SqlEquiv.Expr =>
    match List.findIdx? (fun x => x.1 == e_1) [(e.inSubquery neg sq, sq)] with
    | some j => if h : n + j < n + 1 then some (Expr.col (⟨n + j, h⟩ : Fin (n + 1))) else none
    | none => none) = hook at h
  have hhk : hook = hookOf n (.inSubquery e neg sq) sq := hH.symm
  subst hhk
  rcases hP : elabExpr (Fin.append cols ![subCol .bool]) N.fold
      (hookOf n (.inSubquery e neg sq) sq) w with err | P
  · simp [hP] at h
  simp only [hP, Nat.le_add_right, ↓reduceDIte, Except.ok.injEq] at h
  subst h
  exact ⟨r, h1, e', P, rfl, rfl, rfl, rfl⟩

/-- The elaborated `WHERE w` when `w`'s one subquery is a scalar subquery. -/
theorem elabWhere_one_scalar (N : NamedSchema) (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S))
    {n : ℕ} (cols : Fin n → Column) (q : Query N.S n) {w : SqlEquiv.Expr}
    {sq : SqlEquiv.SubQuery} {q₀ : Query N.S n}
    (hs : subsOf w = [(.subquery sq, sq)])
    (h : elabWhere N sub cols q (some w) = .ok q₀) :
    ∃ (r : Elaborated N.S) (h1 : r.n = 1) (P : Expr (n + 1)), sub sq = .ok r ∧
      elabExpr (Fin.append cols ![subCol (r.cols ⟨0, by omega⟩).type]) N.fold
        (hookOf n (.subquery sq) sq) w = .ok P ∧
      q₀ = .project (fun i : Fin n => .col (Fin.castLE (Nat.le_succ n) i))
        (.select P (.attach (.scalar (N.config.scalarSubqueryRows == .firstRow))
          (h1 ▸ r.q) q)) := by
  simp only [elabWhere, hs, List.foldl_cons, List.foldl_nil, List.any_nil, Bool.false_eq_true,
    ↓reduceIte, List.nil_append, List.isEmpty_cons, List.mapM_cons, List.mapM_nil] at h
  rcases hsb : sub sq with err | r
  · rw [hsb] at h
    cases err <;> first
      | (simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h; done)
      | (dsimp only at h; split at h <;>
          simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h)
  rw [hsb] at h
  by_cases h1 : r.n = 1
  swap
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at h
  simp only [h1, ↓reduceDIte, pure, Except.pure, bind, Except.bind, List.foldlM_cons,
    List.foldlM_nil] at h
  have hsc : ∀ τ : SqlType, ({ qualifier := none, name := "?subquery?", type := τ } : Column) =
      subCol τ := fun _ => rfl
  simp only [hsc] at h
  generalize hH : (fun e_1 : SqlEquiv.Expr =>
    match List.findIdx? (fun x => x.1 == e_1) [(SqlEquiv.Expr.subquery sq, sq)] with
    | some j => if h : n + j < n + 1 then some (Expr.col (⟨n + j, h⟩ : Fin (n + 1))) else none
    | none => none) = hook at h
  have hhk : hook = hookOf n (.subquery sq) sq := hH.symm
  subst hhk
  rcases hP : elabExpr (Fin.append cols ![subCol (r.cols ⟨0, by omega⟩).type]) N.fold
      (hookOf n (.subquery sq) sq) w with err | P
  · simp [hP] at h
  simp only [hP, Nat.le_add_right, ↓reduceDIte, Except.ok.injEq] at h
  subst h
  exact ⟨r, h1, P, rfl, hP, rfl⟩

theorem conforms_append_single {n : ℕ} {Γ : Fin n → SqlType} {r : Row n} {τ : SqlType} {d : Datum}
    (hr : r.Conforms Γ) (hd : d.HasType τ) :
    Row.Conforms (Fin.append Γ ![τ]) (Fin.append r ![d] : Row (n + 1)) := by
  intro i
  induction i using Fin.addCases with
  | left j => simpa [Fin.append_left] using hr j
  | right j =>
    have : j = 0 := Subsingleton.elim _ _
    subst this
    simpa [Fin.append_right] using hd

/-- The type of the elaborated `WHERE` over an attached subquery of either kind. -/
theorem typeOf_attachWhere {S : DbSchema} {n : ℕ} {kind : SubKind n} {sub : Query S 1}
    {q : Query S n} {P : Expr (n + 1)} {Γ : Fin n → SqlType}
    (h : (Query.project (fun i : Fin n => Expr.col (Fin.castLE (Nat.le_succ n) i))
      (.select P (.attach kind sub q))).typeOf = some Γ) :
    q.typeOf = some Γ ∧ ∃ Δ τ, sub.typeOf = some Δ ∧
      (Query.attach kind sub q).typeOf = some (Fin.append Γ ![τ]) ∧
      (∀ fr, kind = .scalar fr → τ = Δ 0) ∧ (∀ neg e, kind = .inSub neg e → τ = .bool) := by
  obtain ⟨Γ', hsel, hproj⟩ := Query.typeOf_project_eq_some.mp h
  obtain ⟨hatt, -⟩ := Query.typeOf_select_eq_some.mp hsel
  have hatt' := hatt
  simp only [Query.typeOf, Option.bind_eq_bind, Option.bind_eq_some_iff] at hatt
  obtain ⟨Δ, hΔ, Γq, hΓq, hk⟩ := hatt
  have key : ∃ τ, Γ' = Fin.append Γq ![τ] ∧ (∀ fr, kind = .scalar fr → τ = Δ 0) ∧
      (∀ neg e, kind = .inSub neg e → τ = .bool) := by
    cases kind with
    | scalar fr =>
      simp only [Option.some.injEq] at hk
      exact ⟨Δ 0, hk.symm, (fun _ _ => rfl), (fun _ _ h => (by cases h))⟩
    | inSub neg e =>
      dsimp only at hk
      split at hk
      · simp only [Option.some.injEq] at hk
        exact ⟨.bool, hk.symm, (fun _ h => (by cases h)), (fun _ _ _ => rfl)⟩
      · cases hk
  obtain ⟨τ, rfl, hk1, hk2⟩ := key
  have hΓ : Γq = Γ := by
    funext i
    have := hproj i
    have hC : Fin.castLE (Nat.le_succ n) i = Fin.castAdd 1 i := by ext; simp
    simp only [Expr.typeOf, hC, Fin.append_left, Option.some.injEq] at this
    exact this
  subst hΓ
  exact ⟨hΓq, Δ, τ, hΔ, hatt', hk1, hk2⟩

/-- **A `WHERE` that reads one attached subquery, of either kind, provides `WhereOk`.** -/
theorem whereOk_attach {S : DbSchema} {n : ℕ} (cf : Fin n → Column) (fold : String → String)
    (db : SqlEquiv.Database) (D : Database S) {qf : Query S n} {kind : SubKind n}
    {rq : Query S 1} {P : Expr (n + 1)} {w node : SqlEquiv.Expr}
    (hkdiv : kind.divSafe = true) (hPdiv : P.divSafe = true)
    (hbody : rq.typeOf.isSome → QNoBoolOrder rq → rq.divSafe = true)
    (hnode : ∀ (Γ : Fin n → SqlType) (Δ : Fin 1 → SqlType) (τ : SqlType), qf.typeOf = some Γ →
      rq.typeOf = some Δ → (Query.attach kind rq qf).typeOf = some (Fin.append Γ ![τ]) →
      QNoBoolOrder (Query.attach kind rq qf) →
      (∀ fr, kind = .scalar fr → τ = Δ 0) → (∀ neg e, kind = .inSub neg e → τ = .bool) →
      ∀ ss x, rq.eval D = .ok ss → kind.extra (ss.map (· 0)) = .ok x →
      ∀ r u, RowRel cf fold r u → r.Conforms Γ → ∀ d, x.eval r = .ok d →
        ∃ vn, SqlEquiv.evalExprWithDb db u node = some vn ∧ DatumRel d vn ∧
          Row.Conforms (Fin.append Γ ![τ]) (Fin.append r ![d] : Row (n + 1)))
    (hctx : ∀ (Γ : Fin n → SqlType) (τ : SqlType), NoBoolOrder (Fin.append Γ ![τ]) P →
      ∀ (r : Row n) (u : SqlEquiv.Row), RowRel cf fold r u → r.Conforms Γ →
      ∀ (d : Datum) (vn : SqlEquiv.Value), SqlEquiv.evalExprWithDb db u node = some vn →
        DatumRel d vn → Row.Conforms (Fin.append Γ ![τ]) (Fin.append r ![d] : Row (n + 1)) →
      ∀ dp, P.eval (Fin.append r ![d]) = .ok dp →
        ∃ v, SqlEquiv.evalExprWithDb db u w = some v ∧ DatumRel dp v) :
    WhereOk cf fold db D (some w) qf
      (.project (fun i : Fin n => .col (Fin.castLE (Nat.le_succ n) i))
        (.select P (.attach kind rq qf))) := by
  refine ⟨fun Γ hΓ => (typeOf_attachWhere hΓ).1, fun h => h.2.2.2.2, ?_, ?_⟩
  · intro Γ hΓ hnb hd
    obtain ⟨-, Δ, τ, hΔ, -, -, -⟩ := typeOf_attachWhere hΓ
    have hs := hbody (by simp [hΔ]) hnb.2.2.2.1
    simp [Query.divSafe, Expr.divSafe, hd, hs, hkdiv, hPdiv]
  · intro Γ Rf R U hΓ hnb hRf hR hrows
    obtain ⟨hqfT, Δ, τ, hΔ, hattT, hk1, hk2⟩ := typeOf_attachWhere hΓ
    rw [Query.eval_project, Query.eval_select, Query.eval_attach] at hR
    obtain ⟨F, hF, hR⟩ := bind_ok hR
    obtain ⟨E, hE, hF⟩ := bind_ok hF
    obtain ⟨ss, hss, hE⟩ := bind_ok hE
    obtain ⟨x, hx, hE⟩ := bind_ok hE
    obtain ⟨Rf', hRf', hE⟩ := bind_ok hE
    rw [hRf] at hRf'
    cases hRf'
    refine attachFilter_rel cf fold (fun u => SqlEquiv.evalExprWithDb db u w)
      (fun r u hru hc d hd dp hdp => ?_) hrows hE hF hR
    obtain ⟨vn, hvn, hrn, hcx⟩ := hnode Γ Δ τ hqfT hΔ hattT hnb.2.2 hk1 hk2 ss x hss hx r u hru
      hc d hd
    exact hctx Γ τ (hnb.2.1 _ hattT) r u hru hc d vn hvn hrn hcx dp hdp

/-- The subquery bodies of steps 6b and 6c: a statement of `elabStmt_correct_join` or of
    `elabStmt_correct_agg`, without `ORDER BY`, `LIMIT` or `OFFSET`. -/
inductive BodyOk : SqlEquiv.SelectStmt → Prop
  | plain {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
      {wh : Option SqlEquiv.Expr} (hit : itemsFragment items = true)
      (hff : fromFragment f = true) (hw : ∀ w ∈ wh, isFragment w = true) :
      BodyOk (.mk false items (some f) wh [] none [] none none)
  | agg {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
      {wh : Option SqlEquiv.Expr} (hai : CorrectAgg.aggItems items = true) (hne : items ≠ [])
      (hff : fromFragment f = true) (hw : ∀ w ∈ wh, isFragment w = true) :
      BodyOk (.mk false items (some f) wh [] none [] none none)

/-- Such a body, elaborated as a subquery, is safe, evaluates, and its rows relate to the rows
    `SqlEquiv` computes for it under every outer row. -/
theorem body_ctx (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {body : SqlEquiv.SelectStmt} (hb : BodyOk body) {rq : Query N.S 1} {rc : Fin 1 → Column}
    (hsub : elabSubQuery N 15 (.simple body) = .ok ⟨1, rq, rc⟩)
    (hty : rq.typeOf.isSome) (hnbq : QNoBoolOrder rq) :
    rq.IsSafe ∧ ∃ ss, rq.eval D = .ok ss ∧
      ∀ ctx, List.Forall₂ OutRel ss (SqlEquiv.evalSelectWithContext db ctx body) := by
  cases hb with
  | @plain items f wh hit hff hw =>
    have hst : elabStmt N (joinStmt items f wh [] none none) = .ok ⟨1, rq, rc⟩ := by
      rw [elabSubQuery] at hsub
      simp only [joinStmt, elabStmt, elabQuery, elabQueryRaw, elabSelect]
      rw [elabSelectF_fuel N 16 14 hff hw, hsub]
      simp [hty, bind, Except.bind, pure, Except.pure]
    obtain ⟨hs, ss, hss, -, -, -, hctx'⟩ := elabStmt_correct_join_ctx N hfold hfoldCI hwn hfix hD
      hrel hit hff (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq) (by simp) (by simp) hst hnbq
    exact ⟨hs, ss, hss, hctx' rfl⟩
  | @agg items f wh hai hne hff hw =>
    have hst : elabStmt N (CorrectAgg.aggStmt items f wh) = .ok ⟨1, rq, rc⟩ := by
      rw [elabSubQuery] at hsub
      simp only [CorrectAgg.aggStmt, elabStmt, elabQuery, elabQueryRaw, elabSelect]
      rw [elabSelectF_fuel N 16 14 hff hw, hsub]
      simp [hty, bind, Except.bind, pure, Except.pure]
    obtain ⟨hs, ss, hss, -, -, -, hctx'⟩ := CorrectAgg.elabStmt_correct_agg_w N hfold hfoldCI hwn
      hfix hD hrel hai hne hff (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq) hst hnbq
    exact ⟨hs, ss, hss, hctx'⟩

/-- The typed value of `e [NOT] IN (vals)` is a truth value. -/
theorem inExpr_hasType {n : ℕ} {neg : Bool} {e' : Expr n} {vals : List Datum} {r : Row n}
    {d : Datum} (h : (inExpr neg e' vals).eval r = .ok d) : d.HasType .bool := by
  unfold inExpr at h
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte, Expr.eval_inList] at h
    obtain ⟨de, -, h⟩ := bind_ok h
    obtain ⟨t, -, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h; exact Truth.toDatum_hasType t
  · simp only [↓reduceIte, Expr.eval] at h
    obtain ⟨dl, hdl, h⟩ := bind_ok h
    obtain ⟨de, -, hdl⟩ := bind_ok hdl
    obtain ⟨t, -, hdl⟩ := bind_ok hdl
    simp only [pure, Except.pure, Except.ok.injEq] at hdl
    subst hdl
    simp [SqlCore.evalUnOp, Except.map, Functor.map] at h
    subst h; exact Truth.toDatum_hasType _


/-- The subquery nodes of steps 6b and 6c, with their bodies: `e [NOT] IN (body)` with the probe
    in the expression fragment, or the scalar subquery `(body)` in a dialect that takes the
    first row of several (sqlite, `DialectConfig.scalarSubqueryRows`; the typed core's safety
    check asks for it, though a `BodyOk.agg` body has exactly one row). -/
inductive NodeOk (N : NamedSchema) : SqlEquiv.Expr → SqlEquiv.SubQuery → Prop
  | inSub {e : SqlEquiv.Expr} {neg : Bool} {body : SqlEquiv.SelectStmt}
      (he : isFragment e = true) (hb : BodyOk body) :
      NodeOk N (.inSubquery e neg (.simple body)) (.simple body)
  | scalar {body : SqlEquiv.SelectStmt} (hcfg : N.config.scalarSubqueryRows = .firstRow)
      (hb : BodyOk body) : NodeOk N (.subquery (.simple body)) (.simple body)

/-- The `WHERE` clauses of steps 6b and 6c: a `HoleCtx` predicate over such a node: the node,
    `a op node` for a comparison, or either under `AND` next to fragment conjuncts. The other
    expressions must not refer to the name of the column the elaborator attaches (`?subquery?`;
    the parser cannot produce it). -/
def SubWhere (N : NamedSchema) (w : SqlEquiv.Expr) : Prop :=
  ∃ node sq, NodeOk N node sq ∧ HoleCtx N.fold node w

/-- **Such a clause provides `WhereOk`.** -/
theorem whereOk_of_subWhere (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {n : ℕ} {cf : Fin n → Column} {qf q₀ : Query N.S n} {w : SqlEquiv.Expr}
    (hw : SubWhere N w)
    (h : elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf (some w) = .ok q₀) :
    WhereOk cf N.fold db D (some w) qf q₀ := by
  obtain ⟨node, sq, hnode, hctxW⟩ := hw
  cases hnode with
  | @inSub e neg body he hb =>
    have hs := holeCtx_subs (fold := N.fold) (node := .inSubquery e neg (.simple body))
      (sq := .simple body) (by simp [subsOf]) hctxW
    obtain ⟨r, h1, e', P, hsub, he', hP, rfl⟩ := elabWhere_one_inSub N _ cf qf hs h
    obtain ⟨m, rq, rc⟩ := r
    dsimp only at h1
    subst h1
    have htp := translates_of_elab cf N.fold e he he'
    have hel := fun τ => holeCtx_elab cf N.fold .bool τ
      (hookOf n (.inSubquery e neg (.simple body)) (.simple body))
      (.inSubquery e neg (.simple body)) (hookOf_node ..) (fun x hx => hookOf_ne _ _ _ hx) rfl
      (fun _ _ _ hc => by cases hc) db hctxW hP
    refine whereOk_attach cf N.fold db D (Translates.divSafe _ _ htp) (hel .bool).1
      (fun hty hnb => (body_ctx N hfold hfoldCI hwn hfix hD hrel hb hsub hty hnb).1.2) ?_
      (fun Γ τ => (hel τ).2 Γ)
    intro Γ Δ τ hqf hΔ _ hnbA _ hk2 ss x hss hx r u hru hc d hd
    simp only [SubKind.extra, Except.ok.injEq] at hx
    subst hx
    obtain ⟨-, ss', hss', hctx'⟩ := body_ctx N hfold hfoldCI hwn hfix hD hrel hb hsub
      (by simp [hΔ]) hnbA.2.1
    rw [hss] at hss'
    cases hss'
    have hsubrows : List.Forall₂ SubRowRel (ss.map (· 0))
        (SqlEquiv.evalSubQueryWithContext db u (.simple body)) := by
      rw [SqlEquiv.evalSubQuery_simple, List.forall₂_map_left_iff]
      exact (hctx' u).imp fun _ _ h => subRowRel_of_outRel h
    obtain ⟨vn, hvn, hrn⟩ := inExpr_eval_rel cf N.fold db hru hc htp (hnbA.1 Γ hqf) hsubrows hd
    refine ⟨vn, hvn, hrn, conforms_append_single hc ?_⟩
    rw [hk2 neg e' rfl]
    exact inExpr_hasType hd
  | @scalar body hcfg hb =>
    have hs := holeCtx_subs (fold := N.fold) (node := .subquery (.simple body))
      (sq := .simple body) (by simp [subsOf]) hctxW
    obtain ⟨r, h1, P, hsub, hP, rfl⟩ := elabWhere_one_scalar N _ cf qf hs h
    obtain ⟨m, rq, rc⟩ := r
    dsimp only at h1
    subst h1
    have hel := fun τ => holeCtx_elab cf N.fold (rc ⟨0, by omega⟩).type τ
      (hookOf n (.subquery (.simple body)) (.simple body))
      (.subquery (.simple body)) (hookOf_node ..) (fun x hx => hookOf_ne _ _ _ hx) rfl
      (fun _ _ _ hc => by cases hc) db hctxW hP
    refine whereOk_attach cf N.fold db D (by simp only [SubKind.divSafe, hcfg]; decide) (hel .bool).1
      (fun hty hnb => (body_ctx N hfold hfoldCI hwn hfix hD hrel hb hsub hty hnb).1.2) ?_
      (fun Γ τ => (hel τ).2 Γ)
    intro Γ Δ τ hqf hΔ _ hnbA hk1 _ ss x hss hx r u hru hc d hd
    obtain ⟨-, ss', hss', hctx'⟩ := body_ctx N hfold hfoldCI hwn hfix hD hrel hb hsub
      (by simp [hΔ]) hnbA.2.1
    rw [hss] at hss'
    cases hss'
    have hτ := hk1 _ rfl
    have hconf := Query.conforms_of_eval_eq_ok hD hΔ hss
    simp only [SubKind.extra] at hx
    rcases hsc : scalarOf (N.config.scalarSubqueryRows == .firstRow) (ss.map (· 0)) with err | dv
    · simp [hsc] at hx
    simp only [hsc, Functor.map, Except.map, Except.ok.injEq] at hx
    subst hx
    rw [Expr.eval_ofDatum, Except.ok.injEq] at hd
    subst hd
    rw [SqlEquiv.evalExprWithDb_subquery_simple]
    have hfa := hctx' u
    generalize SqlEquiv.evalSelectWithContext db u body = outs at hfa ⊢
    match ss, hfa, hsc, hconf with
    | [], hfa, hsc, _ =>
      cases hfa
      simp only [List.map_nil, scalarOf, Except.ok.injEq] at hsc
      subst hsc
      exact ⟨.null none, rfl, ⟨none, rfl⟩, conforms_append_single hc (Datum.hasType_none _)⟩
    | s :: rest, hfa, hsc, hconf =>
      cases hfa with
      | cons hsu hrest =>
        obtain ⟨nm, val, rfl, hsv⟩ := subRowRel_of_outRel hsu
        have hdv : dv = s 0 := by
          cases rest with
          | nil => simpa [scalarOf] using hsc.symm
          | cons s' rest' =>
            simp only [List.map_cons, scalarOf] at hsc
            split at hsc
            · simpa using hsc.symm
            · cases hsc
        subst hdv
        refine ⟨val, rfl, hsv, conforms_append_single hc ?_⟩
        rw [hτ]
        exact hconf s List.mem_cons_self 0

/-! ### The statement theorems -/

/-- **Elaborator correctness for `WHERE … e [NOT] IN (SELECT …)` (#352, step 6b).** For
    `SELECT e₁, …, eₖ FROM f WHERE w [ORDER BY …] [LIMIT n] [OFFSET m]` with `w` a `SubWhere`
    clause and the rest as in `elabStmt_correct_join`, the subquery uncorrelated (the elaborator
    rejects a correlated one): when the statement elaborates, the typed query evaluates, and its
    rows relate, in order, to `SqlEquiv`'s. `SqlEquiv` re-evaluates the body for every outer row,
    on rows that carry the outer row; the typed core evaluates it once. The three-valued result
    agrees, `NULL`s included (`inSub_agree`). -/
theorem elabStmt_correct_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
    {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ} {w : SqlEquiv.Expr}
    (hit : itemsFragment items = true) (hff : fromFragment f = true) (hw : SubWhere N w)
    (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c)
    (hnamed : orderBy ≠ [] → itemsNamed items = true)
    {el : Elaborated N.S}
    (h : elabStmt N (joinStmt items f (some w) orderBy lim off) = .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (joinStmt items f (some w) orderBy lim off)).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  obtain ⟨-, rs, hrs, out, hout, hr, -⟩ := elabStmt_correct_join_ctx N hfold hfoldCI hwn hfix hD
    hrel hit hff (fun _ _ _ _ hq => whereOk_of_subWhere N hfold hfoldCI hwn hfix hD hrel hw hq)
    hcols hnamed h hnb
  exact ⟨rs, hrs, out, hout, hr⟩

/-- **The same under `SELECT DISTINCT`**, up to the order of the rows (as
    `elabStmt_correct_distinct`). -/
theorem elabStmt_correct_distinct_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {w : SqlEquiv.Expr}
    (hit : itemsFragment items = true) (hff : fromFragment f = true) (hw : SubWhere N w)
    {el : Elaborated N.S}
    (h : elabStmt N (CorrectDistinct.distinctStmt items f (some w)) = .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (CorrectDistinct.distinctStmt items f (some w))).2 = some out ∧
        ∃ rs', rs.Perm rs' ∧ List.Forall₂ OutRel rs' out :=
  CorrectDistinct.elabStmt_correct_distinct_w N hfold hfoldCI hwn hfix hD hrel hit hff
    (fun _ _ _ _ hq => whereOk_of_subWhere N hfold hfoldCI hwn hfix hD hrel hw hq) h hnb

/-- **The same under aggregates without `GROUP BY`** (as `elabStmt_correct_agg`): one row,
    related to `SqlEquiv`'s one row. -/
theorem elabStmt_correct_agg_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {w : SqlEquiv.Expr}
    (hai : CorrectAgg.aggItems items = true) (hne : items ≠ []) (hff : fromFragment f = true)
    (hw : SubWhere N w)
    {el : Elaborated N.S}
    (h : elabStmt N (CorrectAgg.aggStmt items f (some w)) = .ok el) (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (CorrectAgg.aggStmt items f (some w))).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  obtain ⟨-, rs, hrs, out, hout, hr, -⟩ := CorrectAgg.elabStmt_correct_agg_w N hfold hfoldCI hwn
    hfix hD hrel hai hne hff
    (fun _ _ _ _ hq => whereOk_of_subWhere N hfold hfoldCI hwn hfix hD hrel hw hq) h hnb
  exact ⟨rs, hrs, out, hout, hr⟩

/-- **The same under aggregates next to bare columns or `AVG`, without `GROUP BY`** (as
    `elabStmt_correct_aggBare`): one row, an `AVG` item related up to rounding (`OutRelI`). -/
theorem elabStmt_correct_aggBare_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {w : SqlEquiv.Expr}
    (hgi : CorrectGrouped.groupedItems items = true)
    (hai : ∃ it ∈ items, CorrectGrouped.itemAggFragment (itemExpr it) = true)
    (hff : fromFragment f = true) (hbf : CorrectGrouped.BareOk N items [] none [])
    (hw : SubWhere N w)
    {el : Elaborated N.S}
    (h : elabStmt N (CorrectGrouped.groupedStmt items f (some w) [] none [] none none) = .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db
        (CorrectGrouped.groupedStmt items f (some w) [] none [] none none)).2 = some out ∧
        List.Forall₂ (CorrectGrouped.OutRelI items) rs out :=
  CorrectAggBare.elabStmt_correct_aggBare_w N hfold hfoldCI hwn hfix hD hrel hgi hai hff
    (fun _ _ _ _ hq => whereOk_of_subWhere N hfold hfoldCI hwn hfix hD hrel hw hq) hbf h hnb

end SqlBridge.CorrectSub
