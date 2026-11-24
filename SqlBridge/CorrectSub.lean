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
  * `AVG` bodies: the attached column relates up to rounding (`whereOk_of_avgWhere`), under
    `NonDecimalIn` (`nonDecimalIn_col`: any column of a schema without decimal columns) and
    `AvgBound` (`avgBound_of_rows`: `FROM` has at most `10¹⁶` rows);
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
    {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} {groupBy : List SqlEquiv.Expr}
    {having : Option SqlEquiv.Expr} {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hff : fromFragment f = true) (hw : ∀ w ∈ wh, isFragment w = true) :
    elabSelectF N a (.mk false items (some f) wh groupBy having orderBy lim off) =
      elabSelectF N b (.mk false items (some f) wh groupBy having orderBy lim off) := by
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
inductive HoleCtx (fold : String → String) (A : SqlEquiv.Expr → Prop) (node : SqlEquiv.Expr) :
    SqlEquiv.Expr → Prop
  | hole : HoleCtx fold A node node
  | cmpR {op : SqlEquiv.BinOp} {a : SqlEquiv.Expr} {c : CmpOp} (hop : elabBinOp op = .ok (.cmp c))
      (ha : isFragment a = true) (hna : noRefTo fold "?subquery?" a = true) (hA : A a) :
      HoleCtx fold A node (.binOp op a node)
  | andL {w b : SqlEquiv.Expr} (hw : HoleCtx fold A node w) (hb : isFragment b = true)
      (hnb : noRefTo fold "?subquery?" b = true) : HoleCtx fold A node (.binOp .and w b)
  | andR {a w : SqlEquiv.Expr} (ha : isFragment a = true)
      (hna : noRefTo fold "?subquery?" a = true) (hw : HoleCtx fold A node w) :
      HoleCtx fold A node (.binOp .and a w)

/-- An operand of a typed `AND` that evaluates is `NULL` or a boolean. -/
theorem and_operands {a b d : Datum} (h : SqlCore.evalBinOp .and a b = .ok d) :
    (a = none ∨ ∃ x, a = some (.bool x)) ∧ (b = none ∨ ∃ x, b = some (.bool x)) := by
  simp only [SqlCore.evalBinOp] at h
  rcases a with _ | a <;> rcases b with _ | b
  · exact ⟨.inl rfl, .inl rfl⟩
  · cases b <;> simp [Datum.toTruth, bind, Except.bind] at h ⊢
  · cases a <;> simp [Datum.toTruth, bind, Except.bind] at h ⊢
  · cases a <;> cases b <;> simp [Datum.toTruth, bind, Except.bind] at h ⊢

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
  (A : SqlEquiv.Expr → Prop) (R : Datum → SqlEquiv.Value → Prop) (Γ : Fin n → SqlType)
  (hRbool : ∀ d v, R d v → (d = none ∨ ∃ x, d = some (.bool x)) → DatumRel d v)
  (hRcmp : ∀ {op : SqlEquiv.BinOp} {c : CmpOp} {a : SqlEquiv.Expr} {a₀ : Expr n},
    elabBinOp op = .ok (.cmp c) → A a → elabExpr cols fold noHook a = .ok a₀ →
    ∀ {r : Row n} {da b d : Datum} {a' b' : SqlEquiv.Value}, r.Conforms Γ → a₀.eval r = .ok da →
      DatumRel da a' → R b b' →
      (c ≠ .eq → c ≠ .ne → ∀ x y, ¬ (da = some (.bool x) ∧ b = some (.bool y))) →
      SqlCore.evalBinOp (.cmp c) da b = .ok d →
      ∃ v, SqlEquiv.evalBinOp op (some a') (some b') = some v ∧ DatumRel d v)
include hhookN hhook hnf hnbin hRbool hRcmp

/-- What the elaboration `P` of a `HoleCtx` predicate `w` gives: it is safe, and it relates to
    `w` row by row, given that the attached column relates to the node's value by `R`. `R` is
    the exact relation, or a weaker one that still decides a comparison (`hRcmp`; an `AVG`, up
    to rounding) and is exact on what an `AND` accepts (`hRbool`). The clause that is the node
    alone relates by `R`. -/
theorem holeCtx_elab (db : SqlEquiv.Database) :
    ∀ {w : SqlEquiv.Expr}, HoleCtx fold A node w → ∀ {P : Expr (n + 1)},
      elabExpr (Fin.append cols ![subCol τc]) fold hook w = .ok P →
      P.divSafe = true ∧
      (NoBoolOrder (Fin.append Γ ![τ]) P →
        ∀ (r : Row n) (u : SqlEquiv.Row), RowRel cols fold r u → r.Conforms Γ →
        ∀ (d : Datum) (vn : SqlEquiv.Value), SqlEquiv.evalExprWithDb db u node = some vn →
          R d vn → Row.Conforms (Fin.append Γ ![τ]) (Fin.append r ![d] : Row (n + 1)) →
        ∀ dp, P.eval (Fin.append r ![d]) = .ok dp →
          ∃ v, SqlEquiv.evalExprWithDb db u w = some v ∧ (w = node → R dp v) ∧
            (w ≠ node → DatumRel dp v)) := by
  have hfragHook : ∀ x, isFragment x = true → hook x = none := fun x hx =>
    hhook x (fun h => by rw [h, hnf] at hx; cases hx)
  have hΓ' : (Fin.append Γ ![τ]) ∘ Fin.castAdd 1 = Γ := by
    funext i; simp [Fin.append_left]
  intro w hw
  induction hw with
  | hole =>
    intro P h
    rw [elabExpr_hook_some _ _ _ hhookN, Except.ok.injEq] at h
    subst h
    refine ⟨rfl, fun _ r u _ _ d vn hvn hrn _ dp hdp => ?_⟩
    rw [eval_col_last_append, Except.ok.injEq] at hdp
    exact ⟨vn, hvn, fun _ => hdp ▸ hrn, fun h => absurd rfl h⟩
  | @cmpR op a c hop ha hna hA =>
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
      BinOp.isDivision], fun hnbP r u hru hc d vn hvn hrn hcx dp hdp => ?_⟩
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
    obtain ⟨v, hv, hrel⟩ := hRcmp hop hA ha₀ hc hea' hra hrn (fun h1 h2 x y hxy => by
      rcases hcc with hcc | hcc | ⟨τa, hτ, hτb⟩
      · exact h1 hcc
      · exact h2 hcc
      · rcases Expr.eval_ok_or_divisionByZero hcx hτ with ⟨d', hd', hty⟩ | ⟨hdz, _⟩
        · rw [hea1] at hd'; cases hd'
          rw [hxy.1] at hty
          exact hτb (by simpa [Datum.HasType, Value.type] using hty.symm)
        · rw [hea1] at hdz; cases hdz) hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_binOp, hva, hvn, hv],
      fun h => absurd h.symm (hnbin op a node), fun _ => hrel⟩
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
      BinOp.isDivision], fun hnbP r u hru hc d vn hvn hrn hcx dp hdp => ?_⟩
    obtain ⟨hnw, hnb'⟩ := hnbP
    obtain ⟨dw, db', hew1, heb1, hd⟩ := eval_binary_ok hdp
    rw [eval_retypeNull] at hew1 heb1
    rw [Expr.eval_rename_castAdd] at heb1
    obtain ⟨vw, hvw, hrw1, hrw2⟩ := hrelw (noBoolOrder_of_retypeNull _ _ hnw) r u hru hc d vn
      hvn hrn hcx dw hew1
    have hrw : DatumRel dw vw := by
      by_cases hwn : w = node
      · exact hRbool _ _ (hrw1 hwn) (and_operands hd).1
      · exact hrw2 hwn
    have hnbb : NoBoolOrder Γ b₀ := by
      have h2 := noBoolOrder_rename _ _ _ (noBoolOrder_of_retypeNull _ _ hnb')
      rwa [hΓ'] at h2
    obtain ⟨vb, hvb, hrb⟩ := Translates.eval_rel cols fold db hru hc htb hnbb heb1
    obtain ⟨v, hv, hrel⟩ := and_agree hrw hrb hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_binOp, hvw, hvb, hv],
      fun h => absurd h.symm (hnbin .and w b), fun _ => hrel⟩
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
      BinOp.isDivision], fun hnbP r u hru hc d vn hvn hrn hcx dp hdp => ?_⟩
    obtain ⟨hna', hnw⟩ := hnbP
    obtain ⟨da, dw, hea1, hew1, hd⟩ := eval_binary_ok hdp
    rw [eval_retypeNull] at hea1 hew1
    rw [Expr.eval_rename_castAdd] at hea1
    obtain ⟨vw, hvw, hrw1, hrw2⟩ := hrelw (noBoolOrder_of_retypeNull _ _ hnw) r u hru hc d vn
      hvn hrn hcx dw hew1
    have hrw : DatumRel dw vw := by
      by_cases hwn : w = node
      · exact hRbool _ _ (hrw1 hwn) (and_operands hd).2
      · exact hrw2 hwn
    have hnba : NoBoolOrder Γ a₀ := by
      have h2 := noBoolOrder_rename _ _ _ (noBoolOrder_of_retypeNull _ _ hna')
      rwa [hΓ'] at h2
    obtain ⟨va, hva, hra⟩ := Translates.eval_rel cols fold db hru hc hta hnba hea1
    obtain ⟨v, hv, hrel⟩ := and_agree hra hrw hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_binOp, hva, hvw, hv],
      fun h => absurd h.symm (hnbin .and a w), fun _ => hrel⟩

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
    {A : SqlEquiv.Expr → Prop} (hn : subsOf node = [(node, sq)]) :
    ∀ {w : SqlEquiv.Expr}, HoleCtx fold A node w → subsOf w = [(node, sq)] := by
  intro w hw
  induction hw with
  | hole => exact hn
  | cmpR _ ha _ _ => simp [subsOf, subsOf_frag _ ha, hn]
  | andL _ hb _ ih => simp [subsOf, subsOf_frag _ hb, ih]
  | andR ha _ _ ih => simp [subsOf, subsOf_frag _ ha, ih]

/-- The elaborated `WHERE w` when `w`'s one subquery is the `IN` node. -/
theorem elabWhere_one_inSub (N : NamedSchema) (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S))
    {n : ℕ} (cols : Fin n → Column) (q : Query N.S n) {w e : SqlEquiv.Expr} {neg : Bool}
    {sq : SqlEquiv.SubQuery} {q₀ : Query N.S n}
    (hs : subsOf w = [(.inSubquery e neg sq, sq)])
    (hun : ∀ qq c, sub sq ≠ .error (.unknownColumn qq c))
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
      | exact absurd hsb (hun _ _)
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
    (hun : ∀ qq c, sub sq ≠ .error (.unknownColumn qq c))
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
      | exact absurd hsb (hun _ _)
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
  simp only [Query.typeOf, Query.typeOfIn, Option.bind_eq_bind, Option.bind_eq_some_iff] at hatt
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
    {R : Datum → SqlEquiv.Value → Prop}
    (hkdiv : kind.divSafe = true) (hPdiv : P.divSafe = true)
    (hbody : rq.typeOf.isSome → QNoBoolOrder rq → rq.divSafe = true)
    (hnode : ∀ (Γ : Fin n → SqlType) (Δ : Fin 1 → SqlType) (τ : SqlType), qf.typeOf = some Γ →
      rq.typeOf = some Δ → (Query.attach kind rq qf).typeOf = some (Fin.append Γ ![τ]) →
      QNoBoolOrder (Query.attach kind rq qf) →
      (∀ fr, kind = .scalar fr → τ = Δ 0) → (∀ neg e, kind = .inSub neg e → τ = .bool) →
      ∀ ss x, rq.eval D = .ok ss → kind.extra (ss.map (· 0)) = .ok x →
      ∀ r u, RowRel cf fold r u → r.Conforms Γ → ∀ d, x.eval r = .ok d →
        ∃ vn, SqlEquiv.evalExprWithDb db u node = some vn ∧ R d vn ∧
          Row.Conforms (Fin.append Γ ![τ]) (Fin.append r ![d] : Row (n + 1)))
    (hctx : ∀ (Γ : Fin n → SqlType) (τ : SqlType), qf.typeOf = some Γ →
      NoBoolOrder (Fin.append Γ ![τ]) P →
      ∀ (r : Row n) (u : SqlEquiv.Row), RowRel cf fold r u → r.Conforms Γ →
      ∀ (d : Datum) (vn : SqlEquiv.Value), SqlEquiv.evalExprWithDb db u node = some vn →
        R d vn → Row.Conforms (Fin.append Γ ![τ]) (Fin.append r ![d] : Row (n + 1)) →
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
    exact hctx Γ τ hqfT (hnb.2.1 _ hattT) r u hru hc d vn hvn hrn hcx dp hdp

/-- The subquery bodies of steps 6b and 6c: a statement of `elabStmt_correct_join`, of
    `elabStmt_correct_agg`, or a grouped one, without `ORDER BY`, `LIMIT` or `OFFSET`. -/
inductive BodyOk : SqlEquiv.SelectStmt → Prop
  /-- A plain statement, with `ORDER BY` columns and `LIMIT` / `OFFSET` (#411). -/
  | plain {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
      {wh : Option SqlEquiv.Expr} {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
      (hit : itemsFragment items = true)
      (hff : fromFragment f = true) (hw : ∀ w ∈ wh, isFragment w = true)
      (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c)
      (hnamed : orderBy ≠ [] → itemsNamed items = true) :
      BodyOk (.mk false items (some f) wh [] none orderBy lim off)
  | agg {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
      {wh : Option SqlEquiv.Expr} (hai : CorrectAgg.aggItems items = true) (hne : items ≠ [])
      (hff : fromFragment f = true) (hw : ∀ w ∈ wh, isFragment w = true) :
      BodyOk (.mk false items (some f) wh [] none [] none none)
  /-- A grouped body (#409): a statement of `elabStmt_correct_grouped_ctx` whose item columns are
      all keys, without an `AVG` item (related only up to rounding, which a membership test could
      tell apart) or an `AVG` comparison in `HAVING`. -/
  | grouped {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
      {wh : Option SqlEquiv.Expr} {groupBy : List SqlEquiv.Expr} {having : Option SqlEquiv.Expr}
      (hgi : CorrectGrouped.groupedItems items = true)
      (hna : ∀ it ∈ items, CorrectAvg.avgFragment (itemExpr it) = false)
      (hgb : groupBy ≠ []) (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c)
      (hkeys : ∀ c ∈ CorrectGroup.colRefs items, SqlEquiv.Expr.col c ∈ groupBy)
      (hff : fromFragment f = true) (hw : ∀ w ∈ wh, isFragment w = true)
      (hhv : ∀ h ∈ having, CorrectGroup.havingFragment groupBy h = true)
      (hhn : ∀ h ∈ having, CorrectGroup.hasCmpAvg h = false)
      {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
      (hob : ∀ o ∈ orderBy, CorrectGrouped.OrderKeyOk items groupBy o.expr)
      (hnm : orderBy ≠ [] → ∀ it ∈ items, '.' ∉ (outName it).toList ∧
        ∀ k, (outName it).toLower ≠ SqlEquiv.groupOrderKeyName k) :
      BodyOk (.mk false items (some f) wh groupBy having orderBy lim off)

/-- Such a body, elaborated as a subquery, is safe, evaluates, and its rows relate to the rows
    `SqlEquiv` computes for it under every outer row. -/
theorem body_ctx (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {body : SqlEquiv.SelectStmt} (hb : BodyOk body) {fu m : ℕ} {rq : Query N.S m}
    {rc : Fin m → Column} (hsub : elabSubQuery N (fu + 1) (.simple body) = .ok ⟨m, rq, rc⟩)
    (hty : rq.typeOf.isSome) (hnbq : QNoBoolOrder rq) :
    rq.IsSafe ∧ ∃ ss, rq.eval D = .ok ss ∧
      ∀ ctx, List.Forall₂ OutRel ss (SqlEquiv.evalSelectWithContext db ctx body) := by
  cases hb with
  | @plain items f wh orderBy lim off hit hff hw hcols hnamed =>
    have hst : elabStmt N (joinStmt items f wh orderBy lim off) = .ok ⟨m, rq, rc⟩ := by
      rw [elabSubQuery] at hsub
      simp only [joinStmt, elabStmt, elabQuery, elabQueryRaw, elabSelect]
      rw [elabSelectF_fuel N 16 fu hff hw, hsub]
      simp [hty, bind, Except.bind, pure, Except.pure]
    obtain ⟨hs, ss, hss, -, -, -, hctx'⟩ := elabStmt_correct_join_ctx N hfold hfoldCI hwn hfix hD
      hrel hit hff (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq) hcols hnamed hst hnbq
    exact ⟨hs, ss, hss, hctx'⟩
  | @agg items f wh hai hne hff hw =>
    have hst : elabStmt N (CorrectAgg.aggStmt items f wh) = .ok ⟨m, rq, rc⟩ := by
      rw [elabSubQuery] at hsub
      simp only [CorrectAgg.aggStmt, elabStmt, elabQuery, elabQueryRaw, elabSelect]
      rw [elabSelectF_fuel N 16 fu hff hw, hsub]
      simp [hty, bind, Except.bind, pure, Except.pure]
    obtain ⟨hs, ss, hss, -, -, -, hctx'⟩ := CorrectAgg.elabStmt_correct_agg_w N hfold hfoldCI hwn
      hfix hD hrel hai hne hff (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq) hst hnbq
    exact ⟨hs, ss, hss, hctx'⟩
  | @grouped items f wh groupBy having hgi hna hgb hgc hkeys hff hw hhv hhn orderBy lim off hob hnm =>
    have hst : elabStmt N (CorrectGrouped.groupedStmt items f wh groupBy having orderBy lim off) =
        .ok ⟨m, rq, rc⟩ := by
      rw [elabSubQuery] at hsub
      simp only [CorrectGrouped.groupedStmt, elabStmt, elabQuery, elabQueryRaw, elabSelect]
      rw [elabSelectF_fuel N 16 fu hff hw, hsub]
      simp [hty, bind, Except.bind, pure, Except.pure]
    obtain ⟨hs, ss, hss, hctx'⟩ := CorrectGrouped.elabStmt_correct_grouped_ctx N hfold hfoldCI hwn
      hfix hD hrel hgi hgb hgc hff (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq) hhv
      (CorrectGrouped.havingAvgOk_of_noAvg hhn) hob (.inl hkeys) hnm hst hnbq
    exact ⟨hs, ss, hss, fun ctx => (hctx' ctx).imp fun _ _ h =>
      CorrectGrouped.outRel_of_outRelI hna h⟩

/-- The bodies of `IN` / `NOT IN` (step 6b, set operations #410): a `BodyOk` statement, or
    `UNION [ALL]`, `INTERSECT` or `EXCEPT` over such bodies, nested. -/
inductive SubBodyOk : SqlEquiv.SubQuery → Prop
  | simple {body : SqlEquiv.SelectStmt} (hb : BodyOk body) : SubBodyOk (.simple body)
  | compound {l r : SqlEquiv.SubQuery} (op : SqlEquiv.SetOp) (hl : SubBodyOk l)
      (hr : SubBodyOk r) : SubBodyOk (.compound l op r)

/-- A compound subquery that elaborates: its branches elaborate, with one fuel less, to queries
    of one arity, and the result is the corresponding typed operator over them. -/
theorem elabSubQuery_compound_shape (N : NamedSchema) {fu : ℕ} {l r : SqlEquiv.SubQuery}
    {op : SqlEquiv.SetOp} {e : Elaborated N.S}
    (h : elabSubQuery N (fu + 1) (.compound l op r) = .ok e) :
    ∃ (n : ℕ) (ql qr : Query N.S n) (cl cr : Fin n → Column),
      elabSubQuery N fu l = .ok ⟨n, ql, cl⟩ ∧ elabSubQuery N fu r = .ok ⟨n, qr, cr⟩ ∧
      e = ⟨n, CorrectSetOp.setOpQuery op ql qr, cl⟩ := by
  rw [elabSubQuery] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  obtain ⟨⟨n, ql, cl⟩, hl, h⟩ := bind_ok h
  obtain ⟨⟨m, qr, cr⟩, hr, h⟩ := bind_ok h
  dsimp only at h
  split at h
  swap
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hmn
  subst hmn
  refine ⟨m, ql, qr, cl, cr, hl, hr, ?_⟩
  cases op <;> simp only [pure, Except.pure, Except.ok.injEq] at h <;>
    simpa [CorrectSetOp.setOpQuery] using h.symm

/-- **The body of `IN` under every outer row, up to row order.** Such a body, elaborated as a
    subquery, is safe and evaluates, and its rows are, up to their order, related to the rows
    `SqlEquiv` computes for it under every outer row. A set operation's rows are related only up
    to order (`CorrectSetOp.PermRel`, registry T18), which membership does not see
    (`inExpr_eval_perm`). -/
theorem subBody_ctx (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {sq : SqlEquiv.SubQuery} (hb : SubBodyOk sq) :
    ∀ {fu m : ℕ} {rq : Query N.S m} {rc : Fin m → Column},
      elabSubQuery N (fu + 1) sq = .ok ⟨m, rq, rc⟩ → rq.typeOf.isSome → QNoBoolOrder rq →
      rq.IsSafe ∧ ∃ ss, rq.eval D = .ok ss ∧
        ∀ ctx, CorrectSetOp.PermRel ss (SqlEquiv.evalSubQueryWithContext db ctx sq) := by
  induction hb with
  | simple hb =>
    intro fu m rq rc hsub hty hnb
    obtain ⟨hs, ss, hss, hctx⟩ := body_ctx N hfold hfoldCI hwn hfix hD hrel hb hsub hty hnb
    exact ⟨hs, ss, hss, fun ctx => by
      rw [SqlEquiv.evalSubQuery_simple]; exact .of_forall₂ (hctx ctx)⟩
  | @compound l r op _ _ ihl ihr =>
    intro fu m rq rc hsub hty hnb
    obtain ⟨n, ql, qr, cl, cr, hl, hr, he⟩ := elabSubQuery_compound_shape N hsub
    cases he
    cases fu with
    | zero => simp [elabSubQuery, throw, throwThe, MonadExceptOf.throw] at hl
    | succ fu =>
    have hΓ : ∃ Γ, ql.typeOf = some Γ ∧ qr.typeOf = some Γ := by
      cases op <;> simp only [CorrectSetOp.setOpQuery, Query.typeOf, Query.typeOfIn,
          Option.bind_eq_bind] at hty <;>
        cases hql : ql.typeOfIn none <;> simp only [hql, Option.bind_none, Option.bind_some,
          Option.isSome_none, Bool.false_eq_true] at hty <;>
        split at hty <;> first | exact ⟨_, hql, by assumption⟩ | simp at hty
    obtain ⟨Γ, hΓl, hΓr⟩ := hΓ
    have hnb' : QNoBoolOrder ql ∧ QNoBoolOrder qr := by
      cases op <;> simp only [CorrectSetOp.setOpQuery, QNoBoolOrder] at hnb <;> exact hnb
    obtain ⟨hsl, rs, hrs, hcl⟩ := ihl hl (by simp [hΓl]) hnb'.1
    obtain ⟨hsr, ss, hss, hcr⟩ := ihr hr (by simp [hΓr]) hnb'.2
    obtain ⟨ts, hts, -⟩ := CorrectSetOp.setOpQuery_rel hD hΓl hΓr hrs hss (hcl []) (hcr [])
      op none
    refine ⟨⟨hty, ?_⟩, ts, hts, fun ctx => ?_⟩
    · have h1 := hsl.2; have h2 := hsr.2
      cases op <;> simp_all [CorrectSetOp.setOpQuery, Query.divSafe]
    · rw [SqlEquiv.evalSubQuery_compound]
      obtain ⟨ts', hts', hp⟩ := CorrectSetOp.setOpQuery_rel hD hΓl hΓr hrs hss (hcl ctx) (hcr ctx)
        op (SqlEquiv.SubQuery.outputNames? l)
      rw [hts] at hts'
      cases hts'
      exact hp

/-- Three-valued membership does not depend on the order of the values. -/
theorem datum_inList_perm {d : Datum} {vs vs' : List Datum} (hp : vs.Perm vs') {t : Truth}
    (h : d.inList vs = .ok t) : d.inList vs' = .ok t := by
  induction hp generalizing t with
  | nil => exact h
  | cons x _ ih =>
    rw [Datum.inList_cons] at h ⊢
    obtain ⟨t₁, ht₁, h⟩ := bind_ok h
    obtain ⟨t₂, ht₂, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [ht₁, ih ht₂, bind, Except.bind, pure, Except.pure]
  | swap x y l =>
    rw [Datum.inList_cons, Datum.inList_cons] at h ⊢
    obtain ⟨t₁, ht₁, h⟩ := bind_ok h
    obtain ⟨u, hu, h⟩ := bind_ok h
    obtain ⟨t₂, ht₂, hu⟩ := bind_ok hu
    obtain ⟨t₃, ht₃, hu⟩ := bind_ok hu
    simp only [pure, Except.pure, Except.ok.injEq] at h hu
    subst hu; subst h
    simp [ht₁, ht₂, ht₃, bind, Except.bind, pure, Except.pure, sup_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)

/-- So `e [NOT] IN (vals)` evaluates the same over a permutation of the values. -/
theorem inExpr_eval_perm {n : ℕ} {neg : Bool} {e' : Expr n} {vals vals' : List Datum}
    (hp : vals.Perm vals') {r : Row n} {d : Datum} (h : (inExpr neg e' vals).eval r = .ok d) :
    (inExpr neg e' vals').eval r = .ok d := by
  have base : ∀ {d : Datum}, (Expr.inList e' vals).eval r = .ok d →
      (Expr.inList e' vals').eval r = .ok d := by
    intro d h
    rw [Expr.eval_inList] at h ⊢
    obtain ⟨de, hde, h⟩ := bind_ok h
    obtain ⟨t, ht, h⟩ := bind_ok h
    simpa [hde, datum_inList_perm hp ht, bind, Except.bind] using h
  unfold inExpr at h ⊢
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact base h
  · simp only [↓reduceIte, Expr.eval_unary] at h ⊢
    obtain ⟨dl, hdl, h⟩ := bind_ok h
    rw [base hdl]
    exact h

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


/-- A subquery body that does not read the outer query (9.4b, decision D6): its elaboration does
    not fail on an unknown column. A correlated body elaborates as a `Query.lateral` column,
    which the engines validate (decision D4), and is outside the theorems of this file. -/
def uncorrelated (N : NamedSchema) (sq : SqlEquiv.SubQuery) : Bool :=
  match elabSubQuery N 15 sq with
  | .error (.unknownColumn _ _) => false
  | _ => true

theorem not_unknownColumn_of_uncorrelated {N : NamedSchema} {sq : SqlEquiv.SubQuery}
    (h : uncorrelated N sq = true) :
    ∀ qq c, elabSubQuery N 15 sq ≠ .error (.unknownColumn qq c) := by
  intro qq c he
  simp [uncorrelated, he] at h

/-- The subquery nodes of steps 6b and 6c, with their bodies: `e [NOT] IN (body)` with the probe
    in the expression fragment, or the scalar subquery `(body)` in a dialect that takes the
    first row of several (sqlite, `DialectConfig.scalarSubqueryRows`; the typed core's safety
    check asks for it, though a `BodyOk.agg` body has exactly one row). -/
inductive NodeOk (N : NamedSchema) : SqlEquiv.Expr → SqlEquiv.SubQuery → Prop
  | inSub {e : SqlEquiv.Expr} {neg : Bool} {sq : SqlEquiv.SubQuery}
      (he : isFragment e = true) (hb : SubBodyOk sq) (hun : uncorrelated N sq = true) :
      NodeOk N (.inSubquery e neg sq) sq
  | scalar {body : SqlEquiv.SelectStmt} (hcfg : N.config.scalarSubqueryRows = .firstRow)
      (hb : BodyOk body) (hun : uncorrelated N (.simple body) = true) :
      NodeOk N (.subquery (.simple body)) (.simple body)

/-- The `WHERE` clauses of steps 6b and 6c: a `HoleCtx` predicate over such a node: the node,
    `a op node` for a comparison, or either under `AND` next to fragment conjuncts. The other
    expressions must not refer to the name of the column the elaborator attaches (`?subquery?`;
    the parser cannot produce it). -/
def SubWhere (N : NamedSchema) (w : SqlEquiv.Expr) : Prop :=
  ∃ node sq, NodeOk N node sq ∧ HoleCtx N.fold (fun _ => True) node w

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
  | @inSub e neg sq he hb hun =>
    have hs := holeCtx_subs (fold := N.fold) (node := .inSubquery e neg sq)
      (sq := sq) (by simp [subsOf]) hctxW
    obtain ⟨r, h1, e', P, hsub, he', hP, rfl⟩ :=
      elabWhere_one_inSub N _ cf qf hs (not_unknownColumn_of_uncorrelated hun) h
    obtain ⟨m, rq, rc⟩ := r
    dsimp only at h1
    subst h1
    have htp := translates_of_elab cf N.fold e he he'
    have hel := fun (Γ : Fin n → SqlType) τ => holeCtx_elab cf N.fold .bool τ
      (hookOf n (.inSubquery e neg sq) sq)
      (.inSubquery e neg sq) (hookOf_node ..) (fun x hx => hookOf_ne _ _ _ hx) rfl
      (fun _ _ _ hc => by cases hc) (fun _ => True) DatumRel Γ (fun _ _ h _ => h)
      (by intro op c a a₀ hop _ _ r da b d a' b' _ _ ha hb hs hd; exact cmp_agree hop ha hb hs hd) db hctxW hP
    refine whereOk_attach cf N.fold db D (Translates.divSafe _ _ htp) (hel (fun _ => .int) .bool).1
      (fun hty hnb => (subBody_ctx N hfold hfoldCI hwn hfix hD hrel hb hsub hty hnb).1.2) ?_
      (fun Γ τ _ hnb r u hru hc d vn hvn hrn hcx dp hdp => by
        obtain ⟨v, hv, h1, h2⟩ := (hel Γ τ).2 hnb r u hru hc d vn hvn hrn hcx dp hdp
        exact ⟨v, hv, (Classical.em _).elim h1 h2⟩)
    intro Γ Δ τ hqf hΔ _ hnbA _ hk2 ss x hss hx r u hru hc d hd
    simp only [SubKind.extra, Except.ok.injEq] at hx
    subst hx
    obtain ⟨-, ss', hss', hctx'⟩ := subBody_ctx N hfold hfoldCI hwn hfix hD hrel hb hsub
      (by simp [hΔ]) hnbA.2.1
    rw [hss] at hss'
    cases hss'
    obtain ⟨sp, hp, hsp⟩ := hctx' u
    have hsubrows : List.Forall₂ SubRowRel (sp.map (· 0))
        (SqlEquiv.evalSubQueryWithContext db u sq) := by
      rw [List.forall₂_map_left_iff]
      exact hsp.imp fun _ _ h => subRowRel_of_outRel h
    obtain ⟨vn, hvn, hrn⟩ := inExpr_eval_rel cf N.fold db hru hc htp (hnbA.1 Γ hqf) hsubrows
      (inExpr_eval_perm (hp.map _) hd)
    refine ⟨vn, hvn, hrn, conforms_append_single hc ?_⟩
    rw [hk2 neg e' rfl]
    exact inExpr_hasType hd
  | @scalar body hcfg hb hun =>
    have hs := holeCtx_subs (fold := N.fold) (node := .subquery (.simple body))
      (sq := .simple body) (by simp [subsOf]) hctxW
    obtain ⟨r, h1, P, hsub, hP, rfl⟩ :=
      elabWhere_one_scalar N _ cf qf hs (not_unknownColumn_of_uncorrelated hun) h
    obtain ⟨m, rq, rc⟩ := r
    dsimp only at h1
    subst h1
    have hel := fun (Γ : Fin n → SqlType) τ => holeCtx_elab cf N.fold (rc ⟨0, by omega⟩).type τ
      (hookOf n (.subquery (.simple body)) (.simple body))
      (.subquery (.simple body)) (hookOf_node ..) (fun x hx => hookOf_ne _ _ _ hx) rfl
      (fun _ _ _ hc => by cases hc) (fun _ => True) DatumRel Γ (fun _ _ h _ => h)
      (by intro op c a a₀ hop _ _ r da b d a' b' _ _ ha hb hs hd; exact cmp_agree hop ha hb hs hd) db hctxW hP
    refine whereOk_attach cf N.fold db D (by simp only [SubKind.divSafe, hcfg]; decide) (hel (fun _ => .int) .bool).1
      (fun hty hnb => (body_ctx N hfold hfoldCI hwn hfix hD hrel hb hsub hty hnb).1.2) ?_
      (fun Γ τ _ hnb r u hru hc d vn hvn hrn hcx dp hdp => by
        obtain ⟨v, hv, h1, h2⟩ := (hel Γ τ).2 hnb r u hru hc d vn hvn hrn hcx dp hdp
        exact ⟨v, hv, (Classical.em _).elim h1 h2⟩)
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

/-! ### `AVG` bodies, compared up to rounding (step 6c) -/

/-- A filter keeps at most the rows it is given. -/
theorem filterRows_length_le {n : ℕ} (p : Expr n) : ∀ {R R' : List (Row n)},
    p.filterRows R = .ok R' → R'.length ≤ R.length
  | [], R', h => by
    simp only [Expr.filterRows, List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact Nat.le_refl _
  | r :: R, R', h => by
    obtain ⟨t, R'', -, hrs, rfl⟩ := filterRows_cons_ok h
    have ih := filterRows_length_le p hrs
    cases t.isTrue <;> simp only [List.length_cons] <;> simp <;> omega

/-- The `AVG` subquery bodies of step 6c: `SELECT AVG(e) FROM f [WHERE p]`. -/
inductive AvgBody : SqlEquiv.SelectStmt → Prop
  | mk {a : SqlEquiv.Expr} {al : Option String} {f : SqlEquiv.FromClause}
      {wh : Option SqlEquiv.Expr} (ha : CorrectAvg.avgFragment a = true) (hff : fromFragment f = true)
      (hw : ∀ w ∈ wh, isFragment w = true) :
      AvgBody (.mk false [.exprItem a al] (some f) wh [] none [] none none)

/-- Such a body, elaborated as a subquery, is safe and evaluates, and under every outer row
    `SqlEquiv` computes one row with one value, the typed one up to rounding (`AvgRel`). -/
theorem avgBody_ctx (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {body : SqlEquiv.SelectStmt} (hb : AvgBody body) {rq : Query N.S 1} {rc : Fin 1 → Column}
    (hsub : elabSubQuery N 15 (.simple body) = .ok ⟨1, rq, rc⟩)
    (hty : rq.typeOf.isSome) (hnbq : QNoBoolOrder rq) :
    rq.IsSafe ∧ ∃ ss, rq.eval D = .ok ss ∧
      ∀ ctx, List.Forall₂ (fun (s : Row 1) o => ∃ nm v, o = [(nm, v)] ∧ CorrectAvg.AvgRel (s 0) v) ss
        (SqlEquiv.evalSelectWithContext db ctx body) := by
  cases hb with
  | @mk a al f wh ha hff hw =>
    have hst : elabStmt N (CorrectGrouped.groupedStmt [.exprItem a al] f wh [] none [] none none) =
        .ok ⟨1, rq, rc⟩ := by
      rw [elabSubQuery] at hsub
      simp only [CorrectGrouped.groupedStmt, elabStmt, elabQuery, elabQueryRaw, elabSelect]
      rw [elabSelectF_fuel N 16 14 hff hw, hsub]
      simp [hty, bind, Except.bind, pure, Except.pure]
    obtain ⟨hs, ss, hss, -, hctx'⟩ := CorrectAggBare.elabStmt_correct_aggBare_ctx N hfold hfoldCI
      hwn hfix hD hrel (items := [.exprItem a al])
      (by simp [CorrectGrouped.groupedItems, CorrectGrouped.itemAggFragment, ha])
      ⟨_, List.mem_singleton_self _, by simp [itemExpr, CorrectGrouped.itemAggFragment, ha]⟩ hff
      (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq)
      (.inl (by cases a <;> simp [CorrectGroup.colRefs, CorrectAvg.avgFragment] at ha ⊢)) hst hnbq
    refine ⟨hs, ss, hss, fun ctx => (hctx' ctx).imp fun s o h => ?_⟩
    obtain ⟨-, h⟩ := h
    simp only [List.ofFn_succ, List.ofFn_zero, List.zip_cons_cons, List.zip_nil_right] at h
    rcases o with _ | ⟨⟨nm, v⟩, _ | ⟨x, rest⟩⟩
    · cases h
    · simp only [List.map_cons, List.map_nil] at h
      cases h with
      | cons h1 _ =>
        simp only [CorrectGrouped.ItemRel, itemExpr, ha, ↓reduceIte] at h1
        exact ⟨nm, v, rfl, h1⟩
    · simp only [List.map_cons] at h
      cases h with
      | cons _ h2 => cases h2

/-- The compared expression of an `AVG` clause is not a decimal: it elaborates, among the
    columns of `FROM f`, to an expression of another type (a comparison then needs an integer).
    A decimal could sit between the exact average and its rounding. -/
def NonDecimalIn (N : NamedSchema) (f : SqlEquiv.FromClause) (a : SqlEquiv.Expr) : Prop :=
  ∀ {n : ℕ} (qf : Query N.S n) (cf : Fin n → Column) (a₀ : Expr n) (Γ : Fin n → SqlType),
    elabFrom N (fun sq => elabSubQuery N 15 sq) f = .ok ⟨n, qf, cf⟩ → qf.typeOf = some Γ →
    elabExpr cf N.fold noHook a = .ok a₀ → ∃ τ, a₀.typeOf Γ = some τ ∧ τ ≠ .decimal

/-- An integer literal is not a decimal, among any columns. -/
theorem nonDecimalIn_lit (N : NamedSchema) (f : SqlEquiv.FromClause) (z : ℤ) :
    NonDecimalIn N f (.lit (.int z)) := by
  intro n qf cf a₀ Γ _ _ h
  unfold elabExpr at h
  simp [noHook, elabValue, pure, Except.pure] at h
  subst h
  exact ⟨.int, rfl, by simp⟩

/-- **In a schema without decimal columns, a column is not a decimal**, among the columns of any
    `FROM` tree of tables. -/
theorem nonDecimalIn_col (N : NamedSchema) (hnd : ∀ T j, (N.S.columns T j).type ≠ .decimal)
    {f : SqlEquiv.FromClause} (hff : fromFragment f = true) (c : SqlEquiv.ColumnRef) :
    NonDecimalIn N f (.col c) := by
  intro n qf cf a₀ Γ hf hΓ ha
  obtain ⟨idx, rfl⟩ := CorrectGroup.elab_col_is_col cf N.fold c ha
  exact ⟨Γ idx, rfl, from_noDecimal N _ hnd f hff hf hΓ idx⟩

/-- The size bound of an `AVG` clause: the average's denominator, in lowest terms, is at most
    `10¹⁶`. It holds when `FROM` has at most `10¹⁶` rows and the argument is not a decimal
    (`avgBound_of_rows`). -/
def AvgBound (N : NamedSchema) (D : Database N.S) (body : SqlEquiv.SelectStmt) : Prop :=
  ∀ (rq : Query N.S 1) (rc : Fin 1 → Column) (ss : List (Row 1)),
    elabSubQuery N 15 (.simple body) = .ok ⟨1, rq, rc⟩ → rq.typeOf.isSome → rq.eval D = .ok ss →
    ∀ s ∈ ss, ∀ q, s 0 = some (.decimal q) → q.den ≤ 10 ^ SqlEquiv.avgPlaces

/-- An aggregate without keys over rows `R`: one row, the aggregates' values. -/
theorem eval_aggregate_noKeys {S : DbSchema} {n a : ℕ} {D : Database S} (keys : Fin 0 → Expr n)
    (aggs : Fin a → AggCall n) {q₀ : Query S n} {R : List (Row n)} (hR : q₀.eval D = .ok R) :
    (Query.aggregate keys aggs q₀).eval D =
      (AggCall.evalAll aggs R).map fun A => [Fin.append (fun _ => none : Row 0) A] := by
  have hk : ∀ r : Row n, Expr.evalRow keys r = .ok (fun _ => none) := fun r =>
    Expr.evalRow_eq_ok_iff.mpr (fun i => i.elim0)
  rw [Query.eval_aggregate, hR]
  simp only [bind, Except.bind]
  rw [CorrectAgg.mapM_ok_map (g := fun r => ((fun _ => none : Row 0), r))
    (fun r _ => by simp [hk, pure, Except.pure])]
  simp only [Row.groups, ↓reduceIte, List.map_map]
  have : ((Prod.snd ∘ fun r : Row n => ((fun _ => none : Row 0), r)) : Row n → Row n) = id := rfl
  cases hA : AggCall.evalAll aggs R <;>
    simp [this, List.mapM_cons, hA, pure, Except.pure, Except.map, bind, Except.bind]

set_option maxHeartbeats 1600000 in
/-- The values of `SELECT AVG(e) FROM f [WHERE p]`, `e` not a decimal: their denominators are at
    most the number of rows of `FROM f`. -/
theorem avg_stmt_den (N : NamedSchema)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower)
    {D : Database N.S} (hD : D.Conforms) {e : SqlEquiv.Expr} {b : SqlEquiv.BoolSumAvg}
    {al : Option String} {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (he : isFragment e = true) (hw : ∀ w ∈ wh, isFragment w = true) (hne : NonDecimalIn N f e)
    {B : ℕ}
    (hrows : ∀ {n : ℕ} (qf : Query N.S n) (cf : Fin n → Column) (Rf : List (Row n)),
      elabFrom N (fun sq => elabSubQuery N 15 sq) f = .ok ⟨n, qf, cf⟩ → qf.eval D = .ok Rf →
      Rf.length ≤ B)
    {el : Elaborated N.S}
    (hst : elabStmt N (CorrectGrouped.groupedStmt [.exprItem (.agg (.avg b) (some e) false) al]
      f wh [] none [] none none) = .ok el)
    (hty : el.q.typeOf.isSome) {ss : List (Row el.n)} (hss : el.q.eval D = .ok ss) :
    ∀ s ∈ ss, ∀ i q, s i = some (.decimal q) → q.den ≤ B := by
  have ha : CorrectAvg.avgFragment (.agg (.avg b) (some e) false) = true := by
    simpa [CorrectAvg.avgFragment] using he
  obtain ⟨-, n, qf, cf, hf, q₀, hq₀, keyList, a, aggs, its, sk, mk, hk, -, -, hits, hsk,
    qh, hqh, rfl⟩ := CorrectGrouped.elab_grouped_shape N hfoldCI
      (items := [.exprItem (.agg (.avg b) (some e) false) al])
      (by simp [CorrectGrouped.groupedItems, CorrectGrouped.itemAggFragment, ha])
      (.inr ⟨_, List.mem_singleton_self _, by simp [itemExpr, CorrectGrouped.itemAggFragment, ha]⟩)
      (by simp) (by simp) (by simp) (.inl (by simp [CorrectGroup.colRefs])) hst
  simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hk
  subst hk
  cases hsk
  rcases hqh with ⟨-, rfl⟩ | ⟨hv, p, out, hhs, -⟩
  swap; · cases hhs
  simp only [limitWrap, List.length_nil, ↓reduceIte] at hty hss ⊢
  -- the one item is the aggregate `aggs j`, the `AVG` of `e`'s elaboration
  cases hits with
  | @cons _ x _ _ hx hrest =>
  cases hrest
  rcases hx with ⟨j, hel, hxj⟩ | ⟨c, i', hc, -⟩ | ⟨c, j, e', hc, -⟩
  rotate_left
  · simp [itemExpr] at hc
  · simp [itemExpr] at hc
  simp only [itemExpr, elabAgg, bind, Except.bind] at hel
  rcases he₀ : elabExpr cf N.fold noHook e with err | e₀
  · simp [he₀] at hel
  simp only [he₀, pure, Except.pure, Except.ok.injEq] at hel
  -- typing: `e₀` is an integer
  obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp hty
  obtain ⟨Γa, hΓa, -⟩ := Query.typeOf_project_eq_some.mp hΔ
  obtain ⟨Γ₀, Δk, Δa, hq₀ty, -, has, -⟩ := Query.typeOf_aggregate_eq_some hΓa
  -- the `WHERE` keeps the type and at most the rows
  have hwf : qf.typeOf = some Γ₀ ∧ ∀ R, q₀.eval D = .ok R →
      ∃ Rf, qf.eval D = .ok Rf ∧ R.length ≤ Rf.length := by
    cases wh with
    | none =>
      simp only [elabWhere, pure, Except.pure, Except.ok.injEq] at hq₀
      subst hq₀
      exact ⟨hq₀ty, fun R hR => ⟨R, hR, Nat.le_refl _⟩⟩
    | some w =>
      simp only [elabWhere, subsOf_frag w (hw w rfl), List.foldl_nil, List.isEmpty_nil,
        ↓reduceIte] at hq₀
      obtain ⟨p, -, hq₀⟩ := bind_ok hq₀
      simp only [pure, Except.pure, Except.ok.injEq] at hq₀
      subst hq₀
      refine ⟨(Query.typeOf_select_eq_some.mp hq₀ty).1, fun R hR => ?_⟩
      rw [Query.eval_select] at hR
      obtain ⟨Rf, hRf, hR⟩ := bind_ok hR
      exact ⟨Rf, hRf, filterRows_length_le p hR⟩
  obtain ⟨hsrc, hlen⟩ := hwf
  obtain ⟨τ, hτ, hτne⟩ := hne qf cf e₀ Γ₀ hf hsrc he₀
  have hτint : e₀.typeOf Γ₀ = some .int := by
    have h1 := has j
    rw [← hel] at h1
    simp only [AggCall.typeOf, hτ] at h1
    cases τ <;> simp_all
  -- evaluation
  rw [Query.eval_project] at hss
  obtain ⟨G, hG, hss⟩ := bind_ok hss
  have hG' := hG
  rw [Query.eval_aggregate] at hG'
  obtain ⟨R, hR, -⟩ := bind_ok hG'
  rw [eval_aggregate_noKeys _ _ hR] at hG
  rcases hA : AggCall.evalAll aggs R with err | A
  · simp [hA, Except.map] at hG
  simp only [hA, Except.map, Except.ok.injEq] at hG
  subst hG
  simp only [List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure] at hss
  split at hss
  · cases hss
  rename_i r hrow
  simp only [Except.ok.injEq] at hss
  subst hss
  intro s hs i q hq
  rw [List.mem_singleton] at hs
  subst hs
  have hi := Expr.evalRow_eq_ok_iff.mp hrow i
  have hi0 : ([x][i]).1 = x.1 := by
    have h1 : (i : ℕ) < 1 := i.2
    have h0 : (i : ℕ) = 0 := by omega
    simp [h0]
  rw [hi0, hxj] at hi
  have hAj : s i = A j := by
    have h2 : (Expr.col (Fin.natAdd _ j)).eval (Fin.append (fun _ => none : Row 0) A) =
        .ok (A j) := by
      show Except.ok ((Fin.append (fun _ => none : Row 0) A) (Fin.natAdd _ j)) = _
      rw [Fin.append_right]
    exact Except.ok.inj (hi.symm.trans h2)
  have hev := CorrectAgg.evalAll_get hA j
  rw [← hel, ← hAj, hq] at hev
  have hconf := Query.conforms_of_eval_eq_ok hD hq₀ty hR
  have hden := CorrectAvg.avg_den_le (fun r hr d hd => by
    rcases Expr.eval_ok_or_divisionByZero (hconf r hr) hτint with ⟨d', hd', hty'⟩ | ⟨hdz, _⟩
    · rw [hd] at hd'; cases hd'; exact hty'
    · rw [hd] at hdz; cases hdz) hev
  obtain ⟨Rf, hRf, hle⟩ := hlen R hR
  exact hden.trans (hle.trans (hrows qf cf Rf hf hRf))

/-- **The size bound from a row count.** For `SELECT AVG(e) FROM f [WHERE p]` with `e` not a
    decimal (so an integer, for the `AVG` to type): if `FROM f` has at most `10¹⁶` rows, the
    average's denominator is at most `10¹⁶`. -/
theorem avgBound_of_rows (N : NamedSchema)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower)
    {D : Database N.S} (hD : D.Conforms) {e : SqlEquiv.Expr} {b : SqlEquiv.BoolSumAvg}
    {al : Option String} {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (he : isFragment e = true) (hff : fromFragment f = true)
    (hw : ∀ w ∈ wh, isFragment w = true) (hne : NonDecimalIn N f e)
    (hrows : ∀ {n : ℕ} (qf : Query N.S n) (cf : Fin n → Column) (Rf : List (Row n)),
      elabFrom N (fun sq => elabSubQuery N 15 sq) f = .ok ⟨n, qf, cf⟩ → qf.eval D = .ok Rf →
      Rf.length ≤ 10 ^ SqlEquiv.avgPlaces) :
    AvgBound N D (.mk false [.exprItem (.agg (.avg b) (some e) false) al] (some f) wh [] none []
      none none) := by
  intro rq rc ss hsub hty hss s hs q hq
  have hst : elabStmt N (CorrectGrouped.groupedStmt [.exprItem (.agg (.avg b) (some e) false) al]
      f wh [] none [] none none) = .ok ⟨1, rq, rc⟩ := by
    rw [elabSubQuery] at hsub
    simp only [CorrectGrouped.groupedStmt, elabStmt, elabQuery, elabQueryRaw, elabSelect]
    rw [elabSelectF_fuel N 16 14 hff hw, hsub]
    simp [hty, bind, Except.bind, pure, Except.pure]
  exact avg_stmt_den N hfoldCI hD he hw hne hrows hst hty hss s hs 0 q hq

/-- The rows of `FROM t` are the table's: a bound on every table's size bounds them. -/
theorem fromRows_table (N : NamedSchema) (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S))
    {D : Database N.S} {B : ℕ} (hB : ∀ T, (D T).length ≤ B) (tr : SqlEquiv.TableRef)
    {n : ℕ} (qf : Query N.S n) (cf : Fin n → Column) (Rf : List (Row n))
    (h : elabFrom N sub (.table tr) = .ok ⟨n, qf, cf⟩) (hRf : qf.eval D = .ok Rf) :
    Rf.length ≤ B := by
  obtain ⟨name, al⟩ := tr
  rcases hT : N.tables.find? (fun x => x.1 == N.fold name) with _ | ⟨nm, T⟩
  · simp [elabFrom, lookupTable, hT, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  simp only [elabFrom, lookupTable, hT, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  cases h
  cases hRf
  exact hB T

/-- The `WHERE` clauses of step 6c over an `AVG` body: `a op (SELECT AVG(e) FROM …)`, alone or
    under `AND` next to fragment conjuncts, with `a` not a decimal and the average under the size
    bound, in a dialect that takes the first row of several. -/
def AvgWhere (N : NamedSchema) (D : Database N.S) (f : SqlEquiv.FromClause)
    (w : SqlEquiv.Expr) : Prop :=
  N.config.scalarSubqueryRows = .firstRow ∧ ∃ body, AvgBody body ∧
    uncorrelated N (.simple body) = true ∧ AvgBound N D body ∧
    w ≠ .subquery (.simple body) ∧ HoleCtx N.fold (NonDecimalIn N f) (.subquery (.simple body)) w

/-- **Such a clause provides `WhereOk`**: `SqlEquiv` compares with the rounded average, the typed
    core with the exact one, and under the bound the two comparisons agree
    (`cmp_agree_avg`). -/
theorem whereOk_of_avgWhere (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {n : ℕ} {cf : Fin n → Column} {qf q₀ : Query N.S n} {f : SqlEquiv.FromClause}
    {w : SqlEquiv.Expr} (hw : AvgWhere N D f w)
    (hf : elabFrom N (fun sq => elabSubQuery N 15 sq) f = .ok ⟨n, qf, cf⟩)
    (h : elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf (some w) = .ok q₀) :
    WhereOk cf N.fold db D (some w) qf q₀ := by
  obtain ⟨hcfg, body, hb, hun, hbound, hne, hctxW⟩ := hw
  have hs := holeCtx_subs (fold := N.fold) (node := .subquery (.simple body))
    (sq := .simple body) (by simp [subsOf]) hctxW
  obtain ⟨r, h1, P, hsub, hP, rfl⟩ :=
    elabWhere_one_scalar N _ cf qf hs (not_unknownColumn_of_uncorrelated hun) h
  obtain ⟨m, rq, rc⟩ := r
  dsimp only at h1
  subst h1
  let R : Datum → SqlEquiv.Value → Prop := fun d v =>
    CorrectAvg.AvgRel d v ∧ ∀ q, d = some (.decimal q) → q.den ≤ 10 ^ SqlEquiv.avgPlaces
  have hRbool : ∀ d v, R d v → (d = none ∨ ∃ x, d = some (.bool x)) → DatumRel d v := by
    rintro d v ⟨⟨rfl, t, rfl⟩ | ⟨q, p, rfl, -, -⟩, -⟩ hd
    · exact ⟨t, rfl⟩
    · rcases hd with hd | ⟨x, hd⟩ <;> cases hd
  have hdiv : P.divSafe = true := (holeCtx_elab cf N.fold (rc ⟨0, by omega⟩).type .bool
    (hookOf n (.subquery (.simple body)) (.simple body))
    (.subquery (.simple body)) (hookOf_node ..) (fun x hx => hookOf_ne _ _ _ hx) rfl
    (fun _ _ _ hc => by cases hc) (NonDecimalIn N f) (fun _ _ => False) (fun _ => .int)
    (fun _ _ h _ => h.elim)
    (by intro op c a a₀ _ _ _ r da b d a' b' _ _ _ hb; exact hb.elim) db hctxW hP).1
  have hel := fun (Γ : Fin n → SqlType) (hqf : qf.typeOf = some Γ) τ =>
    holeCtx_elab cf N.fold (rc ⟨0, by omega⟩).type τ
    (hookOf n (.subquery (.simple body)) (.simple body))
    (.subquery (.simple body)) (hookOf_node ..) (fun x hx => hookOf_ne _ _ _ hx) rfl
    (fun _ _ _ hc => by cases hc) (NonDecimalIn N f) R Γ hRbool
    (by
      intro op c a a₀ hop hA ha₀ r da b d a' b' hc he ha hb _ hd
      obtain ⟨τa, hτ, hτne⟩ := hA qf cf a₀ Γ hf hqf ha₀
      have hat : ∀ q, da ≠ some (.decimal q) := by
        rintro q rfl
        rcases Expr.eval_ok_or_divisionByZero hc hτ with ⟨d', hd', hty⟩ | ⟨hdz, _⟩
        · rw [he] at hd'; cases hd'
          exact hτne (by simpa [Datum.HasType, Value.type] using hty.symm)
        · rw [he] at hdz; cases hdz
      exact CorrectAvg.cmp_agree_avg hop ha hat hb.1 hb.2 hd) db hctxW hP
  refine whereOk_attach (R := R) cf N.fold db D (by simp only [SubKind.divSafe, hcfg]; decide) hdiv
    (fun hty hnb => (avgBody_ctx N hfold hfoldCI hwn hfix hD hrel hb hsub hty hnb).1.2) ?_
    (fun Γ τ hqf hnb r u hru hc d vn hvn hrn hcx dp hdp => by
      obtain ⟨v, hv, -, h2⟩ := (hel Γ hqf τ).2 hnb r u hru hc d vn hvn hrn hcx dp hdp
      exact ⟨v, hv, h2 hne⟩)
  intro Γ Δ τ hqf hΔ _ hnbA hk1 _ ss x hss hx r u hru hc d hd
  obtain ⟨-, ss', hss', hctx'⟩ := avgBody_ctx N hfold hfoldCI hwn hfix hD hrel hb hsub
    (by simp [hΔ]) hnbA.2.1
  rw [hss] at hss'
  cases hss'
  have hτ := hk1 _ rfl
  have hconf := Query.conforms_of_eval_eq_ok hD hΔ hss
  have hbd := hbound rq rc ss hsub (by simp [hΔ]) hss
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
  match ss, hfa, hsc, hconf, hbd with
  | [], hfa, hsc, _, _ =>
    cases hfa
    simp only [List.map_nil, scalarOf, Except.ok.injEq] at hsc
    subst hsc
    exact ⟨.null none, rfl, ⟨.inl ⟨rfl, none, rfl⟩, fun q hq => by cases hq⟩,
      conforms_append_single hc (Datum.hasType_none _)⟩
  | s :: rest, hfa, hsc, hconf, hbd =>
    cases hfa with
    | cons hsu hrest =>
      obtain ⟨nm, val, rfl, hsv⟩ := hsu
      have hdv : dv = s 0 := by
        cases rest with
        | nil => simpa [scalarOf] using hsc.symm
        | cons s' rest' =>
          simp only [List.map_cons, scalarOf] at hsc
          split at hsc
          · simpa using hsc.symm
          · cases hsc
      subst hdv
      refine ⟨val, rfl, ⟨hsv, hbd s List.mem_cons_self⟩, conforms_append_single hc ?_⟩
      rw [hτ]
      exact hconf s List.mem_cons_self 0

/-- The `WHERE` clauses of steps 6b and 6c: a `SubWhere` clause, or an `AvgWhere` one. -/
def AnySubWhere (N : NamedSchema) (D : Database N.S) (f : SqlEquiv.FromClause)
    (w : SqlEquiv.Expr) : Prop :=
  SubWhere N w ∨ AvgWhere N D f w

theorem whereOk_of_anySubWhere (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {n : ℕ} {cf : Fin n → Column} {qf q₀ : Query N.S n} {f : SqlEquiv.FromClause}
    {w : SqlEquiv.Expr} (hw : AnySubWhere N D f w)
    (hf : elabFrom N (fun sq => elabSubQuery N 15 sq) f = .ok ⟨n, qf, cf⟩)
    (h : elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf (some w) = .ok q₀) :
    WhereOk cf N.fold db D (some w) qf q₀ :=
  hw.elim (fun hw => whereOk_of_subWhere N hfold hfoldCI hwn hfix hD hrel hw h)
    (fun hw => whereOk_of_avgWhere N hfold hfoldCI hwn hfix hD hrel hw hf h)

/-! ### The statement theorems -/

/-- **Elaborator correctness for `WHERE … e [NOT] IN (SELECT …)` (#352, step 6b).** For
    `SELECT e₁, …, eₖ FROM f WHERE w [ORDER BY …] [LIMIT n] [OFFSET m]` with `w` an `AnySubWhere`
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
    (hit : itemsFragment items = true) (hff : fromFragment f = true) (hw : AnySubWhere N D f w)
    (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c)
    (hnamed : orderBy ≠ [] → itemsNamed items = true)
    {el : Elaborated N.S}
    (h : elabStmt N (joinStmt items f (some w) orderBy lim off) = .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (joinStmt items f (some w) orderBy lim off)).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  obtain ⟨-, rs, hrs, out, hout, hr, -⟩ := elabStmt_correct_join_ctx N hfold hfoldCI hwn hfix hD
    hrel hit hff (fun _ _ _ hf hq => whereOk_of_anySubWhere N hfold hfoldCI hwn hfix hD hrel hw hf hq)
    hcols hnamed h hnb
  exact ⟨rs, hrs, out, hout, hr⟩

/-- **The same under `SELECT DISTINCT`**, up to the order of the rows (as
    `elabStmt_correct_distinct`). -/
theorem elabStmt_correct_distinct_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {w : SqlEquiv.Expr}
    (hit : itemsFragment items = true) (hff : fromFragment f = true) (hw : AnySubWhere N D f w)
    {el : Elaborated N.S}
    (h : elabStmt N (CorrectDistinct.distinctStmt items f (some w)) = .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (CorrectDistinct.distinctStmt items f (some w))).2 = some out ∧
        ∃ rs', rs.Perm rs' ∧ List.Forall₂ OutRel rs' out :=
  CorrectDistinct.elabStmt_correct_distinct_w N hfold hfoldCI hwn hfix hD hrel hit hff
    (fun _ _ _ hf hq => whereOk_of_anySubWhere N hfold hfoldCI hwn hfix hD hrel hw hf hq) h hnb

/-- **The same under aggregates without `GROUP BY`** (as `elabStmt_correct_agg`): one row,
    related to `SqlEquiv`'s one row. -/
theorem elabStmt_correct_agg_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {w : SqlEquiv.Expr}
    (hai : CorrectAgg.aggItems items = true) (hne : items ≠ []) (hff : fromFragment f = true)
    (hw : AnySubWhere N D f w)
    {el : Elaborated N.S}
    (h : elabStmt N (CorrectAgg.aggStmt items f (some w)) = .ok el) (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (CorrectAgg.aggStmt items f (some w))).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  obtain ⟨-, rs, hrs, out, hout, hr, -⟩ := CorrectAgg.elabStmt_correct_agg_w N hfold hfoldCI hwn
    hfix hD hrel hai hne hff
    (fun _ _ _ hf hq => whereOk_of_anySubWhere N hfold hfoldCI hwn hfix hD hrel hw hf hq) h hnb
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
    (hw : AnySubWhere N D f w)
    {el : Elaborated N.S}
    (h : elabStmt N (CorrectGrouped.groupedStmt items f (some w) [] none [] none none) = .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db
        (CorrectGrouped.groupedStmt items f (some w) [] none [] none none)).2 = some out ∧
        List.Forall₂ (CorrectGrouped.OutRelI items) rs out :=
  CorrectAggBare.elabStmt_correct_aggBare_w N hfold hfoldCI hwn hfix hD hrel hgi hai hff
    (fun _ _ _ hf hq => whereOk_of_anySubWhere N hfold hfoldCI hwn hfix hD hrel hw hf hq) hbf h hnb

/-- **The same under `GROUP BY`** (as `elabStmt_correct_grouped`). -/
theorem elabStmt_correct_grouped_inSub (N : NamedSchema)
    (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {w : SqlEquiv.Expr}
    {groupBy : List SqlEquiv.Expr} {having : Option SqlEquiv.Expr}
    {orderBy : List SqlEquiv.OrderByItem} {lim off : Option ℕ}
    (hgi : CorrectGrouped.groupedItems items = true) (hgb : groupBy ≠ [])
    (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment f = true)
    (hw : AnySubWhere N D f w)
    (hhv : ∀ h ∈ having, CorrectGroup.havingFragment groupBy h = true)
    (hav : CorrectGrouped.HavingAvgOk N D f having)
    (hob : ∀ o ∈ orderBy, CorrectGrouped.OrderKeyOk items groupBy o.expr)
    (hbf : CorrectGrouped.BareOk N items groupBy having orderBy)
    (hnm : orderBy ≠ [] → ∀ it ∈ items, '.' ∉ (outName it).toList ∧
      ∀ k, (outName it).toLower ≠ SqlEquiv.groupOrderKeyName k)
    {el : Elaborated N.S}
    (h : elabStmt N (CorrectGrouped.groupedStmt items f (some w) groupBy having orderBy lim off) =
      .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db
        (CorrectGrouped.groupedStmt items f (some w) groupBy having orderBy lim off)).2 =
          some out ∧ List.Forall₂ (CorrectGrouped.OutRelI items) rs out :=
  CorrectGrouped.elabStmt_correct_grouped_w N hfold hfoldCI hwn hfix hD hrel hgi hgb hgc hff
    (fun _ _ _ hf hq => whereOk_of_anySubWhere N hfold hfoldCI hwn hfix hD hrel hw hf hq)
    hhv hav hob hbf hnm h hnb

end SqlBridge.CorrectSub
