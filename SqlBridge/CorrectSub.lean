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


theorem typeOf_attachWhere {S : DbSchema} {n : ℕ} {neg : Bool} {e : Expr n} {sub : Query S 1}
    {q : Query S n} {P : Expr (n + 1)} {Γ : Fin n → SqlType}
    (h : (Query.project (fun i : Fin n => Expr.col (Fin.castLE (Nat.le_succ n) i))
      (.select P (.attach (.inSub neg e) sub q))).typeOf = some Γ) :
    q.typeOf = some Γ ∧ sub.typeOf.isSome ∧
      (Query.attach (.inSub neg e) sub q).typeOf = some (Fin.append Γ ![.bool]) := by
  obtain ⟨Γ', hsel, hproj⟩ := Query.typeOf_project_eq_some.mp h
  obtain ⟨hatt, -⟩ := Query.typeOf_select_eq_some.mp hsel
  obtain ⟨Δ, Γq, hΔ, hΓq, rfl⟩ := typeOf_attach_inSub hatt
  have hΓ : Γq = Γ := by
    funext i
    have := hproj i
    have hC : Fin.castLE (Nat.le_succ n) i = Fin.castAdd 1 i := by ext; simp
    simp only [Expr.typeOf, hC, Fin.append_left, Option.some.injEq] at this
    exact this
  subst hΓ
  exact ⟨hΓq, by simp [hΔ], hatt⟩

/-- **A `WHERE` that reads one attached `IN` subquery provides `WhereOk`**, when its typed
    predicate `P` relates to the untyped clause `w` on every row, given that the attached column
    relates to the subquery node's value. -/
theorem whereOk_attach (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {n : ℕ} {cf : Fin n → Column} {qf : Query N.S n}
    {e : SqlEquiv.Expr} {neg : Bool} {items : List SqlEquiv.SelectItem}
    {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (he : isFragment e = true) (hit : itemsFragment items = true) (hff : fromFragment f = true)
    (hw : ∀ w ∈ wh, isFragment w = true)
    {w : SqlEquiv.Expr} {P : Expr (n + 1)} {e' : Expr n} {rq : Query N.S 1} {rc : Fin 1 → Column}
    (hsub : elabSubQuery N 15 (.simple (.mk false items (some f) wh [] none [] none none)) =
      .ok ⟨1, rq, rc⟩)
    (he' : elabExpr cf N.fold noHook e = .ok e') (hPdiv : P.divSafe = true)
    (hctx : ∀ Γ, qf.typeOf = some Γ → NoBoolOrder (Fin.append Γ ![SqlType.bool]) P →
      ∀ r u, RowRel cf N.fold r u → r.Conforms Γ → ∀ d vn,
        SqlEquiv.evalExprWithDb db u
          (.inSubquery e neg (.simple (.mk false items (some f) wh [] none [] none none))) =
            some vn → DatumRel d vn →
        ∀ dp, P.eval (Fin.append r ![d]) = .ok dp →
          ∃ v, SqlEquiv.evalExprWithDb db u w = some v ∧ DatumRel dp v) :
    WhereOk cf N.fold db D (some w) qf
      (.project (fun i : Fin n => .col (Fin.castLE (Nat.le_succ n) i))
        (.select P (.attach (.inSub neg e') rq qf))) := by
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
    obtain ⟨hs, ss, hss, -, -, -, hctx'⟩ := elabStmt_correct_join_ctx N hfold hfoldCI hwn hfix hD
      hrel hit hff (fun _ _ _ _ hq => whereOk_frag N _ db D hw hq) (by simp) (by simp) hst hnbq
    exact ⟨hs, ss, hss, hctx' rfl⟩
  refine ⟨fun Γ hΓ => (typeOf_attachWhere hΓ).1, fun h => h.2.2.2.2, ?_, ?_⟩
  · intro Γ hΓ hnb hd
    obtain ⟨hs, -⟩ := hleaf (typeOf_attachWhere hΓ).2.1 hnb.2.2.2.1
    simp [Query.divSafe, SubKind.divSafe, Expr.divSafe, hd, hs.2, Translates.divSafe _ _ htp, hPdiv]
  · intro Γ Rf R U hΓ hnb hRf hR hrows
    obtain ⟨hqfT, hsubT, hattT⟩ := typeOf_attachWhere hΓ
    obtain ⟨-, ss, hss, hctx'⟩ := hleaf hsubT hnb.2.2.2.1
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
      exact (hctx' u).imp fun _ _ h => subRowRel_of_outRel h
    refine attachFilter_rel cf N.fold (fun u => SqlEquiv.evalExprWithDb db u w)
      (fun r u hru hc d hd dp hdp => ?_) hrows hE hF hR
    obtain ⟨vn, hvn, hrn⟩ := inExpr_eval_rel cf N.fold db hru hc htp (hnb.2.2.1 Γ hqfT)
      (hsubrows u) hd
    exact hctx Γ hqfT (hnb.2.1 _ hattT) r u hru hc d vn hvn hrn dp hdp

/-- The body of the subqueries this file takes. -/
abbrev plainBody (items : List SqlEquiv.SelectItem) (f : SqlEquiv.FromClause)
    (wh : Option SqlEquiv.Expr) : SqlEquiv.SubQuery :=
  .simple (.mk false items (some f) wh [] none [] none none)

/-- The hidden column the elaborator appends for an attached subquery. -/
def subCol (ty : SqlType) : Column := { qualifier := none, name := "?subquery?", type := ty }

/-- The elaborated `WHERE a AND e [NOT] IN (sq)`, `a` in the expression fragment and not
    referring to the hidden column's name. -/
theorem elabWhere_and_inSub (N : NamedSchema) (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S))
    {n : ℕ} (cols : Fin n → Column) (q : Query N.S n) {a e : SqlEquiv.Expr} {neg : Bool}
    {sq : SqlEquiv.SubQuery} {q₀ : Query N.S n} (ha : isFragment a = true)
    (hna : noRefTo N.fold "?subquery?" a = true)
    (h : elabWhere N sub cols q (some (.binOp .and a (.inSubquery e neg sq))) = .ok q₀) :
    ∃ (r : Elaborated N.S) (h1 : r.n = 1) (e' a₀ : Expr n), sub sq = .ok r ∧
      elabExpr cols N.fold noHook e = .ok e' ∧ elabExpr cols N.fold noHook a = .ok a₀ ∧
      q₀ = .project (fun i : Fin n => .col (Fin.castLE (Nat.le_succ n) i))
        (.select (.binary .and
            (retypeNull (Fin.append cols ![subCol .bool]) (a₀.rename (Fin.castAdd 1))
              (.col (Fin.last n)))
            (retypeNull (Fin.append cols ![subCol .bool]) (.col (Fin.last n))
              (a₀.rename (Fin.castAdd 1))))
          (.attach (.inSub neg e') (h1 ▸ r.q) q)) := by
  simp only [elabWhere, subsOf, subsOf_frag a ha, List.nil_append, List.foldl_cons, List.foldl_nil,
    List.any_nil, Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons, List.mapM_cons,
    List.mapM_nil] at h
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
  have hbeq : ∀ x : SqlEquiv.Expr, isFragment x = true →
      (SqlEquiv.Expr.inSubquery e neg sq == x) = false := by
    intro x hx
    rw [beq_eq_false_iff_ne]
    rintro rfl
    simp [isFragment] at hx
  have hnode : (SqlEquiv.Expr.inSubquery e neg sq ==
      SqlEquiv.Expr.binOp .and a (.inSubquery e neg sq)) = false := by
    rw [beq_eq_false_iff_ne]
    intro hc
    cases hc
  generalize hH : (fun e_1 : SqlEquiv.Expr =>
    match List.findIdx? (fun x => x.1 == e_1) [(e.inSubquery neg sq, sq)] with
    | some j => if h : n + j < n + 1 then some (Expr.col (⟨n + j, h⟩ : Fin (n + 1))) else none
    | none => none) = hook at h
  have hhook : ∀ x, isFragment x = true → hook x = none := by
    intro x hx
    rw [← hH]
    simp [List.findIdx?_cons, hbeq x hx]
  have hhookW : hook (.binOp .and a (.inSubquery e neg sq)) = none := by
    rw [← hH]
    simp [List.findIdx?_cons, hnode]
  have hhookN : hook (.inSubquery e neg sq) = some (.col (Fin.last n)) := by
    rw [← hH]
    simp [List.findIdx?_cons, Fin.last]
  rw [elabExpr] at h
  have hsc : ({ qualifier := none, name := "?subquery?", type := SqlType.bool } : Column) =
      subCol .bool := rfl
  simp only [hhookW, elabBinOp, pure, Except.pure, bind, Except.bind, hsc] at h
  rcases hea : elabExpr (Fin.append cols ![subCol .bool]) N.fold hook a with err | a'
  · simp [hea] at h
  obtain ⟨a₀, ha₀, rfl⟩ := elabExpr_weaken cols N.fold (subCol .bool) hook hhook a ha hna hea
  have hen : elabExpr (Fin.append cols ![subCol .bool]) N.fold hook (.inSubquery e neg sq) =
      .ok (.col (Fin.last n)) := by
    rw [elabExpr]; simp [hhookN, pure, Except.pure]
  simp only [hea, hen, Nat.le_add_right, ↓reduceDIte, Except.ok.injEq] at h
  subst h
  exact ⟨r, h1, e', a₀, rfl, rfl, ha₀, rfl⟩

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

/-- `e [NOT] IN (plain subquery)` provides `WhereOk` (the bare clause). -/
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
      (some (.inSubquery e neg (plainBody items f wh))) = .ok q₀) :
    WhereOk cf N.fold db D (some (.inSubquery e neg (plainBody items f wh))) qf q₀ := by
  obtain ⟨r, h1, e', hsub, he', rfl⟩ := elabWhere_inSub N _ cf qf h
  obtain ⟨m, rq, rc⟩ := r
  dsimp only at h1
  subst h1
  refine whereOk_attach N hfold hfoldCI hwn hfix hD hrel he hit hff hw hsub he' rfl ?_
  intro Γ _ _ r u _ _ d vn hvn hrn dp hdp
  rw [eval_col_last_append, Except.ok.injEq] at hdp
  exact ⟨vn, hvn, hdp ▸ hrn⟩

/-- `a AND e [NOT] IN (plain subquery)` provides `WhereOk`, `a` in the expression fragment and
    not referring to the hidden column's name. -/
theorem whereOk_and_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {n : ℕ} {cf : Fin n → Column} {qf q₀ : Query N.S n}
    {a e : SqlEquiv.Expr} {neg : Bool} {items : List SqlEquiv.SelectItem}
    {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (ha : isFragment a = true) (hna : noRefTo N.fold "?subquery?" a = true)
    (he : isFragment e = true) (hit : itemsFragment items = true) (hff : fromFragment f = true)
    (hw : ∀ w ∈ wh, isFragment w = true)
    (h : elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf
      (some (.binOp .and a (.inSubquery e neg (plainBody items f wh)))) = .ok q₀) :
    WhereOk cf N.fold db D (some (.binOp .and a (.inSubquery e neg (plainBody items f wh))))
      qf q₀ := by
  obtain ⟨r, h1, e', a₀, hsub, he', ha₀, rfl⟩ := elabWhere_and_inSub N _ cf qf ha hna h
  obtain ⟨m, rq, rc⟩ := r
  dsimp only at h1
  subst h1
  have hta := translates_of_elab cf N.fold a ha ha₀
  refine whereOk_attach N hfold hfoldCI hwn hfix hD hrel he hit hff hw hsub he' ?_ ?_
  · simp [Expr.divSafe, divSafe_retypeNull, Translates.divSafe _ _ hta, BinOp.isDivision]
  · intro Γ _ hnbP r u hru hc d vn hvn hrn dp hdp
    obtain ⟨da, db', hea, heb, hd⟩ := eval_binary_ok hdp
    rw [eval_retypeNull] at hea heb
    rw [Expr.eval_rename_castAdd] at hea
    rw [eval_col_last_append, Except.ok.injEq] at heb
    subst heb
    have hnba : NoBoolOrder Γ a₀ := by
      have h1 := noBoolOrder_of_retypeNull _ _ hnbP.1
      have h2 := noBoolOrder_rename _ _ _ h1
      have hΓ' : (Fin.append Γ ![SqlType.bool]) ∘ Fin.castAdd 1 = Γ := by
        funext i; simp [Fin.append_left]
      rwa [hΓ'] at h2
    obtain ⟨va, hva, hra⟩ := Translates.eval_rel cf N.fold db hru hc hta hnba hea
    obtain ⟨v, hv, hrel⟩ := and_agree hra hrn hd
    exact ⟨v, by rw [SqlEquiv.evalExprWithDb_binOp, hva, hvn, hv], hrel⟩

/-- The `WHERE` clauses of step 6b: `e [NOT] IN (SELECT e' FROM f' [WHERE p'])`, alone or after
    `a AND`, with `e`, `a` and the body in the fragment of `elabStmt_correct_join` (the body
    without `ORDER BY`, `LIMIT` or `OFFSET`), and `a` not referring to the name of the column the
    elaborator attaches (`?subquery?`; the parser cannot produce it). -/
inductive InSubWhere (N : NamedSchema) : SqlEquiv.Expr → Prop
  | bare {e : SqlEquiv.Expr} {neg : Bool} {items : List SqlEquiv.SelectItem}
      {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} (he : isFragment e = true)
      (hit : itemsFragment items = true) (hff : fromFragment f = true)
      (hw : ∀ w ∈ wh, isFragment w = true) :
      InSubWhere N (.inSubquery e neg (plainBody items f wh))
  | and {a e : SqlEquiv.Expr} {neg : Bool} {items : List SqlEquiv.SelectItem}
      {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} (ha : isFragment a = true)
      (hna : noRefTo N.fold "?subquery?" a = true) (he : isFragment e = true)
      (hit : itemsFragment items = true) (hff : fromFragment f = true)
      (hw : ∀ w ∈ wh, isFragment w = true) :
      InSubWhere N (.binOp .and a (.inSubquery e neg (plainBody items f wh)))

/-- Such a clause provides `WhereOk`. -/
theorem whereOk_of_inSubWhere (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {n : ℕ} {cf : Fin n → Column} {qf q₀ : Query N.S n} {w : SqlEquiv.Expr}
    (hw : InSubWhere N w)
    (h : elabWhere N (fun sq => elabSubQuery N 15 sq) cf qf (some w) = .ok q₀) :
    WhereOk cf N.fold db D (some w) qf q₀ := by
  cases hw with
  | bare he hit hff hw => exact whereOk_inSub N hfold hfoldCI hwn hfix hD hrel he hit hff hw h
  | and ha hna he hit hff hw =>
    exact whereOk_and_inSub N hfold hfoldCI hwn hfix hD hrel ha hna he hit hff hw h

/-- **Elaborator correctness for `WHERE … e [NOT] IN (SELECT …)` (#352, step 6b).** For
    `SELECT e₁, …, eₖ FROM f WHERE w [ORDER BY …] [LIMIT n] [OFFSET m]` with `w` an `InSubWhere`
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
    (hit : itemsFragment items = true) (hff : fromFragment f = true) (hw : InSubWhere N w)
    (hcols : ∀ o ∈ orderBy, ∃ c, o.expr = .col c)
    (hnamed : orderBy ≠ [] → itemsNamed items = true)
    {el : Elaborated N.S}
    (h : elabStmt N (joinStmt items f (some w) orderBy lim off) = .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (joinStmt items f (some w) orderBy lim off)).2 = some out ∧
        List.Forall₂ OutRel rs out := by
  obtain ⟨-, rs, hrs, out, hout, hr, -⟩ := elabStmt_correct_join_ctx N hfold hfoldCI hwn hfix hD
    hrel hit hff (fun _ _ _ _ hq => whereOk_of_inSubWhere N hfold hfoldCI hwn hfix hD hrel hw hq)
    hcols hnamed h hnb
  exact ⟨rs, hrs, out, hout, hr⟩

/-- **The same under `SELECT DISTINCT`**, up to the order of the rows (as
    `elabStmt_correct_distinct`). -/
theorem elabStmt_correct_distinct_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {w : SqlEquiv.Expr}
    (hit : itemsFragment items = true) (hff : fromFragment f = true) (hw : InSubWhere N w)
    {el : Elaborated N.S}
    (h : elabStmt N (CorrectDistinct.distinctStmt items f (some w)) = .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (CorrectDistinct.distinctStmt items f (some w))).2 = some out ∧
        ∃ rs', rs.Perm rs' ∧ List.Forall₂ OutRel rs' out :=
  CorrectDistinct.elabStmt_correct_distinct_w N hfold hfoldCI hwn hfix hD hrel hit hff
    (fun _ _ _ _ hq => whereOk_of_inSubWhere N hfold hfoldCI hwn hfix hD hrel hw hq) h hnb

/-- **The same under aggregates without `GROUP BY`** (as `elabStmt_correct_agg`): one row,
    related to `SqlEquiv`'s one row. -/
theorem elabStmt_correct_agg_inSub (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {w : SqlEquiv.Expr}
    (hai : CorrectAgg.aggItems items = true) (hne : items ≠ []) (hff : fromFragment f = true)
    (hw : InSubWhere N w)
    {el : Elaborated N.S}
    (h : elabStmt N (CorrectAgg.aggStmt items f (some w)) = .ok el) (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (CorrectAgg.aggStmt items f (some w))).2 = some out ∧
        List.Forall₂ OutRel rs out :=
  CorrectAgg.elabStmt_correct_agg_w N hfold hfoldCI hwn hfix hD hrel hai hne hff
    (fun _ _ _ _ hq => whereOk_of_inSubWhere N hfold hfoldCI hwn hfix hD hrel hw hq) h hnb

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
    (hw : InSubWhere N w)
    {el : Elaborated N.S}
    (h : elabStmt N (CorrectGrouped.groupedStmt items f (some w) [] none [] none none) = .ok el)
    (hnb : QNoBoolOrder el.q) :
    ∃ rs, el.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db
        (CorrectGrouped.groupedStmt items f (some w) [] none [] none none)).2 = some out ∧
        List.Forall₂ (CorrectGrouped.OutRelI items) rs out :=
  CorrectAggBare.elabStmt_correct_aggBare_w N hfold hfoldCI hwn hfix hD hrel hgi hai hff
    (fun _ _ _ _ hq => whereOk_of_inSubWhere N hfold hfoldCI hwn hfix hD hrel hw hq) hbf h hnb

end SqlBridge.CorrectSub
