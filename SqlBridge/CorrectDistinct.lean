/-
  Elaborator correctness for `SELECT DISTINCT` (#352, roadmap step 5):
  `SELECT DISTINCT e₁, …, eₖ FROM f [WHERE p]`, up to the order of the rows.

  Both evaluators remove the same duplicates: rows equal column by column, `NULL` type tags
  erased and numbers compared by value (`Row.valueKey` in `SqlEquiv`, equality of typed rows in
  the core; `row_eq_iff_valueKey`). They keep different copies: `SqlEquiv` the first of each
  class (`dedupByKey`), the typed core the last (`List.dedup`, as in cslib-frontier). SQL
  promises no order without `ORDER BY`, so the theorem relates the typed rows to `SqlEquiv`'s
  up to a permutation (`elabStmt_correct_distinct`). With a `LIMIT` and no `ORDER BY` the two
  can return different rows (registry T18); that shape is outside the theorem.

  * `evalSelectCore_distinct`: `SqlEquiv`'s `DISTINCT` without `ORDER BY`/`LIMIT` is `dedupByKey`
    of the statement without `DISTINCT`.
  * `elab_distinct_shape`: the elaborated query is `Query.distinct` of the plain statement's.
  * `distinct_rel`: related lists deduplicate to related lists, up to a permutation.
-/
import SqlBridge.CorrectJoin
import SqlBridge.CorrectAgg

namespace SqlBridge.CorrectDistinct
open SqlEquiv

/-- `DISTINCT` without `ORDER BY`, `LIMIT` or `OFFSET`: the rows of the same statement without
    `DISTINCT`, deduplicated by value, first copy kept. -/
theorem evalSelectCore_distinct (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool) (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : Option FromClause) (wh : Option Expr)
    (groupBy : List Expr) (having : Option Expr) :
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk true items from_ wh groupBy having [] none none) =
    dedupByKey Row.valueKey
      (evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
        (SelectStmt.mk false items from_ wh groupBy having [] none none)) := by
  have hg : ∀ c : Bool, (if c then groupOrderByItems [] else ([] : List OrderByItem)).isEmpty = true := by
    intro c; cases c <;> simp [groupOrderByItems]
  have hp : ∀ rows, evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg true items groupBy having rows =
      dedupByKey Row.valueKey (evalSelectProjectDistinct db exprEval selectItemEval
        selectItemWithAggEval exprWithAggEval exprWithWindowEval hasWindowFn hasAgg false items
        groupBy having rows) := by
    intro rows
    simp [evalSelectProjectDistinct]
  rw [evalSelectCore_eq_afterFilter, evalSelectCore_eq_afterFilter]
  simp only [evalSelectAfterFilter, applyOrderByLimitOffsetAligned, hg, ↓reduceIte, hp]

end SqlBridge.CorrectDistinct

namespace SqlBridge.CorrectDistinct
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectJoin
open SqlBridge.CorrectAgg

/-- The statements of step 5: `SELECT DISTINCT items FROM f [WHERE p]`. -/
def distinctStmt (items : List SqlEquiv.SelectItem) (f : SqlEquiv.FromClause)
    (wh : Option SqlEquiv.Expr) : SqlEquiv.Stmt :=
  .query (.simple (.mk true items (some f) wh [] none [] none none))

/-- Typed rows of one typing are equal exactly when the related untyped rows have equal value
    keys: the two evaluators remove the same duplicates. -/
theorem row_eq_iff_valueKey {k : ℕ} {Γ : Fin k → SqlType} {r r' : Row k} {u u' : SqlEquiv.Row}
    (h : OutRel r u) (hc : r.Conforms Γ) (h' : OutRel r' u') (hc' : r'.Conforms Γ) :
    r = r' ↔ u.valueKey = u'.valueKey := by
  unfold OutRel at h h'
  have hl := h.length_eq
  have hl' := h'.length_eq
  simp only [List.length_ofFn, List.length_map] at hl hl'
  have hcol : ∀ i : Fin k, r i = r' i ↔
      ((u.map Prod.snd)[i.1]'(by simp; omega)).setKey =
        ((u'.map Prod.snd)[i.1]'(by simp; omega)).setKey := by
    intro i
    have h1 := (List.forall₂_iff_get.mp h).2 i.1 (by simp) (by simp; omega)
    have h2 := (List.forall₂_iff_get.mp h').2 i.1 (by simp) (by simp; omega)
    simp only [List.get_eq_getElem, List.getElem_ofFn] at h1 h2
    exact trel_iff (τ := Γ i) _ _ _ _ ⟨h1, hc i⟩ ⟨h2, hc' i⟩
  simp only [SqlEquiv.Row.valueKey]
  constructor
  · rintro rfl
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [List.getElem_map]
    have hi : i < k := by simp at h1; omega
    have := (hcol ⟨i, hi⟩).mp rfl
    simpa using this
  · intro he
    funext i
    apply (hcol i).mpr
    have h1 : i.1 < ((u.map Prod.snd).map SqlEquiv.Value.setKey).length := by simp; omega
    have h2 : i.1 < ((u'.map Prod.snd).map SqlEquiv.Value.setKey).length := by simp; omega
    have := List.getElem_of_eq he h1
    simpa using this

/-- Related lists deduplicate to related lists, up to the order: the typed side keeps the last
    copy of each row (`List.dedup`), `SqlEquiv` the first (`dedupByKey`). -/
theorem distinct_rel {k : ℕ} {Γ : Fin k → SqlType} {rs : List (Row k)} {out : List SqlEquiv.Row}
    (h : List.Forall₂ OutRel rs out) (hc : ∀ r ∈ rs, r.Conforms Γ) :
    ∃ rs', rs.dedup.Perm rs' ∧
      List.Forall₂ OutRel rs' (SqlEquiv.dedupByKey SqlEquiv.Row.valueKey out) := by
  have h' : List.Forall₂ (fun r u => OutRel r u ∧ r.Conforms Γ) rs out := by
    refine List.forall₂_iff_get.mpr ⟨h.length_eq, fun i h1 h2 => ?_⟩
    exact ⟨(List.forall₂_iff_get.mp h).2 i h1 h2, hc _ (List.get_mem ..)⟩
  have hrel := dedup_rel (R := fun (r : Row k) (u : SqlEquiv.Row) => OutRel r u ∧ r.Conforms Γ)
    (f := SqlEquiv.Row.valueKey)
    (fun a b x y ha hb => row_eq_iff_valueKey ha.1 ha.2 hb.1 hb.2) rs.length le_rfl h'
  obtain ⟨hnd, hmem⟩ := dedupFirst_spec rs.length rs le_rfl
  refine ⟨dedupFirst rs.length rs, ?_, hrel.imp fun _ _ h => h.1⟩
  exact (List.perm_ext_iff_of_nodup (List.nodup_dedup _) hnd).mpr fun x => by
    simp [List.mem_dedup, hmem]

/-- `finishSelect` without `ORDER BY`/`LIMIT`: the projection, under `DISTINCT` when asked. -/
theorem finishSelect_plain {S : DbSchema} (fold : String → String) (sc : Scoped S) (d : Bool) :
    finishSelect fold sc d [] none none =
      .ok ⟨sc.items.length,
        (if d then .distinct (.project (fun i => (sc.items[i]).1) sc.q)
         else .project (fun i => (sc.items[i]).1) sc.q),
        fun i => (sc.items[i]).2⟩ := by
  unfold finishSelect
  cases d <;> cases sc.q.typeOf <;>
    simp [bind, Except.bind, pure, Except.pure]

/-- The elaborated `SELECT DISTINCT` is `Query.distinct` over the query of the same statement
    without `DISTINCT`, which elaborates too. -/
theorem elab_distinct_shape (N : NamedSchema) {items : List SqlEquiv.SelectItem}
    {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr} (hit : itemsFragment items = true)
    (hw : ∀ w ∈ wh, isFragment w = true) {e : Elaborated N.S}
    (h : elabStmt N (distinctStmt items f wh) = .ok e) :
    ∃ e₀ : Elaborated N.S, elabStmt N (joinStmt items f wh [] none none) = .ok e₀ ∧
      e = ⟨e₀.n, .distinct e₀.q, e₀.cols⟩ := by
  simp only [distinctStmt, elabStmt, elabQuery, bind, Except.bind] at h
  rcases hraw : elabQueryRaw N (.simple (.mk true items (some f) wh [] none [] none none))
    with _ | e₁
  · simp [hraw] at h
  simp only [hraw] at h
  split at h
  swap
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hty
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  -- the raw elaborations of the two statements differ by the `DISTINCT` on top
  suffices hs : ∃ e₀ : Elaborated N.S,
      elabQueryRaw N (.simple (.mk false items (some f) wh [] none [] none none)) = .ok e₀ ∧
      e₁ = ⟨e₀.n, .distinct e₀.q, e₀.cols⟩ by
    obtain ⟨e₀, he₀, rfl⟩ := hs
    refine ⟨e₀, ?_, rfl⟩
    simp only [joinStmt, elabStmt, elabQuery, bind, Except.bind, he₀]
    have : e₀.q.typeOf.isSome = true := by simpa using hty
    simp [this, pure, Except.pure]
  simp only [elabQueryRaw, elabSelect] at hraw ⊢
  rw [elabSelectF] at hraw ⊢
  unfold elabWhere at hraw ⊢
  obtain ⟨⟨n, qf, cf⟩, hf, hraw⟩ := bind_ok hraw
  simp only [hf, bind, Except.bind]
  dsimp only at hraw ⊢
  cases wh with
  | none =>
    simp only [pure, Except.pure, bind, Except.bind] at hraw ⊢
    rw [aggsOfList_items (fun _ _ => rfl) items hit] at hraw ⊢
    simp only [List.map_nil, aggsOfList, List.isEmpty_nil, aggsOfOpt, List.append_nil,
      List.eraseDups_nil, Option.isNone_none, Bool.and_self, ↓reduceIte] at hraw ⊢
    rcases hits : elabItems N cf items with _ | its
    · simp [hits] at hraw
    simp only [hits, finishSelect_plain, ↓reduceIte, Bool.false_eq_true, Except.ok.injEq] at hraw ⊢
    exact ⟨_, rfl, hraw.symm⟩
  | some w =>
    simp only [subsOf_frag w (hw w rfl), List.foldl_nil, List.isEmpty_nil, ↓reduceIte] at hraw ⊢
    rcases hp : elabExpr cf N.fold noHook w with _ | p
    · simp [hp, bind, Except.bind] at hraw
    simp only [hp, bind, Except.bind, pure, Except.pure] at hraw ⊢
    rw [aggsOfList_items (fun _ _ => rfl) items hit] at hraw ⊢
    simp only [List.map_nil, aggsOfList, List.isEmpty_nil, aggsOfOpt, List.append_nil,
      List.eraseDups_nil, Option.isNone_none, Bool.and_self, ↓reduceIte] at hraw ⊢
    rcases hits : elabItems N cf items with _ | its
    · simp [hits] at hraw
    simp only [hits, finishSelect_plain, ↓reduceIte, Bool.false_eq_true, Except.ok.injEq] at hraw ⊢
    exact ⟨_, rfl, hraw.symm⟩

/-- **Elaborator correctness for `SELECT DISTINCT` (#352, roadmap step 5).** For
    `SELECT DISTINCT e₁, …, eₖ FROM f [WHERE p]`, `f` and the expressions as in
    `elabStmt_correct_join`: when the statement elaborates, the typed query evaluates, and its
    rows are, up to their order, related to `SqlEquiv`'s. (The order differs: the typed core keeps
    the last copy of each row, `SqlEquiv` the first; SQL fixes none without `ORDER BY`.) -/
theorem elabStmt_correct_distinct (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause} {wh : Option SqlEquiv.Expr}
    (hit : itemsFragment items = true) (hff : fromFragment f = true)
    (hw : ∀ w ∈ wh, isFragment w = true)
    {e : Elaborated N.S} (h : elabStmt N (distinctStmt items f wh) = .ok e)
    (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (distinctStmt items f wh)).2 = some out ∧
        ∃ rs', rs.Perm rs' ∧ List.Forall₂ OutRel rs' out := by
  obtain ⟨e₀, he₀, rfl⟩ := elab_distinct_shape N hit hw h
  obtain ⟨rs₀, hrs₀, out₀, hout₀, hrel₀⟩ := elabStmt_correct_join N hfold hfoldCI hwn hfix hD hrel
    hit hff hw (by simp) (by simp) he₀ hnb
  -- the plain statement's rows conform to its type
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, e₀.q.typeOf = some Γ := by
    simp only [joinStmt, elabStmt, elabQuery, bind, Except.bind] at he₀
    split at he₀
    · cases he₀
    · split at he₀
      · rename_i hty
        simp only [pure, Except.pure, Except.ok.injEq] at he₀
        subst he₀
        exact Option.isSome_iff_exists.mp hty
      · simp [throw, throwThe, MonadExceptOf.throw] at he₀
  have hconf := Query.conforms_of_eval_eq_ok hD hΓ hrs₀
  obtain ⟨rs', hperm, hrel'⟩ := distinct_rel hrel₀ hconf
  refine ⟨rs₀.dedup, by simp [Query.eval_distinct, hrs₀, pure, Except.pure, bind, Except.bind],
    SqlEquiv.dedupByKey SqlEquiv.Row.valueKey out₀, ?_, rs', hperm, hrel'⟩
  simp only [distinctStmt, joinStmt, SqlEquiv.evalStmt, SqlEquiv.evalQuery] at hout₀ ⊢
  rw [SqlEquiv.evalSelect_eq_evalSelectCore] at hout₀ ⊢
  rw [evalSelectCore_distinct]
  simp only [Option.some.injEq] at hout₀ ⊢
  rw [hout₀]

end SqlBridge.CorrectDistinct
