/-
  Elaborator correctness for set operations (#352, the subquery block, part A):
  `q₁ UNION [ALL] q₂`, `q₁ INTERSECT q₂`, `q₁ EXCEPT q₂`, nested freely, up to the order of
  the rows.

  As for `DISTINCT` (registry T18), both evaluators compare rows the same way (by position and
  value, `NULL`s equal: `row_eq_iff_valueKey`) and keep different copies of a duplicate:
  `SqlEquiv` the first (`dedupByKey`), the typed core the last (`List.dedup`). So the result of
  a set operation is the same rows in a different order, and the theorem relates the two up to
  a permutation (`PermRel`). `UNION ALL` removes nothing and would keep the order; it is stated
  with the others because its branches are only related up to order.

  * `permRel_append`, `permRel_dedup`, `permRel_filter_mem`: the three list operations the set
    operations are made of preserve `PermRel`.
  * `elab_compound_shape`: the branches of a compound query that elaborates elaborate too, to
    queries of one type, and the result is the corresponding typed operator over them.
  * `compound_rel`: if both branches are related, so is the compound query.
  * `setOpTree_rel`: the same over a whole tree of set operations, for any class of leaves
    that is related.
-/
import SqlBridge.CorrectDistinct
import SqlBridge.CorrectGrouped

namespace SqlBridge.CorrectSetOp
open SqlCore SqlBridge SqlBridge.Correct SqlBridge.CorrectOrder SqlBridge.CorrectAgg
open SqlBridge.CorrectDistinct SqlBridge.CorrectJoin SqlBridge.CorrectGroup SqlBridge.CorrectGrouped

/-- Typed rows relate to an untyped table up to the order of the rows. -/
def PermRel {k : ℕ} (rs : List (Row k)) (out : List SqlEquiv.Row) : Prop :=
  ∃ rs', rs.Perm rs' ∧ List.Forall₂ OutRel rs' out

theorem PermRel.of_forall₂ {k : ℕ} {rs : List (Row k)} {out : List SqlEquiv.Row}
    (h : List.Forall₂ OutRel rs out) : PermRel rs out := ⟨rs, .refl _, h⟩

theorem forall₂_mem_left {α β : Type _} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) {a : α} (ha : a ∈ as) : ∃ b ∈ bs, R a b := by
  induction h with
  | nil => cases ha
  | cons hab _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) {b : β} (hb : b ∈ bs) : ∃ a ∈ as, R a b := by
  induction h with
  | nil => cases hb
  | cons hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- Related lists filter to related lists when the two predicates agree on related elements. -/
theorem forall₂_filter {α β : Type _} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    {as : List α} {bs : List β} (h : List.Forall₂ R as bs)
    (hpq : ∀ a ∈ as, ∀ b, R a b → p a = q b) :
    List.Forall₂ R (as.filter p) (bs.filter q) := by
  induction h with
  | nil => exact .nil
  | @cons a b as bs hab _ ih =>
    have hab' := hpq a List.mem_cons_self b hab
    have ih' := ih fun a ha b hr => hpq a (List.mem_cons_of_mem _ ha) b hr
    simp only [List.filter_cons, hab']
    split
    · exact .cons hab ih'
    · exact ih'

/-- Renaming an untyped row's columns does not change what it relates to. -/
theorem outRel_renameTo {k : ℕ} {r : Row k} {u : SqlEquiv.Row} (ns : Option (List String))
    (h : OutRel r u) : OutRel r (SqlEquiv.Row.renameTo ns u) := by
  cases ns with
  | none => exact h
  | some ns =>
    simp only [SqlEquiv.Row.renameTo]
    split
    · next hl =>
      unfold OutRel at h ⊢
      rwa [List.map_snd_zip (by simp [hl])]
    · exact h

/-- `UNION ALL`: concatenation. -/
theorem permRel_append {k : ℕ} {rs ss : List (Row k)} {l r : List SqlEquiv.Row}
    (h₁ : PermRel rs l) (h₂ : PermRel ss r) (ns : Option (List String)) :
    PermRel (rs ++ ss) (l ++ r.map (SqlEquiv.Row.renameTo ns)) := by
  obtain ⟨rs', hp₁, hr₁⟩ := h₁
  obtain ⟨ss', hp₂, hr₂⟩ := h₂
  refine ⟨rs' ++ ss', hp₁.append hp₂, List.rel_append hr₁ ?_⟩
  rw [List.forall₂_map_right_iff]
  exact hr₂.imp fun _ _ h => outRel_renameTo ns h

/-- Deduplication: the typed side keeps the last copy, `SqlEquiv` the first. -/
theorem permRel_dedup {k : ℕ} {Γ : Fin k → SqlType} {rs : List (Row k)}
    {out : List SqlEquiv.Row} (h : PermRel rs out) (hc : ∀ r ∈ rs, r.Conforms Γ) :
    PermRel rs.dedup (SqlEquiv.dedupByKey SqlEquiv.Row.valueKey out) := by
  obtain ⟨rs', hp, hr⟩ := h
  obtain ⟨rs'', hp', hr'⟩ := distinct_rel hr fun r hr => hc r (hp.mem_iff.mpr hr)
  exact ⟨rs'', hp.dedup.trans hp', hr'⟩

/-- Membership in the other branch: a typed row occurs in the typed branch exactly when the
    related untyped row's value key occurs among the untyped branch's. -/
theorem mem_iff_contains_valueKey {k : ℕ} {Γ : Fin k → SqlType} {ss : List (Row k)}
    {r : List SqlEquiv.Row} (h₂ : PermRel ss r) (hc₂ : ∀ s ∈ ss, s.Conforms Γ)
    {x : Row k} {u : SqlEquiv.Row} (hxu : OutRel x u) (hcx : x.Conforms Γ) :
    decide (x ∈ ss) = (r.map SqlEquiv.Row.valueKey).contains u.valueKey := by
  obtain ⟨ss', hp, hr⟩ := h₂
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.contains_iff_mem, List.mem_map]
  constructor
  · intro hx
    obtain ⟨u', hu', hxu'⟩ := forall₂_mem_left hr (hp.mem_iff.mp hx)
    exact ⟨u', hu', ((row_eq_iff_valueKey hxu hcx hxu' hcx).mp rfl).symm⟩
  · rintro ⟨u', hu', hk⟩
    obtain ⟨x', hx', hxu'⟩ := forall₂_mem_right hr hu'
    have hx'ss := hp.mem_iff.mpr hx'
    have : x = x' := (row_eq_iff_valueKey hxu hcx hxu' (hc₂ x' hx'ss)).mpr hk.symm
    exact this ▸ hx'ss

/-- `INTERSECT` (`keep = true`) and `EXCEPT` (`keep = false`) before deduplication: the rows of
    one branch that occur, or do not occur, in the other. -/
theorem permRel_filter_mem {k : ℕ} {Γ : Fin k → SqlType} {rs ss : List (Row k)}
    {l r : List SqlEquiv.Row} (keep : Bool) (h₁ : PermRel rs l) (h₂ : PermRel ss r)
    (hc₁ : ∀ x ∈ rs, x.Conforms Γ) (hc₂ : ∀ s ∈ ss, s.Conforms Γ) :
    PermRel (rs.filter fun x => decide (x ∈ ss) == keep)
      (l.filter fun u => (r.map SqlEquiv.Row.valueKey).contains u.valueKey == keep) := by
  obtain ⟨rs', hp, hr⟩ := h₁
  refine ⟨rs'.filter fun x => decide (x ∈ ss) == keep, hp.filter _, forall₂_filter hr ?_⟩
  intro x hx u hxu
  rw [mem_iff_contains_valueKey h₂ hc₂ hxu (hc₁ x (hp.mem_iff.mpr hx))]

/-- `INTERSECT` and `EXCEPT`. -/
theorem permRel_setOp {k : ℕ} {Γ : Fin k → SqlType} {rs ss : List (Row k)}
    {l r : List SqlEquiv.Row} (keep : Bool) (h₁ : PermRel rs l) (h₂ : PermRel ss r)
    (hc₁ : ∀ x ∈ rs, x.Conforms Γ) (hc₂ : ∀ s ∈ ss, s.Conforms Γ) :
    PermRel (Row.setOp keep rs ss)
      (SqlEquiv.dedupByKey SqlEquiv.Row.valueKey
        (l.filter fun u => (r.map SqlEquiv.Row.valueKey).contains u.valueKey == keep)) :=
  permRel_dedup (permRel_filter_mem keep h₁ h₂ hc₁ hc₂)
    fun x hx => hc₁ x (List.mem_filter.mp hx).1

/-! ### The elaborated shape and the statement -/

/-- The typed operator a set operation elaborates to. -/
def setOpQuery {S : DbSchema} {n : ℕ} (op : SqlEquiv.SetOp) (ql qr : Query S n) : Query S n :=
  match op with
  | .unionAll => .unionAll ql qr
  | .union => .distinct (.unionAll ql qr)
  | .intersect => .intersect ql qr
  | .exceptOp => .difference ql qr

/-- The branches of a compound query that elaborates elaborate too, to queries of one type, and
    the result is the corresponding typed operator over them, with the left branch's columns. -/
theorem elab_compound_shape (N : NamedSchema) {l r : SqlEquiv.Query} {op : SqlEquiv.SetOp}
    {e : Elaborated N.S} (h : elabQuery N (.compound l op r) = .ok e) :
    ∃ (n : ℕ) (ql qr : Query N.S n) (cl cr : Fin n → Column) (Γ : Fin n → SqlType),
      elabQuery N l = .ok ⟨n, ql, cl⟩ ∧ elabQuery N r = .ok ⟨n, qr, cr⟩ ∧
      ql.typeOf = some Γ ∧ qr.typeOf = some Γ ∧
      e = ⟨n, setOpQuery op ql qr, cl⟩ := by
  simp only [elabQuery] at h
  obtain ⟨e₁, hraw, h⟩ := bind_ok h
  split at h
  swap
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hty
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rw [elabQueryRaw] at hraw
  split at hraw
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hraw
  obtain ⟨⟨n, ql, cl⟩, hl, hraw⟩ := bind_ok hraw
  obtain ⟨⟨m, qr, cr⟩, hr, hraw⟩ := bind_ok hraw
  dsimp only at hraw
  split at hraw
  swap
  · simp [throw, throwThe, MonadExceptOf.throw] at hraw
  rename_i hmn
  subst hmn
  -- the result's type gives both branches the same type
  have hΓ : ∃ Γ, ql.typeOf = some Γ ∧ qr.typeOf = some Γ := by
    cases op <;> simp only [pure, Except.pure, Except.ok.injEq] at hraw <;> subst hraw <;>
      simp only [Query.typeOf, Option.bind_eq_bind] at hty <;>
      cases hql : ql.typeOf <;> simp only [hql, Option.bind_none, Option.bind_some,
        Option.isSome_none, Bool.false_eq_true] at hty <;>
      split at hty <;> first | exact ⟨_, rfl, by assumption⟩ | simp at hty
  obtain ⟨Γ, hΓl, hΓr⟩ := hΓ
  refine ⟨m, ql, qr, cl, cr, Γ, ?_, ?_, hΓl, hΓr, ?_⟩
  · simp [elabQuery, hl, hΓl, bind, Except.bind, pure, Except.pure]
  · simp [elabQuery, hr, hΓr, bind, Except.bind, pure, Except.pure]
  · cases op <;> simp only [pure, Except.pure, Except.ok.injEq] at hraw <;>
      simpa [setOpQuery] using hraw.symm

/-- **One set operation, on evaluated branches.** If both branches' rows are related up to order
    to two untyped tables, the typed operator's rows are related, up to order, to `SqlEquiv`'s
    `applySetOp` of them, whatever names it renames the right branch to. Used for statements
    (`compound_rel`) and for subquery bodies under an outer row (`SqlBridge.CorrectSub`, #410). -/
theorem setOpQuery_rel {S : DbSchema} {D : Database S} (hD : D.Conforms) {n : ℕ}
    {ql qr : Query S n} {Γ : Fin n → SqlType} (hΓl : ql.typeOf = some Γ)
    (hΓr : qr.typeOf = some Γ) {rs ss : List (Row n)} (hrs : ql.eval D = .ok rs)
    (hss : qr.eval D = .ok ss) {l r : List SqlEquiv.Row} (h₁ : PermRel rs l) (h₂ : PermRel ss r)
    (op : SqlEquiv.SetOp) (names : Option (List String)) :
    ∃ ts, (setOpQuery op ql qr).eval D = .ok ts ∧
      PermRel ts (SqlEquiv.applySetOp op names l r) := by
  have hc₁ := Query.conforms_of_eval_eq_ok hD hΓl hrs
  have hc₂ := Query.conforms_of_eval_eq_ok hD hΓr hss
  cases op <;> simp only [setOpQuery]
  · -- UNION
    refine ⟨(rs ++ ss).dedup, by simp [Query.eval_distinct, Query.eval_unionAll, hrs, hss,
      pure, Except.pure, bind, Except.bind], ?_⟩
    exact permRel_dedup (permRel_append h₁ h₂ _) fun x hx =>
      (List.mem_append.mp hx).elim (hc₁ x) (hc₂ x)
  · -- UNION ALL
    exact ⟨rs ++ ss, by simp [Query.eval_unionAll, hrs, hss, pure, Except.pure, bind,
      Except.bind], permRel_append h₁ h₂ _⟩
  · -- INTERSECT
    refine ⟨Row.setOp true rs ss, by simp [Query.eval_intersect, hrs, hss, pure, Except.pure,
      bind, Except.bind], ?_⟩
    simpa [SqlEquiv.applySetOp] using permRel_setOp true h₁ h₂ hc₁ hc₂
  · -- EXCEPT
    refine ⟨Row.setOp false rs ss, by simp [Query.eval_difference, hrs, hss, pure, Except.pure,
      bind, Except.bind], ?_⟩
    simpa [SqlEquiv.applySetOp] using permRel_setOp false h₁ h₂ hc₁ hc₂

/-- A parsed query and its elaboration are related: the typed query evaluates, and its rows
    are `SqlEquiv`'s up to their order. -/
def QueryRel {N : NamedSchema} (D : Database N.S) (db : SqlEquiv.Database)
    (q : SqlEquiv.Query) (e : Elaborated N.S) : Prop :=
  ∃ rs, e.q.eval D = .ok rs ∧ PermRel rs (SqlEquiv.evalQuery db q)

/-- **One set operation.** The branches of a compound query that elaborates elaborate; if both
    are related to `SqlEquiv`'s results, so is the compound query. -/
theorem compound_rel (N : NamedSchema) {D : Database N.S} (hD : D.Conforms)
    (db : SqlEquiv.Database) {l r : SqlEquiv.Query} {op : SqlEquiv.SetOp} {e : Elaborated N.S}
    (h : elabQuery N (.compound l op r) = .ok e) :
    ∃ el er : Elaborated N.S, elabQuery N l = .ok el ∧ elabQuery N r = .ok er ∧
      (QNoBoolOrder e.q → QNoBoolOrder el.q ∧ QNoBoolOrder er.q) ∧
      (QueryRel D db l el → QueryRel D db r er → QueryRel D db (.compound l op r) e) := by
  obtain ⟨n, ql, qr, cl, cr, Γ, hl, hr, hΓl, hΓr, he⟩ := elab_compound_shape N h
  clear h
  subst he
  refine ⟨_, _, hl, hr, ?_, ?_⟩
  · cases op <;> simp only [setOpQuery, QNoBoolOrder] <;> exact id
  rintro ⟨rs, hrs, h₁⟩ ⟨ss, hss, h₂⟩
  obtain ⟨ts, hts, hrel⟩ := setOpQuery_rel hD hΓl hΓr hrs hss h₁ h₂ op (SqlEquiv.Query.outputNames? l)
  exact ⟨ts, hts, by rw [SqlEquiv.evalQuery_compound]; exact hrel⟩

/-- A tree of set operations over leaves of a given class. -/
inductive SetOpTree (leaf : SqlEquiv.Query → Prop) : SqlEquiv.Query → Prop
  | leaf {q : SqlEquiv.Query} : leaf q → SetOpTree leaf q
  | node {l r : SqlEquiv.Query} (op : SqlEquiv.SetOp) :
    SetOpTree leaf l → SetOpTree leaf r → SetOpTree leaf (.compound l op r)

/-- **Trees of set operations.** If every leaf of the class is related whenever it elaborates,
    so is every tree of set operations over such leaves. -/
theorem setOpTree_rel (N : NamedSchema) {D : Database N.S} (hD : D.Conforms)
    (db : SqlEquiv.Database) {leaf : SqlEquiv.Query → Prop}
    (hleaf : ∀ q (e : Elaborated N.S), leaf q → elabQuery N q = .ok e → QNoBoolOrder e.q →
      QueryRel D db q e)
    {q : SqlEquiv.Query} (ht : SetOpTree leaf q) :
    ∀ e : Elaborated N.S, elabQuery N q = .ok e → QNoBoolOrder e.q → QueryRel D db q e := by
  induction ht with
  | leaf hq => exact fun e h hnb => hleaf _ e hq h hnb
  | node op _ _ ihl ihr =>
    intro e h hnb
    obtain ⟨el, er, hl, hr, hnb', hrel⟩ := compound_rel N hD db h
    exact hrel (ihl el hl (hnb' hnb).1) (ihr er hr (hnb' hnb).2)

/-! ### The leaves, and the statement for parsed set operations -/

/-- The branches the set-operation theorem takes: the statements of the earlier steps that
    have no `ORDER BY`, `LIMIT` or `OFFSET` (a branch cannot have one) and whose results are
    related exactly or up to order. `AVG` items are left out: their values are related only up
    to rounding (step 3c), which a set operation's row comparison could tell apart. -/
inductive Leaf (N : NamedSchema) : SqlEquiv.Query → Prop
  /-- `SELECT e₁, …, eₖ FROM f [WHERE p]` (`elabStmt_correct_join`). -/
  | plain {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
      {wh : Option SqlEquiv.Expr} (hit : itemsFragment items = true)
      (hff : fromFragment f = true) (hw : ∀ w ∈ wh, isFragment w = true) :
      Leaf N (.simple (.mk false items (some f) wh [] none [] none none))
  /-- `SELECT DISTINCT e₁, …, eₖ FROM f [WHERE p]` (`elabStmt_correct_distinct`). -/
  | distinct {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
      {wh : Option SqlEquiv.Expr} (hit : itemsFragment items = true)
      (hff : fromFragment f = true) (hw : ∀ w ∈ wh, isFragment w = true) :
      Leaf N (.simple (.mk true items (some f) wh [] none [] none none))
  /-- Aggregates without `GROUP BY` (`elabStmt_correct_agg`). -/
  | agg {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
      {wh : Option SqlEquiv.Expr} (hai : CorrectAgg.aggItems items = true) (hne : items ≠ [])
      (hff : fromFragment f = true) (hw : ∀ w ∈ wh, isFragment w = true) :
      Leaf N (.simple (.mk false items (some f) wh [] none [] none none))
  /-- `GROUP BY` columns with an optional `HAVING`, bare columns included, no `AVG` item
      (`elabStmt_correct_grouped`). -/
  | grouped {items : List SqlEquiv.SelectItem} {f : SqlEquiv.FromClause}
      {wh : Option SqlEquiv.Expr} {groupBy : List SqlEquiv.Expr} {having : Option SqlEquiv.Expr}
      (hgi : groupedItems items = true) (hgb : groupBy ≠ [])
      (hgc : ∀ e ∈ groupBy, ∃ c, e = .col c) (hff : fromFragment f = true)
      (hw : ∀ w ∈ wh, isFragment w = true) (hhv : ∀ h ∈ having, havingFragment groupBy h = true)
      (hnv : ∀ h ∈ having, hasCmpAvg h = false)
      (hbf : BareOk N items groupBy having [])
      (hna : ∀ it ∈ items, CorrectAvg.avgFragment (itemExpr it) = false) :
      Leaf N (.simple (.mk false items (some f) wh groupBy having [] none none))

/-- **Elaborator correctness for set operations (#352).** For a tree of `UNION [ALL]`,
    `INTERSECT` and `EXCEPT` whose branches are statements of the earlier steps (`Leaf`): when
    the query elaborates, the typed query evaluates, and its rows are, up to their order,
    related to `SqlEquiv`'s. (The order differs as for `DISTINCT`: the typed core keeps the last
    copy of a duplicate row, `SqlEquiv` the first; SQL fixes none without `ORDER BY`.) -/
theorem elabStmt_correct_setOp (N : NamedSchema) (hfold : ∀ s, (N.fold s).toLower = s.toLower)
    (hfoldCI : ∀ x y, N.fold x = N.fold y ↔ x.toLower = y.toLower) (hwn : WellNamed N)
    (hfix : ∀ T j, N.fold (N.S.columns T j).name = (N.S.columns T j).name)
    {db : SqlEquiv.Database} {D : Database N.S} (hD : D.Conforms) (hrel : DbRel N db D)
    {q : SqlEquiv.Query} (ht : SetOpTree (Leaf N) q)
    {e : Elaborated N.S} (h : elabStmt N (.query q) = .ok e) (hnb : QNoBoolOrder e.q) :
    ∃ rs, e.q.eval D = .ok rs ∧
      ∃ out, (SqlEquiv.evalStmt db (.query q)).2 = some out ∧
        ∃ rs', rs.Perm rs' ∧ List.Forall₂ OutRel rs' out := by
  have key : QueryRel D db q e := by
    refine setOpTree_rel N hD db (leaf := Leaf N) ?_ ht e h hnb
    intro q e hq h hnb
    cases hq with
    | @plain items f wh hit hff hw =>
      obtain ⟨rs, hrs, out, hout, hr⟩ := elabStmt_correct_join N hfold hfoldCI hwn hfix hD hrel
        (orderBy := []) (lim := none) (off := none) hit hff hw (by simp) (by simp) h hnb
      simp only [joinStmt, SqlEquiv.evalStmt, Option.some.injEq] at hout
      exact ⟨rs, hrs, hout ▸ .of_forall₂ hr⟩
    | @distinct items f wh hit hff hw =>
      obtain ⟨rs, hrs, out, hout, hr⟩ := elabStmt_correct_distinct N hfold hfoldCI hwn hfix hD
        hrel hit hff hw h hnb
      simp only [distinctStmt, SqlEquiv.evalStmt, Option.some.injEq] at hout
      exact ⟨rs, hrs, hout ▸ hr⟩
    | @agg items f wh hai hne hff hw =>
      obtain ⟨rs, hrs, out, hout, hr⟩ := elabStmt_correct_agg N hfold hfoldCI hwn hfix hD hrel
        hai hne hff hw h hnb
      simp only [aggStmt, SqlEquiv.evalStmt, Option.some.injEq] at hout
      exact ⟨rs, hrs, hout ▸ .of_forall₂ hr⟩
    | @grouped items f wh groupBy having hgi hgb hgc hff hw hhv hnv hbf hna =>
      obtain ⟨rs, hrs, out, hout, hr⟩ := elabStmt_correct_grouped N hfold hfoldCI hwn hfix hD
        hrel (orderBy := []) (lim := none) (off := none) hgi hgb hgc hff hw hhv
        (havingAvgOk_of_noAvg hnv) (by simp) hbf
        (by simp) h hnb
      simp only [groupedStmt, SqlEquiv.evalStmt, Option.some.injEq] at hout
      exact ⟨rs, hrs, hout ▸ .of_forall₂ (hr.imp fun _ _ h => outRel_of_outRelI hna h)⟩
  obtain ⟨rs, hrs, rs', hp, hr⟩ := key
  exact ⟨rs, hrs, _, rfl, rs', hp, hr⟩

end SqlBridge.CorrectSetOp
