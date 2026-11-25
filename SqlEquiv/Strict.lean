/-
  Strict evaluation per dialect (#270, registry row 23)

  **Part of the reference oracle (decision D7 as amended, #466).** The typed core (`SqlCore`) is
  strict by construction; this layer stays as the oracle's error mode, which the oracle's DuckDB
  and Postgres differential suites use to compare error cases.

  The evaluator is quiet: an evaluation error (`none`) drops the row in `WHERE` and shows as NULL
  in the select list, and every theorem is stated over that evaluator. Postgres and DuckDB abort
  the statement instead. This module layers the dialect's choice on top, without touching the
  evaluator or any theorem:

  - `checkQuery` walks a query and reports the first clause expression that yields an error on a
    row the quiet evaluator evaluates it on: `WHERE`, join `ON`, `GROUP BY` keys, aggregate
    arguments, `HAVING`, select items (window items included), window arguments and keys, and
    `ORDER BY` keys. It recurses into derived tables, set operation branches, CTE bodies (each
    working table of a recursive CTE), and the subqueries engines always evaluate with an
    expression (scalar subqueries and `IN (subquery)`, `strictSubqueries`), with the row as the
    outer row. `checkDml` does the same for INSERT, UPDATE and DELETE.
  - `evalQueryIn mode db q` is the quiet result, or the error when the mode is strict and the
    check finds one. `evalQueryIn_transfer`: quiet-equivalent queries that both succeed give
    the same rows, so every proved equivalence carries over.

  The check is a runtime approximation of the engines. Not seen (decided on #448): errors engines
  raise at bind time (a type mismatch behind `FALSE AND …` or over an empty table; SqlEquiv's
  database has no schema), subqueries under `AND`/`OR`, past a CASE's first condition or in
  `EXISTS` (engines short-circuit or differ), the items of a window query under LIMIT without
  ORDER BY (which rows are returned is unknown), and `ORDER BY` keys of an aggregate query without
  `GROUP BY` (one row, never compared).
-/
import SqlEquiv.Semantics

namespace SqlEquiv

-- ============================================================================
-- DuckDB: division and modulo by zero are not errors
-- ============================================================================

/-- `a / b` and `a % b` become `CASE WHEN b = 0 THEN NULL = (a op 1) ELSE … END`, so a division
    by zero yields NULL instead of an error when the expression is checked
    (`ErrorMode.strictDivZeroNull`). A divisor that is itself an error, or not a number, still
    yields an error, and so does a dividend that is an error or not a number: `a op 1` is the
    operator's own type check of `a` with a divisor that cannot be zero, and `NULL = x` is NULL for
    every value `x` and an error when `x` is one. A plain `THEN NULL` hid `(s + 1) % 0` (`/audit`,
    23 Nov 2026); `THEN NULL = a` still hid `s % 0` and `TRUE / 0`, which DuckDB rejects at bind
    time (`/audit`, 25 Nov 2026). Does not enter subqueries or window functions. Used only by the
    checker, never for results; it does not preserve `≃ₑ`, on purpose. -/
def nullOnDivZero : Expr → Expr
  | .binOp op l r =>
    let l' := nullOnDivZero l
    let r' := nullOnDivZero r
    if op == .div || op == .mod then
      .case [(.binOp .eq r' (.lit (.int 0)),
          .binOp .eq (.lit (.null none)) (.binOp op l' (.lit (.int 1))))]
        (some (.binOp op l' r'))
    else .binOp op l' r'
  | .unaryOp op e => .unaryOp op (nullOnDivZero e)
  | .func name args => .func name (args.attach.map fun ⟨x, _⟩ => nullOnDivZero x)
  | .agg fn a d =>
    .agg fn (match a with
      | some x => some (nullOnDivZero x)
      | none => none) d
  | .case branches else_ =>
    .case (branches.attach.map fun ⟨p, _⟩ => (nullOnDivZero p.1, nullOnDivZero p.2))
      (match else_ with
        | some x => some (nullOnDivZero x)
        | none => none)
  | .inList e neg vals => .inList (nullOnDivZero e) neg (vals.attach.map fun ⟨x, _⟩ => nullOnDivZero x)
  | .between e lo hi => .between (nullOnDivZero e) (nullOnDivZero lo) (nullOnDivZero hi)
  | .inSubquery e neg sq => .inSubquery (nullOnDivZero e) neg sq
  | e => e
termination_by e => e.size
decreasing_by
  all_goals simp only [Expr.size, Expr.sizeOpt]
  all_goals first
    | omega
    | (have := Expr.size_le_sizeList_of_mem ‹_›; omega)
    | (have := Expr.size_le_sizePairs_of_mem (a := p.1) (b := p.2) ‹_›; omega)

/-- The expression the checker evaluates in place of `e`. -/
def ErrorMode.prep : ErrorMode → Expr → Expr
  | .strictDivZeroNull, e => nullOnDivZero e
  | _, e => e

/-- The arguments of the aggregate calls in `e`, outside subqueries and window functions.
    Engines evaluate them on every row of the group; the quiet aggregate evaluator skips an
    argument that is an error, so the checker evaluates them itself. -/
def aggArgs : Expr → List Expr
  | .agg _ (some a) _ => [a]
  | .binOp _ l r => aggArgs l ++ aggArgs r
  | .unaryOp _ e => aggArgs e
  | .func _ args => args.attach.flatMap fun ⟨x, _⟩ => aggArgs x
  | .case branches else_ =>
    branches.attach.flatMap (fun ⟨p, _⟩ => aggArgs p.1 ++ aggArgs p.2) ++
      (match else_ with
        | some x => aggArgs x
        | none => [])
  | .inList e _ vals => aggArgs e ++ vals.attach.flatMap fun ⟨x, _⟩ => aggArgs x
  | .between e lo hi => aggArgs e ++ aggArgs lo ++ aggArgs hi
  | .inSubquery e _ _ => aggArgs e
  | _ => []
termination_by e => e.size
decreasing_by
  all_goals simp only [Expr.size, Expr.sizeOpt]
  all_goals first
    | omega
    | (have := Expr.size_le_sizeList_of_mem ‹_›; omega)
    | (have := Expr.size_le_sizePairs_of_mem (a := p.1) (b := p.2) ‹_›; omega)

-- ============================================================================
-- The check
-- ============================================================================

/-- The expressions of the select items (stars have none). -/
def selectItemExprs (items : List SelectItem) : List Expr :=
  items.filterMap fun
    | .exprItem e _ => some e
    | .star _ => none

/-- The subqueries of `e` that the engines evaluate whenever `e` is evaluated (#448): scalar
    subqueries and the body of `IN (subquery)`. Not those under `AND`/`OR` (Postgres reorders
    and short-circuits the operands), past a CASE's first condition, past COALESCE's/IFNULL's
    first argument, among the values of `IN (list)`, inside aggregates or window functions, or in
    `EXISTS` (Postgres ignores its select list and stops at the first row; DuckDB scans its WHERE
    in full). -/
def strictSubqueries : Expr → List SubQuery
  | .subquery sq => [sq]
  | .inSubquery e _ sq => strictSubqueries e ++ [sq]
  | .binOp op l r =>
    if op == .and || op == .or then [] else strictSubqueries l ++ strictSubqueries r
  | .unaryOp _ e => strictSubqueries e
  | .func name args =>
    if name.toUpper == "COALESCE" || name.toUpper == "IFNULL" then
      match args with
      | a :: _ => strictSubqueries a
      | [] => []
    else args.attach.flatMap fun ⟨x, _⟩ => strictSubqueries x
  | .case branches _ =>
    match branches with
    | (c, _) :: _ => strictSubqueries c
    | [] => []
  | .inList e _ _ => strictSubqueries e
  | .between e lo hi => strictSubqueries e ++ strictSubqueries lo ++ strictSubqueries hi
  | _ => []
termination_by e => e.size
decreasing_by
  all_goals simp only [Expr.size, Expr.sizeList, Expr.sizePairs]
  all_goals first
    | omega
    | (have := Expr.size_le_sizeList_of_mem ‹_›; omega)

/-- The expressions inside the window functions of `e` (arguments, `PARTITION BY` and `ORDER BY`
    keys), outside subqueries. Engines evaluate them on every row of the window's input. -/
def windowParts : Expr → List Expr
  | .windowFn _ a spec =>
    (match a with
      | some x => [x]
      | none => []) ++ spec.partitionBy ++ spec.orderBy.map (·.expr)
  | .binOp _ l r => windowParts l ++ windowParts r
  | .unaryOp _ e => windowParts e
  | .func _ args => args.attach.flatMap fun ⟨x, _⟩ => windowParts x
  | .case branches else_ =>
    branches.attach.flatMap (fun ⟨p, _⟩ => windowParts p.1 ++ windowParts p.2) ++
      (match else_ with
        | some x => windowParts x
        | none => [])
  | .inList e _ vals => windowParts e ++ vals.attach.flatMap fun ⟨x, _⟩ => windowParts x
  | .between e lo hi => windowParts e ++ windowParts lo ++ windowParts hi
  | .inSubquery e _ _ => windowParts e
  | _ => []
termination_by e => e.size
decreasing_by
  all_goals simp only [Expr.size, Expr.sizeOpt]
  all_goals first
    | omega
    | (have := Expr.size_le_sizeList_of_mem ‹_›; omega)
    | (have := Expr.size_le_sizePairs_of_mem (a := p.1) (b := p.2) ‹_›; omega)

/-- The inputs a recursive CTE's body is evaluated on by `fixedPointIterate`, in order. -/
def fixedPointInputs (step : Table → Table) (init : Table) : Nat → List Table
  | 0 => []
  | n + 1 =>
    let result := step init
    init :: (if result == init then [] else fixedPointInputs step result n)

mutual

/-- The first error of a subquery body evaluated with outer row `outer`: each SELECT, and both
    branches of a set operation. -/
def checkSubQuery (m : ErrorMode) (db : Database) (outer : Row) (sq : SubQuery) : Option String :=
  match sq with
  | .simple sel => checkSelect m db outer sel
  | .compound l _ r => checkSubQuery m db outer l <|> checkSubQuery m db outer r
termination_by sq.size
decreasing_by all_goals (simp_wf; simp only [SubQuery.size]; omega)

/-- The first error of a FROM clause: derived tables, and join `ON` conditions (with their
    subqueries) on every pair of rows the join evaluates them on. -/
def checkFrom (m : ErrorMode) (db : Database) (fc : FromClause) : Option String :=
  match fc with
  | .table _ => none
  | .subquery sq _ => checkSubQuery m db [] sq
  | .join l _ r on_ =>
    checkFrom m db l <|> checkFrom m db r <|>
      match on_ with
      | none => none
      | some c =>
        let rs := evalFrom db r
        (evalFrom db l).findSome? fun lr => rs.findSome? fun rr =>
          if (evalExprWithDb db (lr ++ rr) (m.prep c)).isNone then some "ON"
          else (strictSubqueries c).attach.findSome? fun ⟨sq, _⟩ =>
            if _h : sq.size < 1 + l.size + r.size + c.size then checkSubQuery m db (lr ++ rr) sq
            else none
termination_by fc.size
decreasing_by all_goals (simp_wf; first | omega | (simp only [FromClause.size, Expr.sizeOpt]; omega))

/-- The first error of a SELECT evaluated with outer row `outer` (as `evalSelectWithContext db
    outer sel`, on the same rows): its FROM clause, then `WHERE`, `GROUP BY` keys, aggregate
    arguments, `HAVING`, select items (window items included), and `ORDER BY` keys; and the
    subqueries the engines evaluate with each of them (`strictSubqueries`), with the row as
    outer row. -/
def checkSelect (m : ErrorMode) (db : Database) (outer : Row) (sel : SelectStmt) :
    Option String :=
  let ee : Database → Row → Expr → Option Value := fun db' r e => evalExprWithDb db' r e
  let ea := evalExprWithAggParam ee
  let bad (r : Row) (e : Expr) : Bool := (evalExprWithDb db r (m.prep e)).isNone
  let badAgg (rows : Table) (sample : Row) (e : Expr) : Bool :=
    (ea db rows sample (m.prep e)).isNone
  -- the strict subqueries of `e`, evaluated with outer row `r`
  let subErr (r : Row) (e : Expr) : Option String :=
    (strictSubqueries e).attach.findSome? fun ⟨sq, _⟩ =>
      if _h : sq.size < sel.size then checkSubQuery m db r sq else none
  let exprErr (what : String) (r : Row) (e : Expr) : Option String :=
    if bad r e then some what else subErr r e
  let rowsErr (what : String) (rows : Table) (es : List Expr) : Option String :=
    rows.findSome? fun r => es.findSome? (exprErr what r)
  let fromErr := match sel.fromClause with
    | some f => if _h : f.size < sel.size then checkFrom m db f else none
    | none => none
  let base : Table := (match sel.fromClause with
    | some f => evalFrom db f
    | none => [[]]).map fun r => r ++ outer
  let strip (r : Row) : Row := r.take (r.length - outer.length)
  let filtered : Table := match sel.whereClause with
    | some c => base.filter fun r => evalExprWithDb db r c == some (Value.bool true)
    | none => base
  let items := selectItemExprs sel.items
  let win := selectHasWindowFn sel.items
  let grouped := !sel.groupBy.isEmpty
  let aggregated := selectHasAggregate sel.items || implicitGroup selectHasWindowFn sel.items sel.having
  let calls := selectMinMaxCalls sel.items sel.having
  -- each group with its sample row (the row bare columns read)
  let groups : List (Table × Row) :=
    if grouped then
      (groupRowsByKeyParam ee db filtered sel.groupBy).filterMap fun (_, rows) =>
        (bareSampleRow (evalExprWithDb db) calls rows).map fun s => (rows, s)
    else [(filtered, (bareSampleRow (evalExprWithDb db) calls filtered).getD [])]
  let passes (g : Table × Row) : Bool := match sel.having with
    | none => true
    | some c => ea db g.1 g.2 c == some (Value.bool true)
  let surv := groups.filter passes
  let synth := groupWindowRows surv
  let gev := groupWindowEval ea surv
  let whereErr := match sel.whereClause with
    | some c => rowsErr "WHERE" base [c]
    | none => none
  let groupErr := rowsErr "GROUP BY" filtered sel.groupBy
  let aggErr :=
    if grouped || aggregated then
      rowsErr "aggregate argument" filtered ((items ++ sel.having.toList).flatMap aggArgs)
    else none
  let havingErr :=
    if grouped || aggregated then
      match sel.having with
      | some c => groups.findSome? fun g => if badAgg g.1 g.2 c then some "HAVING" else subErr g.2 c
      | none => none
    else none
  -- window arguments, PARTITION BY and ORDER BY keys, on every row of the window's input
  let windowErr :=
    if !win then none
    else if grouped || aggregated then
      synth.findSome? fun row => (items.flatMap windowParts).findSome? fun x =>
        if (gev db row (m.prep x)).isNone then some "window" else none
    else rowsErr "window" filtered (items.flatMap windowParts)
  let itemErr :=
    if grouped || aggregated then
      ((List.range surv.length).zip (synth.zip surv)).findSome? fun (i, (row, (rs, s))) =>
        items.findSome? fun e =>
          if win && exprHasWindowFn e then
            if (evalExprWithWindowParam gev db row synth synth i (m.prep e)).isNone then
              some "SELECT" else none
          else if badAgg rs s e then some "SELECT" else subErr s e
    else if win then
      -- under LIMIT without ORDER BY or DISTINCT, Postgres evaluates the items only on the rows
      -- it returns, in the windows' order, which the plain path does not keep: not checked
      -- (window arguments and keys are, on every row, by `windowErr`)
      if sel.limitVal.isSome && sel.orderBy.isEmpty && !sel.distinct then none else
      ((List.range filtered.length).zip filtered).findSome? fun (i, r) =>
        items.findSome? fun e =>
          if (evalExprWithWindowParam ee db r filtered filtered i (m.prep e)).isNone then
            some "SELECT" else subErr r e
    else
      -- without ORDER BY or DISTINCT, Postgres stops evaluating the items once LIMIT is
      -- reached; the rows OFFSET skips are evaluated
      let shown := match sel.limitVal with
        | some n => if sel.orderBy.isEmpty && !sel.distinct then
            filtered.take (sel.offsetVal.getD 0 + n) else filtered
        | none => filtered
      rowsErr "SELECT" shown items
  let orderErr :=
    if sel.orderBy.isEmpty then none
    else if grouped then
      -- each surviving group's keys, against its projected row and sample row (#234, #429)
      let projected : Table :=
        if win then projectGroupsWithWindows db (evalSelectItemWithAggParam ee) ea sel.items surv
        else surv.map fun (rs, s) => sel.items.flatMap (evalSelectItemWithAggParam ee db rs s)
      ((List.range surv.length).zip ((synth.zip surv).zip projected)).findSome?
        fun (i, ((row, (rs, s)), p)) => sel.orderBy.findSome? fun o =>
          if exprHasWindowFn o.expr then
            if (evalExprWithWindowParam gev db row synth synth i (m.prep o.expr)).isNone then
              some "ORDER BY" else none
          else if badAgg rs (p ++ s) o.expr then some "ORDER BY" else none
    else if aggregated then none  -- one row: never compared (#448, residual)
    else
      ((List.range filtered.length).zip filtered).findSome? fun (i, r) =>
        let projected :=
          if win then projectWindowItems (evalExprWithWindowParam ee) db r filtered filtered i sel.items
          else sel.items.flatMap (evalSelectItem db r)
        sel.orderBy.findSome? fun o =>
          if exprHasWindowFn o.expr then
            if (evalExprWithWindowParam ee db r filtered filtered i (m.prep o.expr)).isNone then
              some "ORDER BY" else none
          else exprErr "ORDER BY" (projected ++ strip r) o.expr
  fromErr <|> whereErr <|> groupErr <|> aggErr <|> havingErr <|> windowErr <|> itemErr <|>
    orderErr
termination_by sel.size
decreasing_by all_goals (simp_wf; omega)

end

/-- The first error of an expression evaluated on row `r` outside any SELECT (INSERT values,
    UPDATE and DELETE clauses), with its strict subqueries. -/
def checkExprAt (m : ErrorMode) (db : Database) (what : String) (r : Row) (e : Expr) :
    Option String :=
  if (evalExprWithDb db r (m.prep e)).isNone then some what
  else (strictSubqueries e).findSome? (checkSubQuery m db r)

/-- The first error of a query, if any. A CTE body is checked against the database it is
    evaluated in; a recursive CTE's body against each working table of its iteration. -/
def checkQuery (m : ErrorMode) (db : Database) (q : Query) : Option String :=
  match q with
  | .simple sel => checkSelect m db [] sel
  | .compound l _ r => checkQuery m db l <|> checkQuery m db r
  | .withCTE [] query => checkQuery m db query
  | .withCTE (cte :: rest) query =>
    let withTable (w : Table) : Database := fun n => if n == cte.name then w else db n
    let step := fun workingTable => evalQuery (withTable workingTable) cte.query
    let cteResult :=
      if cte.isRecursive then fixedPointIterate step [] maxCTEIterations
      else evalQuery db cte.query
    let newDb : Database := fun name => if name == cte.name then cteResult else db name
    (if cte.isRecursive then
      (fixedPointInputs step [] maxCTEIterations).findSome? fun w =>
        checkQuery m (withTable w) cte.query
     else checkQuery m db cte.query) <|>
      checkQuery m newDb (.withCTE rest query)
  | .ordered query ob _ _ =>
    checkQuery m db query <|>
      if (evalQuery db query).any (fun r => ob.any fun o =>
          (evalExprWithDb db r (m.prep o.expr)).isNone) then some "ORDER BY"
      else none
termination_by sizeOf q
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (obtain ⟨_, cq, _⟩ := cte
       simp only [CTEDef.query, CTEDef.mk.sizeOf_spec]
       omega)

/-- The first error of an INSERT, UPDATE or DELETE. UPDATE's assignments are checked on the row
    before the update, as engines evaluate them. -/
def checkDml (m : ErrorMode) (db : Database) : Stmt → Option String
  | .query _ => none
  | .insert ins =>
    match ins.source with
    | .values rowExprs => rowExprs.findSome? fun es => es.findSome? (checkExprAt m db "VALUES" [])
    | .selectStmt sel => checkSelect m db [] sel
  | .update upd =>
    (db upd.table).findSome? fun row =>
      let passes := match upd.whereClause with
        | some c => evalExprWithDb db row c == some (Value.bool true)
        | none => true
      (match upd.whereClause with
        | some c => checkExprAt m db "WHERE" row c
        | none => none) <|>
      if passes then upd.assignments.findSome? fun a => checkExprAt m db "SET" row a.value
      else none
  | .delete del =>
    match del.whereClause with
    | some c => (db del.table).findSome? fun row => checkExprAt m db "WHERE" row c
    | none => none

-- ============================================================================
-- Evaluation in a dialect
-- ============================================================================

/-- Evaluate a query under an error mode: the quiet result, or the first error when the mode is
    strict and `checkQuery` finds one. -/
def evalQueryIn (m : ErrorMode) (db : Database) (q : Query) : Except String Table :=
  match m with
  | .quiet => .ok (evalQuery db q)
  | _ =>
    match checkQuery m db q with
    | some what => .error s!"evaluation error in {what}"
    | none => .ok (evalQuery db q)

/-- Evaluate a statement under an error mode. -/
def evalStmtIn (m : ErrorMode) (db : Database) : Stmt → Except String (Database × Option Table)
  | .query q => (evalQueryIn m db q).map fun t => (db, some t)
  | s =>
    match m with
    | .quiet => .ok (evalStmt db s)
    | _ =>
      match checkDml m db s with
      | some what => .error s!"evaluation error in {what}"
      | none => .ok (evalStmt db s)

/-- The quiet mode is the evaluator. -/
@[simp] theorem evalQueryIn_quiet (db : Database) (q : Query) :
    evalQueryIn .quiet db q = .ok (evalQuery db q) := rfl

/-- A query that succeeds under any mode returns the quiet result. -/
theorem evalQueryIn_ok {m : ErrorMode} {db : Database} {q : Query} {t : Table}
    (h : evalQueryIn m db q = .ok t) : t = evalQuery db q := by
  unfold evalQueryIn at h
  split at h
  · exact (Except.ok.inj h).symm
  · split at h
    · exact absurd h (by simp)
    · exact (Except.ok.inj h).symm

/-- A strict mode either fails or returns the quiet result. -/
theorem evalQueryIn_ok_or_error (m : ErrorMode) (db : Database) (q : Query) :
    evalQueryIn m db q = .ok (evalQuery db q) ∨ ∃ msg, evalQueryIn m db q = .error msg := by
  cases h : evalQueryIn m db q with
  | ok t => exact Or.inl (by rw [evalQueryIn_ok h])
  | error msg => exact Or.inr ⟨msg, rfl⟩

/-- Transfer: two queries the quiet evaluator gives equal results on that both succeed under a
    mode give the same rows. Every proved equivalence therefore holds in every dialect whenever
    neither side fails; whether one side fails while the other does not is not covered (an
    equivalence may move an error to a row that is filtered out). -/
theorem evalQueryIn_transfer {m : ErrorMode} {db : Database} {q₁ q₂ : Query} {t₁ t₂ : Table}
    (heq : evalQuery db q₁ = evalQuery db q₂)
    (h₁ : evalQueryIn m db q₁ = .ok t₁) (h₂ : evalQueryIn m db q₂ = .ok t₂) : t₁ = t₂ := by
  rw [evalQueryIn_ok h₁, evalQueryIn_ok h₂, heq]

end SqlEquiv
