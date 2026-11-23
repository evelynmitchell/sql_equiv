/-
  Strict evaluation per dialect (#270, registry row 23)

  The evaluator is quiet: an evaluation error (`none`) drops the row in `WHERE` and shows as NULL
  in the select list, and every theorem is stated over that evaluator. Postgres and DuckDB abort
  the statement instead. This module layers the dialect's choice on top, without touching the
  evaluator or any theorem:

  - `checkQuery` walks a query and reports the first clause expression that yields an error on a
    row the quiet evaluator evaluates it on: `WHERE`, join `ON`, `GROUP BY` keys, aggregate
    arguments, `HAVING`, select items and `ORDER BY` keys, recursing into derived tables, set
    operation branches and CTE bodies.
  - `evalQueryIn mode db q` is the quiet result, or the error when the mode is strict and the
    check finds one. `evalQueryIn_transfer`: quiet-equivalent queries that both succeed give
    the same rows, so every proved equivalence carries over.

  The check is a runtime approximation of the engines, with documented gaps (#448): errors that
  engines raise at bind time (a type mismatch over an empty table), errors inside expression
  subqueries (`IN (SELECT …)`, `EXISTS`, scalar subqueries), select items and ORDER BY keys of
  window queries, ORDER BY keys of grouped queries, and INSERT/UPDATE/DELETE.
-/
import SqlEquiv.Semantics

namespace SqlEquiv

-- ============================================================================
-- DuckDB: division and modulo by zero are not errors
-- ============================================================================

/-- `a / b` and `a % b` become `CASE WHEN b = 0 THEN NULL ELSE … END`, so a division by zero
    yields NULL instead of an error when the expression is checked (`ErrorMode.strictDivZeroNull`).
    A divisor that is itself an error, or not a number, still yields an error. Does not enter
    subqueries or window functions. Used only by the checker, never for results. -/
def nullOnDivZero : Expr → Expr
  | .binOp op l r =>
    let l' := nullOnDivZero l
    let r' := nullOnDivZero r
    if op == .div || op == .mod then
      .case [(.binOp .eq r' (.lit (.int 0)), .lit (.null none))] (some (.binOp op l' r'))
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

/-- The first error of one SELECT's own clauses, derived tables excluded (`checkSelect` adds
    them). It evaluates as `evalSelectWithContext db [] sel` does, on the same rows. -/
def checkSelectClauses (m : ErrorMode) (db : Database) (sel : SelectStmt) : Option String :=
  let ee : Database → Row → Expr → Option Value := fun db' r e => evalExprWithDb db' r e
  let bad (r : Row) (e : Expr) : Bool := (evalExprWithDb db r (m.prep e)).isNone
  let badAgg (rows : Table) (sample : Row) (e : Expr) : Bool :=
    (evalExprWithAggParam ee db rows sample (m.prep e)).isNone
  let firstBad (what : String) (rows : Table) (es : List Expr) : Option String :=
    if rows.any (fun r => es.any (bad r)) then some what else none
  let base : Table := match sel.fromClause with
    | some f => evalFrom db f
    | none => [[]]
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
    | some c => evalExprWithAggParam ee db g.1 g.2 c == some (Value.bool true)
  let whereErr := match sel.whereClause with
    | some c => firstBad "WHERE" base [c]
    | none => none
  let groupErr := firstBad "GROUP BY" filtered sel.groupBy
  let aggErr :=
    if grouped || aggregated then
      firstBad "aggregate argument" filtered
        ((items ++ sel.having.toList).flatMap aggArgs)
    else none
  let havingErr :=
    if grouped || aggregated then
      match sel.having with
      | some c => if groups.any (fun g => badAgg g.1 g.2 c) then some "HAVING" else none
      | none => none
    else none
  let itemErr :=
    if win then none  -- window queries: a documented gap (#448)
    else if grouped || aggregated then
      if (groups.filter passes).any (fun g => items.any (badAgg g.1 g.2)) then some "SELECT"
      else none
    else
      -- without ORDER BY or DISTINCT, Postgres stops evaluating the items once LIMIT is
      -- reached; the rows OFFSET skips are evaluated
      let shown := match sel.limitVal with
        | some n => if sel.orderBy.isEmpty && !sel.distinct then
            filtered.take (sel.offsetVal.getD 0 + n) else filtered
        | none => filtered
      firstBad "SELECT" shown items
  let orderErr :=
    if win || grouped || aggregated || orderByHasWindow sel.orderBy then none  -- gaps (#448)
    else if filtered.any (fun r =>
        let projected := sel.items.flatMap (evalSelectItem db r)
        sel.orderBy.any fun o => bad (projected ++ r) o.expr) then some "ORDER BY"
    else none
  whereErr <|> groupErr <|> aggErr <|> havingErr <|> itemErr <|> orderErr

mutual

/-- The first error of a subquery body: each SELECT, and both branches of a set operation. -/
def checkSubQuery (m : ErrorMode) (db : Database) (sq : SubQuery) : Option String :=
  match sq with
  | .simple sel => checkSelect m db sel
  | .compound l _ r => checkSubQuery m db l <|> checkSubQuery m db r
termination_by sq.size
decreasing_by all_goals (simp_wf; simp only [SubQuery.size]; omega)

/-- The first error of a FROM clause: derived tables, and join `ON` conditions on every pair of
    rows the join evaluates them on. -/
def checkFrom (m : ErrorMode) (db : Database) (fc : FromClause) : Option String :=
  match fc with
  | .table _ => none
  | .subquery sq _ => checkSubQuery m db sq
  | .join l _ r on_ =>
    checkFrom m db l <|> checkFrom m db r <|>
      match on_ with
      | none => none
      | some c =>
        let rs := evalFrom db r
        if (evalFrom db l).any (fun lr =>
            rs.any fun rr => (evalExprWithDb db (lr ++ rr) (m.prep c)).isNone) then some "ON"
        else none
termination_by fc.size
decreasing_by all_goals (simp_wf; simp only [FromClause.size]; omega)

/-- The first error of a SELECT: its FROM clause, then its own clauses. -/
def checkSelect (m : ErrorMode) (db : Database) (sel : SelectStmt) : Option String :=
  (match sel.fromClause with
    | some f => if _h : f.size < sel.size then checkFrom m db f else none
    | none => none) <|>
  checkSelectClauses m db sel
termination_by sel.size

end

/-- The first error of a query, if any. A CTE body is checked against the database it is
    evaluated in; a recursive CTE's body against its final result (an approximation of the
    iterations). -/
def checkQuery (m : ErrorMode) (db : Database) (q : Query) : Option String :=
  match q with
  | .simple sel => checkSelect m db sel
  | .compound l _ r => checkQuery m db l <|> checkQuery m db r
  | .withCTE [] query => checkQuery m db query
  | .withCTE (cte :: rest) query =>
    let cteResult :=
      if cte.isRecursive then
        fixedPointIterate (fun workingTable =>
          evalQuery (fun n => if n == cte.name then workingTable else db n) cte.query)
          [] maxCTEIterations
      else evalQuery db cte.query
    let newDb : Database := fun name => if name == cte.name then cteResult else db name
    checkQuery m (if cte.isRecursive then newDb else db) cte.query <|>
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

/-- Evaluate a statement under an error mode. INSERT, UPDATE and DELETE are evaluated quietly
    (a documented gap, #448). -/
def evalStmtIn (m : ErrorMode) (db : Database) : Stmt → Except String (Database × Option Table)
  | .query q => (evalQueryIn m db q).map fun t => (db, some t)
  | s => .ok (evalStmt db s)

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
