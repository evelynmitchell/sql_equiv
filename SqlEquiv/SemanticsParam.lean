/-
  SQL Semantics: parameterized evaluators

  The aggregate- and window-aware expression evaluators and their helpers, parameterized by the
  row evaluator. They sit ahead of `SqlEquiv.SemanticsCore` so the SELECT pipeline can call the
  window evaluator with a callback of its own: a window over grouped rows evaluates each group's
  aggregates over that group (#429). Moved unchanged from `Semantics.lean`.
-/
import SqlEquiv.SemanticsBase
import SqlEquiv.AstSize

namespace SqlEquiv
-- ============================================================================
-- Aggregate Detection and Evaluation
-- ============================================================================

/-- Check if expression contains aggregate functions. Looks through operators,
    function arguments, CASE, IN lists, BETWEEN and the left side of IN (subquery),
    not into subqueries or window functions. Total and structurally recursive (#278 step 3; it was a
    `partial def`, opaque to proofs). -/
def hasAggregate : Expr → Bool
  | .agg _ _ _ => true
  | .countStar => true
  | .binOp _ l r => hasAggregate l || hasAggregate r
  | .unaryOp _ e => hasAggregate e
  | .func _ args => hasAggregateList args
  | .case branches else_ => hasAggregatePairs branches || hasAggregateOpt else_
  | .inList e _ vals => hasAggregate e || hasAggregateList vals
  | .between e lo hi => hasAggregate e || hasAggregate lo || hasAggregate hi
  | .inSubquery e _ _ => hasAggregate e
  | _ => false
where
  /-- `args.any hasAggregate` -/
  hasAggregateList : List Expr → Bool
    | [] => false
    | e :: es => hasAggregate e || hasAggregateList es
  /-- `branches.any fun (c, r) => hasAggregate c || hasAggregate r` -/
  hasAggregatePairs : List (Expr × Expr) → Bool
    | [] => false
    | (c, r) :: ps => hasAggregate c || hasAggregate r || hasAggregatePairs ps
  hasAggregateOpt : Option Expr → Bool
    | none => false
    | some e => hasAggregate e

/-- Check if any SELECT item contains aggregates -/
def selectHasAggregate (items : List SelectItem) : Bool :=
  items.any fun
    | .star _ => false
    | .exprItem e _ => hasAggregate e


-- ============================================================================
-- Window Function Detection (extracted from mutual block)
-- ============================================================================

/-- Check if expression contains window functions. Looks through operators,
    function arguments, CASE, IN (list), BETWEEN and the left side of IN (subquery),
    the nodes `evalExprWithWindowParam` evaluates through (#418, #422). Total and structurally
    recursive (#278 step 3; it was a `partial def`). -/
def exprHasWindowFn : Expr → Bool
  | .windowFn _ _ _ => true
  | .binOp _ l r => exprHasWindowFn l || exprHasWindowFn r
  | .unaryOp _ e => exprHasWindowFn e
  | .func _ args => exprHasWindowFnList args
  | .case branches else_ => exprHasWindowFnPairs branches || exprHasWindowFnOpt else_
  | .inList e _ vals => exprHasWindowFn e || exprHasWindowFnList vals
  | .between e lo hi => exprHasWindowFn e || exprHasWindowFn lo || exprHasWindowFn hi
  | .inSubquery e _ _ => exprHasWindowFn e
  | _ => false
where
  exprHasWindowFnList : List Expr → Bool
    | [] => false
    | e :: es => exprHasWindowFn e || exprHasWindowFnList es
  exprHasWindowFnPairs : List (Expr × Expr) → Bool
    | [] => false
    | (c, r) :: ps => exprHasWindowFn c || exprHasWindowFn r || exprHasWindowFnPairs ps
  exprHasWindowFnOpt : Option Expr → Bool
    | none => false
    | some e => exprHasWindowFn e

/-- Whether an expression has an aggregate call outside subqueries, inside window functions too
    (their argument, `PARTITION BY` and `ORDER BY`): `SUM(SUM(x)) OVER ()`. `hasAggregate` does not
    look inside window functions. Used to tell when a window query aggregates (#438). -/
def exprHasAggregateDeep : Expr → Bool
  | .agg _ _ _ => true
  | .countStar => true
  | .windowFn _ a spec =>
    (match a with
      | some x => exprHasAggregateDeep x
      | none => false) ||
    spec.partitionBy.attach.any (fun ⟨x, _⟩ => exprHasAggregateDeep x) ||
    spec.orderBy.attach.any (fun ⟨o, _⟩ => exprHasAggregateDeep o.expr)
  | .binOp _ l r => exprHasAggregateDeep l || exprHasAggregateDeep r
  | .unaryOp _ e => exprHasAggregateDeep e
  | .func _ args => args.attach.any (fun ⟨x, _⟩ => exprHasAggregateDeep x)
  | .case branches else_ =>
    branches.attach.any (fun ⟨p, _⟩ => exprHasAggregateDeep p.1 || exprHasAggregateDeep p.2) ||
    (match else_ with
      | some x => exprHasAggregateDeep x
      | none => false)
  | .inList e _ vals =>
    exprHasAggregateDeep e || vals.attach.any (fun ⟨x, _⟩ => exprHasAggregateDeep x)
  | .between e lo hi =>
    exprHasAggregateDeep e || exprHasAggregateDeep lo || exprHasAggregateDeep hi
  | .inSubquery e _ _ => exprHasAggregateDeep e
  | _ => false
termination_by e => e.size
decreasing_by
  all_goals simp only [Expr.size, Expr.sizeOpt]
  all_goals first
    | omega
    | (have := Expr.size_le_sizeList_of_mem ‹_›; omega)
    | (have := WindowSpec.partitionBy_size_lt ‹_›; omega)
    | (have := WindowSpec.orderBy_size_lt ‹_›; omega)
    | (have := Expr.size_le_sizePairs_of_mem (a := p.1) (b := p.2) ‹_›; omega)

/-- A window query aggregates without `GROUP BY` and without an aggregate in its items outside
    window functions when an aggregate occurs inside a window in the items or in `HAVING`
    (`SELECT SUM(SUM(x)) OVER () FROM t`): sqlite, DuckDB and Postgres then form one group, as
    for any aggregate query (#438). An aggregate only in `ORDER BY` is handled by
    `effectiveHaving` (#445).
    The SELECT pipeline conjoins this with "the items have a window function"
    (`implicitGroup`), so a query without one keeps its path. -/
def windowQueryAggregates (items : List SelectItem) (having : Option Expr) : Bool :=
  items.any (fun | .exprItem e _ => exprHasAggregateDeep e | .star _ => false) ||
  having.any exprHasAggregateDeep

/-- A query whose only aggregate is in `ORDER BY` (#445, registry row 22): no `GROUP BY`, no
    `HAVING`, and no aggregate in the items (one inside a window counts, as for #438), but one in an
    `ORDER BY` key (`SELECT 1 FROM t ORDER BY COUNT(*)`). DuckDB and Postgres form one group, as for
    any aggregate query; the sqlite dialect rejects it at parse time, as sqlite does. -/
def orderByOnlyAggregates (groupBy : List Expr) (items : List SelectItem) (having : Option Expr)
    (orderBy : List OrderByItem) : Bool :=
  groupBy.isEmpty && having.isNone &&
    !items.any (fun | .exprItem e _ => exprHasAggregateDeep e | .star _ => false) &&
    orderBy.any (fun o => exprHasAggregateDeep o.expr)

/-- The `HAVING` the SELECT pipeline evaluates: `HAVING TRUE` for a query whose only aggregate is
    in `ORDER BY` (`orderByOnlyAggregates`), which makes it one group (`implicitGroup`) and keeps
    the group; otherwise the query's own. -/
def effectiveHaving (groupBy : List Expr) (items : List SelectItem) (having : Option Expr)
    (orderBy : List OrderByItem) : Option Expr :=
  if orderByOnlyAggregates groupBy items having orderBy then some (.lit (.bool true)) else having

@[simp] theorem effectiveHaving_of_not {groupBy : List Expr} {items : List SelectItem}
    {having : Option Expr} {orderBy : List OrderByItem}
    (h : orderByOnlyAggregates groupBy items having orderBy = false) :
    effectiveHaving groupBy items having orderBy = having := by
  simp [effectiveHaving, h]

/-- The evaluated `HAVING` is the query's own, or `HAVING TRUE` when the only aggregate is in
    `ORDER BY`. -/
theorem effectiveHaving_cases (groupBy : List Expr) (items : List SelectItem)
    (having : Option Expr) (orderBy : List OrderByItem) :
    effectiveHaving groupBy items having orderBy = having ∨
    (orderByOnlyAggregates groupBy items having orderBy = true ∧
      effectiveHaving groupBy items having orderBy = some (.lit (.bool true))) := by
  unfold effectiveHaving
  split <;> simp_all

/-- A query whose only aggregate is in `ORDER BY` has an `ORDER BY` key. -/
theorem orderByOnlyAggregates_mem {groupBy : List Expr} {items : List SelectItem}
    {having : Option Expr} {orderBy : List OrderByItem}
    (h : orderByOnlyAggregates groupBy items having orderBy = true) : ∃ o, o ∈ orderBy := by
  simp only [orderByOnlyAggregates, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨_, o, ho, _⟩ := h
  exact ⟨o, ho⟩

/-- Without `ORDER BY` the query's own `HAVING` is the one evaluated. -/
@[simp] theorem effectiveHaving_nil {groupBy : List Expr} {items : List SelectItem}
    {having : Option Expr} : effectiveHaving groupBy items having [] = having := by
  simp [effectiveHaving, orderByOnlyAggregates]

/-- With a `HAVING` the query's own `HAVING` is the one evaluated. -/
@[simp] theorem effectiveHaving_some {groupBy : List Expr} {items : List SelectItem}
    {h : Expr} {orderBy : List OrderByItem} :
    effectiveHaving groupBy items (some h) orderBy = some h := by
  simp [effectiveHaving, orderByOnlyAggregates]

/-- Check if SELECT items contain window functions -/
def selectHasWindowFn (items : List SelectItem) : Bool :=
  items.any fun
    | .exprItem e _ => exprHasWindowFn e
    | _ => false

-- ============================================================================
-- Parameterized helpers (defined before mutual block, take exprEval callback)
-- ============================================================================

/-- Parameterized SELECT item evaluator -/
def evalSelectItemParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (row : Row) (item : SelectItem) : List (String × Value) :=
  match item with
  | .star none => row
  | .star (some t) => row.filter fun (k, _) => k.startsWith s!"{t}."
  | .exprItem e alias =>
    match exprEval db row e with
    | some v => [(alias.getD (exprToName e), v)]
    | none => [(alias.getD (exprToName e), .null none)]

/-- Parameterized aggregate over table -/
def evalAggOverTableParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (fn : AggFunc) (argExpr : Option Expr) (distinct : Bool) (rows : Table) : Option Value :=
  let values : List Value := match argExpr with
    | none => []
    | some e => rows.filterMap fun row => exprEval db row e
  let distinctValues := if distinct then dedupByKey Value.setKey values else values
  match fn with
  -- COUNT(col) skips NULLs per the SQL standard (COUNT(*) is Expr.countStar,
  -- which doesn't go through here); the window-fn COUNT already does this.
  | .count => some (.int (distinctValues.filter (fun v => !v.isNull)).length)
  | .sum b => sumAgg b distinctValues
  | .avg b => avgAgg b distinctValues
  | .min m => minMaxAgg m false distinctValues
  | .max m => minMaxAgg m true distinctValues

/-- CASE over evaluated branches: the result of the first branch whose condition is `TRUE`,
    else the ELSE value. -/
def evalCasePicked : List (Option Value × Option Value) → Option Value → Option Value
  | [], elseVal => elseVal
  | (c, r) :: rest, elseVal =>
    match c with
    | some (.bool true) => r
    | _ => evalCasePicked rest elseVal

/-- Parameterized expression evaluator with aggregate support -/
def evalExprWithAggParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (rows : Table) (row : Row) : Expr → Option Value
  | .agg fn arg distinct => evalAggOverTableParam exprEval db fn arg distinct rows
  | .countStar => some (.int rows.length)
  -- Operators combine their operands' results as `evalExprCore` does, an error included:
  -- `FALSE AND <error>` is FALSE and `<error> IS NULL` is TRUE on every path (#423).
  | .binOp op l r =>
    evalBinOp op (evalExprWithAggParam exprEval db rows row l)
      (evalExprWithAggParam exprEval db rows row r)
  | .unaryOp op e => evalUnaryOp op (evalExprWithAggParam exprEval db rows row e)
  -- An aggregate under a function call, CASE, IN (list) or BETWEEN is evaluated over the
  -- group, then combined as `evalExprCore` combines values. Without an aggregate inside,
  -- these go to the row evaluator unchanged.
  | .func name args =>
    if hasAggregate (.func name args) then
      evalFunc name (args.map fun a => evalExprWithAggParam exprEval db rows row a)
    else exprEval db row (.func name args)
  | .case branches else_ =>
    if hasAggregate (.case branches else_) then
      evalCasePicked
        (branches.map fun pair =>
          (evalExprWithAggParam exprEval db rows row pair.1,
            evalExprWithAggParam exprEval db rows row pair.2))
        (match else_ with
          | some e => evalExprWithAggParam exprEval db rows row e
          | none => some (.null none))
    else exprEval db row (.case branches else_)
  | .inList e neg vals =>
    if hasAggregate (.inList e neg vals) then
      let ev := evalExprWithAggParam exprEval db rows row e
      let result := vals.foldl (fun acc vi =>
        evalBinOp .or acc (evalBinOp .eq ev (evalExprWithAggParam exprEval db rows row vi))
      ) (some (.bool false))
      if neg then evalUnaryOp .not result else result
    else exprEval db row (.inList e neg vals)
  | .between e lo hi =>
    if hasAggregate (.between e lo hi) then
      let ev := evalExprWithAggParam exprEval db rows row e
      let evlo := evalExprWithAggParam exprEval db rows row lo
      let evhi := evalExprWithAggParam exprEval db rows row hi
      evalBinOp .and (evalBinOp .ge ev evlo) (evalBinOp .le ev evhi)
    else exprEval db row (.between e lo hi)
  -- IN (subquery) with an aggregate on the left (#422): the left side is evaluated over the
  -- group and its value handed to the row evaluator as a literal, which runs the subquery.
  -- The substituted expression is no larger than the original.
  | .inSubquery e neg sq =>
    if hasAggregate (.inSubquery e neg sq) then
      match evalExprWithAggParam exprEval db rows row e with
      | some v => exprEval db row (.inSubquery (.lit v) neg sq)
      | none => none
    else exprEval db row (.inSubquery e neg sq)
  | e => exprEval db row e
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_›; omega)
    | (have h := List.sizeOf_lt_of_mem ‹_›
       have : sizeOf pair = 1 + sizeOf pair.fst + sizeOf pair.snd := by
         obtain ⟨a, b⟩ := pair; simp [Prod.mk.sizeOf_spec]
       omega)

/-- Parameterized SELECT item evaluator with aggregate support -/
def evalSelectItemWithAggParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (rows : Table) (row : Row) (item : SelectItem) : List (String × Value) :=
  match item with
  | .star none => row
  | .star (some t) => row.filter fun (k, _) => k.startsWith s!"{t}."
  | .exprItem e alias =>
    match evalExprWithAggParam exprEval db rows row e with
    | some v => [(alias.getD (exprToName e), v)]
    | none => [(alias.getD (exprToName e), .null none)]

/-- Whether an ORDER BY key value sorts as NULL: SQL NULL, or an evaluation
    error (`none`), which is positioned like NULL so the ordering stays
    consistent. -/
def orderKeyIsNull : Option Value → Bool
  | none => true
  | some (.null _) => true
  | some _ => false

/-- Compare one ORDER BY key of two rows. `some true`: the first row sorts
    first; `some false`: the second does; `none`: tie, so the next key decides.
    NULLs sort together, placed by the item's `NullsOrder` (`NULLS FIRST` /
    `NULLS LAST`, absolute regardless of direction); non-NULL values compare by
    `Value.compare` in the item's direction. -/
def orderKeyCmp (item : OrderByItem) (v1 v2 : Option Value) : Option Bool :=
  match orderKeyIsNull v1, orderKeyIsNull v2 with
  | true, true => none
  | true, false => some (item.nulls == .first)
  | false, true => some (item.nulls == .last)
  | false, false =>
    match v1, v2 with
    | some a, some b =>
      match a.compare b with
      | some .lt => some (item.dir == .asc)
      | some .gt => some (item.dir == .desc)
      | _ => none
    | _, _ => none

/-- Parameterized ORDER BY comparator -/
def compareByOrderItemsParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (r1 r2 : Row) : List OrderByItem → Bool
  | [] => true
  | item :: rest =>
    match orderKeyCmp item (exprEval db r1 item.expr) (exprEval db r2 item.expr) with
    | some b => b
    | none => compareByOrderItemsParam exprEval db r1 r2 rest

/-- Parameterized GROUP BY key -/
def evalGroupKeyParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (row : Row) (groupExprs : List Expr) : List (Option Value) :=
  groupExprs.map (fun e => (exprEval db row e).map Value.setKey)

/-- Parameterized group rows by key -/
def groupRowsByKeyParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (rows : Table) (groupExprs : List Expr) : List (List (Option Value) × Table) :=
  let addToGroups (groups : List (List (Option Value) × Table)) (row : Row) :=
    let key := evalGroupKeyParam exprEval db row groupExprs
    match groups.find? (fun (k, _) => k == key) with
    | some _ => groups.map fun (k, rs) => if k == key then (k, rs ++ [row]) else (k, rs)
    | none => groups ++ [(key, [row])]
  rows.foldl addToGroups []

/-- Parameterized sort partition -/
def sortPartitionParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (rows : Table) (orderBy : List OrderByItem) : Table :=
  if orderBy.isEmpty then rows
  else rows.mergeSort fun r1 r2 => compareByOrderItemsParam exprEval db r1 r2 orderBy

/-- Compute ROW_NUMBER for each row in a sorted partition -/
def computeRowNumbers (rows : Table) : List (Row × Nat) :=
  (List.range rows.length).zip rows |>.map fun (i, row) => (row, i + 1)

/-- Parameterized RANK computation -/
def computeRanksParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (rows : Table) (orderBy : List OrderByItem) : List (Row × Nat) :=
  let rec go (remaining : List Row) (currentRank : Nat) (nextRank : Nat)
      (prevKey : Option (List (Option Value))) : List (Row × Nat) :=
    match remaining with
    | [] => []
    | row :: rest =>
      let key := orderBy.map fun item => exprEval db row item.expr
      let (rank, newNextRank) := match prevKey with
        | none => (1, 2)
        | some pk => if pk == key then (currentRank, nextRank + 1) else (nextRank, nextRank + 1)
      (row, rank) :: go rest rank newNextRank (some key)
  go rows 1 2 none

/-- Parameterized DENSE_RANK computation -/
def computeDenseRanksParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (rows : Table) (orderBy : List OrderByItem) : List (Row × Nat) :=
  let rec go (remaining : List Row) (currentRank : Nat)
      (prevKey : Option (List (Option Value))) : List (Row × Nat) :=
    match remaining with
    | [] => []
    | row :: rest =>
      let key := orderBy.map fun item => exprEval db row item.expr
      let rank := match prevKey with
        | none => 1
        | some pk => if pk == key then currentRank else currentRank + 1
      (row, rank) :: go rest rank (some key)
  go rows 1 none

/-- Default window frame for aggregate window functions (#214): the whole
    partition when the window has no ORDER BY; otherwise the SQL-standard
    default `RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW` — the rows of
    the sorted partition up to the current row plus its ORDER BY peers
    (rows with an equal sort key). Matches DuckDB/SQLite/PostgreSQL. -/
def windowFrameRowsParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (orderBy : List OrderByItem)
    (sortedPartition : Table) (row : Row) (rowIndex : Nat) : Table :=
  if orderBy.isEmpty then sortedPartition
  else
    let key := fun (r : Row) => orderBy.map fun item => exprEval db r item.expr
    let curKey := key row
    sortedPartition.take (rowIndex + 1) ++
      (sortedPartition.drop (rowIndex + 1)).takeWhile (fun r => key r == curKey)

/-- Parameterized window function evaluator. `sortedPartition` must be the
    row's PARTITION BY group sorted by `orderBy` (the window's ORDER BY), and
    `rowIndex` the row's index within it — evalExprWithWindowParam computes
    both from the WindowSpec. -/
def evalWindowFnParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (fn : WindowFunc) (arg : Option Expr)
    (orderBy : List OrderByItem)
    (sortedPartition : Table) (row : Row) (rowIndex : Nat) : Option Value :=
  let frame := windowFrameRowsParam exprEval db orderBy sortedPartition row rowIndex
  match fn with
  | .rowNumber => some (.int (Int.ofNat (rowIndex + 1)))
  | .rank =>
    let ranks := computeRanksParam exprEval db sortedPartition orderBy
    match ranks.find? (fun (r, _) => r == row) with
    | some (_, rank) => some (.int (Int.ofNat rank))
    | none => some (.int (Int.ofNat (rowIndex + 1)))
  | .denseRank =>
    let ranks := computeDenseRanksParam exprEval db sortedPartition orderBy
    match ranks.find? (fun (r, _) => r == row) with
    | some (_, rank) => some (.int (Int.ofNat rank))
    | none => some (.int (Int.ofNat (rowIndex + 1)))
  | .sum b =>
    match arg with
    | none => none
    | some e => sumAgg b (frame.filterMap fun r => exprEval db r e)
  | .avg b =>
    match arg with
    | none => none
    | some e => avgAgg b (frame.filterMap fun r => exprEval db r e)
  | .min m =>
    match arg with
    | none => none
    | some e =>
      let vals := frame.filterMap fun r => exprEval db r e
      minMaxAgg m false vals
  | .max m =>
    match arg with
    | none => none
    | some e =>
      let vals := frame.filterMap fun r => exprEval db r e
      minMaxAgg m true vals
  | .count =>
    match arg with
    | none => some (.int (Int.ofNat frame.length))
    | some e =>
      let nonNullCount := frame.filter fun r =>
        match exprEval db r e with
        | some v => !isNullValue v
        | none => false
      some (.int (Int.ofNat nonNullCount.length))

/-- Parameterized expression evaluator with window function support -/
def evalExprWithWindowParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (row : Row) (partition : Table)
    (sortedPartition : Table) (rowIndex : Nat) : Expr → Option Value
  | .windowFn fn arg spec =>
    -- The caller (evalSelectCore's window branch) passes the full
    -- HAVING-filtered row set as both `partition` and `sortedPartition`,
    -- with `rowIndex` relative to it. The WindowSpec is applied HERE (#214):
    -- PARTITION BY restricts to the current row's group, ORDER BY sorts it,
    -- and the row's index is recomputed within the sorted partition.
    let part :=
      if spec.partitionBy.isEmpty then partition
      else
        let key := fun (r : Row) => spec.partitionBy.map (exprEval db r)
        let curKey := key row
        partition.filter fun r => key r == curKey
    let winSorted := if spec.orderBy.isEmpty then part
                     else sortPartitionParam exprEval db part spec.orderBy
    let idx := (winSorted.findIdx? (fun r => r == row)).getD rowIndex
    evalWindowFnParam exprEval db fn arg spec.orderBy winSorted row idx
  -- Operators combine their operands' results as `evalExprCore` does, an error included (#423).
  | .binOp op l r =>
    evalBinOp op (evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex l)
      (evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex r)
  | .unaryOp op e =>
    evalUnaryOp op (evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex e)
  -- A window function under a function call, CASE, IN (list) or BETWEEN is evaluated for
  -- the current row, then combined as `evalExprCore` combines values (#418). Without a
  -- window function inside, these go to the row evaluator unchanged.
  | .func name args =>
    if exprHasWindowFn (.func name args) then
      evalFunc name (args.map fun a =>
        evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex a)
    else exprEval db row (.func name args)
  | .case branches else_ =>
    if exprHasWindowFn (.case branches else_) then
      evalCasePicked
        (branches.map fun pair =>
          (evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex pair.1,
            evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex pair.2))
        (match else_ with
          | some e => evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex e
          | none => some (.null none))
    else exprEval db row (.case branches else_)
  | .inList e neg vals =>
    if exprHasWindowFn (.inList e neg vals) then
      let ev := evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex e
      let result := vals.foldl (fun acc vi =>
        evalBinOp .or acc (evalBinOp .eq ev
          (evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex vi))
      ) (some (.bool false))
      if neg then evalUnaryOp .not result else result
    else exprEval db row (.inList e neg vals)
  | .between e lo hi =>
    if exprHasWindowFn (.between e lo hi) then
      let ev := evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex e
      let evlo := evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex lo
      let evhi := evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex hi
      evalBinOp .and (evalBinOp .ge ev evlo) (evalBinOp .le ev evhi)
    else exprEval db row (.between e lo hi)
  -- IN (subquery) with a window function on the left (#422): as for aggregates, the left
  -- side's value goes to the row evaluator as a literal.
  | .inSubquery e neg sq =>
    if exprHasWindowFn (.inSubquery e neg sq) then
      match evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex e with
      | some v => exprEval db row (.inSubquery (.lit v) neg sq)
      | none => none
    else exprEval db row (.inSubquery e neg sq)
  | e => exprEval db row e
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_›; omega)
    | (have h := List.sizeOf_lt_of_mem ‹_›
       have : sizeOf pair = 1 + sizeOf pair.fst + sizeOf pair.snd := by
         obtain ⟨a, b⟩ := pair; simp [Prod.mk.sizeOf_spec]
       omega)

end SqlEquiv
