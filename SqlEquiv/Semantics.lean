/-
  SQL Semantics: Evaluation Model

  Defines what SQL statements *mean* using a relational algebra model.
  This enables formal equivalence proofs.
-/
import SqlEquiv.SemanticsBase
import SqlEquiv.SemanticsCore
import SqlEquiv.AstSize

namespace SqlEquiv

-- ============================================================================
-- Aggregate Detection and Evaluation
-- ============================================================================

/-- Check if expression contains aggregate functions. Looks through operators,
    function arguments, CASE, IN lists and BETWEEN, not into subqueries or
    window functions. Total and structurally recursive (#278 step 3; it was a
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
    function arguments and CASE only (as before). Total and structurally
    recursive (#278 step 3; it was a `partial def`). -/
def exprHasWindowFn : Expr → Bool
  | .windowFn _ _ _ => true
  | .binOp _ l r => exprHasWindowFn l || exprHasWindowFn r
  | .unaryOp _ e => exprHasWindowFn e
  | .func _ args => exprHasWindowFnList args
  | .case branches else_ => exprHasWindowFnPairs branches || exprHasWindowFnOpt else_
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
  | .binOp op l r =>
    match evalExprWithAggParam exprEval db rows row l, evalExprWithAggParam exprEval db rows row r with
    | some a, some b => evalBinOp op a b
    | _, _ => none
  | .unaryOp op e =>
    match evalExprWithAggParam exprEval db rows row e with
    | some v => evalUnaryOp op v
    | none => none
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
  | .binOp op l r =>
    let lv := evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex l
    let rv := evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex r
    match lv, rv with
    | some a, some b => evalBinOp op a b
    | _, _ => none
  | .unaryOp op e =>
    match evalExprWithWindowParam exprEval db row partition sortedPartition rowIndex e with
    | some v => evalUnaryOp op v
    | none => none
  | e => exprEval db row e
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; omega

-- ============================================================================
-- Mutually Recursive Evaluation Functions (WFR - 3 function core)
-- ============================================================================

mutual

/-- Evaluate expression against a row (with database for subqueries).
    Termination (#212): each recursive callback is guarded by a size check, so
    the well-founded recursion checker sees the decrease. The `*Core`
    evaluators only call a callback on parts of their input, which always
    pass the guard; expressions that the SELECT pipeline builds itself (e.g.
    the #234 grouped sort keys) contain no subqueries, and for those the
    fallback (subqueries disabled) gives the same result. -/
def evalExprWithDb (db : Database) (row : Row) (e : Expr) : Option Value :=
  evalExprCore db row (fun db' row' sq =>
    if _h : sq.size < e.size then evalSubQueryWithContext db' row' sq else []) e
termination_by e.size
decreasing_by all_goals (simp_wf; first | omega | (simp only [SubQuery.size]; omega))

/-- Evaluate FROM clause to get source rows -/
def evalFrom (db : Database) (fc : FromClause) : Table :=
  evalFromCore db
    (fun db' r expr =>
      if _h : expr.size < fc.size then evalExprWithDb db' r expr
      else evalExprCore db' r (fun _ _ _ => []) expr)
    (fun db' sq =>
      if _h : sq.size < fc.size then evalSubQueryWithContext db' [] sq else []) fc
termination_by fc.size
decreasing_by all_goals (simp_wf; first | omega | (simp only [SubQuery.size]; omega))

/-- Evaluate a subquery body (#218): a SELECT or a set operation over
    subqueries. Set-op semantics shared with top-level Query via applySetOp. -/
def evalSubQueryWithContext (db : Database) (outerRow : Row) (sq : SubQuery) : Table :=
  match sq with
  | .simple sel => evalSelectWithContext db outerRow sel
  | .compound l op r =>
    applySetOp op (SubQuery.outputNames? l) (evalSubQueryWithContext db outerRow l)
                  (evalSubQueryWithContext db outerRow r)
termination_by sq.size
decreasing_by all_goals (simp_wf; first | omega | (simp only [SubQuery.size]; omega))

/-- Evaluate SELECT statement with outer row context (for correlated subqueries) -/
def evalSelectWithContext (db : Database) (outerRow : Row) (sel : SelectStmt) : Table :=
  let ee := fun db' r e =>
    if _h : e.size < sel.size then evalExprWithDb db' r e
    else evalExprCore db' r (fun _ _ _ => []) e
  evalSelectCore db outerRow
    (fun db' fc => if _h : fc.size < sel.size then evalFrom db' fc else [])
    ee
    (evalSelectItemParam ee)
    (evalSelectItemWithAggParam ee)
    (evalExprWithAggParam ee)
    (compareByOrderItemsParam ee)
    (evalExprWithWindowParam ee)
    selectHasWindowFn
    selectHasAggregate
    sel
termination_by sel.size
decreasing_by all_goals (simp_wf; first | omega | (simp only [SubQuery.size]; omega))

end

-- ============================================================================
-- Standalone Evaluation Functions (defined after the mutual block)
-- ============================================================================

/-- Evaluate full SELECT statement -/
def evalSelect (db : Database) (sel : SelectStmt) : Table :=
  evalSelectWithContext db [] sel

/-- Helper for CASE expression evaluation -/
def evalCase (db : Database) (row : Row) (branches : List (Expr × Expr)) (else_ : Option Expr) : Option Value :=
  let elseVal := match else_ with
    | some e => evalExprWithDb db row e
    | none => some (.null none)
  evalCaseHelper (evalExprWithDb db row) elseVal branches

/-- Evaluate SELECT item to extract columns from row -/
def evalSelectItem (db : Database) (row : Row) (item : SelectItem) : List (String × Value) :=
  match item with
  | .star none => row
  | .star (some t) => row.filter fun (k, _) => k.startsWith s!"{t}."
  | .exprItem e alias =>
    match evalExprWithDb db row e with
    | some v => [(alias.getD (exprToName e), v)]
    | none => [(alias.getD (exprToName e), .null none)]

-- (The legacy non-`Param` aggregate/ORDER BY/window evaluators that lived here
-- — evalAggOverTable, evalExprWithAgg, evalSelectItemWithAgg,
-- compareByOrderItems, evalGroupKey, groupRowsByKey, partitionRows,
-- sortPartition, computeRanks, computeDenseRanks, evalWindowFn,
-- evalExprWithWindow — were unreferenced and were removed in #278 step 3.
-- The live versions are the `*Param` functions above.)

/-- Simple evalExpr without database context (for backwards compatibility) -/
def evalExpr (row : Row) : Expr → Option Value :=
  evalExprWithDb (fun _ => []) row

-- ============================================================================
-- Bridge axioms: connect partial defs to non-partial core functions
-- ============================================================================

/-- Bridge: evalSubQueryWithContext unfolds on .simple to evalSelectWithContext (#218) -/
theorem evalSubQuery_simple (db : Database) (r : Row) (sel : SelectStmt) :
    evalSubQueryWithContext db r (.simple sel) = evalSelectWithContext db r sel := by
  rw [evalSubQueryWithContext]

/-- Bridge: evalSubQueryWithContext unfolds on .compound to applySetOp (#218) -/
theorem evalSubQuery_compound (db : Database) (r : Row) (l : SubQuery) (op : SetOp) (rq : SubQuery) :
    evalSubQueryWithContext db r (.compound l op rq) =
    applySetOp op (SubQuery.outputNames? l) (evalSubQueryWithContext db r l)
      (evalSubQueryWithContext db r rq) := by
  rw [evalSubQueryWithContext]

/-- Bridge: evalExprWithDb equals evalExprCore instantiated with evalSubQueryWithContext -/
theorem evalExprWithDb_eq_evalExprCore (db : Database) (row : Row) (e : Expr) :
  evalExprWithDb db row e = evalExprCore db row (fun db' row' sq => evalSubQueryWithContext db' row' sq) e := by
  -- the size guard holds for every subquery evalExprCore can reach (#212)
  rw [evalExprWithDb]
  exact evalExprCore_congr_subq db row e.size e (Nat.le_refl _) _ _
    (fun sq hsq => by simp only [dif_pos hsq])

/-- Bridge: evalCase equals evalCaseHelper instantiated with evalExprCore/evalSubQueryWithContext -/
theorem evalCase_eq_evalCaseHelper (db : Database) (row : Row) (branches : List (Expr × Expr)) (else_ : Option Expr) :
  evalCase db row branches else_ =
    let sqe := fun db' row' sq => evalSubQueryWithContext db' row' sq
    let elseVal := match else_ with
      | some e => evalExprCore db row sqe e
      | none => some (.null none)
    evalCaseHelper (evalExprCore db row sqe) elseVal branches := by
  have h : evalExprWithDb db row = evalExprCore db row (fun db' row' sq => evalSubQueryWithContext db' row' sq) :=
    funext fun e => evalExprWithDb_eq_evalExprCore db row e
  simp only [evalCase, h]

/-- Bridge: evalFrom equals evalFromCore instantiated with evalExprWithDb and evalSubQueryWithContext -/
theorem evalFrom_eq_evalFromCore (db : Database) (fc : FromClause) :
  evalFrom db fc = evalFromCore db evalExprWithDb (fun db' sq => evalSubQueryWithContext db' [] sq) fc := by
  -- the size guards hold for every part of fc evalFromCore can reach (#212)
  rw [evalFrom]
  exact evalFromCore_congr db fc.size fc (Nat.le_refl _) _ _ _ _
    (fun e he r => by simp only [dif_pos he])
    (fun sq hsq => by simp only [dif_pos hsq])

-- ============================================================================
-- Theorems: expression evaluation unfolding (proved via bridge axioms)
-- ============================================================================

/-- evalExprWithDb unfolds for literals -/
theorem evalExprWithDb_lit (db : Database) (row : Row) (v : Value) :
  evalExprWithDb db row (Expr.lit v) = some v := by
  rw [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_lit ..

/-- evalExprWithDb unfolds for column references -/
theorem evalExprWithDb_col (db : Database) (row : Row) (c : ColumnRef) :
  evalExprWithDb db row (Expr.col c) = row.getQualified c.table c.column := by
  rw [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_col ..

/-- evalExprWithDb unfolds for binOp -/
theorem evalExprWithDb_binOp (db : Database) (row : Row) (op : BinOp) (l r : Expr) :
  evalExprWithDb db row (Expr.binOp op l r) = evalBinOp op (evalExprWithDb db row l) (evalExprWithDb db row r) := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_binOp ..

/-- evalExprWithDb unfolds for unaryOp -/
theorem evalExprWithDb_unaryOp (db : Database) (row : Row) (op : UnaryOp) (e : Expr) :
  evalExprWithDb db row (Expr.unaryOp op e) = evalUnaryOp op (evalExprWithDb db row e) := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_unaryOp ..

/-- evalExprWithDb unfolds for EXISTS expressions (generic SubQuery payload, #218) -/
theorem evalExprWithDb_exists (db : Database) (row : Row) (neg : Bool) (sq : SubQuery) :
    evalExprWithDb db row (Expr.exists neg sq) =
    (let subResult := evalSubQueryWithContext db row sq
     let hasExists := !subResult.isEmpty
     some (Value.bool (if neg then !hasExists else hasExists))) := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_exists ..

/-- evalExprWithDb unfolds for EXISTS over a simple SELECT subquery -/
theorem evalExprWithDb_exists_simple (db : Database) (row : Row) (neg : Bool) (sel : SelectStmt) :
    evalExprWithDb db row (Expr.exists neg (.simple sel)) =
    (let subResult := evalSelectWithContext db row sel
     let hasExists := !subResult.isEmpty
     some (Value.bool (if neg then !hasExists else hasExists))) := by
  rw [evalExprWithDb_exists, evalSubQuery_simple]

/-- evalExprWithDb unfolds for scalar subquery expressions (generic SubQuery payload, #218) -/
theorem evalExprWithDb_subquery (db : Database) (row : Row) (sq : SubQuery) :
    evalExprWithDb db row (Expr.subquery sq) =
    (match (evalSubQueryWithContext db row sq).head? with
     | some subRow => subRow.head?.map (·.2)
     | none => some (.null none)) := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_subquery ..

/-- evalExprWithDb unfolds for scalar subqueries over a simple SELECT -/
theorem evalExprWithDb_subquery_simple (db : Database) (row : Row) (sel : SelectStmt) :
    evalExprWithDb db row (Expr.subquery (.simple sel)) =
    (match (evalSelectWithContext db row sel).head? with
     | some subRow => subRow.head?.map (·.2)
     | none => some (.null none)) := by
  rw [evalExprWithDb_subquery, evalSubQuery_simple]

/-- evalExprWithDb unfolds for IN subquery expressions (generic SubQuery payload, #218) -/
theorem evalExprWithDb_inSubquery (db : Database) (row : Row) (e : Expr) (neg : Bool) (sq : SubQuery) :
    evalExprWithDb db row (.inSubquery e neg sq) =
    (match evalExprWithDb db row e with
     | none => none
     | some v => some (inSubqueryResult neg v (evalSubQueryWithContext db row sq))) := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_inSubquery ..

/-- evalExprWithDb unfolds for IN over a simple SELECT subquery -/
theorem evalExprWithDb_inSubquery_simple (db : Database) (row : Row) (e : Expr) (neg : Bool) (sel : SelectStmt) :
    evalExprWithDb db row (.inSubquery e neg (.simple sel)) =
    (match evalExprWithDb db row e with
     | none => none
     | some v => some (inSubqueryResult neg v (evalSelectWithContext db row sel))) := by
  rw [evalExprWithDb_inSubquery, evalSubQuery_simple]

/-- evalExprWithDb unfolds for case expressions -/
theorem evalExprWithDb_case (db : Database) (row : Row) (branches : List (Expr × Expr)) (else_ : Option Expr) :
  evalExprWithDb db row (Expr.case branches else_) = evalCase db row branches else_ := by
  have h1 := evalExprWithDb_eq_evalExprCore db row (Expr.case branches else_)
  have h2 := evalExprCore_case db row (fun db' row' sq => evalSubQueryWithContext db' row' sq) branches else_
  have h3 := (evalCase_eq_evalCaseHelper db row branches else_).symm
  exact h1.trans (h2.trans h3)

/-- evalCase unfolds for empty branches with else -/
theorem evalCase_nil_some (db : Database) (row : Row) (e : Expr) :
  evalCase db row [] (some e) = evalExprWithDb db row e := by
  rw [evalCase_eq_evalCaseHelper]
  simp [evalCaseHelper]
  exact (evalExprWithDb_eq_evalExprCore db row e).symm

/-- evalCase unfolds for empty branches with no else -/
theorem evalCase_nil_none (db : Database) (row : Row) :
  evalCase db row [] none = some (.null none) := by
  rw [evalCase_eq_evalCaseHelper]
  simp [evalCaseHelper]

/-- evalCase unfolds for cons branches when condition is true -/
theorem evalCase_cons_true (db : Database) (row : Row) (cond result : Expr) (rest : List (Expr × Expr)) (else_ : Option Expr) :
  evalExprWithDb db row cond = some (.bool true) →
  evalCase db row ((cond, result) :: rest) else_ = evalExprWithDb db row result := by
  intro h
  have hcore : evalExprCore db row (fun db' row' sq => evalSubQueryWithContext db' row' sq) cond = some (.bool true) := by
    rwa [← evalExprWithDb_eq_evalExprCore]
  rw [evalCase_eq_evalCaseHelper]
  simp [evalCaseHelper, hcore]
  exact (evalExprWithDb_eq_evalExprCore db row result).symm

/-- evalCase unfolds for cons branches when condition is false -/
theorem evalCase_cons_false (db : Database) (row : Row) (cond result : Expr) (rest : List (Expr × Expr)) (else_ : Option Expr) :
  evalExprWithDb db row cond = some (.bool false) →
  evalCase db row ((cond, result) :: rest) else_ = evalCase db row rest else_ := by
  intro h
  have hcore : evalExprCore db row (fun db' row' sq => evalSubQueryWithContext db' row' sq) cond = some (.bool false) := by
    rwa [← evalExprWithDb_eq_evalExprCore]
  simp only [evalCase_eq_evalCaseHelper]
  simp [evalCaseHelper, hcore]

/-- evalExprWithDb unfolds for function calls -/
theorem evalExprWithDb_func (db : Database) (row : Row) (name : String) (args : List Expr) :
  evalExprWithDb db row (Expr.func name args) = evalFunc name (args.map (evalExprWithDb db row)) := by
  rw [evalExprWithDb_eq_evalExprCore, evalExprCore_func]
  exact congrArg (evalFunc name) (List.map_congr_left fun e _ => (evalExprWithDb_eq_evalExprCore db row e).symm)

/-- evalExprWithDb unfolds for BETWEEN -/
theorem evalExprWithDb_between (db : Database) (row : Row) (e lo hi : Expr) :
  evalExprWithDb db row (Expr.between e lo hi) =
  let ev := evalExprWithDb db row e
  let evlo := evalExprWithDb db row lo
  let evhi := evalExprWithDb db row hi
  evalBinOp .and (evalBinOp .ge ev evlo) (evalBinOp .le ev evhi) := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_between ..

/-- evalExprWithDb unfolds for IN list -/
theorem evalExprWithDb_inList (db : Database) (row : Row) (e : Expr) (neg : Bool) (vals : List Expr) :
  evalExprWithDb db row (Expr.inList e neg vals) =
  let ev := evalExprWithDb db row e
  let result := vals.foldl (fun acc vi =>
    evalBinOp .or acc (evalBinOp .eq ev (evalExprWithDb db row vi))
  ) (some (.bool false))
  if neg then evalUnaryOp .not result else result := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_inList ..

-- ============================================================================
-- Infrastructure axioms for evalFrom join decomposition
-- ============================================================================

/-- evalFrom for table reference produces qualified rows from the database. -/
theorem evalFrom_table (db : Database) (t : TableRef) :
    evalFrom db (.table t) =
    let qualifier := t.alias.getD t.name
    (db t.name).map fun row =>
      row.map fun (col, val) => (s!"{qualifier}.{col}", val) := by
  simp only [evalFrom_eq_evalFromCore]
  exact evalFromCore_table ..

/-- evalFrom for a derived table: the inner result with every key re-qualified
    by the alias (standard derived-table scoping, #257). -/
theorem evalFrom_subquery (db : Database) (sq : SubQuery) (alias : String) :
    evalFrom db (.subquery sq alias) =
      (evalSubQueryWithContext db [] sq).map (requalifyRow alias) := by
  simp only [evalFrom_eq_evalFromCore]
  exact evalFromCore_subquery ..

/-- evalFrom for a simple SELECT subquery: the inner SELECT result, re-qualified. -/
theorem evalFrom_subquery_simple (db : Database) (sel : SelectStmt) (alias : String) :
    evalFrom db (.subquery (.simple sel) alias) = (evalSelect db sel).map (requalifyRow alias) := by
  rw [evalFrom_subquery, evalSubQuery_simple]; rfl

/-- Rows of a base table are keyed by its qualifier, so re-qualifying them by
    that same qualifier changes nothing (#257, #269). -/
theorem requalifyRow_table_row (db : Database) (t : TableRef) :
    ∀ row ∈ evalFrom db (.table t), requalifyRow (t.alias.getD t.name) row = row := by
  intro row hrow
  rw [evalFrom_table] at hrow
  simp only [List.mem_map] at hrow
  obtain ⟨r, _, rfl⟩ := hrow
  simp only [requalifyRow, List.map_map]
  apply List.map_congr_left
  intro ⟨c, v⟩ _
  simp [requalifyKey_mk]

/-- evalFrom decomposes CROSS JOIN into flatMap/map on left/right rows. -/
theorem evalFrom_cross_join (db : Database) (left right : FromClause) :
    evalFrom db (.join left .cross right none) =
    let rightRows := evalFrom db right
    (evalFrom db left).flatMap fun lr =>
      rightRows.map fun rr => lr ++ rr := by
  simp only [evalFrom_eq_evalFromCore]
  exact evalFromCore_cross_join ..

/-- evalFrom decomposes INNER JOIN into flatMap/filterMap on left/right rows. -/
theorem evalFrom_inner_join (db : Database) (left right : FromClause) (on_ : Option Expr) :
    evalFrom db (.join left .inner right on_) =
    let rightRows := evalFrom db right
    (evalFrom db left).flatMap fun lr =>
      rightRows.filterMap fun rr =>
        let combined := lr ++ rr
        match on_ with
        | none => some combined
        | some cond =>
          match evalExprWithDb db combined cond with
          | some (.bool true) => some combined
          | _ => none := by
  simp only [evalFrom_eq_evalFromCore]
  exact evalFromCore_inner_join ..

/-- evalFrom decomposes LEFT JOIN into flatMap with NULL-padding fallback. -/
theorem evalFrom_left_join (db : Database) (left right : FromClause) (on_ : Option Expr) :
    evalFrom db (.join left .left right on_) =
    let rightRows := evalFrom db right
    (evalFrom db left).flatMap fun lr =>
      let matchingRows := rightRows.filterMap fun rr =>
        let combined := lr ++ rr
        match on_ with
        | none => some combined
        | some cond =>
          match evalExprWithDb db combined cond with
          | some (.bool true) => some combined
          | _ => none
      if matchingRows.isEmpty then
        match rightRows.head? with
        | some rightRow => [lr ++ rightRow.map fun (k, _) => (k, .null none)]
        | none => [lr]
      else
        matchingRows := by
  simp only [evalFrom_eq_evalFromCore]
  exact evalFromCore_left_join ..

/-- evalFrom decomposes RIGHT JOIN into flatMap with NULL-padding fallback. -/
theorem evalFrom_right_join (db : Database) (left right : FromClause) (on_ : Option Expr) :
    evalFrom db (.join left .right right on_) =
    let leftRows := evalFrom db left
    (evalFrom db right).flatMap fun rr =>
      let matchingRows := leftRows.filterMap fun lr =>
        let combined := lr ++ rr
        match on_ with
        | none => some combined
        | some cond =>
          match evalExprWithDb db combined cond with
          | some (.bool true) => some combined
          | _ => none
      if matchingRows.isEmpty then
        match leftRows.head? with
        | some leftRow => [leftRow.map (fun (k, _) => (k, .null none)) ++ rr]
        | none => [rr]
      else
        matchingRows := by
  simp only [evalFrom_eq_evalFromCore]
  exact evalFromCore_right_join ..

-- ============================================================================
-- INSERT/UPDATE/DELETE Evaluation
-- ============================================================================

/-- Evaluate INSERT statement, return new database -/
def evalInsert (db : Database) (ins : InsertStmt) : Database :=
  let newRows : List Row := match ins.source with
    | .values rowExprs =>
      rowExprs.map fun (exprs : List Expr) =>
        match ins.columns with
        | some cols =>
          cols.zip (exprs.map fun e => (evalExprWithDb db [] e).getD (.null none))
        | none =>
          (listEnumerate exprs).map fun (i, e) =>
            (s!"col{i}", (evalExprWithDb db [] e).getD (.null none))
    | .selectStmt sel =>
      evalSelect db sel
  fun name =>
    if name == ins.table then
      db name ++ newRows
    else
      db name

/-- Evaluate UPDATE statement, return new database -/
def evalUpdate (db : Database) (upd : UpdateStmt) : Database :=
  fun name =>
    if name == upd.table then
      (db name).map fun row =>
        let shouldUpdate := match upd.whereClause with
          | some cond => evalExprWithDb db row cond == some (Value.bool true)
          | none => true
        if shouldUpdate then
          upd.assignments.foldl (fun r a =>
            r.map fun (k, v) =>
              if k == a.column || k.endsWith s!".{a.column}" then
                (k, (evalExprWithDb db r a.value).getD (.null none))
              else
                (k, v)
          ) row
        else
          row
    else
      db name

/-- Evaluate DELETE statement, return new database -/
def evalDelete (db : Database) (del : DeleteStmt) : Database :=
  fun name =>
    if name == del.table then
      (db name).filter fun row =>
        match del.whereClause with
        | some cond => evalExprWithDb db row cond != some (Value.bool true)
        | none => false  -- DELETE without WHERE deletes all
    else
      db name

/-- Maximum iterations for recursive CTE to prevent infinite loops -/
def maxCTEIterations : Nat := 1000

/-- Parameterized recursive CTE evaluation using fixed-point iteration -/
def evalRecursiveCTEParam (db : Database) (cteName : String) (cteQuery : Query)
    (queryEval : Database → Query → Table) : Table :=
  let rec iterate (workingTable : Table) (iteration : Nat) : Table :=
    if iteration >= maxCTEIterations then workingTable
    else
      let dbWithCTE : Database := fun name =>
        if name == cteName then workingTable else db name
      let result := queryEval dbWithCTE cteQuery
      if result == workingTable then workingTable
      else iterate result (iteration + 1)
  termination_by maxCTEIterations - iteration
  iterate [] 0

/-- Fixed-point iteration: apply `step` repeatedly up to `fuel` times,
    stopping early when the result stabilizes. Structurally recursive on Nat. -/
def fixedPointIterate (step : Table → Table) (init : Table) : Nat → Table
  | 0 => init
  | n + 1 =>
    let result := step init
    if result == init then init else fixedPointIterate step result n

/-- Evaluate a Query (simple SELECT or compound with set operations).
    CTEs are processed by matching on the list structure (cons vs nil)
    instead of using foldl, making all recursive calls structurally visible
    for the termination checker. -/
def evalQuery (db : Database) (q : Query) : Table :=
  match q with
  | .simple sel => evalSelect db sel
  | .compound left op right =>
    applySetOp op (Query.outputNames? left) (evalQuery db left) (evalQuery db right)
  | .withCTE [] query => evalQuery db query
  | .withCTE (cte :: rest) query =>
    let cteResult :=
      if cte.isRecursive then
        fixedPointIterate
          (fun workingTable =>
            evalQuery (fun n => if n == cte.name then workingTable else db n) cte.query)
          [] maxCTEIterations
      else
        evalQuery db cte.query
    let newDb : Database := fun name =>
      if name == cte.name then cteResult else db name
    evalQuery newDb (.withCTE rest query)
  | .ordered query ob lim off =>
    -- #317: sort/limit the whole compound result; keys are evaluated on its output rows.
    applyOrderByLimitOffsetAligned (compareByOrderItemsParam evalExprWithDb) db ob lim off false []
      (evalQuery db query)
termination_by sizeOf q
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (obtain ⟨_, cq, _⟩ := cte
       simp only [CTEDef.query, CTEDef.mk.sizeOf_spec]
       omega)

/-- Evaluate a recursive CTE using fixed-point iteration -/
def evalRecursiveCTE (db : Database) (cteName : String) (cteQuery : Query) : Table :=
  evalRecursiveCTEParam db cteName cteQuery (fun db' q => evalQuery db' q)

/-- Bridge: evalQuery on .simple equals evalQueryCore -/
theorem evalQuery_eq_evalQueryCore_simple (db : Database) (sel : SelectStmt) :
    evalQuery db (.simple sel) = evalQueryCore db evalSelect evalQuery evalRecursiveCTE (.simple sel) := by
  unfold evalQuery; simp [evalQueryCore]

/-- Bridge: evalQuery on .compound equals evalQueryCore -/
theorem evalQuery_eq_evalQueryCore_compound (db : Database) (left right : Query) (op : SetOp) :
    evalQuery db (.compound left op right) =
    evalQueryCore db evalSelect evalQuery evalRecursiveCTE (.compound left op right) := by
  unfold evalQuery evalQueryCore; rfl

-- ============================================================================
-- Helper congruence (#212 phase 2): the *Param helpers only call their
-- expression callback on parts of their input, so callbacks that agree on all
-- expressions below a size bound give equal results on inputs below it.
-- ============================================================================
section HelperCongr
variable (e1 e2 : Database → Row → Expr → Option Value) (N : Nat)
  (hE : ∀ e, e.size < N → ∀ db r, e1 db r e = e2 db r e)

include hE in
theorem evalAggOverTableParam_congr (db : Database) (fn : AggFunc) (a : Option Expr)
    (dist : Bool) (rows : Table) (ha : Expr.sizeOpt a < N) :
    evalAggOverTableParam e1 db fn a dist rows = evalAggOverTableParam e2 db fn a dist rows := by
  cases a with
  | none => rfl
  | some x =>
    have hx := hE x (by simpa [Expr.sizeOpt] using ha)
    simp only [evalAggOverTableParam, hx]

include hE in
theorem evalExprWithAggParam_congr (db : Database) (rows : Table) (r : Row) :
    ∀ (n : Nat) (e : Expr), e.size ≤ n → e.size < N →
    evalExprWithAggParam e1 db rows r e = evalExprWithAggParam e2 db rows r e := by
  intro n
  induction n with
  | zero => intro e h; have := Expr.size_pos e; omega
  | succ n ih =>
    intro e hn hN
    cases e with
    | agg fn a d =>
      simp only [evalExprWithAggParam]
      exact evalAggOverTableParam_congr e1 e2 N hE db fn a d rows
        (by simp [Expr.size] at hN; omega)
    | countStar => simp only [evalExprWithAggParam]
    | binOp op l rr =>
      simp only [evalExprWithAggParam]
      simp only [Expr.size] at hn hN
      rw [ih l (by omega) (by omega), ih rr (by omega) (by omega)]
    | unaryOp op x =>
      simp only [evalExprWithAggParam]
      simp only [Expr.size] at hn hN
      rw [ih x (by omega) (by omega)]
    | func nm args =>
      have hargs : ∀ a ∈ args,
          evalExprWithAggParam e1 db rows r a = evalExprWithAggParam e2 db rows r a :=
        fun a ha => by
          have := Expr.size_le_sizeList_of_mem ha
          simp only [Expr.size] at hn hN
          exact ih a (by omega) (by omega)
      simp only [evalExprWithAggParam, List.map_congr_left hargs, hE _ hN db r]
    | «case» branches else_ =>
      have hsz := hN; have hsn := hn
      simp only [Expr.size] at hsz hsn
      have hpair : ∀ p ∈ branches,
          evalExprWithAggParam e1 db rows r p.1 = evalExprWithAggParam e2 db rows r p.1 ∧
          evalExprWithAggParam e1 db rows r p.2 = evalExprWithAggParam e2 db rows r p.2 :=
        fun p hp => by
          obtain ⟨a, b⟩ := p
          have := Expr.size_le_sizePairs_of_mem hp
          exact ⟨ih a (by omega) (by omega), ih b (by omega) (by omega)⟩
      have hmap : branches.map (fun pair =>
            (evalExprWithAggParam e1 db rows r pair.1, evalExprWithAggParam e1 db rows r pair.2)) =
          branches.map (fun pair =>
            (evalExprWithAggParam e2 db rows r pair.1, evalExprWithAggParam e2 db rows r pair.2)) :=
        List.map_congr_left fun p hp => by rw [(hpair p hp).1, (hpair p hp).2]
      cases else_ with
      | none =>
        simp only [evalExprWithAggParam, hmap, hE _ hN db r]
      | some e =>
        simp only [Expr.sizeOpt] at hsz hsn
        simp only [evalExprWithAggParam, hmap, hE _ hN db r, ih e (by omega) (by omega)]
    | inList x neg vals =>
      have hsz := hN; have hsn := hn
      simp only [Expr.size] at hsz hsn
      have hx := ih x (by omega) (by omega)
      have hvals : ∀ (ev : Option Value) (l : List Expr), (∀ v ∈ l, v ∈ vals) →
          ∀ (acc : Option Value),
          l.foldl (fun acc vi => evalBinOp .or acc
            (evalBinOp .eq ev (evalExprWithAggParam e1 db rows r vi))) acc =
          l.foldl (fun acc vi => evalBinOp .or acc
            (evalBinOp .eq ev (evalExprWithAggParam e2 db rows r vi))) acc := by
        intro ev l hl
        induction l with
        | nil => intro acc; rfl
        | cons v vs ihl =>
          intro acc
          have hv := Expr.size_le_sizeList_of_mem (hl v List.mem_cons_self)
          simp only [List.foldl_cons, ih v (by omega) (by omega)]
          exact ihl (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
      simp only [evalExprWithAggParam, hvals _ vals (fun _ h => h), hx, hE _ hN db r]
    | between x lo hi =>
      simp only [evalExprWithAggParam, hE _ hN db r]
      simp only [Expr.size] at hn hN
      rw [ih x (by omega) (by omega), ih lo (by omega) (by omega), ih hi (by omega) (by omega)]
    | _ => simp only [evalExprWithAggParam]; exact hE _ hN db r

include hE in
theorem compareByOrderItemsParam_congr (db : Database) (r1 r2 : Row) :
    ∀ (ob : List OrderByItem), (∀ o ∈ ob, o.expr.size < N) →
    compareByOrderItemsParam e1 db r1 r2 ob = compareByOrderItemsParam e2 db r1 r2 ob
  | [], _ => by simp only [compareByOrderItemsParam]
  | o :: rest, h => by
    simp only [compareByOrderItemsParam]
    rw [hE o.expr (h o List.mem_cons_self) db r1, hE o.expr (h o List.mem_cons_self) db r2,
      compareByOrderItemsParam_congr db r1 r2 rest (fun x hx => h x (List.mem_cons_of_mem o hx))]

include hE in
theorem computeRanksParam_congr (db : Database) (rows : Table) (ob : List OrderByItem)
    (h : ∀ o ∈ ob, o.expr.size < N) :
    computeRanksParam e1 db rows ob = computeRanksParam e2 db rows ob := by
  have hk : ∀ r, ob.map (fun item => e1 db r item.expr) = ob.map (fun item => e2 db r item.expr) :=
    fun r => List.map_congr_left (fun o ho => hE o.expr (h o ho) db r)
  simp only [computeRanksParam]
  suffices ∀ rem c nx pk, computeRanksParam.go e1 db ob rem c nx pk =
      computeRanksParam.go e2 db ob rem c nx pk from this _ _ _ _
  intro rem
  induction rem with
  | nil => intro c nx pk; simp only [computeRanksParam.go]
  | cons row rest ih => intro c nx pk; simp only [computeRanksParam.go, hk, ih]

include hE in
theorem computeDenseRanksParam_congr (db : Database) (rows : Table) (ob : List OrderByItem)
    (h : ∀ o ∈ ob, o.expr.size < N) :
    computeDenseRanksParam e1 db rows ob = computeDenseRanksParam e2 db rows ob := by
  have hk : ∀ r, ob.map (fun item => e1 db r item.expr) = ob.map (fun item => e2 db r item.expr) :=
    fun r => List.map_congr_left (fun o ho => hE o.expr (h o ho) db r)
  simp only [computeDenseRanksParam]
  suffices ∀ rem c pk, computeDenseRanksParam.go e1 db ob rem c pk =
      computeDenseRanksParam.go e2 db ob rem c pk from this _ _ _
  intro rem
  induction rem with
  | nil => intro c pk; simp only [computeDenseRanksParam.go]
  | cons row rest ih => intro c pk; simp only [computeDenseRanksParam.go, hk, ih]

include hE in
theorem sortPartitionParam_congr (db : Database) (rows : Table) (ob : List OrderByItem)
    (h : ∀ o ∈ ob, o.expr.size < N) :
    sortPartitionParam e1 db rows ob = sortPartitionParam e2 db rows ob := by
  simp only [sortPartitionParam, compareByOrderItemsParam_congr e1 e2 N hE db _ _ ob h]

include hE in
theorem windowFrameRowsParam_congr (db : Database) (ob : List OrderByItem)
    (sp : Table) (r : Row) (i : Nat) (h : ∀ o ∈ ob, o.expr.size < N) :
    windowFrameRowsParam e1 db ob sp r i = windowFrameRowsParam e2 db ob sp r i := by
  have hk : ∀ r, ob.map (fun item => e1 db r item.expr) = ob.map (fun item => e2 db r item.expr) :=
    fun r => List.map_congr_left (fun o ho => hE o.expr (h o ho) db r)
  simp only [windowFrameRowsParam, hk]

include hE in
theorem evalWindowFnParam_congr (db : Database) (fn : WindowFunc) (a : Option Expr)
    (ob : List OrderByItem) (sp : Table) (r : Row) (i : Nat)
    (ha : Expr.sizeOpt a < N) (h : ∀ o ∈ ob, o.expr.size < N) :
    evalWindowFnParam e1 db fn a ob sp r i = evalWindowFnParam e2 db fn a ob sp r i := by
  have hf := windowFrameRowsParam_congr e1 e2 N hE db ob sp r i h
  have hr := computeRanksParam_congr e1 e2 N hE db sp ob h
  have hd := computeDenseRanksParam_congr e1 e2 N hE db sp ob h
  cases a with
  | none => cases fn <;> simp only [evalWindowFnParam, hf, hr, hd]
  | some x =>
    have hx := hE x (by simpa [Expr.sizeOpt] using ha)
    cases fn <;> simp only [evalWindowFnParam, hf, hr, hd, hx]

theorem WindowSpec.partitionBy_size_lt {spec : WindowSpec} {x : Expr}
    (hx : x ∈ spec.partitionBy) : x.size < spec.size := by
  cases spec with
  | mk ps os =>
    simp only [WindowSpec.partitionBy] at hx
    have := Expr.size_le_sizeList_of_mem hx
    simp [WindowSpec.size]; omega

theorem WindowSpec.orderBy_size_lt {spec : WindowSpec} {o : OrderByItem}
    (ho : o ∈ spec.orderBy) : o.expr.size < spec.size := by
  cases spec with
  | mk ps os =>
    simp only [WindowSpec.orderBy] at ho
    have := OrderByItem.size_le_sizeList_of_mem ho
    have := OrderByItem.expr_size_lt o
    simp [WindowSpec.size]; omega

include hE in
theorem evalExprWithWindowParam_congr (db : Database) (r : Row) (p sp : Table) (i : Nat) :
    ∀ (n : Nat) (e : Expr), e.size ≤ n → e.size < N →
    evalExprWithWindowParam e1 db r p sp i e = evalExprWithWindowParam e2 db r p sp i e := by
  intro n
  induction n with
  | zero => intro e h; have := Expr.size_pos e; omega
  | succ n ih =>
    intro e hn hN
    cases e with
    | windowFn fn a spec =>
      simp only [Expr.size] at hN
      have hpb : ∀ x ∈ spec.partitionBy, x.size < N := fun x hx => by
        have := WindowSpec.partitionBy_size_lt hx; omega
      have hob : ∀ o ∈ spec.orderBy, o.expr.size < N := fun o ho => by
        have := WindowSpec.orderBy_size_lt ho; omega
      have hkey : ∀ r, spec.partitionBy.map (e1 db r) = spec.partitionBy.map (e2 db r) :=
        fun r => List.map_congr_left (fun x hx => hE x (hpb x hx) db r)
      simp only [evalExprWithWindowParam, hkey,
        sortPartitionParam_congr e1 e2 N hE db _ spec.orderBy hob,
        evalWindowFnParam_congr e1 e2 N hE db fn a spec.orderBy _ r _ (by omega) hob]
    | binOp op l rr =>
      simp only [evalExprWithWindowParam]
      simp only [Expr.size] at hn hN
      rw [ih l (by omega) (by omega), ih rr (by omega) (by omega)]
    | unaryOp op x =>
      simp only [evalExprWithWindowParam]
      simp only [Expr.size] at hn hN
      rw [ih x (by omega) (by omega)]
    | _ => simp only [evalExprWithWindowParam]; exact hE _ hN db r

end HelperCongr

-- A MIN/MAX call's argument is smaller than the expression it occurs in (used to show the
-- guarded and unguarded evaluators agree on it, for `bareSampleRow`).
mutual
theorem minMaxCalls_arg_size : ∀ (e : Expr) {w : Bool} {m : MinMaxMode} {a : Expr} {d : Bool},
    (w, m, some a, d) ∈ minMaxCalls e → a.size < e.size
  | .agg (.min _) arg _, _, _, _, _, h => by
    simp only [minMaxCalls, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl, -⟩ := h; simp [Expr.size, Expr.sizeOpt]
  | .agg (.max _) arg _, _, _, _, _, h => by
    simp only [minMaxCalls, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl, -⟩ := h; simp [Expr.size, Expr.sizeOpt]
  | .agg .count _ _, _, _, _, _, h | .agg (.sum _) _ _, _, _, _, _, h
  | .agg (.avg _) _ _, _, _, _, _, h => by simp [minMaxCalls] at h
  | .binOp _ l r, _, _, _, _, h => by
    simp only [minMaxCalls, List.mem_append] at h
    rcases h with h | h
    · have := minMaxCalls_arg_size l h; simp [Expr.size]; omega
    · have := minMaxCalls_arg_size r h; simp [Expr.size]; omega
  | .unaryOp _ x, _, _, _, _, h => by
    simp only [minMaxCalls] at h
    have := minMaxCalls_arg_size x h; simp [Expr.size]; omega
  | .func _ args, _, _, _, _, h => by
    simp only [minMaxCalls] at h
    have := minMaxCallsList_arg_size args h; simp [Expr.size]; omega
  | .case bs els, _, _, _, _, h => by
    simp only [minMaxCalls, List.mem_append] at h
    rcases h with h | h
    · have := minMaxCallsPairs_arg_size bs h; simp [Expr.size]; omega
    · have := minMaxCallsOpt_arg_size els h; simp [Expr.size]; omega
  | .inList x _ vs, _, _, _, _, h => by
    simp only [minMaxCalls, List.mem_append] at h
    rcases h with h | h
    · have := minMaxCalls_arg_size x h; simp [Expr.size]; omega
    · have := minMaxCallsList_arg_size vs h; simp [Expr.size]; omega
  | .between x lo hi, _, _, _, _, h => by
    simp only [minMaxCalls, List.mem_append] at h
    rcases h with (h | h) | h
    · have := minMaxCalls_arg_size x h; simp [Expr.size]; omega
    · have := minMaxCalls_arg_size lo h; simp [Expr.size]; omega
    · have := minMaxCalls_arg_size hi h; simp [Expr.size]; omega
  | .lit _, _, _, _, _, h | .col _, _, _, _, _, h | .countStar, _, _, _, _, h
  | .inSubquery .., _, _, _, _, h | .exists .., _, _, _, _, h | .subquery _, _, _, _, _, h
  | .windowFn .., _, _, _, _, h => by simp [minMaxCalls] at h
theorem minMaxCallsList_arg_size : ∀ (es : List Expr) {w : Bool} {m : MinMaxMode} {a : Expr}
    {d : Bool}, (w, m, some a, d) ∈ minMaxCalls.minMaxCallsList es → a.size < Expr.sizeList es
  | [], _, _, _, _, h => by simp [minMaxCalls.minMaxCallsList] at h
  | e :: es, _, _, _, _, h => by
    simp only [minMaxCalls.minMaxCallsList, List.mem_append] at h
    rcases h with h | h
    · have := minMaxCalls_arg_size e h; simp [Expr.sizeList]; omega
    · have := minMaxCallsList_arg_size es h; simp [Expr.sizeList]; omega
theorem minMaxCallsPairs_arg_size : ∀ (ps : List (Expr × Expr)) {w : Bool} {m : MinMaxMode}
    {a : Expr} {d : Bool},
    (w, m, some a, d) ∈ minMaxCalls.minMaxCallsPairs ps → a.size < Expr.sizePairs ps
  | [], _, _, _, _, h => by simp [minMaxCalls.minMaxCallsPairs] at h
  | (c, r) :: ps, _, _, _, _, h => by
    simp only [minMaxCalls.minMaxCallsPairs, List.mem_append] at h
    rcases h with (h | h) | h
    · have := minMaxCalls_arg_size c h; simp [Expr.sizePairs]; omega
    · have := minMaxCalls_arg_size r h; simp [Expr.sizePairs]; omega
    · have := minMaxCallsPairs_arg_size ps h; simp [Expr.sizePairs]; omega
theorem minMaxCallsOpt_arg_size : ∀ (o : Option Expr) {w : Bool} {m : MinMaxMode} {a : Expr}
    {d : Bool}, (w, m, some a, d) ∈ minMaxCalls.minMaxCallsOpt o → a.size < Expr.sizeOpt o
  | none, _, _, _, _, h => by simp [minMaxCalls.minMaxCallsOpt] at h
  | some e, _, _, _, _, h => by
    simp only [minMaxCalls.minMaxCallsOpt] at h
    have := minMaxCalls_arg_size e h; simp [Expr.sizeOpt]; omega
end

private abbrev ee := fun db' (r : Row) e => @evalExprWithDb db' r e

/-- Bridge: evalSelectWithContext equals evalSelectCore instantiated with all eval callbacks -/
theorem evalSelectWithContext_eq_evalSelectCore (db : Database) (outerRow : Row) (sel : SelectStmt) :
  evalSelectWithContext db outerRow sel = evalSelectCore db outerRow
    (fun db' fc => evalFrom db' fc)
    ee
    (evalSelectItemParam ee)
    (evalSelectItemWithAggParam ee)
    (evalExprWithAggParam ee)
    (compareByOrderItemsParam ee)
    (evalExprWithWindowParam ee)
    selectHasWindowFn
    selectHasAggregate
    sel := by
  -- The guarded callbacks of the definition agree with the unguarded ones on
  -- every expression smaller than `sel`, and evalSelectCore and its helpers
  -- only use them on parts of `sel` (or on the size-1 grouped sort keys) (#212).
  rw [evalSelectWithContext]
  obtain ⟨d, items, from_, w, gb, hv, ob, lim, off⟩ := sel
  have hsz : (SelectStmt.mk d items from_ w gb hv ob lim off).size =
      1 + SelectItem.sizeList items + FromClause.sizeOpt from_ + Expr.sizeOpt w +
        Expr.sizeList gb + Expr.sizeOpt hv + OrderByItem.sizeList ob := by
    simp [SelectStmt.size]
  generalize hN : (SelectStmt.mk d items from_ w gb hv ob lim off).size = N at hsz ⊢
  have hE : ∀ e, e.size < N → ∀ db' r,
      (fun db' r e => if _h : e.size < N then evalExprWithDb db' r e
        else evalExprCore db' r (fun _ _ _ => []) e) db' r e = ee db' r e := by
    intro e he db' r; simp only [dif_pos he]
  have hItem : ∀ e a, SelectItem.exprItem e a ∈ items → e.size < N := by
    intro e a hm
    have := SelectItem.size_le_sizeList_of_mem hm
    simp [SelectItem.size] at this; omega
  have hOb : ∀ o ∈ ob, o.expr.size < N := by
    intro o ho
    have := OrderByItem.size_le_sizeList_of_mem ho
    have := OrderByItem.expr_size_lt o
    omega
  apply evalSelectCore_callbacks_congr
  case hB =>
    intro rs
    apply bareSampleRow_congr
    intro w' m' a d' hmem r
    have ha : a.size < N := by
      simp only [SelectStmt.items, SelectStmt.having, selectMinMaxCalls, List.mem_append,
        List.mem_flatMap] at hmem
      rcases hmem with ⟨item, hitem, hin⟩ | hin
      · cases item with
        | star t => simp at hin
        | exprItem e al =>
          have := minMaxCalls_arg_size e hin
          have := hItem e al hitem
          omega
      · have := minMaxCallsOpt_arg_size hv hin
        omega
    exact hE a ha db r
  case hF =>
    intro f hf
    simp only [SelectStmt.fromClause] at hf
    subst hf
    simp only [dif_pos (show f.size < N by simp [FromClause.sizeOpt] at hsz; omega)]
  case hW =>
    intro c hc
    simp only [SelectStmt.whereClause] at hc
    subst hc
    exact hE c (by simp [Expr.sizeOpt] at hsz; omega) db
  case hHe =>
    intro c hc
    simp only [SelectStmt.having] at hc
    subst hc
    exact hE c (by simp [Expr.sizeOpt] at hsz; omega) db
  case hHa =>
    intro c hc rs r
    simp only [SelectStmt.having] at hc
    subst hc
    exact evalExprWithAggParam_congr _ ee N hE db rs r c.size c (Nat.le_refl _)
      (by simp [Expr.sizeOpt] at hsz; omega)
  case hG =>
    intro r
    simp only [SelectStmt.groupBy]
    exact List.map_congr_left (fun x hx => hE x
      (by have := Expr.size_le_sizeList_of_mem hx; omega) db r)
  case hSI =>
    intro r
    simp only [SelectStmt.items]
    apply flatMap_congr_mem
    intro item hm
    cases item with
    | star t => cases t <;> rfl
    | exprItem e a =>
      simp only [evalSelectItemParam, hE e (hItem e a hm) db r]
  case hSIA =>
    intro rs r
    simp only [SelectStmt.items]
    apply flatMap_congr_mem
    intro item hm
    cases item with
    | star t => cases t <;> rfl
    | exprItem e a =>
      simp only [evalSelectItemWithAggParam,
        evalExprWithAggParam_congr _ ee N hE db rs r e.size e (Nat.le_refl _) (hItem e a hm)]
  case hEW =>
    intro e a hm r p sp i
    simp only [SelectStmt.items] at hm
    exact evalExprWithWindowParam_congr _ ee N hE db r p sp i e.size e (Nat.le_refl _)
      (hItem e a hm)
  case hC1 =>
    intro r1 r2
    exact compareByOrderItemsParam_congr _ ee N hE db r1 r2 ob hOb
  case hC2 =>
    intro r1 r2
    apply compareByOrderItemsParam_congr _ ee N hE db r1 r2
    intro o ho
    simp only [SelectStmt.orderBy, groupOrderByItems, List.mem_map] at ho
    obtain ⟨⟨k, item⟩, hk, rfl⟩ := ho
    have hitem := (List.of_mem_zip hk).2
    have := OrderByItem.size_le_sizeList_of_mem hitem
    have := OrderByItem.size_pos item
    simp [OrderByItem.expr, Expr.size]; omega
  case hOK =>
    intro o ho rs r
    simp only [SelectStmt.orderBy] at ho
    exact evalExprWithAggParam_congr _ ee N hE db rs r o.expr.size o.expr (Nat.le_refl _)
      (hOb o ho)

theorem evalSelect_eq_evalSelectCore (db : Database) (sel : SelectStmt) :
  evalSelect db sel = evalSelectCore db []
    (fun db' fc => evalFrom db' fc)
    ee
    (evalSelectItemParam ee)
    (evalSelectItemWithAggParam ee)
    (evalExprWithAggParam ee)
    (compareByOrderItemsParam ee)
    (evalExprWithWindowParam ee)
    selectHasWindowFn
    selectHasAggregate
    sel := by
  rw [evalSelect]
  exact evalSelectWithContext_eq_evalSelectCore db [] sel

-- ============================================================================
-- Infrastructure theorems for evalSelect (proved via evalSelectCore bridge)
-- ============================================================================

/-- Infrastructure: evalSelect decomposes limit/offset into drop/take on the base result.
    This captures steps 8 (OFFSET) and 9 (LIMIT) of the evaluation pipeline.
    Proved via evalSelectCore bridge. -/
theorem evalSelect_limit_offset (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
  evalSelect db (SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit offset) =
    let base := evalSelect db (SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none)
    let offsetRows := match offset with | some n => base.drop n | none => base
    match limit with | some n => offsetRows.take n | none => offsetRows := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  exact evalSelectCore_limit_offset ..

/-- Infrastructure: ORDER BY preserves row count (mergeSort preserves length).
    Changing the ORDER BY clause does not change the number of result rows.
    Proved via evalSelectCore bridge. -/
theorem evalSelect_orderBy_length (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy1 orderBy2 : List OrderByItem) (limit offset : Option Nat) :
  (evalSelect db (SelectStmt.mk distinct items from_ where_ groupBy having orderBy1 limit offset)).length =
  (evalSelect db (SelectStmt.mk distinct items from_ where_ groupBy having orderBy2 limit offset)).length := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  exact evalSelectCore_orderBy_length ..

/-- Infrastructure: WHERE clause only affects filtering; if two WHERE clauses
    produce the same filtering behavior for every row, evalSelect produces the same result.
    Proved via evalSelectCore bridge. -/
theorem evalSelect_where_congr (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (w1 w2 : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
  (∀ row : Row,
    (match w1 with | some c => evalExprWithDb db row c == some (Value.bool true) | none => true) =
    (match w2 with | some c => evalExprWithDb db row c == some (Value.bool true) | none => true)) →
  evalSelect db (SelectStmt.mk distinct items from_ w1 groupBy having orderBy limit offset) =
  evalSelect db (SelectStmt.mk distinct items from_ w2 groupBy having orderBy limit offset) := by
  intro hCongr
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  exact evalSelectCore_where_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hCongr

/-- Infrastructure: WHERE clause that rejects all rows produces empty result when no aggregates.
    Proved via evalSelectCore bridge. -/
theorem evalSelect_filter_all_false (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (cond : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
  selectHasAggregate items = false →
  (∀ row : Row, (evalExprWithDb db row cond == some (Value.bool true)) = false) →
  evalSelect db (SelectStmt.mk distinct items from_ (some cond) groupBy having orderBy limit offset) = [] := by
  intro hNoAgg hAllFalse
  rw [evalSelect_eq_evalSelectCore]
  exact evalSelectCore_filter_all_false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hAllFalse

-- ============================================================================
-- Infrastructure theorems for evalSelectWithContext (proved via evalSelectCore bridge)
-- ============================================================================

/-- Infrastructure: WHERE clause congr for evalSelectWithContext (correlated subqueries).
    Proved via evalSelectCore bridge. -/
theorem evalSelectWithContext_where_congr (db : Database) (outerRow : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (w1 w2 : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
  (∀ row : Row,
    (match w1 with | some c => evalExprWithDb db row c == some (Value.bool true) | none => true) =
    (match w2 with | some c => evalExprWithDb db row c == some (Value.bool true) | none => true)) →
  evalSelectWithContext db outerRow (SelectStmt.mk distinct items from_ w1 groupBy having orderBy limit offset) =
  evalSelectWithContext db outerRow (SelectStmt.mk distinct items from_ w2 groupBy having orderBy limit offset) := by
  intro hCongr
  rw [evalSelectWithContext_eq_evalSelectCore, evalSelectWithContext_eq_evalSelectCore]
  exact evalSelectCore_where_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hCongr

/-- Infrastructure: WHERE clause that rejects all rows produces empty result when no aggregates.
    For evalSelectWithContext (correlated subqueries). Proved via evalSelectCore bridge. -/
theorem evalSelectWithContext_filter_all_false (db : Database) (outerRow : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (cond : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
  selectHasAggregate items = false →
  (∀ row : Row, (evalExprWithDb db row cond == some (Value.bool true)) = false) →
  evalSelectWithContext db outerRow (SelectStmt.mk distinct items from_ (some cond) groupBy having orderBy limit offset) = [] := by
  intro hNoAgg hAllFalse
  rw [evalSelectWithContext_eq_evalSelectCore]
  exact evalSelectCore_filter_all_false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hAllFalse

/-- Infrastructure: evalSelectWithContext decomposes limit/offset into drop/take on the base result.
    Proved via evalSelectCore bridge. -/
theorem evalSelectWithContext_limit_offset (db : Database) (outerRow : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
  evalSelectWithContext db outerRow (SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit offset) =
    let base := evalSelectWithContext db outerRow (SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none)
    let offsetRows := match offset with | some n => base.drop n | none => base
    match limit with | some n => offsetRows.take n | none => offsetRows := by
  rw [evalSelectWithContext_eq_evalSelectCore, evalSelectWithContext_eq_evalSelectCore]
  exact evalSelectCore_limit_offset ..

/-- Infrastructure: evalQuery on a simple SELECT decomposes to evalSelect.
    Proved via evalQueryCore bridge. -/
theorem evalQuery_simple (db : Database) (sel : SelectStmt) :
    evalQuery db (.simple sel) = evalSelect db sel :=
  (evalQuery_eq_evalQueryCore_simple db sel).trans (evalQueryCore_simple ..)

/-- Infrastructure: evalQuery on a compound query decomposes into the set operation.
    Proved via evalQueryCore bridge. -/
theorem evalQuery_compound (db : Database) (left right : Query) (op : SetOp) :
    evalQuery db (.compound left op right) =
    applySetOp op (Query.outputNames? left) (evalQuery db left) (evalQuery db right) :=
  (evalQuery_eq_evalQueryCore_compound db left right op).trans (evalQueryCore_compound ..)

-- ============================================================================
-- Simple SELECT decomposition (for IN/EXISTS subquery proofs)
-- ============================================================================

/-- Simple SELECT items FROM from_ (no WHERE) evaluates to projecting each base row. -/
theorem evalSelectWithContext_simple_project (db : Database) (outerRow : Row)
    (items : List SelectItem) (from_ : FromClause)
    (hNoAgg : selectHasAggregate items = false)
    (hNoWin : selectHasWindowFn items = false) :
    evalSelectWithContext db outerRow
      (SelectStmt.mk false items (some from_) none [] none [] none none) =
    List.map (fun row => items.flatMap (evalSelectItem db row))
      (List.map (· ++ outerRow) (evalFrom db from_)) := by
  rw [evalSelectWithContext_eq_evalSelectCore]
  exact evalSelectCore_simple_project _ _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hNoWin

/-- Simple SELECT items FROM from_ WHERE cond evaluates to filtering then projecting. -/
theorem evalSelectWithContext_simple_project_where (db : Database) (outerRow : Row)
    (items : List SelectItem) (from_ : FromClause) (cond : Expr)
    (hNoAgg : selectHasAggregate items = false)
    (hNoWin : selectHasWindowFn items = false) :
    evalSelectWithContext db outerRow
      (SelectStmt.mk false items (some from_) (some cond) [] none [] none none) =
    List.map (fun row => items.flatMap (evalSelectItem db row))
      (List.filter (fun row => evalExprWithDb db row cond == some (Value.bool true))
        (List.map (· ++ outerRow) (evalFrom db from_))) := by
  rw [evalSelectWithContext_eq_evalSelectCore]
  exact evalSelectCore_simple_project_where _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hNoWin

-- ============================================================================
-- Filter combination infrastructure (proved via evalSelectCore bridge)
-- ============================================================================

/-- selectHasAggregate returns false for [.star none]. -/
private theorem selectHasAggregate_star : selectHasAggregate [.star none] = false := by rfl

/-- selectHasWindowFn returns false for [.star none]. -/
private theorem selectHasWindowFn_star : selectHasWindowFn [.star none] = false := by rfl

/-- evalSelectItem on .star none returns the row (now provable). -/
theorem evalSelectItem_star (db : Database) (row : Row) :
    evalSelectItem db row (.star none) = row := by
  simp [evalSelectItem]

/-- selectHasAggregate returns false for [.star (some t)]. -/
theorem selectHasAggregate_qualified_star (t : String) :
    selectHasAggregate [.star (some t)] = false := by rfl

/-- selectHasWindowFn returns false for [.star (some t)]. -/
theorem selectHasWindowFn_qualified_star (t : String) :
    selectHasWindowFn [.star (some t)] = false := by rfl

/-- evalSelectItem on .star (some t) filters to t-prefixed columns. -/
theorem evalSelectItem_qualified_star (db : Database) (row : Row) (t : String) :
    evalSelectItem db row (.star (some t)) =
    row.filter fun (k, _) => k.startsWith s!"{t}." := by
  simp [evalSelectItem]

/-- Helper: List.map (· ++ []) l = l (avoids simp/map_id matching issues). -/
private theorem list_map_nil_append_eq (l : Table) : l.map (· ++ []) = l := by
  induction l with
  | nil => rfl
  | cons h t ih => simp only [List.map_cons, List.append_nil] at ih ⊢; exact congrArg _ ih

/-- SELECT DISTINCT items FROM from_ = (project base rows), deduplicated by value key (#315) -/
theorem evalSelect_distinct_project (db : Database)
    (items : List SelectItem) (from_ : FromClause)
    (hNoAgg : selectHasAggregate items = false)
    (hNoWin : selectHasWindowFn items = false) :
    evalSelect db (SelectStmt.mk true items (some from_) none [] none [] none none) =
    dedupByKey Row.valueKey ((evalFrom db from_).map (fun row => items.flatMap (evalSelectItem db row))) := by
  have raw : evalSelect db (SelectStmt.mk true items (some from_) none [] none [] none none) =
    dedupByKey Row.valueKey (List.map (fun row => items.flatMap (evalSelectItem db row))
      (List.map (· ++ []) (evalFrom db from_))) := by
    rw [evalSelect_eq_evalSelectCore]
    exact evalSelectCore_distinct_project _ _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hNoWin
  rw [raw, list_map_nil_append_eq]

/-- SELECT DISTINCT items FROM from_ WHERE cond = (filter then project), deduplicated by value
    key (#315) -/
theorem evalSelect_distinct_project_where (db : Database)
    (items : List SelectItem) (from_ : FromClause) (cond : Expr)
    (hNoAgg : selectHasAggregate items = false)
    (hNoWin : selectHasWindowFn items = false) :
    evalSelect db (SelectStmt.mk true items (some from_) (some cond) [] none [] none none) =
    dedupByKey Row.valueKey
      ((evalFrom db from_).filter (fun row => evalExprWithDb db row cond == some (Value.bool true))
        |>.map (fun row => items.flatMap (evalSelectItem db row))) := by
  have raw : evalSelect db (SelectStmt.mk true items (some from_) (some cond) [] none [] none none) =
    dedupByKey Row.valueKey (List.map (fun row => items.flatMap (evalSelectItem db row))
      (List.filter (fun row => evalExprWithDb db row cond == some (Value.bool true))
        (List.map (· ++ []) (evalFrom db from_)))) := by
    rw [evalSelect_eq_evalSelectCore]
    exact evalSelectCore_distinct_project_where _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hNoWin
  rw [raw, list_map_nil_append_eq]

/-- SELECT items FROM from_ (non-distinct) = project base rows -/
theorem evalSelect_nondistinct_project (db : Database)
    (items : List SelectItem) (from_ : FromClause)
    (hNoAgg : selectHasAggregate items = false)
    (hNoWin : selectHasWindowFn items = false) :
    evalSelect db (SelectStmt.mk false items (some from_) none [] none [] none none) =
    (evalFrom db from_).map (fun row => items.flatMap (evalSelectItem db row)) := by
  have raw : evalSelect db (SelectStmt.mk false items (some from_) none [] none [] none none) =
    List.map (fun row => items.flatMap (evalSelectItem db row))
      (List.map (· ++ []) (evalFrom db from_)) := by
    rw [evalSelect_eq_evalSelectCore]
    exact evalSelectCore_simple_project _ _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hNoWin
  rw [raw, list_map_nil_append_eq]

/-- SELECT items FROM from_ WHERE cond (non-distinct) = filter then project -/
theorem evalSelect_nondistinct_project_where (db : Database)
    (items : List SelectItem) (from_ : FromClause) (cond : Expr)
    (hNoAgg : selectHasAggregate items = false)
    (hNoWin : selectHasWindowFn items = false) :
    evalSelect db (SelectStmt.mk false items (some from_) (some cond) [] none [] none none) =
    ((evalFrom db from_).filter (fun row => evalExprWithDb db row cond == some (Value.bool true))
      |>.map (fun row => items.flatMap (evalSelectItem db row))) := by
  have raw : evalSelect db (SelectStmt.mk false items (some from_) (some cond) [] none [] none none) =
    List.map (fun row => items.flatMap (evalSelectItem db row))
      (List.filter (fun row => evalExprWithDb db row cond == some (Value.bool true))
        (List.map (· ++ []) (evalFrom db from_))) := by
    rw [evalSelect_eq_evalSelectCore]
    exact evalSelectCore_simple_project_where _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hNoWin
  rw [raw, list_map_nil_append_eq]

/-- AND distributes over == some true for evalExprWithDb. -/
private theorem evalExprWithDb_and_true_iff (db : Database) (row : Row) (p q : Expr) :
    (evalExprWithDb db row (.binOp .and p q) == some (.bool true)) =
    ((evalExprWithDb db row p == some (.bool true)) && (evalExprWithDb db row q == some (.bool true))) := by
  rw [evalExprWithDb_binOp]
  exact evalBinOp_and_true_iff _ _

/-- Infrastructure: SELECT * FROM from_ WHERE p (all trivial options) = filter of base rows. -/
theorem evalSelect_star_where_eq_filter (db : Database) (from_ : Option FromClause) (p : Expr) :
    evalSelect db (.mk false [.star none] from_ (some p) [] none [] none none) =
    let baseRows := match from_ with | some f => evalFrom db f | none => [[]]
    (baseRows.map fun row => row ++ ([] : Row)).filter fun row =>
      evalExprWithDb db row p == some (Value.bool true) := by
  rw [evalSelect_eq_evalSelectCore]
  exact evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _
    selectHasAggregate_star selectHasWindowFn_star (fun db' row => evalSelectItem_star db' row)

/-- The derived table `(SELECT * FROM t WHERE r) AS q`, with `q` the table's
    own qualifier, evaluates to its inner SELECT: base rows are keyed `q.col`,
    so re-qualifying them by `q` renames nothing (#257, #269). -/
theorem evalFrom_filtered_table (db : Database) (t : TableRef) (r : Expr) :
    evalFrom db (.subquery (.simple (.mk false [.star none] (some (.table t)) (some r) [] none [] none none))
      (t.alias.getD t.name)) =
    evalSelect db (.mk false [.star none] (some (.table t)) (some r) [] none [] none none) := by
  rw [evalFrom_subquery_simple]
  refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
  intro row hrow
  rw [evalSelect_star_where_eq_filter] at hrow
  simp only [List.mem_filter, List.mem_map, List.append_nil] at hrow
  obtain ⟨⟨r', hr', rfl⟩, _⟩ := hrow
  exact requalifyRow_table_row db t r' hr'

/-- Bridge from `evalFrom_filtered_table` to `evalSelectCore`. -/
private theorem evalFrom_filtered_core (db : Database) (t : TableRef) (r : Expr) :
    evalFrom db (.subquery (.simple (.mk false [.star none] (some (.table t)) (some r) [] none [] none none))
      (t.alias.getD t.name)) =
    evalSelectCore db []
      (fun db' fc => evalFrom db' fc)
      ee
      (evalSelectItemParam ee)
      (evalSelectItemWithAggParam ee)
      (evalExprWithAggParam ee)
      (compareByOrderItemsParam ee)
      (evalExprWithWindowParam ee)
      selectHasWindowFn
      selectHasAggregate
      (.mk false [.star none] (some (.table t)) (some r) [] none [] none none) := by
  rw [evalFrom_filtered_table, evalSelect_eq_evalSelectCore]

/-- Infrastructure: filter_and at the evalSelect level.
    SELECT items FROM (SELECT * FROM t WHERE p) AS t WHERE q ...
    = SELECT items FROM t WHERE (p AND q) ... -/
theorem evalSelect_filter_and (db : Database) (items : List SelectItem) (t : TableRef)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.simple (.mk false [.star none] (some (.table t)) (some p) [] none [] none none)) (t.alias.getD t.name)))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.table t)) (some (.binOp .and p q)) groupBy having orderBy limit offset) := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  apply evalSelectCore_filter_and
  · exact selectHasAggregate_star
  · exact selectHasWindowFn_star
  · intro db' row; exact evalSelectItem_star db' row
  · intro r; exact evalFrom_filtered_core db t r
  · intro row; exact evalExprWithDb_and_true_iff db row p q

/-- Infrastructure: filter_commute at the evalSelect level.
    SELECT items FROM (SELECT * FROM t WHERE p) AS t WHERE q ...
    = SELECT items FROM (SELECT * FROM t WHERE q) AS t WHERE p ... -/
theorem evalSelect_filter_commute (db : Database) (items : List SelectItem) (t : TableRef)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.simple (.mk false [.star none] (some (.table t)) (some p) [] none [] none none)) (t.alias.getD t.name)))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items
      (some (.subquery (.simple (.mk false [.star none] (some (.table t)) (some q) [] none [] none none)) (t.alias.getD t.name)))
      (some p) groupBy having orderBy limit offset) := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  apply evalSelectCore_filter_commute
  · exact selectHasAggregate_star
  · exact selectHasWindowFn_star
  · intro db' row; exact evalSelectItem_star db' row
  · intro r; exact evalFrom_filtered_core db t r

/-- Infrastructure: filter_idempotent at the evalSelect level.
    SELECT items FROM (SELECT * FROM t WHERE p) AS t WHERE p ...
    = SELECT items FROM t WHERE p ... -/
theorem evalSelect_filter_idempotent (db : Database) (items : List SelectItem) (t : TableRef)
    (p : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.simple (.mk false [.star none] (some (.table t)) (some p) [] none [] none none)) (t.alias.getD t.name)))
      (some p) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.table t)) (some p) groupBy having orderBy limit offset) := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  apply evalSelectCore_filter_idempotent
  · exact selectHasAggregate_star
  · exact selectHasWindowFn_star
  · intro db' row; exact evalSelectItem_star db' row
  · intro r; exact evalFrom_filtered_core db t r

/-- Infrastructure: filter_pushdown_table at the evalSelect level.
    SELECT items FROM t WHERE filter ... = SELECT items FROM (SELECT * FROM t WHERE filter) AS t ... -/
theorem evalSelect_filter_pushdown_table (db : Database) (items : List SelectItem)
    (t : TableRef) (filter : Expr)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items (some (.table t)) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items
      (some (.subquery (.simple (.mk false [.star none] (some (.table t)) (some filter) [] none [] none none)) (t.alias.getD t.name)))
      none groupBy having orderBy limit offset) := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  apply evalSelectCore_filter_pushdown_table
  · exact selectHasAggregate_star
  · exact selectHasWindowFn_star
  · intro db' row; exact evalSelectItem_star db' row
  · intro r; exact evalFrom_filtered_core db t r

/-- Infrastructure: predicate_pushdown at the evalSelect level.
    (evalSelect db (SELECT * FROM t WHERE p)).filter q = evalSelect db (SELECT * FROM t WHERE (p AND q)) -/
theorem evalSelect_predicate_pushdown (db : Database) (t : String) (p q : Expr) :
    let inner := SelectStmt.mk false [.star none] (some (.table ⟨t, none⟩)) (some p) [] none [] none none
    let outer := SelectStmt.mk false [.star none] (some (.table ⟨t, none⟩)) (some (.binOp .and p q)) [] none [] none none
    (evalSelect db inner).filter (fun row => evalExprWithDb db row q == some (.bool true)) = evalSelect db outer := by
  simp only []
  rw [evalSelect_star_where_eq_filter db (some (.table ⟨t, none⟩)) p,
      evalSelect_star_where_eq_filter db (some (.table ⟨t, none⟩)) (.binOp .and p q)]
  simp only [List.append_nil, List.map_id']
  rw [← list_filter_and_eq]
  congr 1; funext row
  exact (evalExprWithDb_and_true_iff db row p q).symm

/-- A WHERE over FROM `f1` equals no WHERE over FROM `f2` when `f2`'s rows are
    exactly `f1`'s rows that pass the filter. -/
theorem evalSelect_where_to_from (db : Database) (items : List SelectItem)
    (f1 f2 : FromClause) (filter : Expr)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h : evalFrom db f2 =
      (evalFrom db f1).filter (fun row => evalExprWithDb db row filter == some (Value.bool true))) :
    evalSelect db (.mk false items (some f1) (some filter) groupBy having orderBy limit offset) =
      evalSelect db (.mk false items (some f2) none groupBy having orderBy limit offset) := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  simp only [evalSelectCore_eq_afterFilter]
  congr 1
  simp only [List.append_nil, List.map_id']
  rw [h]

/-- Infrastructure: filter pushdown through an inner join to the left side,
    for a left table `ta` wrapped as a derived table named after its own
    qualifier (#269). When the filter evaluates the same on `lr ++ rr` as on
    `lr` alone, filtering the join equals joining the filtered table. -/
theorem evalSelect_filter_join_left (db : Database) (ta : TableRef) (b : FromClause) (cond filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_filter_left : ∀ lr ∈ evalFrom db (.table ta), ∀ rr ∈ evalFrom db b,
        evalExprWithDb db (lr ++ rr) filter = evalExprWithDb db lr filter) :
    evalSelect db (.mk false items (some (.join (.table ta) .inner b (some cond))) (some filter)
      groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join (.subquery (.simple (.mk false [.star none] (some (.table ta))
      (some filter) [] none [] none none)) (ta.alias.getD ta.name)) .inner b (some cond)))
      none groupBy having orderBy limit offset) := by
  apply evalSelect_where_to_from
  symm
  rw [evalFrom_inner_join, evalFrom_inner_join (db := db) (left := .subquery _ _),
    evalFrom_filtered_table, evalSelect_star_where_eq_filter]
  simp only [List.append_nil, List.map_id']
  apply list_flatMap_filter_comm
  intro lr hlr combined hcombined
  simp only [List.mem_filterMap] at hcombined
  obtain ⟨rr, hrr, hfm⟩ := hcombined
  split at hfm
  · simp only [Option.some.injEq] at hfm; subst hfm
    congr 1
    exact h_filter_left lr hlr rr hrr
  · simp at hfm

/-- Infrastructure: filter pushdown through an inner join to the right side,
    for a right table `tb` wrapped as a derived table named after its own
    qualifier (#269). -/
theorem evalSelect_filter_join_right (db : Database) (a : FromClause) (tb : TableRef) (cond filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_filter_right : ∀ lr ∈ evalFrom db a, ∀ rr ∈ evalFrom db (.table tb),
        evalExprWithDb db (lr ++ rr) filter = evalExprWithDb db rr filter) :
    evalSelect db (.mk false items (some (.join a .inner (.table tb) (some cond))) (some filter)
      groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join a .inner (.subquery (.simple (.mk false [.star none] (some (.table tb))
      (some filter) [] none [] none none)) (tb.alias.getD tb.name)) (some cond)))
      none groupBy having orderBy limit offset) := by
  apply evalSelect_where_to_from
  symm
  rw [evalFrom_inner_join, evalFrom_inner_join (db := db) (right := .subquery _ _),
    evalFrom_filtered_table, evalSelect_star_where_eq_filter]
  simp only [List.append_nil, List.map_id']
  rw [List.filter_flatMap]
  apply flatMap_congr_mem
  intro lr hlr
  apply list_filter_filterMap_comm
  intro rr hrr combined hfm
  split at hfm
  · simp only [Option.some.injEq] at hfm; subst hfm
    congr 1
    exact h_filter_right lr hlr rr hrr
  · simp at hfm

/-- Evaluate any statement -/
def evalStmt (db : Database) : Stmt → Database × Option Table
  | .query q => (db, some (evalQuery db q))
  | .insert i => (evalInsert db i, none)
  | .update u => (evalUpdate db u, none)
  | .delete d => (evalDelete db d, none)

end SqlEquiv
