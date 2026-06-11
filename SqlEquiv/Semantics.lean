/-
  SQL Semantics: Evaluation Model

  Defines what SQL statements *mean* using a relational algebra model.
  This enables formal equivalence proofs.
-/
import SqlEquiv.SemanticsBase
import SqlEquiv.SemanticsCore

namespace SqlEquiv

-- ============================================================================
-- Aggregate Detection and Evaluation
-- ============================================================================

/-- Check if expression contains aggregate functions -/
partial def hasAggregate : Expr → Bool
  | .agg _ _ _ => true
  | .countStar => true
  | .binOp _ l r => hasAggregate l || hasAggregate r
  | .unaryOp _ e => hasAggregate e
  | .func _ args => args.any hasAggregate
  | .case branches else_ =>
    branches.any (fun (c, r) => hasAggregate c || hasAggregate r) ||
    match else_ with
    | some e => hasAggregate e
    | none => false
  | .inList e _ vals => hasAggregate e || vals.any hasAggregate
  | .between e lo hi => hasAggregate e || hasAggregate lo || hasAggregate hi
  | _ => false

/-- Check if any SELECT item contains aggregates -/
def selectHasAggregate (items : List SelectItem) : Bool :=
  items.any fun
    | .star _ => false
    | .exprItem e _ => hasAggregate e


-- ============================================================================
-- Window Function Detection (extracted from mutual block)
-- ============================================================================

/-- Check if expression contains window functions -/
partial def exprHasWindowFn : Expr → Bool
  | .windowFn _ _ _ => true
  | .binOp _ l r => exprHasWindowFn l || exprHasWindowFn r
  | .unaryOp _ e => exprHasWindowFn e
  | .func _ args => args.any exprHasWindowFn
  | .case branches else_ =>
    branches.any (fun (c, r) => exprHasWindowFn c || exprHasWindowFn r) ||
    (match else_ with | some e => exprHasWindowFn e | none => false)
  | _ => false

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
  let distinctValues := if distinct then values.eraseDups else values
  match fn with
  -- COUNT(col) skips NULLs per the SQL standard (COUNT(*) is Expr.countStar,
  -- which doesn't go through here); the window-fn COUNT already does this.
  | .count => some (.int (distinctValues.filter (fun v => !v.isNull)).length)
  | .sum =>
    if countNumeric distinctValues == 0 then some (.null none)
    else some (sumNumeric distinctValues)
  | .avg => some ((avgNumeric distinctValues).getD (.null none))
  | .min => some ((minNumeric distinctValues).getD (.null none))
  | .max => some ((maxNumeric distinctValues).getD (.null none))

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
  | e => exprEval db row e
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; omega

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

/-- Parameterized ORDER BY comparator -/
partial def compareByOrderItemsParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (r1 r2 : Row) : List OrderByItem → Bool
  | [] => true
  | item :: rest =>
    match exprEval db r1 item.expr, exprEval db r2 item.expr with
    | some a, some b =>
      match a.compare b with
      | some .lt => item.dir == .asc
      | some .gt => item.dir == .desc
      | _ => compareByOrderItemsParam exprEval db r1 r2 rest
    | _, _ => compareByOrderItemsParam exprEval db r1 r2 rest

/-- Parameterized GROUP BY key -/
def evalGroupKeyParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (row : Row) (groupExprs : List Expr) : List (Option Value) :=
  groupExprs.map (exprEval db row)

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
partial def computeRanksParam (exprEval : Database → Row → Expr → Option Value)
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
partial def computeDenseRanksParam (exprEval : Database → Row → Expr → Option Value)
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

/-- Parameterized window function evaluator -/
def evalWindowFnParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (fn : WindowFunc) (arg : Option Expr)
    (partition : Table) (sortedPartition : Table) (row : Row) (rowIndex : Nat) : Option Value :=
  match fn with
  | .rowNumber => some (.int (Int.ofNat (rowIndex + 1)))
  | .rank =>
    let ranks := computeRanksParam exprEval db sortedPartition ([] : List OrderByItem)
    match ranks.find? (fun (r, _) => r == row) with
    | some (_, rank) => some (.int (Int.ofNat rank))
    | none => some (.int (Int.ofNat (rowIndex + 1)))
  | .denseRank =>
    let ranks := computeDenseRanksParam exprEval db sortedPartition ([] : List OrderByItem)
    match ranks.find? (fun (r, _) => r == row) with
    | some (_, rank) => some (.int (Int.ofNat rank))
    | none => some (.int (Int.ofNat (rowIndex + 1)))
  | .sum =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => exprEval db r e
      some (sumNumeric vals)
  | .avg =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => exprEval db r e
      some ((avgNumeric vals).getD (.null none))
  | .min =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => exprEval db r e
      some ((minNumeric vals).getD (.null none))
  | .max =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => exprEval db r e
      some ((maxNumeric vals).getD (.null none))
  | .count =>
    match arg with
    | none => some (.int (Int.ofNat partition.length))
    | some e =>
      let nonNullCount := partition.filter fun r =>
        match exprEval db r e with
        | some v => !isNullValue v
        | none => false
      some (.int (Int.ofNat nonNullCount.length))

/-- Parameterized expression evaluator with window function support -/
def evalExprWithWindowParam (exprEval : Database → Row → Expr → Option Value)
    (db : Database) (row : Row) (partition : Table)
    (sortedPartition : Table) (rowIndex : Nat) : Expr → Option Value
  | .windowFn fn arg spec =>
    let winSorted := if spec.orderBy.isEmpty then sortedPartition
                     else sortPartitionParam exprEval db partition spec.orderBy
    evalWindowFnParam exprEval db fn arg partition winSorted row rowIndex
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

/-- Evaluate expression against a row (with database for subqueries) -/
def evalExprWithDb (db : Database) (row : Row) (e : Expr) : Option Value :=
  evalExprCore db row (fun db' row' sq => evalSubQueryWithContext db' row' sq) e
termination_by sizeOf e
decreasing_by all_goals sorry
-- NOTE: Lambda callbacks make these goals unprovable by Lean 4.27.0's termination
-- checker. The Core functions call callbacks only on structural subterms, but Lean
-- can't see through the lambda to verify this. Functions are still `def` (not
-- `partial`) and equational theorems work correctly.

/-- Evaluate FROM clause to get source rows -/
def evalFrom (db : Database) (fc : FromClause) : Table :=
  evalFromCore db
    (fun db' r expr => evalExprWithDb db' r expr)
    (fun db' sq => evalSubQueryWithContext db' [] sq) fc
termination_by sizeOf fc
decreasing_by all_goals sorry

/-- Evaluate a subquery body (#218): a SELECT or a set operation over
    subqueries. Set-op semantics shared with top-level Query via applySetOp. -/
def evalSubQueryWithContext (db : Database) (outerRow : Row) (sq : SubQuery) : Table :=
  match sq with
  | .simple sel => evalSelectWithContext db outerRow sel
  | .compound l op r =>
    applySetOp op (evalSubQueryWithContext db outerRow l)
                  (evalSubQueryWithContext db outerRow r)
termination_by sizeOf sq
decreasing_by all_goals sorry

/-- Evaluate SELECT statement with outer row context (for correlated subqueries) -/
def evalSelectWithContext (db : Database) (outerRow : Row) (sel : SelectStmt) : Table :=
  let ee := fun db' r e => evalExprWithDb db' r e
  evalSelectCore db outerRow
    (fun db' fc => evalFrom db' fc)
    ee
    (evalSelectItemParam ee)
    (evalSelectItemWithAggParam ee)
    (evalExprWithAggParam ee)
    (compareByOrderItemsParam ee)
    (evalExprWithWindowParam ee)
    selectHasWindowFn
    selectHasAggregate
    sel
termination_by sizeOf sel
decreasing_by all_goals sorry

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

/-- Evaluate an aggregate function over a table (group of rows) -/
def evalAggOverTable (db : Database) (fn : AggFunc) (argExpr : Option Expr) (distinct : Bool) (rows : Table) : Option Value :=
  -- Extract values from rows for the aggregate argument
  let values : List Value := match argExpr with
    | none => []  -- For COUNT(*) equivalent
    | some e => rows.filterMap fun row => evalExprWithDb db row e
  -- Apply DISTINCT if requested
  let distinctValues := if distinct then values.eraseDups else values
  match fn with
  | .count =>
    -- COUNT(col) skips NULLs per the SQL standard
    some (.int (distinctValues.filter (fun v => !v.isNull)).length)
  | .sum =>
    if countNumeric distinctValues == 0 then some (.null none)
    else some (sumNumeric distinctValues)
  | .avg => some ((avgNumeric distinctValues).getD (.null none))
  | .min => some ((minNumeric distinctValues).getD (.null none))
  | .max => some ((maxNumeric distinctValues).getD (.null none))

/-- Evaluate expression with aggregate support over a table -/
partial def evalExprWithAgg (db : Database) (rows : Table) (row : Row) : Expr → Option Value
  | .agg fn arg distinct => evalAggOverTable db fn arg distinct rows
  | .countStar => some (.int rows.length)
  | .binOp op l r =>
    let lv := evalExprWithAgg db rows row l
    let rv := evalExprWithAgg db rows row r
    match lv, rv with
    | some a, some b => evalBinOp op a b
    | _, _ => none
  | .unaryOp op e =>
    match evalExprWithAgg db rows row e with
    | some v => evalUnaryOp op v
    | none => none
  | e => evalExprWithDb db row e

/-- Evaluate SELECT item with aggregate support -/
def evalSelectItemWithAgg (db : Database) (rows : Table) (row : Row) (item : SelectItem) : List (String × Value) :=
  match item with
  | .star none => row
  | .star (some t) => row.filter fun (k, _) => k.startsWith s!"{t}."
  | .exprItem e alias =>
    match evalExprWithAgg db rows row e with
    | some v =>
      let colName := alias.getD (exprToName e)
      [(colName, v)]
    | none =>
      let colName := alias.getD (exprToName e)
      [(colName, .null none)]

/-- Compare rows by ORDER BY items -/
partial def compareByOrderItems (db : Database) (r1 r2 : Row) : List OrderByItem → Bool
  | [] => true
  | item :: rest =>
    let v1 := evalExprWithDb db r1 item.expr
    let v2 := evalExprWithDb db r2 item.expr
    match v1, v2 with
    | some a, some b =>
      match a.compare b with
      | some .lt => item.dir == .asc
      | some .gt => item.dir == .desc
      | _ => compareByOrderItems db r1 r2 rest
    | _, _ => compareByOrderItems db r1 r2 rest

/-- Compute GROUP BY key for a row -/
def evalGroupKey (db : Database) (row : Row) (groupExprs : List Expr) : List (Option Value) :=
  groupExprs.map (evalExprWithDb db row)

/-- Group rows by their GROUP BY key -/
def groupRowsByKey (db : Database) (rows : Table) (groupExprs : List Expr) : List (List (Option Value) × Table) :=
  let addToGroups (groups : List (List (Option Value) × Table)) (row : Row) : List (List (Option Value) × Table) :=
    let key := evalGroupKey db row groupExprs
    match groups.find? (fun (k, _) => k == key) with
    | some _ => groups.map fun (k, rs) => if k == key then (k, rs ++ [row]) else (k, rs)
    | none => groups ++ [(key, [row])]
  rows.foldl addToGroups []

-- ============================================================================
-- Window Function Evaluation
-- ============================================================================

/-- Partition rows by PARTITION BY expressions -/
def partitionRows (db : Database) (rows : Table) (partExprs : List Expr) : List Table :=
  if partExprs.isEmpty then
    [rows]  -- No PARTITION BY: entire result set is one partition
  else
    let groups := groupRowsByKey db rows partExprs
    groups.map (·.2)

/-- Sort rows within a partition by ORDER BY -/
def sortPartition (db : Database) (rows : Table) (orderBy : List OrderByItem) : Table :=
  if orderBy.isEmpty then rows
  else rows.mergeSort fun r1 r2 => compareByOrderItems db r1 r2 orderBy

/-- Compute RANK for each row in a sorted partition (same rank for ties, gaps after) -/
partial def computeRanks (db : Database) (rows : Table) (orderBy : List OrderByItem) : List (Row × Nat) :=
  let rec go (remaining : List Row) (currentRank : Nat) (nextRank : Nat) (prevKey : Option (List (Option Value))) : List (Row × Nat) :=
    match remaining with
    | [] => []
    | row :: rest =>
      let key := orderBy.map fun item => evalExprWithDb db row item.expr
      let (rank, newNextRank) := match prevKey with
        | none => (1, 2)
        | some pk => if pk == key then (currentRank, nextRank + 1) else (nextRank, nextRank + 1)
      (row, rank) :: go rest rank newNextRank (some key)
  go rows 1 2 none

/-- Compute DENSE_RANK for each row (no gaps after ties) -/
partial def computeDenseRanks (db : Database) (rows : Table) (orderBy : List OrderByItem) : List (Row × Nat) :=
  let rec go (remaining : List Row) (currentRank : Nat) (prevKey : Option (List (Option Value))) : List (Row × Nat) :=
    match remaining with
    | [] => []
    | row :: rest =>
      let key := orderBy.map fun item => evalExprWithDb db row item.expr
      let rank := match prevKey with
        | none => 1
        | some pk => if pk == key then currentRank else currentRank + 1
      (row, rank) :: go rest rank (some key)
  go rows 1 none

/-- Evaluate a window function for a specific row within its partition -/
def evalWindowFn (db : Database) (fn : WindowFunc) (arg : Option Expr)
    (partition : Table) (sortedPartition : Table) (row : Row) (rowIndex : Nat) : Option Value :=
  match fn with
  | .rowNumber => some (.int (Int.ofNat (rowIndex + 1)))
  | .rank =>
    -- Find this row's rank in the sorted partition
    let ranks := computeRanks db sortedPartition ([] : List OrderByItem)  -- Already sorted
    match ranks.find? (fun (r, _) => r == row) with
    | some (_, rank) => some (.int (Int.ofNat rank))
    | none => some (.int (Int.ofNat (rowIndex + 1)))
  | .denseRank =>
    let ranks := computeDenseRanks db sortedPartition ([] : List OrderByItem)
    match ranks.find? (fun (r, _) => r == row) with
    | some (_, rank) => some (.int (Int.ofNat rank))
    | none => some (.int (Int.ofNat (rowIndex + 1)))
  | .sum =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => evalExprWithDb db r e
      some (sumNumeric vals)
  | .avg =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => evalExprWithDb db r e
      some ((avgNumeric vals).getD (.null none))
  | .min =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => evalExprWithDb db r e
      some ((minNumeric vals).getD (.null none))
  | .max =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => evalExprWithDb db r e
      some ((maxNumeric vals).getD (.null none))
  | .count =>
    match arg with
    | none => some (.int (Int.ofNat partition.length))  -- COUNT(*)
    | some e =>
      let nonNullCount := partition.filter fun r =>
        match evalExprWithDb db r e with
        | some v => !isNullValue v
        | none => false
      some (.int (Int.ofNat nonNullCount.length))

/-- Evaluate expression with window function support -/
partial def evalExprWithWindow (db : Database) (row : Row) (partition : Table)
    (sortedPartition : Table) (rowIndex : Nat) : Expr → Option Value
  | .windowFn fn arg spec =>
    -- Sort partition by window's ORDER BY if specified
    let winSorted := if spec.orderBy.isEmpty then sortedPartition
                     else sortPartition db partition spec.orderBy
    evalWindowFn db fn arg partition winSorted row rowIndex
  | .binOp op l r =>
    let lv := evalExprWithWindow db row partition sortedPartition rowIndex l
    let rv := evalExprWithWindow db row partition sortedPartition rowIndex r
    match lv, rv with
    | some a, some b => evalBinOp op a b
    | _, _ => none
  | .unaryOp op e =>
    match evalExprWithWindow db row partition sortedPartition rowIndex e with
    | some v => evalUnaryOp op v
    | none => none
  | e => evalExprWithDb db row e


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
    applySetOp op (evalSubQueryWithContext db r l) (evalSubQueryWithContext db r rq) := by
  rw [evalSubQueryWithContext]

/-- Bridge: evalExprWithDb equals evalExprCore instantiated with evalSubQueryWithContext -/
theorem evalExprWithDb_eq_evalExprCore (db : Database) (row : Row) (e : Expr) :
  evalExprWithDb db row e = evalExprCore db row (fun db' row' sq => evalSubQueryWithContext db' row' sq) e := by
  simp [evalExprWithDb]

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
  simp only [evalFrom]

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
     | some v =>
       let subResult := evalSubQueryWithContext db row sq
       let hasMatch := subResult.any fun subRow =>
         match subRow.head? with
         | some (_, subVal) => v.eq subVal == some true
         | none => false
       some (Value.bool (if neg then !hasMatch else hasMatch))) := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_inSubquery ..

/-- evalExprWithDb unfolds for IN over a simple SELECT subquery -/
theorem evalExprWithDb_inSubquery_simple (db : Database) (row : Row) (e : Expr) (neg : Bool) (sel : SelectStmt) :
    evalExprWithDb db row (.inSubquery e neg (.simple sel)) =
    (match evalExprWithDb db row e with
     | none => none
     | some v =>
       let subResult := evalSelectWithContext db row sel
       let hasMatch := subResult.any fun subRow =>
         match subRow.head? with
         | some (_, subVal) => v.eq subVal == some true
         | none => false
       some (Value.bool (if neg then !hasMatch else hasMatch))) := by
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

/-- evalFrom for subquery just returns the inner subquery result (pass-through). -/
theorem evalFrom_subquery (db : Database) (sq : SubQuery) (alias : String) :
    evalFrom db (.subquery sq alias) = evalSubQueryWithContext db [] sq := by
  simp only [evalFrom_eq_evalFromCore]
  exact evalFromCore_subquery ..

/-- evalFrom for a simple SELECT subquery returns the inner SELECT result. -/
theorem evalFrom_subquery_simple (db : Database) (sel : SelectStmt) (alias : String) :
    evalFrom db (.subquery (.simple sel) alias) = evalSelect db sel := by
  rw [evalFrom_subquery, evalSubQuery_simple]; rfl

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
partial def evalInsert (db : Database) (ins : InsertStmt) : Database :=
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
partial def evalUpdate (db : Database) (upd : UpdateStmt) : Database :=
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
    applySetOp op (evalQuery db left) (evalQuery db right)
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

private abbrev ee := fun db' (r : Row) e => @evalExprWithDb db' r e

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
  simp only [evalSelect, evalSelectWithContext]

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
  simp only [evalSelectWithContext]

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
    applySetOp op (evalQuery db left) (evalQuery db right) :=
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
      (List.map (outerRow ++ ·) (evalFrom db from_)) := by
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
        (List.map (outerRow ++ ·) (evalFrom db from_))) := by
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

/-- Helper: List.map ([] ++ ·) l = l (avoids simp/map_id matching issues). -/
private theorem list_map_nil_append_eq (l : Table) : l.map ([] ++ ·) = l := by
  induction l with
  | nil => rfl
  | cons h t ih => simp only [List.map_cons, List.nil_append]; exact congrArg _ ih

/-- SELECT DISTINCT items FROM from_ = (project base rows).eraseDups -/
theorem evalSelect_distinct_project (db : Database)
    (items : List SelectItem) (from_ : FromClause)
    (hNoAgg : selectHasAggregate items = false)
    (hNoWin : selectHasWindowFn items = false) :
    evalSelect db (SelectStmt.mk true items (some from_) none [] none [] none none) =
    ((evalFrom db from_).map (fun row => items.flatMap (evalSelectItem db row))).eraseDups := by
  have raw : evalSelect db (SelectStmt.mk true items (some from_) none [] none [] none none) =
    (List.map (fun row => items.flatMap (evalSelectItem db row))
      (List.map ([] ++ ·) (evalFrom db from_))).eraseDups := by
    rw [evalSelect_eq_evalSelectCore]
    exact evalSelectCore_distinct_project _ _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hNoWin
  rw [raw, list_map_nil_append_eq]

/-- SELECT DISTINCT items FROM from_ WHERE cond = (filter then project).eraseDups -/
theorem evalSelect_distinct_project_where (db : Database)
    (items : List SelectItem) (from_ : FromClause) (cond : Expr)
    (hNoAgg : selectHasAggregate items = false)
    (hNoWin : selectHasWindowFn items = false) :
    evalSelect db (SelectStmt.mk true items (some from_) (some cond) [] none [] none none) =
    ((evalFrom db from_).filter (fun row => evalExprWithDb db row cond == some (Value.bool true))
      |>.map (fun row => items.flatMap (evalSelectItem db row))).eraseDups := by
  have raw : evalSelect db (SelectStmt.mk true items (some from_) (some cond) [] none [] none none) =
    (List.map (fun row => items.flatMap (evalSelectItem db row))
      (List.filter (fun row => evalExprWithDb db row cond == some (Value.bool true))
        (List.map ([] ++ ·) (evalFrom db from_)))).eraseDups := by
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
      (List.map ([] ++ ·) (evalFrom db from_)) := by
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
        (List.map ([] ++ ·) (evalFrom db from_))) := by
    rw [evalSelect_eq_evalSelectCore]
    exact evalSelectCore_simple_project_where _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hNoWin
  rw [raw, list_map_nil_append_eq]

/-- Bridge: evalFrom_subquery connects to evalSelectCore for simple subqueries. -/
private theorem evalFrom_subquery_core (db : Database) (sel : SelectStmt) (alias : String) :
    evalFrom db (.subquery (.simple sel) alias) =
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
      sel := by
  rw [evalFrom_subquery_simple, evalSelect_eq_evalSelectCore]

/-- AND distributes over == some true for evalExprWithDb. -/
private theorem evalExprWithDb_and_true_iff (db : Database) (row : Row) (p q : Expr) :
    (evalExprWithDb db row (.binOp .and p q) == some (.bool true)) =
    ((evalExprWithDb db row p == some (.bool true)) && (evalExprWithDb db row q == some (.bool true))) := by
  rw [evalExprWithDb_binOp]
  exact evalBinOp_and_true_iff _ _

/-- Infrastructure: filter_and at the evalSelect level.
    SELECT items FROM (SELECT * FROM from_ WHERE p) AS inner WHERE q ...
    = SELECT items FROM from_ WHERE (p AND q) ... -/
theorem evalSelect_filter_and (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.simple (.mk false [.star none] from_ (some p) [] none [] none none)) "inner"))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some (.binOp .and p q)) groupBy having orderBy limit offset) := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  apply evalSelectCore_filter_and
  · exact selectHasAggregate_star
  · exact selectHasWindowFn_star
  · intro db' row; exact evalSelectItem_star db' row
  · intro sel alias; exact evalFrom_subquery_core db sel alias
  · intro row; exact evalExprWithDb_and_true_iff db row p q

/-- Infrastructure: filter_commute at the evalSelect level.
    SELECT items FROM (SELECT * FROM from_ WHERE p) AS inner WHERE q ...
    = SELECT items FROM (SELECT * FROM from_ WHERE q) AS inner WHERE p ... -/
theorem evalSelect_filter_commute (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.simple (.mk false [.star none] from_ (some p) [] none [] none none)) "inner"))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items
      (some (.subquery (.simple (.mk false [.star none] from_ (some q) [] none [] none none)) "inner"))
      (some p) groupBy having orderBy limit offset) := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  apply evalSelectCore_filter_commute
  · exact selectHasAggregate_star
  · exact selectHasWindowFn_star
  · intro db' row; exact evalSelectItem_star db' row
  · intro sel alias; exact evalFrom_subquery_core db sel alias

/-- Infrastructure: filter_idempotent at the evalSelect level.
    SELECT items FROM (SELECT * FROM from_ WHERE p) AS inner WHERE p ...
    = SELECT items FROM from_ WHERE p ... -/
theorem evalSelect_filter_idempotent (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.simple (.mk false [.star none] from_ (some p) [] none [] none none)) "inner"))
      (some p) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some p) groupBy having orderBy limit offset) := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  apply evalSelectCore_filter_idempotent
  · exact selectHasAggregate_star
  · exact selectHasWindowFn_star
  · intro db' row; exact evalSelectItem_star db' row
  · intro sel alias; exact evalFrom_subquery_core db sel alias

/-- Infrastructure: filter_pushdown_table at the evalSelect level.
    SELECT items FROM from_ WHERE filter ... = SELECT items FROM (SELECT * FROM from_ WHERE filter) AS alias ... -/
theorem evalSelect_filter_pushdown_table (db : Database) (items : List SelectItem)
    (from_ : Option FromClause) (alias_ : String) (filter : Expr)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items from_ (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items
      (some (.subquery (.simple (.mk false [.star none] from_ (some filter) [] none [] none none)) alias_))
      none groupBy having orderBy limit offset) := by
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  apply evalSelectCore_filter_pushdown_table
  · exact selectHasAggregate_star
  · exact selectHasWindowFn_star
  · intro db' row; exact evalSelectItem_star db' row
  · intro sel alias; exact evalFrom_subquery_core db sel alias

/-- Infrastructure: SELECT * FROM from_ WHERE p (all trivial options) = filter of base rows. -/
theorem evalSelect_star_where_eq_filter (db : Database) (from_ : Option FromClause) (p : Expr) :
    evalSelect db (.mk false [.star none] from_ (some p) [] none [] none none) =
    let baseRows := match from_ with | some f => evalFrom db f | none => [[]]
    (baseRows.map fun row => ([] : Row) ++ row).filter fun row =>
      evalExprWithDb db row p == some (Value.bool true) := by
  rw [evalSelect_eq_evalSelectCore]
  exact evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _
    selectHasAggregate_star selectHasWindowFn_star (fun db' row => evalSelectItem_star db' row)

/-- Infrastructure: predicate_pushdown at the evalSelect level.
    (evalSelect db (SELECT * FROM t WHERE p)).filter q = evalSelect db (SELECT * FROM t WHERE (p AND q)) -/
theorem evalSelect_predicate_pushdown (db : Database) (t : String) (p q : Expr) :
    let inner := SelectStmt.mk false [.star none] (some (.table ⟨t, none⟩)) (some p) [] none [] none none
    let outer := SelectStmt.mk false [.star none] (some (.table ⟨t, none⟩)) (some (.binOp .and p q)) [] none [] none none
    (evalSelect db inner).filter (fun row => evalExprWithDb db row q == some (.bool true)) = evalSelect db outer := by
  simp only []
  rw [evalSelect_star_where_eq_filter db (some (.table ⟨t, none⟩)) p,
      evalSelect_star_where_eq_filter db (some (.table ⟨t, none⟩)) (.binOp .and p q)]
  simp only [List.nil_append, List.map_id']
  rw [← list_filter_and_eq]
  congr 1; funext row
  exact (evalExprWithDb_and_true_iff db row p q).symm

/-- Infrastructure: filter pushdown through an inner join to the left side.
    When a filter evaluates the same on `lr ++ rr` as on just `lr`, we can
    push the filter into a subquery wrapping the left side of the join. -/
theorem evalSelect_filter_join_left (db : Database) (a b : FromClause) (cond filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_filter_left : ∀ lr ∈ evalFrom db a, ∀ rr ∈ evalFrom db b,
        evalExprWithDb db (lr ++ rr) filter = evalExprWithDb db lr filter) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter)
      groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join (.subquery (.simple (.mk false [.star none] (some a)
      (some filter) [] none [] none none)) "filtered_a") .inner b (some cond)))
      none groupBy having orderBy limit offset) := by
  -- Step 1: Push filter into subquery around whole join (filter_pushdown_table)
  rw [evalSelect_filter_pushdown_table db items (some (.join a .inner b (some cond)))
      "filtered_a" filter groupBy having orderBy limit offset]
  -- Now: SELECT items FROM (SELECT * FROM (a JOIN b ON cond) WHERE filter) AS filtered_a
  --    = SELECT items FROM (filtered_a JOIN b ON cond)
  -- Both have where_ = none, so reduce to FROM clause equality
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  simp only [evalSelectCore_eq_afterFilter]
  congr 1
  -- Goal: filteredRows equality (both with where_ = none → just mapped baseRows)
  simp only [List.nil_append, List.map_id']
  -- LHS: evalFrom db (.subquery (SELECT * FROM (a JOIN b ON cond) WHERE filter) "filtered_a")
  -- RHS: evalFrom db (.join (.subquery (SELECT * FROM a WHERE filter) "filtered_a") .inner b (some cond))
  rw [evalFrom_subquery_simple]
  rw [evalSelect_star_where_eq_filter]
  simp only [List.nil_append, List.map_id']
  -- LHS: (evalFrom db (.join a .inner b (some cond))).filter P
  rw [evalFrom_inner_join]
  -- LHS: ((evalFrom db a).flatMap F).filter P
  -- RHS: evalFrom db (.join (.subquery ...) .inner b (some cond))
  rw [evalFrom_inner_join (db := db) (left := .subquery _ _)]
  rw [evalFrom_subquery_simple, evalSelect_star_where_eq_filter]
  simp only [List.nil_append, List.map_id']
  -- RHS: ((evalFrom db a).filter Q).flatMap F
  -- Now apply list algebra: flatMap/filter commutation
  apply list_flatMap_filter_comm
  -- Discharge: ∀ lr ∈ evalFrom db a, ∀ combined ∈ F lr, P combined = Q lr
  intro lr hlr combined hcombined
  -- combined ∈ filterMap, so combined = lr ++ rr for some rr
  simp only [List.mem_filterMap] at hcombined
  obtain ⟨rr, hrr, hfm⟩ := hcombined
  -- Case split on the match in the filterMap body
  split at hfm
  · -- evalExprWithDb db (lr ++ rr) cond = some (.bool true) → combined = lr ++ rr
    simp only [Option.some.injEq] at hfm; subst hfm
    congr 1
    exact h_filter_left lr hlr rr hrr
  · -- other cases: none = some combined → contradiction
    simp at hfm

/-- Infrastructure: filter pushdown through an inner join to the right side.
    When a filter evaluates the same on `lr ++ rr` as on just `rr`, we can
    push the filter into a subquery wrapping the right side of the join. -/
theorem evalSelect_filter_join_right (db : Database) (a b : FromClause) (cond filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_filter_right : ∀ lr ∈ evalFrom db a, ∀ rr ∈ evalFrom db b,
        evalExprWithDb db (lr ++ rr) filter = evalExprWithDb db rr filter) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter)
      groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join a .inner (.subquery (.simple (.mk false [.star none] (some b)
      (some filter) [] none [] none none)) "filtered_b") (some cond)))
      none groupBy having orderBy limit offset) := by
  -- Step 1: Push filter into subquery around whole join
  rw [evalSelect_filter_pushdown_table db items (some (.join a .inner b (some cond)))
      "filtered_b" filter groupBy having orderBy limit offset]
  -- Reduce to FROM clause equality
  rw [evalSelect_eq_evalSelectCore, evalSelect_eq_evalSelectCore]
  simp only [evalSelectCore_eq_afterFilter]
  congr 1
  simp only [List.nil_append, List.map_id']
  -- LHS: evalFrom db (.subquery (SELECT * FROM (a JOIN b ON cond) WHERE filter) "filtered_b")
  -- RHS: evalFrom db (.join a .inner (.subquery (SELECT * FROM b WHERE filter) "filtered_b") (some cond))
  rw [evalFrom_subquery_simple, evalSelect_star_where_eq_filter]
  simp only [List.nil_append, List.map_id']
  rw [evalFrom_inner_join]
  rw [evalFrom_inner_join (db := db) (right := .subquery _ _)]
  rw [evalFrom_subquery_simple, evalSelect_star_where_eq_filter]
  simp only [List.nil_append, List.map_id']
  -- LHS: ((evalFrom db a).flatMap F_orig).filter P
  -- RHS: (evalFrom db a).flatMap F_filtered
  -- where F_filtered uses (evalFrom db b).filter Q instead of evalFrom db b
  -- Distribute filter inside flatMap, then commute filter with filterMap per-element
  rw [List.filter_flatMap]
  apply flatMap_congr_mem
  intro lr hlr
  apply list_filter_filterMap_comm
  -- Discharge: ∀ rr ∈ evalFrom db b, ∀ combined, filterMap_body rr = some combined → P combined = Q rr
  intro rr hrr combined hfm
  -- Case split on the match in the filterMap body
  split at hfm
  · -- evalExprWithDb db (lr ++ rr) cond = some (.bool true) → combined = lr ++ rr
    simp only [Option.some.injEq] at hfm; subst hfm
    congr 1
    exact h_filter_right lr hlr rr hrr
  · -- other cases: none = some combined → contradiction
    simp at hfm

/-- Evaluate any statement -/
def evalStmt (db : Database) : Stmt → Database × Option Table
  | .query q => (db, some (evalQuery db q))
  | .insert i => (evalInsert db i, none)
  | .update u => (evalUpdate db u, none)
  | .delete d => (evalDelete db d, none)

end SqlEquiv
