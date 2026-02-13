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
-- Mutually Recursive Evaluation Functions
-- ============================================================================

mutual

/-- Evaluate expression against a row (with database for subqueries) -/
partial def evalExprWithDb (db : Database) (row : Row) : Expr → Option Value
  | .lit v => some v
  | .col c => row.getQualified c.table c.column
  | .binOp op l r => evalBinOp op (evalExprWithDb db row l) (evalExprWithDb db row r)
  | .unaryOp op e => evalUnaryOp op (evalExprWithDb db row e)
  | .func name args => evalFunc name (args.map (evalExprWithDb db row))
  | .agg _fn _arg _distinct =>
    -- Aggregates need group context, return null for single-row evaluation
    none
  | .countStar =>
    -- COUNT(*) needs group context
    none
  | .case branches else_ => evalCase db row branches else_
  | .inList e neg vals =>
    let ev := evalExprWithDb db row e
    let result := vals.foldl (fun acc vi =>
      evalBinOp .or acc (evalBinOp .eq ev (evalExprWithDb db row vi))
    ) (some (.bool false))
    if neg then evalUnaryOp .not result else result
  | .inSubquery e neg sel =>
    match evalExprWithDb db row e with
    | none => none
    | some v =>
      let subResult := evalSelectWithContext db row sel
      let hasMatch := subResult.any fun subRow =>
        match subRow.head? with
        | some (_, subVal) => v.eq subVal == some true
        | none => false
      some (Value.bool (if neg then !hasMatch else hasMatch))
  | .exists neg sel =>
    -- For correlated subqueries, pass the outer row context
    let subResult := evalSelectWithContext db row sel
    let hasExists := !subResult.isEmpty
    some (Value.bool (if neg then !hasExists else hasExists))
  | .subquery sel =>
    -- Scalar subquery - returns first column of first row
    match (evalSelectWithContext db row sel).head? with
    | some subRow => subRow.head?.map (·.2)
    | none => some (.null none)  -- Empty subquery returns NULL
  | .between e lo hi =>
    let ev := evalExprWithDb db row e
    let evlo := evalExprWithDb db row lo
    let evhi := evalExprWithDb db row hi
    evalBinOp .and (evalBinOp .ge ev evlo) (evalBinOp .le ev evhi)
  | .windowFn _fn _arg _spec =>
    -- Window functions need full partition context, return null for single-row evaluation
    none

/-- Helper for CASE expression evaluation -/
partial def evalCase (db : Database) (row : Row) (branches : List (Expr × Expr)) (else_ : Option Expr) : Option Value :=
  match branches with
  | [] =>
    match else_ with
    | some e => evalExprWithDb db row e
    | none => some (.null none)  -- SQL: CASE with no match and no ELSE returns NULL
  | (cond, result) :: rest =>
    match evalExprWithDb db row cond with
    | some (.bool true) => evalExprWithDb db row result
    | some (.bool false) => evalCase db row rest else_
    | _ => evalCase db row rest else_  -- NULL/unknown condition treated as no match (SQL spec)

/-- Evaluate FROM clause to get source rows -/
partial def evalFrom (db : Database) : FromClause → Table
  | .table t =>
    let baseTable := db t.name
    -- Qualify column names with table alias
    let qualifier := t.alias.getD t.name
    baseTable.map fun row =>
      row.map fun (col, val) => (s!"{qualifier}.{col}", val)
  | .subquery sel alias =>
    -- Evaluate subquery and qualify columns with alias.
    -- NOTE: This causes double-qualification when the subquery itself contains
    -- aliased tables. E.g., if the subquery selects from table "users" with alias
    -- "u", columns come out as "u.id". Wrapping with alias "filtered_a" then
    -- produces "filtered_a.u.id" instead of "filtered_a.id". This breaks axioms
    -- like filter_join_left/right that wrap one side of a join in a subquery,
    -- because the join condition still references the original qualifier ("u.id").
    -- See docs/PROVING_AXIOMS_PLAN.md "Known Evaluator Limitations" for details.
    let subResult := evalSelect db sel
    subResult.map fun row =>
      row.map fun (col, val) => (s!"{alias}.{col}", val)
  | .join left jtype right on_ =>
    let leftRows := evalFrom db left
    let rightRows := evalFrom db right
    match jtype with
    | .cross =>
      leftRows.flatMap fun lr =>
        rightRows.map fun rr => lr ++ rr
    | .inner =>
      leftRows.flatMap fun lr =>
        rightRows.filterMap fun rr =>
          let combined := lr ++ rr
          match on_ with
          | none => some combined
          | some cond =>
            match evalExprWithDb db combined cond with
            | some (.bool true) => some combined
            | _ => none
    | .left =>
      leftRows.flatMap fun lr =>
        let matchingRows := rightRows.filterMap fun rr =>
          let combined := lr ++ rr
          match on_ with
          | none => some combined
          | some cond =>
            match evalExprWithDb db combined cond with
            | some (.bool true) => some combined
            | _ => none
        if matchingRows.isEmpty then
          -- Return left row with NULLs for right columns
          match rightRows.head? with
          | some rightRow => [lr ++ rightRow.map fun (k, _) => (k, .null none)]
          | none => [lr]
        else
          matchingRows
    | .right =>
      rightRows.flatMap fun rr =>
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
          matchingRows
    | .full =>
      -- Full outer join: combine left + right outer joins
      evalFrom db (.join left .left right on_) ++
        (rightRows.filterMap fun rr =>
          let hasMatch := leftRows.any fun lr =>
            let combined := lr ++ rr
            match on_ with
            | none => true
            | some cond =>
              match evalExprWithDb db combined cond with
              | some (.bool true) => true
              | _ => false
          if hasMatch then none
          else match leftRows.head? with
            | some leftRow => some (leftRow.map (fun (k, _) => (k, .null none)) ++ rr)
            | none => some rr)

/-- Evaluate SELECT item to extract columns from row -/
partial def evalSelectItem (db : Database) (row : Row) : SelectItem → List (String × Value)
  | .star none =>
    -- Return all columns
    row
  | .star (some t) =>
    -- Return columns from specific table
    row.filter fun (k, _) => k.startsWith s!"{t}."
  | .exprItem e alias =>
    match evalExprWithDb db row e with
    | some v =>
      let colName := alias.getD (exprToName e)
      [(colName, v)]
    | none =>
      let colName := alias.getD (exprToName e)
      [(colName, .null none)]

/-- Evaluate an aggregate function over a table (group of rows) -/
partial def evalAggOverTable (db : Database) (fn : AggFunc) (argExpr : Option Expr) (distinct : Bool) (rows : Table) : Option Value :=
  -- Extract values from rows for the aggregate argument
  let values : List Value := match argExpr with
    | none => []  -- For COUNT(*) equivalent
    | some e => rows.filterMap fun row => evalExprWithDb db row e
  -- Apply DISTINCT if requested
  let distinctValues := if distinct then values.eraseDups else values
  match fn with
  | .count =>
    some (.int distinctValues.length)
  | .sum =>
    let nums := distinctValues.filterMap fun
      | .int n => some n
      | _ => none
    if nums.isEmpty then some (.null none)
    else some (.int (nums.foldl (· + ·) 0))
  | .avg =>
    let nums := distinctValues.filterMap fun
      | .int n => some n
      | _ => none
    if nums.isEmpty then some (.null none)
    else some (.int (nums.foldl (· + ·) 0 / nums.length))
  | .min =>
    let nums := distinctValues.filterMap fun
      | .int n => some n
      | _ => none
    match nums with
    | [] => some (.null none)
    | n :: rest => some (.int (rest.foldl min n))
  | .max =>
    let nums := distinctValues.filterMap fun
      | .int n => some n
      | _ => none
    match nums with
    | [] => some (.null none)
    | n :: rest => some (.int (rest.foldl max n))

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
partial def evalSelectItemWithAgg (db : Database) (rows : Table) (row : Row) : SelectItem → List (String × Value)
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
partial def evalGroupKey (db : Database) (row : Row) (groupExprs : List Expr) : List (Option Value) :=
  groupExprs.map (evalExprWithDb db row)

/-- Group rows by their GROUP BY key -/
partial def groupRowsByKey (db : Database) (rows : Table) (groupExprs : List Expr) : List (List (Option Value) × Table) :=
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
partial def partitionRows (db : Database) (rows : Table) (partExprs : List Expr) : List Table :=
  if partExprs.isEmpty then
    [rows]  -- No PARTITION BY: entire result set is one partition
  else
    let groups := groupRowsByKey db rows partExprs
    groups.map (·.2)

/-- Sort rows within a partition by ORDER BY -/
partial def sortPartition (db : Database) (rows : Table) (orderBy : List OrderByItem) : Table :=
  if orderBy.isEmpty then rows
  else rows.mergeSort fun r1 r2 => compareByOrderItems db r1 r2 orderBy

/-- Compute ROW_NUMBER for each row in a sorted partition -/
partial def computeRowNumbers (rows : Table) : List (Row × Nat) :=
  (List.range rows.length).zip rows |>.map fun (i, row) => (row, i + 1)

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
partial def evalWindowFn (db : Database) (fn : WindowFunc) (arg : Option Expr)
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
      let intVals := vals.filterMap fun v => match v with | .int n => some n | _ => none
      some (.int (intVals.foldl (· + ·) 0))
  | .avg =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => evalExprWithDb db r e
      let intVals := vals.filterMap fun v => match v with | .int n => some n | _ => none
      if intVals.isEmpty then some (.null none)
      else some (.int (intVals.foldl (· + ·) 0 / Int.ofNat intVals.length))
  | .min =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => evalExprWithDb db r e
      let intVals := vals.filterMap fun v => match v with | .int n => some n | _ => none
      match intVals.foldl (fun acc n => match acc with | none => some n | some m => some (if m < n then m else n)) none with
      | some n => some (.int n)
      | none => some (.null none)
  | .max =>
    match arg with
    | none => none
    | some e =>
      let vals := partition.filterMap fun r => evalExprWithDb db r e
      let intVals := vals.filterMap fun v => match v with | .int n => some n | _ => none
      match intVals.foldl (fun acc n => match acc with | none => some n | some m => some (if m > n then m else n)) none with
      | some n => some (.int n)
      | none => some (.null none)
  | .count =>
    match arg with
    | none => some (.int (Int.ofNat partition.length))  -- COUNT(*)
    | some e =>
      let nonNullCount := partition.filter fun r =>
        match evalExprWithDb db r e with
        | some v => !isNullValue v
        | none => false
      some (.int (Int.ofNat nonNullCount.length))

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
partial def selectHasWindowFn (items : List SelectItem) : Bool :=
  items.any fun
    | .exprItem e _ => exprHasWindowFn e
    | _ => false

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

/-- Evaluate full SELECT statement -/
partial def evalSelect (db : Database) (sel : SelectStmt) : Table :=
  evalSelectWithContext db [] sel

/-- Evaluate SELECT statement with outer row context (for correlated subqueries) -/
partial def evalSelectWithContext (db : Database) (outerRow : Row) (sel : SelectStmt) : Table :=
  -- 1. FROM clause
  let baseRows : Table := match sel.fromClause with
    | some f => evalFrom db f
    | none => [[]]  -- Single empty row for SELECT without FROM

  -- Merge outer row context into each base row for correlated subqueries
  let baseRowsWithContext : Table := baseRows.map fun row => outerRow ++ row

  -- 2. WHERE clause
  let filteredRows : Table := match sel.whereClause with
    | some cond =>
      baseRowsWithContext.filter fun row =>
        evalExprWithDb db row cond == some (Value.bool true)
    | none => baseRowsWithContext

  -- 3. GROUP BY and 4. HAVING and 5. SELECT (projection)
  -- These are interrelated for aggregate queries
  let projectedRows : Table :=
    if !sel.groupBy.isEmpty then
      -- GROUP BY present: partition rows and evaluate aggregates per group
      let groups := groupRowsByKey db filteredRows sel.groupBy
      let groupResults := groups.filterMap fun (_key, groupRows) =>
        -- Use first row of group as representative for non-aggregate expressions
        match groupRows.head? with
        | none => none
        | some sampleRow =>
          -- Apply HAVING filter to group (evaluate with aggregate support)
          let passesHaving := match sel.having with
            | none => true
            | some cond =>
              evalExprWithAgg db groupRows sampleRow cond == some (Value.bool true)
          if passesHaving then
            some (sel.items.flatMap (evalSelectItemWithAgg db groupRows sampleRow))
          else
            none
      groupResults
    else if selectHasAggregate sel.items then
      -- Aggregates without GROUP BY: entire filtered table is one group
      let sampleRow := filteredRows.head?.getD []
      -- Apply HAVING filter
      let passesHaving := match sel.having with
        | none => true
        | some cond =>
          evalExprWithAgg db filteredRows sampleRow cond == some (Value.bool true)
      if passesHaving then
        [sel.items.flatMap (evalSelectItemWithAgg db filteredRows sampleRow)]
      else
        []
    else if selectHasWindowFn sel.items then
      -- Window functions present: evaluate with partition context
      let havingRows := match sel.having with
        | some cond =>
          filteredRows.filter fun row =>
            evalExprWithDb db row cond == some (Value.bool true)
        | none => filteredRows
      -- For window functions, we need to track row position within partitions
      -- For simplicity, treat entire result as one partition (no PARTITION BY in SELECT)
      let partition := havingRows
      let sortedPartition := havingRows  -- Will be sorted by window's ORDER BY if needed
      ((List.range havingRows.length).zip havingRows).map fun (idx, row) =>
        sel.items.flatMap fun item =>
          match item with
          | .star none => row
          | .star (some t) => row.filter fun (k, _) => k.startsWith s!"{t}."
          | .exprItem e alias =>
            match evalExprWithWindow db row partition sortedPartition idx e with
            | some v => [(alias.getD (exprToName e), v)]
            | none => [(alias.getD (exprToName e), .null none)]
    else
      -- No aggregates, no GROUP BY, no window functions: apply HAVING as regular filter, project each row
      let havingRows := match sel.having with
        | some cond =>
          filteredRows.filter fun row =>
            evalExprWithDb db row cond == some (Value.bool true)
        | none => filteredRows
      havingRows.map fun row => sel.items.flatMap (evalSelectItem db row)

  -- 6. DISTINCT
  let distinctRows : Table := if sel.distinct then
    projectedRows.eraseDups
  else
    projectedRows

  -- 7. ORDER BY
  let orderedRows : Table := if sel.orderBy.isEmpty then distinctRows else
    distinctRows.mergeSort fun r1 r2 =>
      compareByOrderItems db r1 r2 sel.orderBy

  -- 8. OFFSET and LIMIT
  let offsetRows : Table := match sel.offsetVal with
    | some n => orderedRows.drop n
    | none => orderedRows
  let limitRows : Table := match sel.limitVal with
    | some n => offsetRows.take n
    | none => offsetRows

  limitRows

end

/-- Simple evalExpr without database context (for backwards compatibility) -/
def evalExpr (row : Row) : Expr → Option Value :=
  evalExprWithDb (fun _ => []) row

-- ============================================================================
-- Bridge axioms: connect partial defs to non-partial core functions
-- ============================================================================

/-- Bridge: evalExprWithDb equals evalExprCore instantiated with evalSelectWithContext -/
axiom evalExprWithDb_eq_evalExprCore (db : Database) (row : Row) (e : Expr) :
  evalExprWithDb db row e = evalExprCore db row (fun db' row' sel => evalSelectWithContext db' row' sel) e

/-- Bridge: evalCase equals evalCaseHelper instantiated with evalExprCore/evalSelectWithContext -/
axiom evalCase_eq_evalCaseHelper (db : Database) (row : Row) (branches : List (Expr × Expr)) (else_ : Option Expr) :
  evalCase db row branches else_ =
    let sqe := fun db' row' sel => evalSelectWithContext db' row' sel
    let elseVal := match else_ with
      | some e => evalExprCore db row sqe e
      | none => some (.null none)
    evalCaseHelper (evalExprCore db row sqe) elseVal branches

/-- Bridge: evalFrom equals evalFromCore instantiated with evalExprWithDb and evalSelect -/
axiom evalFrom_eq_evalFromCore (db : Database) (fc : FromClause) :
  evalFrom db fc = evalFromCore db evalExprWithDb evalSelect fc

-- ============================================================================
-- Theorems: expression evaluation unfolding (proved via bridge axioms)
-- ============================================================================

/-- evalExprWithDb unfolds for literals -/
theorem evalExprWithDb_lit (db : Database) (row : Row) (v : Value) :
  evalExprWithDb db row (Expr.lit v) = some v := by
  rw [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_lit ..

/-- evalExprWithDb unfolds for binOp -/
theorem evalExprWithDb_binOp (db : Database) (row : Row) (op : BinOp) (l r : Expr) :
  evalExprWithDb db row (Expr.binOp op l r) = evalBinOp op (evalExprWithDb db row l) (evalExprWithDb db row r) := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_binOp ..

/-- evalExprWithDb unfolds for unaryOp -/
theorem evalExprWithDb_unaryOp (db : Database) (row : Row) (op : UnaryOp) (e : Expr) :
  evalExprWithDb db row (Expr.unaryOp op e) = evalUnaryOp op (evalExprWithDb db row e) := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_unaryOp ..

/-- evalExprWithDb unfolds for EXISTS expressions -/
theorem evalExprWithDb_exists (db : Database) (row : Row) (neg : Bool) (sel : SelectStmt) :
    evalExprWithDb db row (Expr.exists neg sel) =
    (let subResult := evalSelectWithContext db row sel
     let hasExists := !subResult.isEmpty
     some (Value.bool (if neg then !hasExists else hasExists))) := by
  simp only [evalExprWithDb_eq_evalExprCore]; exact evalExprCore_exists ..

/-- evalExprWithDb unfolds for case expressions -/
theorem evalExprWithDb_case (db : Database) (row : Row) (branches : List (Expr × Expr)) (else_ : Option Expr) :
  evalExprWithDb db row (Expr.case branches else_) = evalCase db row branches else_ := by
  have h1 := evalExprWithDb_eq_evalExprCore db row (Expr.case branches else_)
  have h2 := evalExprCore_case db row (fun db' row' sel => evalSelectWithContext db' row' sel) branches else_
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
  have hcore : evalExprCore db row (fun db' row' sel => evalSelectWithContext db' row' sel) cond = some (.bool true) := by
    rwa [← evalExprWithDb_eq_evalExprCore]
  rw [evalCase_eq_evalCaseHelper]
  simp [evalCaseHelper, hcore]
  exact (evalExprWithDb_eq_evalExprCore db row result).symm

/-- evalCase unfolds for cons branches when condition is false -/
theorem evalCase_cons_false (db : Database) (row : Row) (cond result : Expr) (rest : List (Expr × Expr)) (else_ : Option Expr) :
  evalExprWithDb db row cond = some (.bool false) →
  evalCase db row ((cond, result) :: rest) else_ = evalCase db row rest else_ := by
  intro h
  have hcore : evalExprCore db row (fun db' row' sel => evalSelectWithContext db' row' sel) cond = some (.bool false) := by
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

mutual
/-- Evaluate a recursive CTE using fixed-point iteration -/
partial def evalRecursiveCTE (db : Database) (cteName : String) (cteQuery : Query) : Table :=
  -- For recursive CTEs, iterate until fixed point (no new rows)
  -- Start with empty table for self-reference
  let rec iterate (workingTable : Table) (iteration : Nat) : Table :=
    if iteration >= maxCTEIterations then workingTable
    else
      -- Create database with current working table for CTE self-reference
      let dbWithCTE : Database := fun name =>
        if name == cteName then workingTable else db name
      let result := evalQuery dbWithCTE cteQuery
      -- Check for fixed point (no change)
      if result == workingTable then workingTable
      else iterate result (iteration + 1)
  -- Start iteration with empty table
  iterate [] 0

/-- Evaluate a Query (simple SELECT or compound with set operations) -/
partial def evalQuery (db : Database) : Query → Table
  | .simple sel => evalSelect db sel
  | .compound left op right =>
    let leftResult := evalQuery db left
    let rightResult := evalQuery db right
    match op with
    | .union => (leftResult ++ rightResult).eraseDups
    | .unionAll => leftResult ++ rightResult
    | .intersect => leftResult.filter fun row => rightResult.contains row
    | .exceptOp => leftResult.filter fun row => !rightResult.contains row
  | .withCTE ctes query =>
    -- Evaluate CTEs and add them to the database context
    let dbWithCtes := ctes.foldl (fun db' cte =>
      fun name =>
        if name == cte.name then
          if cte.isRecursive then
            evalRecursiveCTE db' cte.name cte.query
          else
            evalQuery db' cte.query
        else
          db' name
    ) db
    evalQuery dbWithCtes query
end

/-- Bridge: evalQuery equals evalQueryCore instantiated with evalSelect, evalQuery, evalRecursiveCTE -/
axiom evalQuery_eq_evalQueryCore (db : Database) (q : Query) :
  evalQuery db q = evalQueryCore db evalSelect evalQuery evalRecursiveCTE q

/-- Bridge: evalSelect equals evalSelectCore instantiated with all partial def callbacks -/
axiom evalSelect_eq_evalSelectCore (db : Database) (sel : SelectStmt) :
  evalSelect db sel = evalSelectCore db [] evalFrom evalExprWithDb
    (fun db row item => evalSelectItem db row item)
    (fun db groupRows sampleRow item => evalSelectItemWithAgg db groupRows sampleRow item)
    (fun db groupRows sampleRow cond => evalExprWithAgg db groupRows sampleRow cond)
    (fun db r1 r2 items => compareByOrderItems db r1 r2 items)
    (fun db row partition sorted idx e => evalExprWithWindow db row partition sorted idx e)
    (fun items => selectHasWindowFn items)
    (fun items => selectHasAggregate items)
    sel

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

/-- Infrastructure: evalQuery on a simple SELECT decomposes to evalSelect.
    Proved via evalQueryCore bridge. -/
theorem evalQuery_simple (db : Database) (sel : SelectStmt) :
    evalQuery db (.simple sel) = evalSelect db sel :=
  (evalQuery_eq_evalQueryCore db (.simple sel)).trans (evalQueryCore_simple ..)

/-- Infrastructure: evalQuery on a compound query decomposes into the set operation.
    Proved via evalQueryCore bridge. -/
theorem evalQuery_compound (db : Database) (left right : Query) (op : SetOp) :
    evalQuery db (.compound left op right) =
    let l : Table := evalQuery db left
    let r : Table := evalQuery db right
    match op with
    | .union => (l ++ r).eraseDups
    | .unionAll => l ++ r
    | .intersect => l.filter (r.contains ·)
    | .exceptOp => l.filter (!r.contains ·) :=
  (evalQuery_eq_evalQueryCore db (.compound left op right)).trans (evalQueryCore_compound ..)

/-- Evaluate any statement -/
def evalStmt (db : Database) : Stmt → Database × Option Table
  | .query q => (db, some (evalQuery db q))
  | .insert i => (evalInsert db i, none)
  | .update u => (evalUpdate db u, none)
  | .delete d => (evalDelete db d, none)

end SqlEquiv
