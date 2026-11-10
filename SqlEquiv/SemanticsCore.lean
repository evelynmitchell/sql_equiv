/-
  SQL Semantics: Non-Partial Core Evaluators

  Non-partial (total) versions of the expression and FROM evaluators,
  parameterized by subquery evaluation. These functions use well-founded
  recursion (termination_by sizeOf) so the kernel can unfold them,
  enabling proofs of infrastructure axioms via rfl.

  IMPORTANT: These must be in a separate file from the theorem proofs
  because WFR functions only reduce definitionally when imported from
  another module (not within the same file).
-/
import SqlEquiv.SemanticsBase

namespace SqlEquiv

-- ============================================================================
-- Non-Partial Core Evaluators
-- ============================================================================

/-- CASE branch evaluator, parameterized by expression evaluator.
    Defined outside the recursive evalExprCore so Lean's checker
    can see through it for structural recursion on Expr. -/
def evalCaseHelper (evalExpr : Expr → Option Value) (elseVal : Option Value) :
    List (Expr × Expr) → Option Value
  | [] => elseVal
  | (cond, result) :: rest =>
    match evalExpr cond with
    | some (.bool true) => evalExpr result
    | some (.bool false) => evalCaseHelper evalExpr elseVal rest
    | _ => evalCaseHelper evalExpr elseVal rest

/-- Non-partial expression evaluator, parameterized by subquery evaluation.
    Single recursive function (not mutual) — uses List.map and List.foldl
    which Lean's WFR checker has built-in support for. -/
def evalExprCore (db : Database) (row : Row)
    (subqueryEval : Database → Row → SubQuery → Table) : Expr → Option Value
  | .lit v => some v
  | .col c => row.getQualified c.table c.column
  | .binOp op l r =>
    evalBinOp op (evalExprCore db row subqueryEval l) (evalExprCore db row subqueryEval r)
  | .unaryOp op e => evalUnaryOp op (evalExprCore db row subqueryEval e)
  | .func name args => evalFunc name (args.map fun e => evalExprCore db row subqueryEval e)
  | .agg _fn _arg _distinct => none
  | .countStar => none
  | .case branches else_ =>
    let elseVal := match else_ with
      | some e => evalExprCore db row subqueryEval e
      | none => some (.null none)
    let result := branches.foldl (fun (found : Bool × Option Value) (pair : Expr × Expr) =>
      if found.1 then found
      else
        match evalExprCore db row subqueryEval pair.1 with
        | some (.bool true) => (true, evalExprCore db row subqueryEval pair.2)
        | _ => (false, none)
    ) (false, none)
    if result.1 then result.2 else elseVal
  | .inList e neg vals =>
    let ev := evalExprCore db row subqueryEval e
    let result := vals.foldl (fun acc vi =>
      evalBinOp .or acc (evalBinOp .eq ev (evalExprCore db row subqueryEval vi))
    ) (some (.bool false))
    if neg then evalUnaryOp .not result else result
  | .inSubquery e neg sel =>
    match evalExprCore db row subqueryEval e with
    | none => none
    | some v =>
      let subResult := subqueryEval db row sel
      let hasMatch := subResult.any fun subRow =>
        match subRow.head? with
        | some (_, subVal) => v.eq subVal == some true
        | none => false
      some (Value.bool (if neg then !hasMatch else hasMatch))
  | .exists neg sel =>
    let subResult := subqueryEval db row sel
    let hasExists := !subResult.isEmpty
    some (Value.bool (if neg then !hasExists else hasExists))
  | .subquery sel =>
    match (subqueryEval db row sel).head? with
    | some subRow => subRow.head?.map (·.2)
    | none => some (.null none)
  | .between e lo hi =>
    let ev := evalExprCore db row subqueryEval e
    let evlo := evalExprCore db row subqueryEval lo
    let evhi := evalExprCore db row subqueryEval hi
    evalBinOp .and (evalBinOp .ge ev evlo) (evalBinOp .le ev evhi)
  | .windowFn _fn _arg _spec => none
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

/-- Non-partial FROM clause evaluator, parameterized by expression and select evaluators -/
def evalFromCore (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectEval : Database → SubQuery → Table) : FromClause → Table
  | .table t =>
    let baseTable := db t.name
    let qualifier := t.alias.getD t.name
    baseTable.map fun row =>
      row.map fun (col, val) => (s!"{qualifier}.{col}", val)
  | .subquery sel _alias =>
    selectEval db sel
  | .join left jtype right on_ =>
    let leftRows := evalFromCore db exprEval selectEval left
    let rightRows := evalFromCore db exprEval selectEval right
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
            match exprEval db combined cond with
            | some (.bool true) => some combined
            | _ => none
    | .left =>
      leftRows.flatMap fun lr =>
        let matchingRows := rightRows.filterMap fun rr =>
          let combined := lr ++ rr
          match on_ with
          | none => some combined
          | some cond =>
            match exprEval db combined cond with
            | some (.bool true) => some combined
            | _ => none
        if matchingRows.isEmpty then
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
            match exprEval db combined cond with
            | some (.bool true) => some combined
            | _ => none
        if matchingRows.isEmpty then
          match leftRows.head? with
          | some leftRow => [leftRow.map (fun (k, _) => (k, .null none)) ++ rr]
          | none => [rr]
        else
          matchingRows
    | .full =>
      -- Inline the left join logic (can't call evalFromCore with same-sized argument)
      let leftJoinResult := leftRows.flatMap fun lr =>
        let matchingRows := rightRows.filterMap fun rr =>
          let combined := lr ++ rr
          match on_ with
          | none => some combined
          | some cond =>
            match exprEval db combined cond with
            | some (.bool true) => some combined
            | _ => none
        if matchingRows.isEmpty then
          match rightRows.head? with
          | some rightRow => [lr ++ rightRow.map fun (k, _) => (k, .null none)]
          | none => [lr]
        else
          matchingRows
      leftJoinResult ++
        (rightRows.filterMap fun rr =>
          let hasMatch := leftRows.any fun lr =>
            let combined := lr ++ rr
            match on_ with
            | none => true
            | some cond =>
              match exprEval db combined cond with
              | some (.bool true) => true
              | _ => false
          if hasMatch then none
          else match leftRows.head? with
            | some leftRow => some (leftRow.map (fun (k, _) => (k, .null none)) ++ rr)
            | none => some rr)

-- ============================================================================
-- Equational Theorems for evalExprCore
-- These are proved here (where simp [evalExprCore] works) and exported
-- for use in Semantics.lean where the partial defs block simp reduction.
-- ============================================================================

theorem evalExprCore_lit (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (v : Value) :
    evalExprCore db row sqe (.lit v) = some v := by
  simp [evalExprCore]

theorem evalExprCore_col (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (c : ColumnRef) :
    evalExprCore db row sqe (.col c) = row.getQualified c.table c.column := by
  simp [evalExprCore]

theorem evalExprCore_binOp (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (op : BinOp) (l r : Expr) :
    evalExprCore db row sqe (.binOp op l r) =
    evalBinOp op (evalExprCore db row sqe l) (evalExprCore db row sqe r) := by
  simp [evalExprCore]

theorem evalExprCore_unaryOp (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (op : UnaryOp) (e : Expr) :
    evalExprCore db row sqe (.unaryOp op e) =
    evalUnaryOp op (evalExprCore db row sqe e) := by
  simp [evalExprCore]

theorem evalExprCore_func (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (name : String) (args : List Expr) :
    evalExprCore db row sqe (.func name args) =
    evalFunc name (args.map fun e => evalExprCore db row sqe e) := by
  simp [evalExprCore]

theorem evalExprCore_between (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (e lo hi : Expr) :
    evalExprCore db row sqe (.between e lo hi) =
    evalBinOp .and (evalBinOp .ge (evalExprCore db row sqe e) (evalExprCore db row sqe lo))
                   (evalBinOp .le (evalExprCore db row sqe e) (evalExprCore db row sqe hi)) := by
  simp [evalExprCore]

theorem evalExprCore_inList (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (e : Expr) (neg : Bool) (vals : List Expr) :
    evalExprCore db row sqe (.inList e neg vals) =
    (let ev := evalExprCore db row sqe e
     let result := vals.foldl (fun acc vi =>
       evalBinOp .or acc (evalBinOp .eq ev (evalExprCore db row sqe vi))
     ) (some (.bool false))
     if neg then evalUnaryOp .not result else result) := by
  simp [evalExprCore]

theorem evalExprCore_exists (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (neg : Bool) (sel : SubQuery) :
    evalExprCore db row sqe (.exists neg sel) =
    (let subResult := sqe db row sel
     let hasExists := !subResult.isEmpty
     some (Value.bool (if neg then !hasExists else hasExists))) := by
  simp [evalExprCore]

/-- evalExprCore unfolds for scalar subquery expressions -/
theorem evalExprCore_subquery (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (sel : SubQuery) :
    evalExprCore db row sqe (.subquery sel) =
    (match (sqe db row sel).head? with
     | some subRow => subRow.head?.map (·.2)
     | none => some (.null none)) := by
  simp [evalExprCore]

/-- evalExprCore unfolds for IN subquery expressions -/
theorem evalExprCore_inSubquery (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (e : Expr) (neg : Bool) (sel : SubQuery) :
    evalExprCore db row sqe (.inSubquery e neg sel) =
    (match evalExprCore db row sqe e with
     | none => none
     | some v =>
       let subResult := sqe db row sel
       let hasMatch := subResult.any fun subRow =>
         match subRow.head? with
         | some (_, subVal) => v.eq subVal == some true
         | none => false
       some (Value.bool (if neg then !hasMatch else hasMatch))) := by
  simp [evalExprCore]

-- ============================================================================
-- Equational Theorems for evalExprCore CASE expression
-- ============================================================================

/-- Once the accumulator reaches (true, v), foldl preserves it. -/
private theorem case_foldl_found_invariant (f : Expr → Option Value)
    (v : Option Value) (branches : List (Expr × Expr)) :
    branches.foldl (fun (found : Bool × Option Value) (pair : Expr × Expr) =>
      if found.1 then found
      else match f pair.1 with
        | some (.bool true) => (true, f pair.2)
        | _ => (false, none)) (true, v) = (true, v) := by
  induction branches with
  | nil => rfl
  | cons _ _ ih => simp [List.foldl]; exact ih

/-- The foldl-based CASE in evalExprCore equals evalCaseHelper. -/
private theorem case_foldl_eq_evalCaseHelper (f : Expr → Option Value)
    (elseVal : Option Value) (branches : List (Expr × Expr)) :
    (let result := branches.foldl (fun (found : Bool × Option Value) (pair : Expr × Expr) =>
      if found.1 then found
      else match f pair.1 with
        | some (.bool true) => (true, f pair.2)
        | _ => (false, none)) (false, none)
     if result.1 then result.2 else elseVal) = evalCaseHelper f elseVal branches := by
  induction branches with
  | nil => simp [List.foldl, evalCaseHelper]
  | cons hd tl ih =>
    simp only [List.foldl, evalCaseHelper]
    generalize hc : f hd.fst = c
    cases c with
    | none => simp; exact ih
    | some v =>
      cases v with
      | bool b =>
        cases b with
        | true => simp [case_foldl_found_invariant]
        | false => simp; exact ih
      | int _ => simp; exact ih
      | string _ => simp; exact ih
      | decimal _ _ => simp; exact ih
      | null _ => simp; exact ih

/-- evalExprCore unfolds for CASE expressions to evalCaseHelper. -/
theorem evalExprCore_case (db : Database) (row : Row)
    (sqe : Database → Row → SubQuery → Table) (branches : List (Expr × Expr)) (else_ : Option Expr) :
    evalExprCore db row sqe (.case branches else_) =
    (let elseVal := match else_ with
      | some e => evalExprCore db row sqe e
      | none => some (.null none)
     evalCaseHelper (evalExprCore db row sqe) elseVal branches) := by
  rw [evalExprCore.eq_def]
  exact case_foldl_eq_evalCaseHelper ..

/-- evalCaseHelper unfolds for empty branches. -/
theorem evalCaseHelper_nil (f : Expr → Option Value) (elseVal : Option Value) :
    evalCaseHelper f elseVal [] = elseVal := by
  simp [evalCaseHelper]

/-- evalCaseHelper unfolds for cons when condition is true. -/
theorem evalCaseHelper_cons_true (f : Expr → Option Value) (elseVal : Option Value)
    (cond result : Expr) (rest : List (Expr × Expr))
    (h : f cond = some (.bool true)) :
    evalCaseHelper f elseVal ((cond, result) :: rest) = f result := by
  simp [evalCaseHelper, h]

/-- evalCaseHelper unfolds for cons when condition is false. -/
theorem evalCaseHelper_cons_false (f : Expr → Option Value) (elseVal : Option Value)
    (cond result : Expr) (rest : List (Expr × Expr))
    (h : f cond = some (.bool false)) :
    evalCaseHelper f elseVal ((cond, result) :: rest) = evalCaseHelper f elseVal rest := by
  simp [evalCaseHelper, h]

-- ============================================================================
-- Equational Theorems for evalFromCore
-- ============================================================================

theorem evalFromCore_table (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectEval : Database → SubQuery → Table)
    (t : TableRef) :
    evalFromCore db exprEval selectEval (.table t) =
    let qualifier := t.alias.getD t.name
    (db t.name).map fun row =>
      row.map fun (col, val) => (s!"{qualifier}.{col}", val) := by
  simp [evalFromCore]

theorem evalFromCore_subquery (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectEval : Database → SubQuery → Table)
    (sel : SubQuery) (alias : String) :
    evalFromCore db exprEval selectEval (.subquery sel alias) = selectEval db sel := by
  simp [evalFromCore]

theorem evalFromCore_cross_join (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectEval : Database → SubQuery → Table)
    (left right : FromClause) :
    evalFromCore db exprEval selectEval (.join left .cross right none) =
    let rightRows := evalFromCore db exprEval selectEval right
    (evalFromCore db exprEval selectEval left).flatMap fun lr =>
      rightRows.map fun rr => lr ++ rr := by
  simp [evalFromCore]

theorem evalFromCore_inner_join (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectEval : Database → SubQuery → Table)
    (left right : FromClause) (on_ : Option Expr) :
    evalFromCore db exprEval selectEval (.join left .inner right on_) =
    let rightRows := evalFromCore db exprEval selectEval right
    (evalFromCore db exprEval selectEval left).flatMap fun lr =>
      rightRows.filterMap fun rr =>
        let combined := lr ++ rr
        match on_ with
        | none => some combined
        | some cond =>
          match exprEval db combined cond with
          | some (.bool true) => some combined
          | _ => none := by
  simp [evalFromCore]

theorem evalFromCore_left_join (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectEval : Database → SubQuery → Table)
    (left right : FromClause) (on_ : Option Expr) :
    evalFromCore db exprEval selectEval (.join left .left right on_) =
    let rightRows := evalFromCore db exprEval selectEval right
    (evalFromCore db exprEval selectEval left).flatMap fun lr =>
      let matchingRows := rightRows.filterMap fun rr =>
        let combined := lr ++ rr
        match on_ with
        | none => some combined
        | some cond =>
          match exprEval db combined cond with
          | some (.bool true) => some combined
          | _ => none
      if matchingRows.isEmpty then
        match rightRows.head? with
        | some rightRow => [lr ++ rightRow.map fun (k, _) => (k, .null none)]
        | none => [lr]
      else
        matchingRows := by
  simp [evalFromCore]

theorem evalFromCore_right_join (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectEval : Database → SubQuery → Table)
    (left right : FromClause) (on_ : Option Expr) :
    evalFromCore db exprEval selectEval (.join left .right right on_) =
    let leftRows := evalFromCore db exprEval selectEval left
    (evalFromCore db exprEval selectEval right).flatMap fun rr =>
      let matchingRows := leftRows.filterMap fun lr =>
        let combined := lr ++ rr
        match on_ with
        | none => some combined
        | some cond =>
          match exprEval db combined cond with
          | some (.bool true) => some combined
          | _ => none
      if matchingRows.isEmpty then
        match leftRows.head? with
        | some leftRow => [leftRow.map (fun (k, _) => (k, .null none)) ++ rr]
        | none => [rr]
      else
        matchingRows := by
  simp [evalFromCore]

-- ============================================================================
-- Non-Partial Core Query Evaluator
-- ============================================================================

/-- Non-partial query evaluator, parameterized by evaluation callbacks.
    Not recursive — delegates to parameters for recursive calls. -/
def evalQueryCore (db : Database)
    (selectEval : Database → SelectStmt → Table)
    (queryEval : Database → Query → Table)
    (cteEval : Database → String → Query → Table) : Query → Table
  | .simple sel => selectEval db sel
  | .compound left op right =>
    applySetOp op (queryEval db left) (queryEval db right)
  | .withCTE ctes query =>
    let dbWithCtes := ctes.foldl (fun db' cte =>
      fun name =>
        if name == cte.name then
          if cte.isRecursive then
            cteEval db' cte.name cte.query
          else
            queryEval db' cte.query
        else
          db' name
    ) db
    queryEval dbWithCtes query

-- ============================================================================
-- Equational Theorems for evalQueryCore
-- ============================================================================

theorem evalQueryCore_simple (db : Database)
    (selectEval : Database → SelectStmt → Table)
    (queryEval : Database → Query → Table)
    (cteEval : Database → String → Query → Table)
    (sel : SelectStmt) :
    evalQueryCore db selectEval queryEval cteEval (.simple sel) = selectEval db sel := by
  rfl

theorem evalQueryCore_compound (db : Database)
    (selectEval : Database → SelectStmt → Table)
    (queryEval : Database → Query → Table)
    (cteEval : Database → String → Query → Table)
    (left right : Query) (op : SetOp) :
    evalQueryCore db selectEval queryEval cteEval (.compound left op right) =
    applySetOp op (queryEval db left) (queryEval db right) := by
  rfl

-- ============================================================================
-- Non-Partial Core SELECT Evaluator
-- ============================================================================

/-- Non-partial SELECT evaluator, parameterized by evaluation callbacks.
    Mirrors evalSelectWithContext (Semantics.lean) exactly, with partial def
    calls replaced by parameters. Not recursive — delegates to parameters
    for recursive calls. -/
def evalSelectCore (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (sel : SelectStmt) : Table :=
  -- 1. FROM clause
  let baseRows : Table := match sel.fromClause with
    | some f => fromEval db f
    | none => [[]]

  -- Merge outer row context into each base row for correlated subqueries
  let baseRowsWithContext : Table := baseRows.map fun row => outerRow ++ row

  -- 2. WHERE clause
  let filteredRows : Table := match sel.whereClause with
    | some cond =>
      baseRowsWithContext.filter fun row =>
        exprEval db row cond == some (Value.bool true)
    | none => baseRowsWithContext

  -- HAVING-filtered source rows: used by the window and plain projection
  -- paths, and as the aligned ORDER BY sources (#206). Grouped/aggregate
  -- paths apply HAVING per-group and ignore this binding.
  let havingRows : Table := match sel.having with
    | some cond =>
      filteredRows.filter fun row =>
        exprEval db row cond == some (Value.bool true)
    | none => filteredRows

  -- 3. GROUP BY and 4. HAVING and 5. SELECT (projection)
  let projectedRows : Table :=
    if !sel.groupBy.isEmpty then
      -- GROUP BY present: partition rows and evaluate aggregates per group
      -- Inline groupRowsByKey logic: rows.foldl addToGroups []
      let addToGroups (groups : List (List (Option Value) × Table)) (row : Row) :
          List (List (Option Value) × Table) :=
        let key := sel.groupBy.map (exprEval db row)
        match groups.find? (fun (k, _) => k == key) with
        | some _ => groups.map fun (k, rs) => if k == key then (k, rs ++ [row]) else (k, rs)
        | none => groups ++ [(key, [row])]
      let groups := filteredRows.foldl addToGroups []
      let groupResults := groups.filterMap fun (_key, groupRows) =>
        match groupRows.head? with
        | none => none
        | some sampleRow =>
          let passesHaving := match sel.having with
            | none => true
            | some cond =>
              exprWithAggEval db groupRows sampleRow cond == some (Value.bool true)
          if passesHaving then
            some (sel.items.flatMap (selectItemWithAggEval db groupRows sampleRow))
          else
            none
      groupResults
    else if hasAgg sel.items then
      let sampleRow := filteredRows.head?.getD []
      let passesHaving := match sel.having with
        | none => true
        | some cond =>
          exprWithAggEval db filteredRows sampleRow cond == some (Value.bool true)
      if passesHaving then
        [sel.items.flatMap (selectItemWithAggEval db filteredRows sampleRow)]
      else
        []
    else if hasWindowFn sel.items then
      let partition := havingRows
      let sortedPartition := havingRows
      ((List.range havingRows.length).zip havingRows).map fun (idx, row) =>
        sel.items.flatMap fun item =>
          match item with
          | .star none => row
          | .star (some t) => row.filter fun (k, _) => k.startsWith s!"{t}."
          | .exprItem e alias =>
            match exprWithWindowEval db row partition sortedPartition idx e with
            | some v => [(alias.getD (exprToName e), v)]
            | none => [(alias.getD (exprToName e), .null none)]
    else
      havingRows.map fun row => sel.items.flatMap (selectItemEval db row)

  -- 6. DISTINCT
  let distinctRows : Table := if sel.distinct then
    projectedRows.eraseDups
  else
    projectedRows

  -- 7. ORDER BY
  -- Sort keys resolve against `projected ++ source` rows so ORDER BY can
  -- reference non-projected columns (#206); output columns win on name
  -- clashes. This applies only where projected rows align 1:1 with source
  -- rows (plain and window paths, no DISTINCT). With DISTINCT the sources
  -- are ambiguous after dedup, and grouped/aggregate rows have no single
  -- source row — in those cases the SQL standard restricts sort keys to
  -- output columns, which is the fallback branch.
  let orderedRows : Table := if sel.orderBy.isEmpty then distinctRows else
    if !sel.distinct && sel.groupBy.isEmpty && !hasAgg sel.items then
      ((distinctRows.zip (havingRows.map (List.drop outerRow.length))).mergeSort fun p1 p2 =>
        compareEval db (p1.1 ++ p1.2) (p2.1 ++ p2.2) sel.orderBy).map (·.1)
    else
      distinctRows.mergeSort fun r1 r2 =>
        compareEval db r1 r2 sel.orderBy

  -- 8. OFFSET and LIMIT
  let offsetRows : Table := match sel.offsetVal with
    | some n => orderedRows.drop n
    | none => orderedRows
  let limitRows : Table := match sel.limitVal with
    | some n => offsetRows.take n
    | none => offsetRows

  limitRows

-- ============================================================================
-- Equational Theorems for evalSelectCore
-- ============================================================================

/-- ORDER BY + OFFSET + LIMIT where sort keys can also resolve against an
    aligned source row (#206): when `useSources` is true, each projected row
    is paired 1:1 with its pre-projection source row and sort keys evaluate
    against `projected ++ source` (output columns win on name clashes).
    With `useSources := false` this is `applyOrderByLimitOffset`. -/
def applyOrderByLimitOffsetAligned
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (db : Database) (orderBy : List OrderByItem) (limit offset : Option Nat)
    (useSources : Bool) (sources : Table) (rows : Table) : Table :=
  let orderedRows : Table := if orderBy.isEmpty then rows else
    if useSources then
      ((rows.zip sources).mergeSort fun p1 p2 =>
        compareEval db (p1.1 ++ p1.2) (p2.1 ++ p2.2) orderBy).map (·.1)
    else
      rows.mergeSort fun r1 r2 =>
        compareEval db r1 r2 orderBy
  let offsetRows : Table := match offset with
    | some n => orderedRows.drop n
    | none => orderedRows
  match limit with
  | some n => offsetRows.take n
  | none => offsetRows

/-- Aligned ORDER BY + OFFSET + LIMIT on empty input is empty (regardless of
    sources, since zipping with an empty list is empty). -/
theorem applyOrderByLimitOffsetAligned_nil
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (db : Database) (orderBy : List OrderByItem) (limit offset : Option Nat)
    (useSources : Bool) (sources : Table) :
    applyOrderByLimitOffsetAligned compareEval db orderBy limit offset
      useSources sources [] = [] := by
  simp only [applyOrderByLimitOffsetAligned, List.zip_nil_left, List.mergeSort_nil,
    List.map_nil]
  cases limit <;> cases offset <;> simp

/-- Aligned ORDER BY + OFFSET + LIMIT length is independent of the orderBy
    list, provided sources align 1:1 with rows whenever they are used. -/
theorem applyOrderByLimitOffsetAligned_length_eq
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (db : Database) (orderBy1 orderBy2 : List OrderByItem)
    (limit offset : Option Nat) (useSources : Bool) (sources rows : Table)
    (halign : useSources = true → sources.length = rows.length) :
    (applyOrderByLimitOffsetAligned compareEval db orderBy1 limit offset
      useSources sources rows).length =
    (applyOrderByLimitOffsetAligned compareEval db orderBy2 limit offset
      useSources sources rows).length := by
  have hlen : ∀ ob : List OrderByItem,
      (if ob.isEmpty then rows else
        if useSources then
          ((rows.zip sources).mergeSort fun p1 p2 =>
            compareEval db (p1.1 ++ p1.2) (p2.1 ++ p2.2) ob).map (·.1)
        else
          rows.mergeSort fun r1 r2 => compareEval db r1 r2 ob).length = rows.length := by
    intro ob
    by_cases hob : ob.isEmpty = true
    · simp [hob]
    · by_cases huse : useSources = true
      · simp [hob, huse, List.length_mergeSort, List.length_zip, halign huse]
      · simp [hob, huse, List.length_mergeSort]
  simp only [applyOrderByLimitOffsetAligned]
  cases limit <;> cases offset <;>
    simp only [List.length_take, List.length_drop, hlen]

/-- Steps 3-6 of the evaluation pipeline (after WHERE, before ORDER BY):
    GROUP BY, HAVING, projection, DISTINCT. -/
def evalSelectProjectDistinct (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr)
    (filteredRows : Table) : Table :=
  let projectedRows : Table :=
    if !groupBy.isEmpty then
      let addToGroups (groups : List (List (Option Value) × Table)) (row : Row) :
          List (List (Option Value) × Table) :=
        let key := groupBy.map (exprEval db row)
        match groups.find? (fun (k, _) => k == key) with
        | some _ => groups.map fun (k, rs) => if k == key then (k, rs ++ [row]) else (k, rs)
        | none => groups ++ [(key, [row])]
      let groups := filteredRows.foldl addToGroups []
      let groupResults := groups.filterMap fun (_key, groupRows) =>
        match groupRows.head? with
        | none => none
        | some sampleRow =>
          let passesHaving := match having with
            | none => true
            | some cond =>
              exprWithAggEval db groupRows sampleRow cond == some (Value.bool true)
          if passesHaving then
            some (items.flatMap (selectItemWithAggEval db groupRows sampleRow))
          else
            none
      groupResults
    else if hasAgg items then
      let sampleRow := filteredRows.head?.getD []
      let passesHaving := match having with
        | none => true
        | some cond =>
          exprWithAggEval db filteredRows sampleRow cond == some (Value.bool true)
      if passesHaving then
        [items.flatMap (selectItemWithAggEval db filteredRows sampleRow)]
      else
        []
    else if hasWindowFn items then
      let havingRows := match having with
        | some cond =>
          filteredRows.filter fun row =>
            exprEval db row cond == some (Value.bool true)
        | none => filteredRows
      let partition := havingRows
      let sortedPartition := havingRows
      ((List.range havingRows.length).zip havingRows).map fun (idx, row) =>
        items.flatMap fun item =>
          match item with
          | .star none => row
          | .star (some t) => row.filter fun (k, _) => k.startsWith s!"{t}."
          | .exprItem e alias =>
            match exprWithWindowEval db row partition sortedPartition idx e with
            | some v => [(alias.getD (exprToName e), v)]
            | none => [(alias.getD (exprToName e), .null none)]
    else
      let havingRows := match having with
        | some cond =>
          filteredRows.filter fun row =>
            exprEval db row cond == some (Value.bool true)
        | none => filteredRows
      havingRows.map fun row => items.flatMap (selectItemEval db row)
  if distinct then projectedRows.eraseDups else projectedRows

/-- In the plain and window paths without DISTINCT, projection is a 1:1 map
    over the HAVING-filtered rows, so lengths agree. This is the alignment
    fact behind the source-aware ORDER BY (#206). -/
theorem evalSelectProjectDistinct_length_aligned (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr)
    (filteredRows : Table)
    (h : (!distinct && groupBy.isEmpty && !hasAgg items) = true) :
    (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg distinct items
      groupBy having filteredRows).length =
    (match having with
      | some cond => filteredRows.filter fun row =>
          exprEval db row cond == some (Value.bool true)
      | none => filteredRows).length := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hd, hgb⟩, hagg⟩ := h
  simp only [evalSelectProjectDistinct, hgb, hagg, hd, Bool.not_true,
    Bool.false_eq_true, if_false]
  by_cases hwin : hasWindowFn items = true
  · simp [hwin, List.length_map, List.length_zip, List.length_range]
  · simp [hwin, List.length_map]

/-- Steps 3-9 of the evaluation pipeline (after WHERE filtering).
    Takes filteredRows as input and applies GROUP BY, HAVING, projection,
    DISTINCT, ORDER BY, OFFSET, and LIMIT. Factored as composition of
    evalSelectProjectDistinct + applyOrderByLimitOffsetAligned. -/
def evalSelectAfterFilter (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (ctxLen : Nat) (filteredRows : Table) : Table :=
  let havingRows : Table := match having with
    | some cond =>
      filteredRows.filter fun row =>
        exprEval db row cond == some (Value.bool true)
    | none => filteredRows
  -- Sort sources have the correlated outer-row prefix stripped: outer columns
  -- are constant per query instance, so they can never affect sort order, and
  -- stripping them keeps ground SELECTs row-context independent (#206).
  applyOrderByLimitOffsetAligned compareEval db orderBy limit offset
    (!distinct && groupBy.isEmpty && !hasAgg items)
    (havingRows.map (List.drop ctxLen))
    (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg distinct items
      groupBy having filteredRows)

/-- evalSelectProjectDistinct on empty input produces empty output
    when there are no aggregates. -/
theorem evalSelectProjectDistinct_nil (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr)
    (hNoAgg : hasAgg items = false) :
    evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg distinct items
      groupBy having [] = [] := by
  simp only [evalSelectProjectDistinct, List.foldl, List.filterMap_nil,
    hNoAgg, List.head?_nil, Option.getD]
  cases having <;> simp [List.map_nil, List.eraseDups_nil]

/-- evalSelectCore decomposes into base rows + filter + afterFilter -/
theorem evalSelectCore_eq_afterFilter (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit offset) =
    let baseRows := match from_ with | some f => fromEval db f | none => [[]]
    let baseRowsWithContext := baseRows.map fun row => outerRow ++ row
    let filteredRows := match where_ with
      | some cond => baseRowsWithContext.filter fun row =>
          exprEval db row cond == some (Value.bool true)
      | none => baseRowsWithContext
    evalSelectAfterFilter db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      distinct items groupBy having orderBy limit offset outerRow.length filteredRows := by
  rfl

/-- Infrastructure: evalSelectCore decomposes limit/offset into drop/take on the base result. -/
theorem evalSelectCore_limit_offset (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit offset) =
    let base := evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none)
    let offsetRows := match offset with | some n => base.drop n | none => base
    match limit with | some n => offsetRows.take n | none => offsetRows := by
  simp only [evalSelectCore_eq_afterFilter, evalSelectAfterFilter,
    applyOrderByLimitOffsetAligned]


/-- Infrastructure: ORDER BY preserves row count (mergeSort preserves length). -/
theorem evalSelectCore_orderBy_length (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy1 orderBy2 : List OrderByItem) (limit offset : Option Nat) :
    (evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ where_ groupBy having orderBy1 limit offset)).length =
    (evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ where_ groupBy having orderBy2 limit offset)).length := by
  simp only [evalSelectCore_eq_afterFilter, evalSelectAfterFilter]
  -- Both sides have the same evalSelectProjectDistinct result. Only orderBy differs.
  exact applyOrderByLimitOffsetAligned_length_eq _ _ _ _ _ _ _ _ _
    (fun huse => by
      rw [List.length_map]
      exact (evalSelectProjectDistinct_length_aligned _ _ _ _ _ _ _ _
        _ _ _ _ _ huse).symm)

/-- Infrastructure: WHERE clause only affects filtering; equivalent WHERE clauses produce identical results. -/
theorem evalSelectCore_where_congr (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (w1 w2 : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    (∀ row : Row,
      (match w1 with | some c => exprEval db row c == some (Value.bool true) | none => true) =
      (match w2 with | some c => exprEval db row c == some (Value.bool true) | none => true)) →
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ w1 groupBy having orderBy limit offset) =
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ w2 groupBy having orderBy limit offset) := by
  intro hCongr
  simp only [evalSelectCore_eq_afterFilter]
  -- Suffices to show the filteredRows are the same
  congr 1
  -- Goal: (match w1 with ...) = (match w2 with ...)
  cases w1 with
  | none =>
    cases w2 with
    | none => rfl
    | some c2 =>
      -- h says: ∀ row, true = (exprEval db row c2 == some (Value.bool true))
      -- So the filter keeps everything (same as identity)
      simp only []
      have : ∀ row, (exprEval db row c2 == some (Value.bool true)) = true := by
        intro row; exact (hCongr row).symm
      rw [List.filter_eq_self.mpr]
      intro x _; exact this x
  | some c1 =>
    cases w2 with
    | some c2 =>
      -- Both are filters with different predicates that agree on all rows
      simp only []
      congr 1; funext row; exact hCongr row
    | none =>
      -- h says: ∀ row, (exprEval db row c1 == some (Value.bool true)) = true
      -- So the filter keeps everything (same as identity)
      simp only []
      have : ∀ row, (exprEval db row c1 == some (Value.bool true)) = true := by
        intro row; exact hCongr row
      rw [List.filter_eq_self.mpr]
      intro x _; exact this x

/-- Helper: List.filter with always-false predicate returns [] -/
private theorem filter_eq_nil_of_false {α : Type} (l : List α) (p : α → Bool)
    (h : ∀ x, p x = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.filter, h x, ih]

/-- Infrastructure: WHERE clause that rejects all rows produces empty result when no aggregates. -/
theorem evalSelectCore_filter_all_false (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (cond : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    hasAgg items = false →
    (∀ row : Row, (exprEval db row cond == some (Value.bool true)) = false) →
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ (some cond) groupBy having orderBy limit offset) = [] := by
  intro hNoAgg hAllFalse
  -- Unfold evalSelectCore directly (it's a regular def)
  show evalSelectAfterFilter db exprEval selectItemEval selectItemWithAggEval
    exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
    distinct items groupBy having orderBy limit offset outerRow.length
    (List.filter (fun row => exprEval db row cond == some (Value.bool true))
      (List.map (fun row => outerRow ++ row)
        (match from_ with | some f => fromEval db f | none => [[]]))) = []
  -- filteredRows = [] because all rows are rejected
  rw [filter_eq_nil_of_false _ _ hAllFalse]
  -- evalSelectAfterFilter ... [] = aligned-orderBy (evalSelectProjectDistinct ... [])
  simp only [evalSelectAfterFilter]
  -- evalSelectProjectDistinct ... [] = [] (no aggregates)
  rw [evalSelectProjectDistinct_nil _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg]
  -- aligned ORDER BY on [] = [] (sources irrelevant for empty input)
  exact applyOrderByLimitOffsetAligned_nil _ _ _ _ _ _ _

-- ============================================================================
-- List filter lemmas (needed for filter_and / filter_commute / filter_idempotent)
-- ============================================================================

/-- Conjunction of filters equals sequential filtering. -/
theorem list_filter_and_eq {α : Type} (f g : α → Bool) (l : List α) :
    l.filter (fun r => f r && g r) = (l.filter f).filter g := by
  induction l with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.filter_cons]
    by_cases hf : f r <;> by_cases hg : g r <;> simp [hf, hg, ih]

/-- Filter order doesn't matter for sequential filtering. -/
private theorem list_filter_comm {α : Type} (f g : α → Bool) (l : List α) :
    (l.filter f).filter g = (l.filter g).filter f := by
  rw [← list_filter_and_eq, ← list_filter_and_eq]
  congr 1; ext r; exact Bool.and_comm (f r) (g r)

-- ============================================================================
-- List algebra: flatMap/filterMap + filter commutation
-- ============================================================================

/-- Filter where all elements fail the predicate gives empty list. -/
private theorem list_filter_false {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ a ∈ l, p a = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [h x List.mem_cons_self,
          ih (fun a ha => h a (List.mem_cons_of_mem x ha))]

/-- When a filter on flatMap results is constant per-outer-element,
    it can be pulled outside as a filter on the outer list. -/
theorem list_flatMap_filter_comm {α β : Type} (xs : List α)
    (f : α → List β) (p : β → Bool) (q : α → Bool)
    (h : ∀ a ∈ xs, ∀ b ∈ f a, p b = q a) :
    (xs.flatMap f).filter p = (xs.filter q).flatMap f := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hx := h x List.mem_cons_self
    have ih' := ih (fun a ha => h a (List.mem_cons_of_mem x ha))
    simp only [List.flatMap_cons, List.filter_append, List.filter_cons]
    cases hq : q x with
    | true =>
      have hself : (f x).filter p = f x :=
        List.filter_eq_self.mpr (fun b hb => (hx b hb).trans hq)
      simp [hself, ih']
    | false =>
      have hnil : (f x).filter p = [] :=
        list_filter_false p (f x) (fun b hb => (hx b hb).trans hq)
      simp [hnil, ih']

/-- When a filter on filterMap results corresponds to a pre-filter
    on the input, the filter can be moved before the filterMap. -/
theorem list_filter_filterMap_comm {α β : Type} (xs : List α)
    (f : α → Option β) (p : β → Bool) (q : α → Bool)
    (h : ∀ a ∈ xs, ∀ b, f a = some b → p b = q a) :
    (xs.filterMap f).filter p = (xs.filter q).filterMap f := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have ih' := ih (fun a ha => h a (List.mem_cons_of_mem x ha))
    simp only [List.filterMap_cons, List.filter_cons]
    cases hfx : f x with
    | none =>
      cases q x <;> simp [hfx, ih']
    | some b =>
      have hpb := h x List.mem_cons_self b hfx
      cases hq : q x with
      | true => simp [hfx, hpb, hq, ih']
      | false => simp [hpb, hq, ih']

-- ============================================================================
-- SELECT * WHERE p = filter (infrastructure for filter_and / filter_commute / etc.)
-- ============================================================================

/-- `evalSelectAfterFilter` with trivial settings (SELECT *, no GROUP BY, no HAVING,
    no ORDER BY, no LIMIT, no OFFSET, not DISTINCT) is the identity on filteredRows. -/
private theorem evalSelectAfterFilter_star_identity (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (filteredRows : Table)
    (h_hasAgg : hasAgg [.star none] = false)
    (h_hasWindowFn : hasWindowFn [.star none] = false)
    (h_star : ∀ db' row, selectItemEval db' row (.star none) = row) :
    ∀ ctxLen,
    evalSelectAfterFilter db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      false [SelectItem.star none] [] none [] none none ctxLen filteredRows = filteredRows := by
  intro ctxLen
  simp [evalSelectAfterFilter, applyOrderByLimitOffsetAligned, evalSelectProjectDistinct,
    h_hasAgg, h_hasWindowFn]
  -- Goal: filteredRows.map (fun row => selectItemEval db row (.star none)) = filteredRows
  have : (fun row => selectItemEval db row (.star none)) = id := by
    funext row; exact h_star db row
  rw [this, List.map_id]

/-- SELECT * FROM from_ WHERE p (with all trivial options) equals the filtered base rows.
    This is the key infrastructure for filter_and, filter_commute, and filter_idempotent. -/
theorem evalSelectCore_star_where_eq_filter (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (from_ : Option FromClause) (p : Expr)
    (h_hasAgg : hasAgg [.star none] = false)
    (h_hasWindowFn : hasWindowFn [.star none] = false)
    (h_star : ∀ db' row, selectItemEval db' row (.star none) = row) :
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false [.star none] from_ (some p) [] none [] none none) =
    let baseRows := match from_ with | some f => fromEval db f | none => [[]]
    (baseRows.map fun row => outerRow ++ row).filter fun row =>
      exprEval db row p == some (Value.bool true) := by
  simp only [evalSelectCore_eq_afterFilter]
  exact evalSelectAfterFilter_star_identity db exprEval selectItemEval selectItemWithAggEval
    exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg _ h_hasAgg h_hasWindowFn h_star _

/-- Core filter_and: filtering a subquery result is the same as combining WHERE clauses. -/
theorem evalSelectCore_filter_and (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_hasAgg_star : hasAgg [.star none] = false)
    (h_hasWindowFn_star : hasWindowFn [.star none] = false)
    (h_star : ∀ db' row, selectItemEval db' row (.star none) = row)
    (h_subquery : ∀ (sel : SelectStmt) alias, fromEval db (.subquery (.simple sel) alias) =
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg sel)
    (h_and : ∀ row, (exprEval db row (.binOp .and p q) == some (Value.bool true)) =
      ((exprEval db row p == some (Value.bool true)) && (exprEval db row q == some (Value.bool true)))) :
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items
        (some (.subquery (.simple (.mk false [.star none] from_ (some p) [] none [] none none)) "inner"))
        (some q) groupBy having orderBy limit offset) =
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items from_ (some (.binOp .and p q)) groupBy having orderBy limit offset) := by
  simp only [evalSelectCore_eq_afterFilter]
  congr 1
  simp only [h_subquery]
  rw [evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _ h_hasAgg_star h_hasWindowFn_star h_star]
  simp only [List.nil_append, List.map_id']
  rw [← list_filter_and_eq]
  congr 1; funext row; exact (h_and row).symm

/-- Core filter_commute: filtering by p then q equals filtering by q then p. -/
theorem evalSelectCore_filter_commute (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_hasAgg_star : hasAgg [.star none] = false)
    (h_hasWindowFn_star : hasWindowFn [.star none] = false)
    (h_star : ∀ db' row, selectItemEval db' row (.star none) = row)
    (h_subquery : ∀ (sel : SelectStmt) alias, fromEval db (.subquery (.simple sel) alias) =
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg sel) :
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items
        (some (.subquery (.simple (.mk false [.star none] from_ (some p) [] none [] none none)) "inner"))
        (some q) groupBy having orderBy limit offset) =
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items
        (some (.subquery (.simple (.mk false [.star none] from_ (some q) [] none [] none none)) "inner"))
        (some p) groupBy having orderBy limit offset) := by
  simp only [evalSelectCore_eq_afterFilter]
  congr 1
  simp only [h_subquery]
  rw [evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _ h_hasAgg_star h_hasWindowFn_star h_star,
      evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _ h_hasAgg_star h_hasWindowFn_star h_star]
  simp only [List.nil_append, List.map_id']
  exact list_filter_comm _ _ _

/-- Core filter_idempotent: filtering by p then p again equals filtering by p once. -/
theorem evalSelectCore_filter_idempotent (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : Option FromClause)
    (p : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_hasAgg_star : hasAgg [.star none] = false)
    (h_hasWindowFn_star : hasWindowFn [.star none] = false)
    (h_star : ∀ db' row, selectItemEval db' row (.star none) = row)
    (h_subquery : ∀ (sel : SelectStmt) alias, fromEval db (.subquery (.simple sel) alias) =
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg sel) :
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items
        (some (.subquery (.simple (.mk false [.star none] from_ (some p) [] none [] none none)) "inner"))
        (some p) groupBy having orderBy limit offset) =
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items from_ (some p) groupBy having orderBy limit offset) := by
  simp only [evalSelectCore_eq_afterFilter]
  congr 1
  simp only [h_subquery]
  rw [evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _ h_hasAgg_star h_hasWindowFn_star h_star]
  simp only [List.nil_append, List.map_id']
  -- Goal: (baseRows.filter p).filter p = baseRows.filter p
  induction (match from_ with | some f => fromEval db f | none => [[]]) with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.filter_cons]
    split <;> simp_all

/-- Core filter_pushdown_table: moving a WHERE filter into a subquery is equivalent.
    SELECT items FROM from_ WHERE filter ... = SELECT items FROM (SELECT * FROM from_ WHERE filter) AS alias ... -/
theorem evalSelectCore_filter_pushdown_table (db : Database)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : Option FromClause) (alias_ : String) (filter : Expr)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_hasAgg_star : hasAgg [.star none] = false)
    (h_hasWindowFn_star : hasWindowFn [.star none] = false)
    (h_star : ∀ db' row, selectItemEval db' row (.star none) = row)
    (h_subquery : ∀ (sel : SelectStmt) alias, fromEval db (.subquery (.simple sel) alias) =
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg sel) :
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items from_ (some filter) groupBy having orderBy limit offset) =
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items
        (some (.subquery (.simple (.mk false [.star none] from_ (some filter) [] none [] none none)) alias_))
        none groupBy having orderBy limit offset) := by
  simp only [evalSelectCore_eq_afterFilter]
  congr 1
  simp only [h_subquery]
  rw [evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _ h_hasAgg_star h_hasWindowFn_star h_star]
  simp only [List.nil_append, List.map_id']

-- ============================================================================
-- Simple SELECT decomposition (for IN/EXISTS subquery proofs)
-- ============================================================================

/-- For a simple SELECT items FROM from_ (no WHERE, no GROUP BY, etc.),
    the result is just projecting each base row. -/
theorem evalSelectCore_simple_project (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause)
    (hNoAgg : hasAgg items = false)
    (hNoWin : hasWindowFn items = false) :
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk false items (some from_) none [] none [] none none) =
    List.map (fun row => items.flatMap (selectItemEval db row))
      (List.map (outerRow ++ ·) (fromEval db from_)) := by
  rw [evalSelectCore_eq_afterFilter]
  dsimp only []
  simp [evalSelectAfterFilter, applyOrderByLimitOffsetAligned, evalSelectProjectDistinct,
    hNoAgg, hNoWin]

/-- For a simple SELECT items FROM from_ WHERE cond (no GROUP BY, etc.),
    the result is filtering then projecting. -/
theorem evalSelectCore_simple_project_where (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause) (cond : Expr)
    (hNoAgg : hasAgg items = false)
    (hNoWin : hasWindowFn items = false) :
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk false items (some from_) (some cond) [] none [] none none) =
    List.map (fun row => items.flatMap (selectItemEval db row))
      (List.filter (fun row => exprEval db row cond == some (Value.bool true))
        (List.map (outerRow ++ ·) (fromEval db from_))) := by
  rw [evalSelectCore_eq_afterFilter]
  dsimp only []
  simp [evalSelectAfterFilter, applyOrderByLimitOffsetAligned, evalSelectProjectDistinct,
    hNoAgg, hNoWin]

/-- For SELECT DISTINCT items FROM from_ (no WHERE, no GROUP BY, etc.),
    the result is (projection of each base row).eraseDups -/
theorem evalSelectCore_distinct_project (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause)
    (hNoAgg : hasAgg items = false)
    (hNoWin : hasWindowFn items = false) :
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk true items (some from_) none [] none [] none none) =
    (List.map (fun row => items.flatMap (selectItemEval db row))
      (List.map (outerRow ++ ·) (fromEval db from_))).eraseDups := by
  rw [evalSelectCore_eq_afterFilter]
  dsimp only []
  simp [evalSelectAfterFilter, applyOrderByLimitOffsetAligned, evalSelectProjectDistinct,
    hNoAgg, hNoWin]

/-- For SELECT DISTINCT items FROM from_ WHERE cond (no GROUP BY, etc.),
    the result is (filter then project).eraseDups -/
theorem evalSelectCore_distinct_project_where (db : Database) (outerRow : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (from_ : FromClause) (cond : Expr)
    (hNoAgg : hasAgg items = false)
    (hNoWin : hasWindowFn items = false) :
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk true items (some from_) (some cond) [] none [] none none) =
    (List.map (fun row => items.flatMap (selectItemEval db row))
      (List.filter (fun row => exprEval db row cond == some (Value.bool true))
        (List.map (outerRow ++ ·) (fromEval db from_)))).eraseDups := by
  rw [evalSelectCore_eq_afterFilter]
  dsimp only []
  simp [evalSelectAfterFilter, applyOrderByLimitOffsetAligned, evalSelectProjectDistinct,
    hNoAgg, hNoWin]

-- ============================================================================
-- Ground Expression Detection (non-partial mirror of Expr.isGround)
-- ============================================================================

/-- Non-partial mirror of `Expr.isGround`, parameterized by a callback for SelectStmt groundness. -/
def isGroundCore (selectGround : SubQuery → Bool) : Expr → Bool
  | .lit _ => true
  | .col _ => false
  | .binOp _ l r => isGroundCore selectGround l && isGroundCore selectGround r
  | .unaryOp _ e => isGroundCore selectGround e
  | .func _ args => args.foldl (fun acc e => acc && isGroundCore selectGround e) true
  | .agg _ arg _ => match arg with | some e => isGroundCore selectGround e | none => true
  | .countStar => true
  | .case branches else_ =>
    branches.foldl (fun acc pair => acc && isGroundCore selectGround pair.1 && isGroundCore selectGround pair.2) true &&
    (match else_ with | some e => isGroundCore selectGround e | none => true)
  | .inList e _ vals => isGroundCore selectGround e && vals.foldl (fun acc vi => acc && isGroundCore selectGround vi) true
  | .inSubquery e _ sel => isGroundCore selectGround e && selectGround sel
  | .exists _ sel => selectGround sel
  | .subquery sel => selectGround sel
  | .between e lo hi => isGroundCore selectGround e && isGroundCore selectGround lo && isGroundCore selectGround hi
  | .windowFn _ _ _ => false
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

-- ============================================================================
-- Helper lemmas for isGroundCore_eval_independent
-- ============================================================================

/-- foldl with && from false always returns false. -/
private theorem foldl_and_false_init {α : Type} {f : α → Bool} (xs : List α) :
    xs.foldl (fun acc e => acc && f e) false = false := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl, Bool.false_and]; exact ih

/-- If foldl with && from true returns true, every element maps to true. -/
private theorem foldl_and_true_forall {α : Type} {f : α → Bool} {xs : List α}
    (h : xs.foldl (fun acc e => acc && f e) true = true)
    {x : α} (hx : x ∈ xs) : f x = true := by
  induction xs with
  | nil => contradiction
  | cons a rest ih =>
    simp only [List.foldl, Bool.true_and] at h
    rcases List.mem_cons.mp hx with rfl | hmem
    · -- x = a, h : rest.foldl ... (f x) = true
      cases hfx : f x with
      | true => rfl
      | false => rw [hfx] at h; rw [foldl_and_false_init] at h; exact absurd h Bool.false_ne_true
    · -- x ∈ rest
      cases hfa : f a with
      | true => rw [hfa] at h; exact ih h hmem
      | false => rw [hfa] at h; rw [foldl_and_false_init] at h; exact absurd h Bool.false_ne_true

/-- foldl with double-&& from false always returns false. -/
private theorem case_foldl_false_init {α : Type} {f g : α → Bool} (xs : List α) :
    xs.foldl (fun acc pair => acc && f pair && g pair) false = false := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl, Bool.false_and]; exact ih

/-- If case foldl from true returns true, both components of every element map to true. -/
private theorem case_foldl_true_forall {α : Type} {f g : α → Bool} {xs : List α}
    (h : xs.foldl (fun acc pair => acc && f pair && g pair) true = true)
    {x : α} (hx : x ∈ xs) : f x = true ∧ g x = true := by
  induction xs with
  | nil => contradiction
  | cons a rest ih =>
    simp only [List.foldl, Bool.true_and] at h
    -- h : rest.foldl step (f a && g a) = true
    cases hv : f a && g a
    case false =>
      rw [hv] at h
      rw [case_foldl_false_init] at h; exact absurd h Bool.false_ne_true
    case true =>
      rw [hv] at h
      rcases List.mem_cons.mp hx with rfl | hmem
      · -- x = a, hv : f x && g x = true
        constructor
        · cases hf : f x with
          | true => rfl
          | false => simp [hf] at hv
        · cases hg : g x with
          | true => rfl
          | false => simp [hg] at hv
      · exact ih h hmem

/-- evalCaseHelper congruence: if two functions agree on all branches, results agree. -/
theorem evalCaseHelper_congr (f g : Expr → Option Value)
    (elseVal1 elseVal2 : Option Value) (h_else : elseVal1 = elseVal2)
    (branches : List (Expr × Expr))
    (h : ∀ pair, pair ∈ branches → f pair.1 = g pair.1 ∧ f pair.2 = g pair.2) :
    evalCaseHelper f elseVal1 branches = evalCaseHelper g elseVal2 branches := by
  induction branches with
  | nil => simp [evalCaseHelper]; exact h_else
  | cons hd tl ih =>
    simp only [evalCaseHelper]
    have ⟨hc, hr⟩ := h hd List.mem_cons_self
    rw [hc]
    generalize g hd.1 = v
    have ih' := ih (fun pair hp => h pair (List.mem_cons_of_mem hd hp))
    cases v with
    | none => exact ih'
    | some val =>
      cases val with
      | bool b => cases b with
        | true => exact hr
        | false => exact ih'
      | int _ => exact ih'
      | string _ => exact ih'
      | decimal _ _ => exact ih'
      | null _ => exact ih'

/-- InList foldl congruence: if ev and all value evaluations agree, foldl results agree. -/
theorem inList_foldl_eval_independent
    (f g : Expr → Option Value)
    (ev1 ev2 : Option Value) (h_ev : ev1 = ev2)
    (vals : List Expr)
    (h : ∀ vi, vi ∈ vals → f vi = g vi)
    (init : Option Value) :
    vals.foldl (fun acc vi => evalBinOp .or acc (evalBinOp .eq ev1 (f vi))) init =
    vals.foldl (fun acc vi => evalBinOp .or acc (evalBinOp .eq ev2 (g vi))) init := by
  subst h_ev
  induction vals generalizing init with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.foldl]
    rw [h v List.mem_cons_self]
    exact ih (fun vi hvi => h vi (List.mem_cons_of_mem v hvi)) _

/-- Extraction: if isGroundCore on .case is true, then branches foldl is true. -/
private theorem isGroundCore_case_branches (sg : SubQuery → Bool)
    (branches : List (Expr × Expr)) (else_ : Option Expr)
    (h : isGroundCore sg (.case branches else_) = true) :
    branches.foldl (fun acc pair => acc && isGroundCore sg pair.1 && isGroundCore sg pair.2) true = true := by
  rw [isGroundCore.eq_def] at h
  exact (Bool.and_eq_true_iff.mp h).1

/-- Extraction: if isGroundCore on .case with some else is true, then the else expr is ground. -/
private theorem isGroundCore_case_else (sg : SubQuery → Bool)
    (branches : List (Expr × Expr)) (e : Expr)
    (h : isGroundCore sg (.case branches (some e)) = true) :
    isGroundCore sg e = true := by
  rw [isGroundCore.eq_def] at h
  exact (Bool.and_eq_true_iff.mp h).2

/-- Extraction: if isGroundCore on .inList is true, then the expression is ground. -/
private theorem isGroundCore_inList_expr (sg : SubQuery → Bool)
    (e : Expr) (neg : Bool) (vals : List Expr)
    (h : isGroundCore sg (.inList e neg vals) = true) :
    isGroundCore sg e = true := by
  rw [isGroundCore.eq_def] at h
  exact (Bool.and_eq_true_iff.mp h).1

/-- Extraction: if isGroundCore on .inList is true, then the vals foldl is true. -/
private theorem isGroundCore_inList_vals (sg : SubQuery → Bool)
    (e : Expr) (neg : Bool) (vals : List Expr)
    (h : isGroundCore sg (.inList e neg vals) = true) :
    vals.foldl (fun acc vi => acc && isGroundCore sg vi) true = true := by
  rw [isGroundCore.eq_def] at h
  exact (Bool.and_eq_true_iff.mp h).2

-- ============================================================================
-- Core theorem: ground expressions are row-independent
-- ============================================================================

/-- If `isGroundCore selectGround e = true` and subqueries are row-independent for ground selects,
    then `evalExprCore` produces the same result for any row. -/
theorem isGroundCore_eval_independent
    (selectGround : SubQuery → Bool)
    (subqueryEval : Database → Row → SubQuery → Table)
    (h_sq : ∀ sel, selectGround sel = true →
      ∀ db r1 r2, subqueryEval db r1 sel = subqueryEval db r2 sel)
    (db : Database) (e : Expr) (hg : isGroundCore selectGround e = true)
    (r1 r2 : Row) :
    evalExprCore db r1 subqueryEval e = evalExprCore db r2 subqueryEval e := by
  -- Expr is mutually inductive so `induction` doesn't work directly.
  -- Use strong induction on sizeOf via Nat induction.
  suffices key : ∀ (n : Nat) (e : Expr), sizeOf e < n →
      isGroundCore selectGround e = true →
      ∀ r1 r2 : Row, evalExprCore db r1 subqueryEval e = evalExprCore db r2 subqueryEval e by
    exact key (sizeOf e + 1) e (Nat.lt_succ_of_le (Nat.le_refl _)) hg r1 r2
  intro n
  induction n with
  | zero => intro e hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro e hlt hg r1 r2
    cases e with
    | lit _ => simp [evalExprCore]
    | col _ => simp [isGroundCore] at hg
    | binOp op l r =>
      simp [isGroundCore] at hg
      have h_sz_l : sizeOf l < sizeOf (Expr.binOp op l r) := by simp_wf; omega
      have h_sz_r : sizeOf r < sizeOf (Expr.binOp op l r) := by simp_wf; omega
      simp only [evalExprCore]
      rw [ih l (by omega) hg.1 r1 r2, ih r (by omega) hg.2 r1 r2]
    | unaryOp op e =>
      simp [isGroundCore] at hg
      have h_sz : sizeOf e < sizeOf (Expr.unaryOp op e) := by simp_wf; omega
      simp only [evalExprCore]
      rw [ih e (by omega) hg r1 r2]
    | func name args =>
      simp only [evalExprCore]
      congr 1
      apply List.map_congr_left
      intro e he
      simp [isGroundCore] at hg
      have hge := foldl_and_true_forall hg he
      have h_sz : sizeOf e < sizeOf (Expr.func name args) := by
        have := List.sizeOf_lt_of_mem he; simp_wf; omega
      exact ih e (by omega) hge r1 r2
    | agg _ _ _ => simp [evalExprCore]
    | countStar => simp [evalExprCore]
    | «case» branches else_ =>
      rw [evalExprCore_case, evalExprCore_case]
      apply evalCaseHelper_congr
      · cases else_ with
        | none => rfl
        | some e =>
          have hg_else := isGroundCore_case_else _ _ _ hg
          have h_sz : sizeOf e < sizeOf (Expr.case branches (some e)) := by simp_wf; omega
          exact ih e (by omega) hg_else r1 r2
      · intro pair hp
        have hg_branches := isGroundCore_case_branches _ _ _ hg
        have ⟨hc, hr⟩ := case_foldl_true_forall hg_branches hp
        have h_pair_lt := List.sizeOf_lt_of_mem hp
        have h_pair_sz : sizeOf pair = 1 + sizeOf pair.fst + sizeOf pair.snd := by
          obtain ⟨a, b⟩ := pair; simp [Prod.mk.sizeOf_spec]
        have h_sz_case : sizeOf branches < sizeOf (Expr.case branches else_) := by simp_wf; omega
        exact ⟨ih pair.1 (by omega) hc r1 r2, ih pair.2 (by omega) hr r1 r2⟩
    | inList e _neg vals =>
      have hge := isGroundCore_inList_expr _ _ _ _ hg
      have hgv := isGroundCore_inList_vals _ _ _ _ hg
      have h_sz_e : sizeOf e < sizeOf (Expr.inList e _neg vals) := by simp_wf; omega
      rw [evalExprCore_inList, evalExprCore_inList]
      have h_ev := ih e (by omega) hge r1 r2
      have h_foldl := inList_foldl_eval_independent
        (evalExprCore db r1 subqueryEval) (evalExprCore db r2 subqueryEval)
        (evalExprCore db r1 subqueryEval e) (evalExprCore db r2 subqueryEval e)
        h_ev vals
        (fun vi hvi => by
          have hgvi := foldl_and_true_forall hgv hvi
          have h_sz_vi : sizeOf vi < sizeOf (Expr.inList e _neg vals) := by
            have := List.sizeOf_lt_of_mem hvi; simp_wf; omega
          exact ih vi (by omega) hgvi r1 r2)
        (some (.bool false))
      -- Reduce let bindings, then rewrite the foldl
      dsimp only []
      rw [h_foldl]
    | inSubquery e _neg sel =>
      simp [isGroundCore] at hg
      have h_sz_e : sizeOf e < sizeOf (Expr.inSubquery e _neg sel) := by simp_wf; omega
      simp only [evalExprCore]
      rw [ih e (by omega) hg.1 r1 r2, h_sq sel hg.2 db r1 r2]
    | «exists» _neg sel =>
      simp [isGroundCore] at hg
      simp only [evalExprCore]
      rw [h_sq sel hg db r1 r2]
    | subquery sel =>
      simp [isGroundCore] at hg
      simp only [evalExprCore]
      rw [h_sq sel hg db r1 r2]
    | between e lo hi =>
      simp [isGroundCore] at hg
      have h_sz_e : sizeOf e < sizeOf (Expr.between e lo hi) := by simp_wf; omega
      have h_sz_lo : sizeOf lo < sizeOf (Expr.between e lo hi) := by simp_wf; omega
      have h_sz_hi : sizeOf hi < sizeOf (Expr.between e lo hi) := by simp_wf; omega
      simp only [evalExprCore]
      -- hg has structure: (isGroundCore sg e ∧ isGroundCore sg lo) ∧ isGroundCore sg hi
      rw [ih e (by omega) hg.1.1 r1 r2,
          ih lo (by omega) hg.1.2 r1 r2,
          ih hi (by omega) hg.2 r1 r2]
    | windowFn _ _ _ => simp [evalExprCore]

/-- Database-and-row independence (#242): if `isGroundCore selectGround e = true` and the
    subqueries accepted by `selectGround` are independent of both database and row, then
    `evalExprCore` gives the same result for any database and any row. Instantiated with
    `selectGround := fun _ => false` (no subqueries at all) the hypothesis is vacuous. -/
theorem isGroundCore_eval_db_row_independent
    (selectGround : SubQuery → Bool)
    (subqueryEval : Database → Row → SubQuery → Table)
    (h_sq : ∀ sel, selectGround sel = true →
      ∀ db1 db2 r1 r2, subqueryEval db1 r1 sel = subqueryEval db2 r2 sel)
    (e : Expr) (hg : isGroundCore selectGround e = true)
    (db1 db2 : Database) (r1 r2 : Row) :
    evalExprCore db1 r1 subqueryEval e = evalExprCore db2 r2 subqueryEval e := by
  -- Expr is mutually inductive so `induction` doesn't work directly.
  -- Use strong induction on sizeOf via Nat induction.
  suffices key : ∀ (n : Nat) (e : Expr), sizeOf e < n →
      isGroundCore selectGround e = true →
      ∀ (db1 db2 : Database) (r1 r2 : Row),
        evalExprCore db1 r1 subqueryEval e = evalExprCore db2 r2 subqueryEval e by
    exact key (sizeOf e + 1) e (Nat.lt_succ_of_le (Nat.le_refl _)) hg db1 db2 r1 r2
  intro n
  induction n with
  | zero => intro e hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro e hlt hg db1 db2 r1 r2
    cases e with
    | lit _ => simp [evalExprCore]
    | col _ => simp [isGroundCore] at hg
    | binOp op l r =>
      simp [isGroundCore] at hg
      have h_sz_l : sizeOf l < sizeOf (Expr.binOp op l r) := by simp_wf; omega
      have h_sz_r : sizeOf r < sizeOf (Expr.binOp op l r) := by simp_wf; omega
      simp only [evalExprCore]
      rw [ih l (by omega) hg.1 db1 db2 r1 r2, ih r (by omega) hg.2 db1 db2 r1 r2]
    | unaryOp op e =>
      simp [isGroundCore] at hg
      have h_sz : sizeOf e < sizeOf (Expr.unaryOp op e) := by simp_wf; omega
      simp only [evalExprCore]
      rw [ih e (by omega) hg db1 db2 r1 r2]
    | func name args =>
      simp only [evalExprCore]
      congr 1
      apply List.map_congr_left
      intro e he
      simp [isGroundCore] at hg
      have hge := foldl_and_true_forall hg he
      have h_sz : sizeOf e < sizeOf (Expr.func name args) := by
        have := List.sizeOf_lt_of_mem he; simp_wf; omega
      exact ih e (by omega) hge db1 db2 r1 r2
    | agg _ _ _ => simp [evalExprCore]
    | countStar => simp [evalExprCore]
    | «case» branches else_ =>
      rw [evalExprCore_case, evalExprCore_case]
      apply evalCaseHelper_congr
      · cases else_ with
        | none => rfl
        | some e =>
          have hg_else := isGroundCore_case_else _ _ _ hg
          have h_sz : sizeOf e < sizeOf (Expr.case branches (some e)) := by simp_wf; omega
          exact ih e (by omega) hg_else db1 db2 r1 r2
      · intro pair hp
        have hg_branches := isGroundCore_case_branches _ _ _ hg
        have ⟨hc, hr⟩ := case_foldl_true_forall hg_branches hp
        have h_pair_lt := List.sizeOf_lt_of_mem hp
        have h_pair_sz : sizeOf pair = 1 + sizeOf pair.fst + sizeOf pair.snd := by
          obtain ⟨a, b⟩ := pair; simp [Prod.mk.sizeOf_spec]
        have h_sz_case : sizeOf branches < sizeOf (Expr.case branches else_) := by simp_wf; omega
        exact ⟨ih pair.1 (by omega) hc db1 db2 r1 r2, ih pair.2 (by omega) hr db1 db2 r1 r2⟩
    | inList e _neg vals =>
      have hge := isGroundCore_inList_expr _ _ _ _ hg
      have hgv := isGroundCore_inList_vals _ _ _ _ hg
      have h_sz_e : sizeOf e < sizeOf (Expr.inList e _neg vals) := by simp_wf; omega
      rw [evalExprCore_inList, evalExprCore_inList]
      have h_ev := ih e (by omega) hge db1 db2 r1 r2
      have h_foldl := inList_foldl_eval_independent
        (evalExprCore db1 r1 subqueryEval) (evalExprCore db2 r2 subqueryEval)
        (evalExprCore db1 r1 subqueryEval e) (evalExprCore db2 r2 subqueryEval e)
        h_ev vals
        (fun vi hvi => by
          have hgvi := foldl_and_true_forall hgv hvi
          have h_sz_vi : sizeOf vi < sizeOf (Expr.inList e _neg vals) := by
            have := List.sizeOf_lt_of_mem hvi; simp_wf; omega
          exact ih vi (by omega) hgvi db1 db2 r1 r2)
        (some (.bool false))
      -- Reduce let bindings, then rewrite the foldl
      dsimp only []
      rw [h_foldl]
    | inSubquery e _neg sel =>
      simp [isGroundCore] at hg
      have h_sz_e : sizeOf e < sizeOf (Expr.inSubquery e _neg sel) := by simp_wf; omega
      simp only [evalExprCore]
      rw [ih e (by omega) hg.1 db1 db2 r1 r2, h_sq sel hg.2 db1 db2 r1 r2]
    | «exists» _neg sel =>
      simp [isGroundCore] at hg
      simp only [evalExprCore]
      rw [h_sq sel hg db1 db2 r1 r2]
    | subquery sel =>
      simp [isGroundCore] at hg
      simp only [evalExprCore]
      rw [h_sq sel hg db1 db2 r1 r2]
    | between e lo hi =>
      simp [isGroundCore] at hg
      have h_sz_e : sizeOf e < sizeOf (Expr.between e lo hi) := by simp_wf; omega
      have h_sz_lo : sizeOf lo < sizeOf (Expr.between e lo hi) := by simp_wf; omega
      have h_sz_hi : sizeOf hi < sizeOf (Expr.between e lo hi) := by simp_wf; omega
      simp only [evalExprCore]
      -- hg has structure: (isGroundCore sg e ∧ isGroundCore sg lo) ∧ isGroundCore sg hi
      rw [ih e (by omega) hg.1.1 db1 db2 r1 r2,
          ih lo (by omega) hg.1.2 db1 db2 r1 r2,
          ih hi (by omega) hg.2 db1 db2 r1 r2]
    | windowFn _ _ _ => simp [evalExprCore]

-- ============================================================================
-- Subquery evaluator congruence
-- ============================================================================

/-- If two subquery evaluators agree on all subqueries that appear inside an expression
    (determined by size bound), then evalExprCore produces the same result. -/
theorem evalExprCore_sqe_congr (db : Database) (row : Row)
    (sqe1 sqe2 : Database → Row → SubQuery → Table)
    (e : Expr)
    (h : ∀ sel, sizeOf sel < sizeOf e → ∀ db' r', sqe1 db' r' sel = sqe2 db' r' sel) :
    evalExprCore db row sqe1 e = evalExprCore db row sqe2 e := by
  suffices key : ∀ (n : Nat) (e : Expr), sizeOf e < n →
      (∀ sel, sizeOf sel < sizeOf e → ∀ db' r', sqe1 db' r' sel = sqe2 db' r' sel) →
      evalExprCore db row sqe1 e = evalExprCore db row sqe2 e by
    exact key (sizeOf e + 1) e (Nat.lt_succ_of_le (Nat.le_refl _)) h
  intro n
  induction n with
  | zero => intro e hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro e hlt h_sq
    cases e with
    | lit _ => simp [evalExprCore]
    | col _ => simp [evalExprCore]
    | binOp op l r =>
      simp only [evalExprCore]
      have h_sz_l : sizeOf l < sizeOf (Expr.binOp op l r) := by simp_wf; omega
      have h_sz_r : sizeOf r < sizeOf (Expr.binOp op l r) := by simp_wf; omega
      rw [ih l (by omega) (fun sel hs => h_sq sel (by omega)),
          ih r (by omega) (fun sel hs => h_sq sel (by omega))]
    | unaryOp op e =>
      simp only [evalExprCore]
      have h_sz : sizeOf e < sizeOf (Expr.unaryOp op e) := by simp_wf; omega
      rw [ih e (by omega) (fun sel hs => h_sq sel (by omega))]
    | func name args =>
      simp only [evalExprCore]
      congr 1
      apply List.map_congr_left
      intro e he
      have h_sz : sizeOf e < sizeOf (Expr.func name args) := by
        have := List.sizeOf_lt_of_mem he; simp_wf; omega
      exact ih e (by omega) (fun sel hs => h_sq sel (by omega))
    | agg _ _ _ => simp [evalExprCore]
    | countStar => simp [evalExprCore]
    | «case» branches else_ =>
      rw [evalExprCore_case, evalExprCore_case]
      have h_sz_case : sizeOf branches < sizeOf (Expr.case branches else_) := by simp_wf; omega
      apply evalCaseHelper_congr
      · cases else_ with
        | none => rfl
        | some e =>
          have h_sz : sizeOf e < sizeOf (Expr.case branches (some e)) := by simp_wf; omega
          exact ih e (by omega) (fun sel hs => h_sq sel (by omega))
      · intro pair hp
        have h_pair_lt := List.sizeOf_lt_of_mem hp
        have h_pair_sz : sizeOf pair = 1 + sizeOf pair.fst + sizeOf pair.snd := by
          obtain ⟨a, b⟩ := pair; simp [Prod.mk.sizeOf_spec]
        exact ⟨ih pair.1 (by omega) (fun sel hs => h_sq sel (by omega)),
               ih pair.2 (by omega) (fun sel hs => h_sq sel (by omega))⟩
    | inList e _neg vals =>
      have h_sz_e : sizeOf e < sizeOf (Expr.inList e _neg vals) := by simp_wf; omega
      have h_ev := ih e (by omega) (fun sel hs => h_sq sel (by omega))
      have h_vals : ∀ vi, vi ∈ vals → evalExprCore db row sqe1 vi = evalExprCore db row sqe2 vi := by
        intro vi hvi
        have h_sz_vi : sizeOf vi < sizeOf (Expr.inList e _neg vals) := by
          have := List.sizeOf_lt_of_mem hvi; simp_wf; omega
        exact ih vi (by omega) (fun sel hs => h_sq sel (by omega))
      rw [evalExprCore_inList, evalExprCore_inList]
      dsimp only []
      rw [inList_foldl_eval_independent (evalExprCore db row sqe1) (evalExprCore db row sqe2) _ _ h_ev vals h_vals]
    | inSubquery e _neg sel =>
      have h_sz_e : sizeOf e < sizeOf (Expr.inSubquery e _neg sel) := by simp_wf; omega
      have h_sz_sel : sizeOf sel < sizeOf (Expr.inSubquery e _neg sel) := by simp_wf
      simp only [evalExprCore]
      rw [ih e (by omega) (fun sel' hs => h_sq sel' (by omega)),
          h_sq sel h_sz_sel db row]
    | «exists» _neg sel =>
      have h_sz_sel : sizeOf sel < sizeOf (Expr.exists _neg sel) := by simp_wf
      simp only [evalExprCore]
      rw [h_sq sel h_sz_sel db row]
    | subquery sel =>
      have h_sz_sel : sizeOf sel < sizeOf (Expr.subquery sel) := by simp_wf
      simp only [evalExprCore]
      rw [h_sq sel h_sz_sel db row]
    | between e lo hi =>
      have h_sz_e : sizeOf e < sizeOf (Expr.between e lo hi) := by simp_wf; omega
      have h_sz_lo : sizeOf lo < sizeOf (Expr.between e lo hi) := by simp_wf; omega
      have h_sz_hi : sizeOf hi < sizeOf (Expr.between e lo hi) := by simp_wf; omega
      simp only [evalExprCore]
      rw [ih e (by omega) (fun sel hs => h_sq sel (by omega)),
          ih lo (by omega) (fun sel hs => h_sq sel (by omega)),
          ih hi (by omega) (fun sel hs => h_sq sel (by omega))]
    | windowFn _ _ _ => simp [evalExprCore]

-- ============================================================================
-- Helper lemmas for evalSelectCore_outerRow_congr
-- ============================================================================

/-- map with a constant function: same length → same result -/
private theorem map_const_length_eq' {α β : Type} (f : α → β)
    (xs ys : List α) (c : β) (hf : ∀ x, f x = c) (hlen : xs.length = ys.length) :
    xs.map f = ys.map f := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a rest ih =>
    cases ys with
    | nil => simp at hlen
    | cons b rest' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.map_cons]
      rw [hf a, hf b]
      exact congrArg (c :: ·) (ih rest' hlen)

/-- filter with a constant predicate: length depends only on input length. -/
private theorem filter_const_length_eq' {α : Type} (f : α → Bool)
    (xs ys : List α) (c : Bool) (hf : ∀ x, f x = c) (hlen : xs.length = ys.length) :
    (xs.filter f).length = (ys.filter f).length := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a rest ih =>
    cases ys with
    | nil => simp at hlen
    | cons b rest' =>
      simp only [List.filter_cons, List.length_cons, Nat.add_right_cancel_iff] at hlen ⊢
      rw [hf a, hf b]
      cases c <;> simp [ih rest' hlen]

/-- flatMap with membership-dependent congr. -/
theorem flatMap_congr_mem {α β : Type} {f g : α → List β} {l : List α}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self]
    rw [ih (fun a ha => h a (List.mem_cons_of_mem x ha))]

/-- When two map functions agree regardless of second argument, mapping over zip
    with different second lists (of the same length) gives the same result. -/
private theorem map_zip_congr_snd {α β γ : Type} (ns : List α) (xs ys : List β)
    (f g : α × β → γ) (hlen : xs.length = ys.length)
    (hfg : ∀ (a : α) (b1 b2 : β), f (a, b1) = g (a, b2)) :
    (ns.zip xs).map f = (ns.zip ys).map g := by
  induction ns generalizing xs ys with
  | nil => simp
  | cons n rest ih =>
    cases xs with
    | nil => cases ys with | nil => simp | cons _ _ => simp at hlen
    | cons x xs' =>
      cases ys with
      | nil => simp at hlen
      | cons y ys' =>
        simp only [List.zip_cons_cons, List.map_cons, List.length_cons,
                   Nat.add_right_cancel_iff] at *
        congr 1
        · exact hfg n x y
        · exact ih xs' ys' hlen

-- ============================================================================
-- GROUP BY with constant keys: foldl addToGroups produces single group
-- ============================================================================

/-- The inline addToGroups function from evalSelectProjectDistinct, extracted for proofs. -/
private def addToGroupsByKey
    (exprEval : Database → Row → Expr → Option Value) (db : Database) (groupBy : List Expr)
    (groups : List (List (Option Value) × Table)) (row : Row) :
    List (List (Option Value) × Table) :=
  let key := groupBy.map (exprEval db row)
  match groups.find? (fun (k, _) => k == key) with
  | some _ => groups.map fun (k, rs) => if k == key then (k, rs ++ [row]) else (k, rs)
  | none => groups ++ [(key, [row])]

/-- Accumulator invariant: foldl with constant key on [(k0, acc)] gives [(k0, acc ++ rows)]. -/
private theorem foldl_addToGroupsByKey_const_key_acc
    (exprEval : Database → Row → Expr → Option Value) (db : Database) (groupBy : List Expr)
    (k0 : List (Option Value)) (acc : Table) (rows : Table)
    (hk : ∀ row ∈ rows, groupBy.map (exprEval db row) = k0) :
    rows.foldl (addToGroupsByKey exprEval db groupBy) [(k0, acc)] = [(k0, acc ++ rows)] := by
  induction rows generalizing acc with
  | nil => simp [List.append_nil]
  | cons row rest ih =>
    simp only [List.foldl_cons]
    have hk_row : groupBy.map (exprEval db row) = k0 := hk row List.mem_cons_self
    have hk_rest : ∀ r ∈ rest, groupBy.map (exprEval db r) = k0 :=
      fun r hr => hk r (List.mem_cons_of_mem row hr)
    simp only [addToGroupsByKey, hk_row]
    simp only [List.find?_cons, beq_self_eq_true, List.map_cons, List.map_nil,
               ite_true]
    rw [ih (acc ++ [row]) hk_rest]
    congr 1; congr 1
    rw [List.append_assoc]; rfl

/-- foldl with constant key from empty produces [(k0, rows)] for non-empty rows. -/
private theorem foldl_addToGroupsByKey_const_key
    (exprEval : Database → Row → Expr → Option Value) (db : Database) (groupBy : List Expr)
    (k0 : List (Option Value)) (row : Row) (rest : Table)
    (hk_row : groupBy.map (exprEval db row) = k0)
    (hk_rest : ∀ r ∈ rest, groupBy.map (exprEval db r) = k0) :
    (row :: rest).foldl (addToGroupsByKey exprEval db groupBy) [] = [(k0, row :: rest)] := by
  simp only [List.foldl_cons, addToGroupsByKey, hk_row, List.find?_nil, List.nil_append]
  rw [foldl_addToGroupsByKey_const_key_acc exprEval db groupBy k0 [row] rest hk_rest]
  simp

-- ============================================================================
-- evalSelectProjectDistinct: equality from length and row-independent callbacks
-- ============================================================================

/-- evalSelectProjectDistinct depends only on filteredRows.length when all callbacks
    are row-independent. This is the core lemma for the outer row congruence. -/
theorem evalSelectProjectDistinct_eq_of_length_eq
    (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr)
    (fr1 fr2 : Table) (hlen : fr1.length = fr2.length)
    (h_gb : ∀ e ∈ groupBy, ∀ row1 row2, exprEval db row1 e = exprEval db row2 e)
    (h_hv : ∀ cond, having = some cond →
        ∀ row1 row2, exprEval db row1 cond = exprEval db row2 cond)
    (h_items_no_star : ∀ item ∈ items, ∃ e alias_, item = .exprItem e alias_)
    (h_si : ∀ item ∈ items, ∀ row1 row2,
        selectItemEval db row1 item = selectItemEval db row2 item)
    (h_sia : ∀ item ∈ items, ∀ rows1 rows2 s1 s2,
        rows1.length = rows2.length →
        selectItemWithAggEval db rows1 s1 item = selectItemWithAggEval db rows2 s2 item)
    (h_ea : ∀ cond, having = some cond → ∀ rows1 rows2 s1 s2,
        rows1.length = rows2.length →
        exprWithAggEval db rows1 s1 cond = exprWithAggEval db rows2 s2 cond)
    (h_ew : ∀ e alias_, .exprItem e alias_ ∈ items → ∀ row1 row2 p1 p2 sp1 sp2 idx,
        p1.length = p2.length →
        exprWithWindowEval db row1 p1 sp1 idx e = exprWithWindowEval db row2 p2 sp2 idx e) :
    evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval exprWithAggEval
      exprWithWindowEval hasWindowFn hasAgg distinct items groupBy having fr1 =
    evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval exprWithAggEval
      exprWithWindowEval hasWindowFn hasAgg distinct items groupBy having fr2 := by
  unfold evalSelectProjectDistinct
  -- Split on distinct (eraseDups wrapper)
  cases distinct
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  -- Split on the 4 branches
  all_goals {
    split
    · -- GROUP BY branch
      first | apply congrArg List.eraseDups | skip
      cases fr1 with
      | nil =>
        cases fr2 with | nil => rfl | cons _ _ => simp at hlen
      | cons row1 rest1 =>
        cases fr2 with
        | nil => simp at hlen
        | cons row2 rest2 =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hk0 : ∀ row, groupBy.map (exprEval db row) = groupBy.map (exprEval db row1) :=
            fun row => List.map_congr_left fun e he => h_gb e he row row1
          have hfold1 := foldl_addToGroupsByKey_const_key exprEval db groupBy _ row1 rest1
            rfl (fun r _ => hk0 r)
          have hfold2 := foldl_addToGroupsByKey_const_key exprEval db groupBy _ row2 rest2
            (hk0 row2) (fun r _ => hk0 r)
          unfold addToGroupsByKey at hfold1 hfold2
          rw [hfold1, hfold2]
          simp only [List.filterMap_cons, List.filterMap_nil, List.head?_cons]
          have hlen' : (row1 :: rest1).length = (row2 :: rest2).length := by simp [hlen]
          cases having with
          | none =>
            dsimp only []
            simp only [ite_true]
            exact congrArg (fun x => [x]) (flatMap_congr_mem fun item hmem =>
              h_sia item hmem (row1 :: rest1) (row2 :: rest2) _ _ hlen')
          | some hcond =>
            dsimp only []
            have hph : (exprWithAggEval db (row1 :: rest1) row1 hcond == some (Value.bool true)) =
                (exprWithAggEval db (row2 :: rest2) row2 hcond == some (Value.bool true)) := by
              congr 1; exact h_ea hcond rfl (row1 :: rest1) (row2 :: rest2) _ _ hlen'
            simp only [hph]
            cases (exprWithAggEval db (row2 :: rest2) row2 hcond == some (Value.bool true)) with
            | true =>
              simp only [ite_true]
              exact congrArg (fun x => [x]) (flatMap_congr_mem fun item hmem =>
                h_sia item hmem (row1 :: rest1) (row2 :: rest2) _ _ hlen')
            | false => simp
    · split
      · -- Aggregate branch
        first | apply congrArg List.eraseDups | skip
        cases having with
        | none =>
          simp only [ite_true]
          exact congrArg (fun x => [x]) (flatMap_congr_mem fun item hmem =>
            h_sia item hmem fr1 fr2 _ _ hlen)
        | some hcond =>
          simp only []
          have hph : (exprWithAggEval db fr1 (fr1.head?.getD []) hcond == some (Value.bool true)) =
              (exprWithAggEval db fr2 (fr2.head?.getD []) hcond == some (Value.bool true)) := by
            congr 1; exact h_ea hcond rfl fr1 fr2 _ _ hlen
          simp only [hph]
          split
          · exact congrArg (fun x => [x]) (flatMap_congr_mem fun item hmem =>
              h_sia item hmem fr1 fr2 _ _ hlen)
          · rfl
      · split
        · -- Window branch
          first | apply congrArg List.eraseDups | skip
          cases having with
          | none =>
            rw [show fr2.length = fr1.length from hlen.symm]
            apply map_zip_congr_snd _ fr1 fr2 _ _ hlen
            intro idx row1 row2
            apply flatMap_congr_mem
            intro item hmem
            obtain ⟨e, alias_, rfl⟩ := h_items_no_star item hmem
            simp only []
            rw [h_ew e alias_ hmem row1 row2 fr1 fr2 fr1 fr2 idx hlen]
          | some hcond =>
            simp only []
            have hlf : (fr1.filter (fun row => exprEval db row hcond == some (Value.bool true))).length =
                (fr2.filter (fun row => exprEval db row hcond == some (Value.bool true))).length :=
              filter_const_length_eq' _ fr1 fr2
                (exprEval db (fr1.head?.getD []) hcond == some (Value.bool true))
                (fun row => by congr 1; exact h_hv hcond rfl row _) hlen
            rw [show (fr2.filter _).length = (fr1.filter _).length from hlf.symm]
            apply map_zip_congr_snd _ _ _ _ _ hlf
            intro idx row1 row2
            apply flatMap_congr_mem
            intro item hmem
            obtain ⟨e, alias_, rfl⟩ := h_items_no_star item hmem
            simp only []
            rw [h_ew e alias_ hmem row1 row2 _ _ _ _ idx hlf]
        · -- Simple branch
          first | apply congrArg List.eraseDups | skip
          have hf_const : ∀ row, items.flatMap (selectItemEval db row) =
              items.flatMap (selectItemEval db (fr1.head?.getD [])) :=
            fun row => flatMap_congr_mem fun item hmem => h_si item hmem row _
          cases having with
          | none =>
            exact map_const_length_eq' _ _ _ _ hf_const hlen
          | some hcond =>
            apply map_const_length_eq' _ _ _ _ hf_const
            apply filter_const_length_eq' _ _ _
              (exprEval db (fr1.head?.getD []) hcond == some (Value.bool true))
            · intro row; congr 1; exact h_hv hcond rfl row _
            · exact hlen
  }

-- ============================================================================
-- evalSelectCore outer row congruence
-- ============================================================================

/-- When all expression callbacks are row-independent for the expressions used
    in sel, changing outerRow doesn't affect the evalSelectCore result. -/
theorem evalSelectCore_outerRow_congr (db : Database) (r1 r2 : Row)
    (fromEval : Database → FromClause → Table)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (sel : SelectStmt)
    (h_wc : ∀ e, sel.whereClause = some e →
        ∀ row1 row2, exprEval db row1 e = exprEval db row2 e)
    (h_gb : ∀ e, e ∈ sel.groupBy → ∀ row1 row2, exprEval db row1 e = exprEval db row2 e)
    (h_hv : ∀ e, sel.having = some e →
        ∀ row1 row2, exprEval db row1 e = exprEval db row2 e)
    (h_items_no_star : ∀ item ∈ sel.items, ∃ e alias_, item = .exprItem e alias_)
    (h_si : ∀ item ∈ sel.items, ∀ row1 row2,
        selectItemEval db row1 item = selectItemEval db row2 item)
    (h_sia : ∀ item ∈ sel.items, ∀ rows1 rows2 s1 s2,
        rows1.length = rows2.length →
        selectItemWithAggEval db rows1 s1 item = selectItemWithAggEval db rows2 s2 item)
    (h_ea : ∀ e, sel.having = some e → ∀ rows1 rows2 s1 s2,
        rows1.length = rows2.length →
        exprWithAggEval db rows1 s1 e = exprWithAggEval db rows2 s2 e)
    (h_ew : ∀ e alias_, .exprItem e alias_ ∈ sel.items → ∀ row1 row2 p1 p2 sp1 sp2 idx,
        p1.length = p2.length →
        exprWithWindowEval db row1 p1 sp1 idx e = exprWithWindowEval db row2 p2 sp2 idx e) :
    evalSelectCore db r1 fromEval exprEval selectItemEval selectItemWithAggEval exprWithAggEval
      compareEval exprWithWindowEval hasWindowFn hasAgg sel =
    evalSelectCore db r2 fromEval exprEval selectItemEval selectItemWithAggEval exprWithAggEval
      compareEval exprWithWindowEval hasWindowFn hasAgg sel := by
  obtain ⟨d, items, from_, wc, gb, hv, ob, lim, off⟩ := sel
  simp only [SelectStmt.whereClause, SelectStmt.groupBy, SelectStmt.having,
             SelectStmt.items] at *
  simp only [evalSelectCore_eq_afterFilter, evalSelectAfterFilter]
  -- The aligned ORDER BY takes (sources, rows); both are row-context
  -- independent: sources because the outer prefix is stripped, rows by the
  -- existing projection congruence.
  have congr2 : ∀ {α β γ : Type} (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β},
      a₁ = a₂ → b₁ = b₂ → f a₁ b₁ = f a₂ b₂ := by
    intro _ _ _ f _ _ _ _ h1 h2; rw [h1, h2]
  apply congr2
  · -- sources: (havingRows).map (drop outer.length) is context-independent
    cases wc with
    | none =>
      cases hv with
      | none =>
        simp [List.map_map, Function.comp_def]
      | some hcond =>
        simp only [List.filter_map, List.map_map, Function.comp_def,
          List.drop_left, List.map_id']
        exact List.filter_congr (fun row _ => by
          congr 1; exact h_hv hcond rfl (r1 ++ row) (r2 ++ row))
    | some wcond =>
      cases hv with
      | none =>
        simp only [List.filter_map, List.map_map, Function.comp_def,
          List.drop_left, List.map_id']
        exact List.filter_congr (fun row _ => by
          congr 1; exact h_wc wcond rfl (r1 ++ row) (r2 ++ row))
      | some hcond =>
        simp only [List.filter_map, List.map_map, Function.comp_def,
          List.drop_left, List.map_id', List.filter_filter]
        exact List.filter_congr (fun row _ => by
          rw [h_wc wcond rfl (r1 ++ row) (r2 ++ row),
              h_hv hcond rfl (r1 ++ row) (r2 ++ row)])
  · -- rows: projection congruence (unchanged machinery)
    cases wc with
    | none =>
      exact evalSelectProjectDistinct_eq_of_length_eq db _ _ _ _ _ _ _
        d items gb hv _ _ (by simp [List.length_map])
        h_gb h_hv h_items_no_star h_si h_sia h_ea h_ew
    | some wcond =>
      exact evalSelectProjectDistinct_eq_of_length_eq db _ _ _ _ _ _ _
        d items gb hv _ _
        (by apply filter_const_length_eq' _ _ _
              (exprEval db r1 wcond == some (Value.bool true))
            · intro row; congr 1; exact h_wc wcond rfl row r1
            · simp [List.length_map])
        h_gb h_hv h_items_no_star h_si h_sia h_ea h_ew

end SqlEquiv
