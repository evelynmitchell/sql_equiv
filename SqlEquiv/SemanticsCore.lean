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
    (subqueryEval : Database → Row → SelectStmt → Table) : Expr → Option Value
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
    (selectEval : Database → SelectStmt → Table) : FromClause → Table
  | .table t =>
    let baseTable := db t.name
    let qualifier := t.alias.getD t.name
    baseTable.map fun row =>
      row.map fun (col, val) => (s!"{qualifier}.{col}", val)
  | .subquery sel alias =>
    let subResult := selectEval db sel
    subResult.map fun row =>
      row.map fun (col, val) => (s!"{alias}.{col}", val)
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
    (sqe : Database → Row → SelectStmt → Table) (v : Value) :
    evalExprCore db row sqe (.lit v) = some v := by
  simp [evalExprCore]

theorem evalExprCore_binOp (db : Database) (row : Row)
    (sqe : Database → Row → SelectStmt → Table) (op : BinOp) (l r : Expr) :
    evalExprCore db row sqe (.binOp op l r) =
    evalBinOp op (evalExprCore db row sqe l) (evalExprCore db row sqe r) := by
  simp [evalExprCore]

theorem evalExprCore_unaryOp (db : Database) (row : Row)
    (sqe : Database → Row → SelectStmt → Table) (op : UnaryOp) (e : Expr) :
    evalExprCore db row sqe (.unaryOp op e) =
    evalUnaryOp op (evalExprCore db row sqe e) := by
  simp [evalExprCore]

theorem evalExprCore_func (db : Database) (row : Row)
    (sqe : Database → Row → SelectStmt → Table) (name : String) (args : List Expr) :
    evalExprCore db row sqe (.func name args) =
    evalFunc name (args.map fun e => evalExprCore db row sqe e) := by
  simp [evalExprCore]

theorem evalExprCore_between (db : Database) (row : Row)
    (sqe : Database → Row → SelectStmt → Table) (e lo hi : Expr) :
    evalExprCore db row sqe (.between e lo hi) =
    evalBinOp .and (evalBinOp .ge (evalExprCore db row sqe e) (evalExprCore db row sqe lo))
                   (evalBinOp .le (evalExprCore db row sqe e) (evalExprCore db row sqe hi)) := by
  simp [evalExprCore]

theorem evalExprCore_inList (db : Database) (row : Row)
    (sqe : Database → Row → SelectStmt → Table) (e : Expr) (neg : Bool) (vals : List Expr) :
    evalExprCore db row sqe (.inList e neg vals) =
    (let ev := evalExprCore db row sqe e
     let result := vals.foldl (fun acc vi =>
       evalBinOp .or acc (evalBinOp .eq ev (evalExprCore db row sqe vi))
     ) (some (.bool false))
     if neg then evalUnaryOp .not result else result) := by
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
      | null _ => simp; exact ih

/-- evalExprCore unfolds for CASE expressions to evalCaseHelper. -/
theorem evalExprCore_case (db : Database) (row : Row)
    (sqe : Database → Row → SelectStmt → Table) (branches : List (Expr × Expr)) (else_ : Option Expr) :
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

theorem evalFromCore_cross_join (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectEval : Database → SelectStmt → Table)
    (left right : FromClause) :
    evalFromCore db exprEval selectEval (.join left .cross right none) =
    let rightRows := evalFromCore db exprEval selectEval right
    (evalFromCore db exprEval selectEval left).flatMap fun lr =>
      rightRows.map fun rr => lr ++ rr := by
  simp [evalFromCore]

theorem evalFromCore_inner_join (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectEval : Database → SelectStmt → Table)
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
    (selectEval : Database → SelectStmt → Table)
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
    (selectEval : Database → SelectStmt → Table)
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
    let leftResult := queryEval db left
    let rightResult := queryEval db right
    match op with
    | .union => (leftResult ++ rightResult).eraseDups
    | .unionAll => leftResult ++ rightResult
    | .intersect => leftResult.filter fun row => rightResult.contains row
    | .exceptOp => leftResult.filter fun row => !rightResult.contains row
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
    let l := queryEval db left
    let r := queryEval db right
    match op with
    | .union => (l ++ r).eraseDups
    | .unionAll => l ++ r
    | .intersect => l.filter fun row => r.contains row
    | .exceptOp => l.filter fun row => !r.contains row := by
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
      let havingRows := match sel.having with
        | some cond =>
          filteredRows.filter fun row =>
            exprEval db row cond == some (Value.bool true)
        | none => filteredRows
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
      let havingRows := match sel.having with
        | some cond =>
          filteredRows.filter fun row =>
            exprEval db row cond == some (Value.bool true)
        | none => filteredRows
      havingRows.map fun row => sel.items.flatMap (selectItemEval db row)

  -- 6. DISTINCT
  let distinctRows : Table := if sel.distinct then
    projectedRows.eraseDups
  else
    projectedRows

  -- 7. ORDER BY
  let orderedRows : Table := if sel.orderBy.isEmpty then distinctRows else
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

/-- Steps 7-9 of the evaluation pipeline: ORDER BY + OFFSET + LIMIT.
    Factored out as a small function for length proofs. -/
private def applyOrderByLimitOffset
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (db : Database) (orderBy : List OrderByItem) (limit offset : Option Nat)
    (rows : Table) : Table :=
  let orderedRows : Table := if orderBy.isEmpty then rows else
    rows.mergeSort fun r1 r2 =>
      compareEval db r1 r2 orderBy
  let offsetRows : Table := match offset with
    | some n => orderedRows.drop n
    | none => orderedRows
  match limit with | some n => offsetRows.take n | none => offsetRows

/-- Changing the ORDER BY comparator doesn't change the length of the pipeline output. -/
private theorem applyOrderByLimitOffset_length_eq
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (db : Database) (orderBy1 orderBy2 : List OrderByItem)
    (limit offset : Option Nat) (rows : Table) :
    (applyOrderByLimitOffset compareEval db orderBy1 limit offset rows).length =
    (applyOrderByLimitOffset compareEval db orderBy2 limit offset rows).length := by
  simp only [applyOrderByLimitOffset]
  -- Case split limit/offset first (they're still in scope), then split the if-then-else
  cases limit <;> cases offset <;>
    simp only [] <;>  -- normalize
    (split <;> split <;> simp [List.length_mergeSort, List.length_take, List.length_drop])

/-- ORDER BY + OFFSET + LIMIT on empty list produces empty list. -/
private theorem applyOrderByLimitOffset_nil
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (db : Database) (orderBy : List OrderByItem) (limit offset : Option Nat) :
    applyOrderByLimitOffset compareEval db orderBy limit offset [] = [] := by
  simp only [applyOrderByLimitOffset, List.mergeSort_nil]
  cases limit <;> cases offset <;> simp

/-- Steps 3-6 of the evaluation pipeline (after WHERE, before ORDER BY):
    GROUP BY, HAVING, projection, DISTINCT. -/
private def evalSelectProjectDistinct (db : Database)
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

/-- Steps 3-9 of the evaluation pipeline (after WHERE filtering).
    Takes filteredRows as input and applies GROUP BY, HAVING, projection,
    DISTINCT, ORDER BY, OFFSET, and LIMIT. Factored as composition of
    evalSelectProjectDistinct + applyOrderByLimitOffset. -/
private def evalSelectAfterFilter (db : Database)
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
    (filteredRows : Table) : Table :=
  applyOrderByLimitOffset compareEval db orderBy limit offset
    (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg distinct items
      groupBy having filteredRows)

/-- evalSelectProjectDistinct on empty input produces empty output
    when there are no aggregates. -/
private theorem evalSelectProjectDistinct_nil (db : Database)
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
private theorem evalSelectCore_eq_afterFilter (db : Database) (outerRow : Row)
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
      distinct items groupBy having orderBy limit offset filteredRows := by
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
  simp only [evalSelectCore_eq_afterFilter, evalSelectAfterFilter, applyOrderByLimitOffset]


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
  exact applyOrderByLimitOffset_length_eq _ _ _ _ _ _ _

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
private theorem List.filter_eq_nil_of_false {α : Type} (l : List α) (p : α → Bool)
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
    distinct items groupBy having orderBy limit offset
    (List.filter (fun row => exprEval db row cond == some (Value.bool true))
      (List.map (fun row => outerRow ++ row)
        (match from_ with | some f => fromEval db f | none => [[]]))) = []
  -- filteredRows = [] because all rows are rejected
  rw [List.filter_eq_nil_of_false _ _ hAllFalse]
  -- evalSelectAfterFilter ... [] = applyOrderByLimitOffset ... (evalSelectProjectDistinct ... [])
  simp only [evalSelectAfterFilter]
  -- evalSelectProjectDistinct ... [] = [] (no aggregates)
  rw [evalSelectProjectDistinct_nil _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg]
  -- applyOrderByLimitOffset ... [] = []
  exact applyOrderByLimitOffset_nil _ _ _ _ _

end SqlEquiv
