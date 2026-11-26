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
import SqlEquiv.SemanticsParam
import SqlEquiv.AstSize

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
    | some v => some (inSubqueryResult neg v (subqueryEval db row sel))
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
  | .subquery sel alias =>
    -- standard derived-table scoping: columns are qualified by the alias (#257)
    (selectEval db sel).map (requalifyRow alias)
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
     | some v => some (inSubqueryResult neg v (sqe db row sel))) := by
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
    simp only [List.foldl, evalCaseHelper, Bool.false_eq_true, ↓reduceIte]
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
    evalFromCore db exprEval selectEval (.subquery sel alias) =
      (selectEval db sel).map (requalifyRow alias) := by
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
    applySetOp op (Query.outputNames? left) (queryEval db left) (queryEval db right)
  | .withCTE ctes query =>
    let dbWithCtes := ctes.foldl (fun db' cte =>
      fun name =>
        if name == cte.name then
          if cte.isRecursive then
            cteEval db' cte.name cte.query
          else
            (queryEval db' cte.query).map unqualifyRow
        else
          db' name
    ) db
    queryEval dbWithCtes query
  -- `ORDER BY`/`LIMIT` over a compound query (#317) is delegated whole to `queryEval`.
  | q@(.ordered ..) => queryEval db q

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
    applySetOp op (Query.outputNames? left) (queryEval db left) (queryEval db right) := by
  rfl

-- ============================================================================
-- Non-Partial Core SELECT Evaluator
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

-- ============================================================================
-- Grouped ORDER BY sort keys (#234)
-- ============================================================================

/-- Name of the hidden sort-key column for the `k`-th ORDER BY item of a
    grouped query. Never part of the query output. -/
def groupOrderKeyName (k : Nat) : String := s!"__group_orderkey_{k}"

/-- Grouped ORDER BY items, rewritten to reference the per-group sort-key
    columns built by `groupOrderKeyRow` (same length and directions). -/
def groupOrderByItems (orderBy : List OrderByItem) : List OrderByItem :=
  ((List.range orderBy.length).zip orderBy).map fun (k, item) =>
    OrderByItem.mk (.col ⟨none, groupOrderKeyName k⟩) item.dir item.nulls

/-- Sort-key row for one group (#234). Each ORDER BY expression is evaluated
    in the group's aggregate context (the same one SELECT items and HAVING
    use) against `projected ++ sampleRow`: aggregates such as `count(*)` range
    over the group's rows, and column names resolve against the output row
    first, so aliases win over source columns, and expressions may mix both
    (`total + COUNT(*)`). Non-projected grouping columns resolve against the
    sample row. Keys that evaluate to `none` are omitted (compared as before:
    skipped). -/
def groupOrderKeyRow (db : Database)
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (orderBy : List OrderByItem) (groupRows : Table) (sampleRow projected : Row) : Row :=
  ((List.range orderBy.length).zip orderBy).filterMap fun (k, item) =>
    (exprWithAggEval db groupRows (projected ++ sampleRow) item.expr).map
      fun v => (groupOrderKeyName k, v)

/-- Per-group sort-key rows for a GROUP BY query, aligned 1:1 with the
    grouped projection in `evalSelectCore` / `evalSelectProjectDistinct`
    (same grouping, same per-group HAVING test, same order). -/
def evalSelectGroupOrderKeys (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (filteredRows : Table) : Table :=
  let addToGroups (groups : List (List (Option Value) × Table)) (row : Row) :
      List (List (Option Value) × Table) :=
    let key := groupBy.map (fun e => (exprEval db row e).map Value.setKey)
    match groups.find? (fun (k, _) => k == key) with
    | some _ => groups.map fun (k, rs) => if k == key then (k, rs ++ [row]) else (k, rs)
    | none => groups ++ [(key, [row])]
  let groups := filteredRows.foldl addToGroups []
  groups.filterMap fun (_key, groupRows) =>
    match bareSampleRow (exprEval db) (selectMinMaxCalls items having) groupRows with
    | none => none
    | some sampleRow =>
      let passesHaving := match having with
        | none => true
        | some cond =>
          exprWithAggEval db groupRows sampleRow cond == some (Value.bool true)
      if passesHaving then
        some (groupOrderKeyRow db exprWithAggEval orderBy groupRows sampleRow
          (items.flatMap (selectItemWithAggEval db groupRows sampleRow)))
      else
        none

/-- Project the SELECT items of one row in the window-function path: `*` and
    `t.*` pass the row through, expression items go through the window-aware
    evaluator. A named helper (rather than an inline lambda) so congruence
    lemmas can rewrite it (#212). -/
def projectWindowItems
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (db : Database) (row : Row) (partition sortedPartition : Table) (idx : Nat)
    (items : List SelectItem) : List (String × Value) :=
  items.flatMap fun item =>
    match item with
    | .star none => row
    | .star (some t) => row.filter fun (k, _) => k.startsWith s!"{t}."
    | .exprItem e alias =>
      match exprWithWindowEval db row partition sortedPartition idx e with
      | some v => [(alias.getD (exprToName e), v)]
      | none => [(alias.getD (exprToName e), .null none)]

/-- `projectWindowItems` only uses the evaluator on the items' expressions. -/
theorem projectWindowItems_congr
    (wA wB : Database → Row → Table → Table → Nat → Expr → Option Value)
    (db : Database) (row : Row) (p sp : Table) (i : Nat) (items : List SelectItem)
    (h : ∀ e a, SelectItem.exprItem e a ∈ items → wA db row p sp i e = wB db row p sp i e) :
    projectWindowItems wA db row p sp i items = projectWindowItems wB db row p sp i items := by
  unfold projectWindowItems
  induction items with
  | nil => rfl
  | cons it rest ih =>
    simp only [List.flatMap_cons]
    rw [ih (fun e a ha => h e a (List.mem_cons_of_mem it ha))]
    congr 1
    cases it with
    | star t => cases t <;> rfl
    | exprItem e a => simp only [h e a List.mem_cons_self]

/-- A query without `GROUP BY` and without an aggregate in its items outside window functions
    that is still evaluated as an aggregate query, one group:
    - a window query with an aggregate inside a window in the items or in `HAVING` (#438);
    - any query with a `HAVING` (#440), as in the standard, DuckDB and Postgres (registry
      row 22; the sqlite dialect rejects it at parse time, as sqlite does);
    - a query whose only aggregate is in `ORDER BY` (#445), which the pipeline evaluates with
      `HAVING TRUE` (`effectiveHaving`). -/
def implicitGroup (hasWindowFn : List SelectItem → Bool) (items : List SelectItem)
    (having : Option Expr) : Bool :=
  (hasWindowFn items && windowQueryAggregates items having) || having.isSome

/-- Without window functions in the items and without `HAVING`, `implicitGroup` is false. -/
@[simp] theorem implicitGroup_of_noWin {hasWindowFn : List SelectItem → Bool}
    {items : List SelectItem} (h : hasWindowFn items = false) :
    implicitGroup hasWindowFn items none = false := by
  simp [implicitGroup, h]

/-- The groups of a GROUP BY query that survive `HAVING`, each with its rows and its sample row
    (the row bare columns are read on), in the order of the grouped projection. Used by the
    window path over groups (#429); the grouped projection without windows inlines the same
    steps. -/
def groupedSurvivors (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (filteredRows : Table) : List (Table × Row) :=
  let addToGroups (groups : List (List (Option Value) × Table)) (row : Row) :
      List (List (Option Value) × Table) :=
    let key := groupBy.map (fun e => (exprEval db row e).map Value.setKey)
    match groups.find? (fun (k, _) => k == key) with
    | some _ => groups.map fun (k, rs) => if k == key then (k, rs ++ [row]) else (k, rs)
    | none => groups ++ [(key, [row])]
  let groups := filteredRows.foldl addToGroups []
  groups.filterMap fun (_key, groupRows) =>
    match bareSampleRow (exprEval db) (selectMinMaxCalls items having) groupRows with
    | none => none
    | some sampleRow =>
      let passesHaving := match having with
        | none => true
        | some cond =>
          exprWithAggEval db groupRows sampleRow cond == some (Value.bool true)
      if passesHaving then some (groupRows, sampleRow) else none

/-- The one group of an aggregate query without GROUP BY, if it survives `HAVING` (#429). -/
def aggSurvivors (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (having : Option Expr) (filteredRows : Table) :
    List (Table × Row) :=
  let sampleRow :=
    (bareSampleRow (exprEval db) (selectMinMaxCalls items having) filteredRows).getD []
  let passesHaving := match having with
    | none => true
    | some cond =>
      exprWithAggEval db filteredRows sampleRow cond == some (Value.bool true)
  if passesHaving then [(filteredRows, sampleRow)] else []

/-- Hidden column that tells the rows standing for groups apart (#429). -/
def groupWindowMarker : String := "__window_group__"

/-- One row per surviving group for the window evaluator (#429): the group's sample row with
    its index in a hidden column, so rows of different groups always differ (the window
    evaluator finds a row's position by equality). -/
def groupWindowRows (groups : List (Table × Row)) : Table :=
  ((List.range groups.length).zip groups).map fun (i, (_, s)) =>
    s ++ [(groupWindowMarker, Value.int (Int.ofNat i))]

/-- Row evaluator for windows over groups (#429): an expression on the row standing for a group
    is evaluated in that group's aggregate context, so `SUM(age)` in a window's argument,
    `PARTITION BY` or `ORDER BY` is the group's sum. -/
def groupWindowEval (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (groups : List (Table × Row)) : Database → Row → Expr → Option Value :=
  fun db r e =>
    match ((groupWindowRows groups).zip groups).find? (fun p => p.1 == r) with
    | some (_, (rs, s)) => exprWithAggEval db rs s e
    | none => none

/-- Projection of a grouped or aggregate query whose items have window functions (#429), in two
    stages: the groups are formed and filtered by `HAVING` first (`groups`), then each item with
    a window function is evaluated by the window evaluator over one row per group, with
    aggregates evaluated per group (`groupWindowEval`). Items without a window function are
    evaluated as in the grouped projection. -/
def projectGroupsWithWindows (db : Database)
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (groups : List (Table × Row)) : Table :=
  let synth := groupWindowRows groups
  let ev := groupWindowEval exprWithAggEval groups
  ((List.range groups.length).zip (synth.zip groups)).map fun (idx, (row, (rs, s))) =>
    items.flatMap fun item =>
      match item with
      | .exprItem e alias =>
        if exprHasWindowFn e then
          match evalExprWithWindowParam ev db row synth synth idx e with
          | some v => [(alias.getD (exprToName e), v)]
          | none => [(alias.getD (exprToName e), .null none)]
        else selectItemWithAggEval db rs s item
      | .star _ => selectItemWithAggEval db rs s item

theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: t, h => by
    simp only [List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr_mem (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- Whether an `ORDER BY` has a window function among its keys (#435). -/
def orderByHasWindow (orderBy : List OrderByItem) : Bool :=
  orderBy.any fun o => exprHasWindowFn o.expr

@[simp] theorem orderByHasWindow_nil : orderByHasWindow [] = false := rfl

/-- Hidden column holding the value of the `k`-th `ORDER BY` key when it is a window function
    (#435). -/
def windowOrderKeyName (k : Nat) : String := s!"__window_orderkey_{k}"

/-- The `ORDER BY` of the plain path with each window key replaced by its hidden column (#435);
    other keys are unchanged. -/
def windowOrderByItems (orderBy : List OrderByItem) : List OrderByItem :=
  ((List.range orderBy.length).zip orderBy).map fun (k, item) =>
    match item with
    | .mk e d n => if exprHasWindowFn e then .mk (.col ⟨none, windowOrderKeyName k⟩) d n else item

@[simp] theorem windowOrderByItems_nil : windowOrderByItems [] = [] := rfl

/-- The hidden window-key columns of one row of the plain path (#435): each window key evaluated
    by the window evaluator over the HAVING-filtered rows, as a window item is. A key that
    evaluates to an error has no column (it sorts as an error key does). -/
def windowOrderKeyCols
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (db : Database) (row : Row) (rows : Table) (idx : Nat) (orderBy : List OrderByItem) : Row :=
  ((List.range orderBy.length).zip orderBy).filterMap fun (k, item) =>
    if exprHasWindowFn item.expr then
      (exprWithWindowEval db row rows rows idx item.expr).map fun v => (windowOrderKeyName k, v)
    else none

/-- Sort-key row of one group (#429, #435): as `groupOrderKeyRow`, against the projected row, so
    `ORDER BY` a window item's alias sorts by its value; a key with a window function is
    evaluated by the window evaluator over the rows standing for the groups (`groupWindowEval`),
    as a window item is. -/
def groupWindowKeyRow (db : Database)
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (orderBy : List OrderByItem) (groups : List (Table × Row)) (idx : Nat)
    (groupRows : Table) (sampleRow projected : Row) : Row :=
  let synth := groupWindowRows groups
  ((List.range orderBy.length).zip orderBy).filterMap fun (k, item) =>
    (if exprHasWindowFn item.expr then
      evalExprWithWindowParam (groupWindowEval exprWithAggEval groups) db
        (synth.getD idx []) synth synth idx item.expr
     else exprWithAggEval db groupRows (projected ++ sampleRow) item.expr).map
      fun v => (groupOrderKeyName k, v)

/-- Without window keys, `groupWindowKeyRow` is `groupOrderKeyRow`. -/
theorem groupWindowKeyRow_of_noWin (db : Database)
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (orderBy : List OrderByItem) (groups : List (Table × Row)) (idx : Nat)
    (groupRows : Table) (sampleRow projected : Row) (h : orderByHasWindow orderBy = false) :
    groupWindowKeyRow db exprWithAggEval orderBy groups idx groupRows sampleRow projected =
    groupOrderKeyRow db exprWithAggEval orderBy groupRows sampleRow projected := by
  simp only [groupWindowKeyRow, groupOrderKeyRow]
  apply filterMap_congr_mem
  intro x hx
  have hk : exprHasWindowFn x.2.expr = false := by
    simp only [orderByHasWindow, List.any_eq_false] at h
    simpa using h x.2 (List.of_mem_zip hx).2
  simp [hk]

/-- Sort-key rows of a grouped query with window items or window `ORDER BY` keys (#429, #435),
    aligned with the grouped projection. -/
def groupWindowOrderKeys (db : Database)
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (orderBy : List OrderByItem) (groups : List (Table × Row)) (projected : Table) : Table :=
  ((List.range groups.length).zip (groups.zip projected)).map fun (i, ((rs, s), p)) =>
    groupWindowKeyRow db exprWithAggEval orderBy groups i rs s p

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

  -- Merge outer row context into each base row for correlated subqueries.
  -- The inner row comes first, so name lookup (first match wins) resolves
  -- against the subquery's own FROM before the outer row: innermost scope
  -- wins, as in standard SQL (#253).
  let baseRowsWithContext : Table := baseRows.map fun row => row ++ outerRow

  -- 2. WHERE clause
  let filteredRows : Table := match sel.whereClause with
    | some cond =>
      baseRowsWithContext.filter fun row =>
        exprEval db row cond == some (Value.bool true)
    | none => baseRowsWithContext

  -- the HAVING evaluated: `HAVING TRUE` when the only aggregate is in ORDER BY (#445)
  let having := effectiveHaving sel.groupBy sel.items sel.having sel.orderBy

  -- HAVING-filtered source rows: used by the window and plain projection
  -- paths, and as the aligned ORDER BY sources (#206). Grouped/aggregate
  -- paths apply HAVING per-group and ignore this binding.
  let havingRows : Table := match having with
    | some cond =>
      filteredRows.filter fun row =>
        exprEval db row cond == some (Value.bool true)
    | none => filteredRows

  -- 3. GROUP BY and 4. HAVING and 5. SELECT (projection)
  -- Groups that survive HAVING, for the window path over groups (#429).
  let windowGroups : List (Table × Row) :=
    if !sel.groupBy.isEmpty then
      groupedSurvivors db exprEval exprWithAggEval sel.items sel.groupBy having filteredRows
    else aggSurvivors db exprEval exprWithAggEval sel.items having filteredRows
  let projectedRows : Table :=
    if (!sel.groupBy.isEmpty || hasAgg sel.items ||
        implicitGroup hasWindowFn sel.items having) && hasWindowFn sel.items then
      projectGroupsWithWindows db selectItemWithAggEval exprWithAggEval sel.items windowGroups
    else if !sel.groupBy.isEmpty then
      -- GROUP BY present: partition rows and evaluate aggregates per group
      -- Inline groupRowsByKey logic: rows.foldl addToGroups []
      let addToGroups (groups : List (List (Option Value) × Table)) (row : Row) :
          List (List (Option Value) × Table) :=
        let key := sel.groupBy.map (fun e => (exprEval db row e).map Value.setKey)
        match groups.find? (fun (k, _) => k == key) with
        | some _ => groups.map fun (k, rs) => if k == key then (k, rs ++ [row]) else (k, rs)
        | none => groups ++ [(key, [row])]
      let groups := filteredRows.foldl addToGroups []
      let groupResults := groups.filterMap fun (_key, groupRows) =>
        match bareSampleRow (exprEval db) (selectMinMaxCalls sel.items having) groupRows with
        | none => none
        | some sampleRow =>
          let passesHaving := match having with
            | none => true
            | some cond =>
              exprWithAggEval db groupRows sampleRow cond == some (Value.bool true)
          if passesHaving then
            some (sel.items.flatMap (selectItemWithAggEval db groupRows sampleRow))
          else
            none
      groupResults
    else if hasAgg sel.items || implicitGroup hasWindowFn sel.items having then
      let sampleRow :=
        (bareSampleRow (exprEval db) (selectMinMaxCalls sel.items having) filteredRows).getD []
      let passesHaving := match having with
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
        projectWindowItems exprWithWindowEval db row partition sortedPartition idx sel.items
    else
      havingRows.map fun row => sel.items.flatMap (selectItemEval db row)

  -- 6. DISTINCT
  let distinctRows : Table := if sel.distinct then
    dedupByKey Row.valueKey projectedRows
  else
    projectedRows

  -- 7. ORDER BY, 8. OFFSET and LIMIT
  -- Sort keys resolve against `projected ++ source` rows so ORDER BY can
  -- reference non-projected columns (#206); output columns win on name
  -- clashes. Plain and window paths (no DISTINCT) align 1:1 with the
  -- HAVING-filtered source rows. Grouped paths (no DISTINCT) align 1:1 with
  -- per-group sort-key rows, so ORDER BY can use aggregates such as
  -- `count(*)` and non-projected grouping columns (#234). Plain DISTINCT sorts
  -- each distinct row with its first source row (#320, registry row 5), as
  -- sqlite and DuckDB do; output columns still win on name clashes.
  let groupedSort := !sel.distinct && !sel.groupBy.isEmpty
  let groupedDistinct := sel.distinct && !sel.groupBy.isEmpty
  let plainDistinct := sel.distinct && sel.groupBy.isEmpty && !hasAgg sel.items &&
    !hasWindowFn sel.items && !implicitGroup hasWindowFn sel.items having
  let strippedSources := havingRows.map (fun r => r.take (r.length - outerRow.length))
  applyOrderByLimitOffsetAligned compareEval db
    (if groupedSort || groupedDistinct then groupOrderByItems sel.orderBy
     else if orderByHasWindow sel.orderBy then windowOrderByItems sel.orderBy else sel.orderBy)
    sel.limitVal sel.offsetVal
    ((!sel.distinct && sel.groupBy.isEmpty && !hasAgg sel.items &&
        !implicitGroup hasWindowFn sel.items having) || groupedSort ||
      groupedDistinct || plainDistinct)
    (if groupedSort then
      (if hasWindowFn sel.items || orderByHasWindow sel.orderBy then
        groupWindowOrderKeys db exprWithAggEval sel.orderBy windowGroups projectedRows
       else
        evalSelectGroupOrderKeys db exprEval selectItemWithAggEval exprWithAggEval
          sel.items sel.groupBy having sel.orderBy filteredRows)
     else if groupedDistinct then
      (dedupByKey (fun p => Row.valueKey p.1)
        (projectedRows.zip
          (if hasWindowFn sel.items || orderByHasWindow sel.orderBy then
            groupWindowOrderKeys db exprWithAggEval sel.orderBy windowGroups projectedRows
           else
            evalSelectGroupOrderKeys db exprEval selectItemWithAggEval exprWithAggEval
              sel.items sel.groupBy having sel.orderBy filteredRows))).map Prod.snd
     else if plainDistinct then
      (dedupByKey (fun p => Row.valueKey p.1)
        ((havingRows.map fun row => sel.items.flatMap (selectItemEval db row)).zip
          strippedSources)).map Prod.snd
     else if orderByHasWindow sel.orderBy then
      -- window ORDER BY keys (#435): each source row carries their values in hidden columns
      ((List.range havingRows.length).zip havingRows).map fun (i, r) =>
        r.take (r.length - outerRow.length) ++
          windowOrderKeyCols exprWithWindowEval db r havingRows i sel.orderBy
     else strippedSources)
    distinctRows

-- ============================================================================
-- Equational Theorems for evalSelectCore
-- ============================================================================

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

/-- General form of `applyOrderByLimitOffsetAligned_length_eq`: the output
    length depends only on `rows`, `limit` and `offset`, for any sort keys,
    sources and `useSources` flag, as long as sources align with rows
    whenever they are used. -/
theorem applyOrderByLimitOffsetAligned_length_eq_general
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (db : Database) (orderBy1 orderBy2 : List OrderByItem)
    (limit offset : Option Nat) (useSources1 useSources2 : Bool)
    (sources1 sources2 rows : Table)
    (halign1 : useSources1 = true → sources1.length = rows.length)
    (halign2 : useSources2 = true → sources2.length = rows.length) :
    (applyOrderByLimitOffsetAligned compareEval db orderBy1 limit offset
      useSources1 sources1 rows).length =
    (applyOrderByLimitOffsetAligned compareEval db orderBy2 limit offset
      useSources2 sources2 rows).length := by
  have hlen : ∀ (ob : List OrderByItem) (us : Bool) (srcs : Table),
      (us = true → srcs.length = rows.length) →
      (if ob.isEmpty then rows else
        if us then
          ((rows.zip srcs).mergeSort fun p1 p2 =>
            compareEval db (p1.1 ++ p1.2) (p2.1 ++ p2.2) ob).map (·.1)
        else
          rows.mergeSort fun r1 r2 => compareEval db r1 r2 ob).length = rows.length := by
    intro ob us srcs hal
    by_cases hob : ob.isEmpty = true
    · simp [hob]
    · by_cases huse : us = true
      · simp [hob, huse, List.length_mergeSort, List.length_zip, hal huse]
      · simp [hob, huse, List.length_mergeSort]
  simp only [applyOrderByLimitOffsetAligned]
  cases limit <;> cases offset <;>
    simp only [List.length_take, List.length_drop, hlen _ _ _ halign1, hlen _ _ _ halign2]

/-- With at most one row, ORDER BY cannot reorder anything: the result is
    independent of the sort keys and (aligned) sources. -/
theorem applyOrderByLimitOffsetAligned_of_length_le_one
    (compareEval : Database → Row → Row → List OrderByItem → Bool)
    (db : Database) (orderBy1 orderBy2 : List OrderByItem)
    (limit offset : Option Nat) (useSources1 useSources2 : Bool)
    (sources1 sources2 rows : Table) (hrows : rows.length ≤ 1)
    (halign1 : useSources1 = true → sources1.length = rows.length)
    (halign2 : useSources2 = true → sources2.length = rows.length) :
    applyOrderByLimitOffsetAligned compareEval db orderBy1 limit offset
      useSources1 sources1 rows =
    applyOrderByLimitOffsetAligned compareEval db orderBy2 limit offset
      useSources2 sources2 rows := by
  have hsorted : ∀ (ob : List OrderByItem) (us : Bool) (srcs : Table),
      (us = true → srcs.length = rows.length) →
      (if ob.isEmpty then rows else
        if us then
          ((rows.zip srcs).mergeSort fun p1 p2 =>
            compareEval db (p1.1 ++ p1.2) (p2.1 ++ p2.2) ob).map (·.1)
        else
          rows.mergeSort fun r1 r2 => compareEval db r1 r2 ob) = rows := by
    intro ob us srcs hal
    match rows, hrows with
    | [], _ => simp
    | [r], _ =>
      by_cases hob : ob.isEmpty = true
      · simp [hob]
      · by_cases hus : us = true
        · have hl := hal hus
          match srcs, hl with
          | [s], _ => simp [hob, hus]
        · simp [hob, hus]
    | _ :: _ :: _, h => simp at h
  simp only [applyOrderByLimitOffsetAligned]
  rw [hsorted _ _ _ halign1, hsorted _ _ _ halign2]

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
    if (!groupBy.isEmpty || hasAgg items || implicitGroup hasWindowFn items having) &&
        hasWindowFn items then
      projectGroupsWithWindows db selectItemWithAggEval exprWithAggEval items
        (if !groupBy.isEmpty then
          groupedSurvivors db exprEval exprWithAggEval items groupBy having filteredRows
         else aggSurvivors db exprEval exprWithAggEval items having filteredRows)
    else if !groupBy.isEmpty then
      let addToGroups (groups : List (List (Option Value) × Table)) (row : Row) :
          List (List (Option Value) × Table) :=
        let key := groupBy.map (fun e => (exprEval db row e).map Value.setKey)
        match groups.find? (fun (k, _) => k == key) with
        | some _ => groups.map fun (k, rs) => if k == key then (k, rs ++ [row]) else (k, rs)
        | none => groups ++ [(key, [row])]
      let groups := filteredRows.foldl addToGroups []
      let groupResults := groups.filterMap fun (_key, groupRows) =>
        match bareSampleRow (exprEval db) (selectMinMaxCalls items having) groupRows with
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
    else if hasAgg items || implicitGroup hasWindowFn items having then
      let sampleRow :=
        (bareSampleRow (exprEval db) (selectMinMaxCalls items having) filteredRows).getD []
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
        projectWindowItems exprWithWindowEval db row partition sortedPartition idx items
    else
      let havingRows := match having with
        | some cond =>
          filteredRows.filter fun row =>
            exprEval db row cond == some (Value.bool true)
        | none => filteredRows
      havingRows.map fun row => items.flatMap (selectItemEval db row)
  if distinct then dedupByKey Row.valueKey projectedRows else projectedRows

/-- DISTINCT deduplicates the projection by value key (#315, #320). -/
theorem evalSelectProjectDistinct_true (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (filteredRows : Table) :
    evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg true items groupBy having
      filteredRows =
    dedupByKey Row.valueKey (evalSelectProjectDistinct db exprEval selectItemEval
      selectItemWithAggEval exprWithAggEval exprWithWindowEval hasWindowFn hasAgg false items
      groupBy having filteredRows) := by
  simp only [evalSelectProjectDistinct, ↓reduceIte, Bool.false_eq_true]

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
    (h : (!distinct && groupBy.isEmpty && !hasAgg items &&
      !implicitGroup hasWindowFn items having) = true) :
    (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg distinct items
      groupBy having filteredRows).length =
    (match having with
      | some cond => filteredRows.filter fun row =>
          exprEval db row cond == some (Value.bool true)
      | none => filteredRows).length := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hd, hgb⟩, hagg⟩, hwa⟩ := h
  simp only [evalSelectProjectDistinct, hgb, hagg, hd, hwa, Bool.not_true,
    Bool.false_eq_true, if_false, Bool.or_false, Bool.false_and]
  by_cases hwin : hasWindowFn items = true
  · simp [hwin, List.length_map, List.length_zip, List.length_range]
  · simp [hwin, List.length_map]

/-- `filterMap` over the same list with the same success pattern gives
    lists of the same length. -/
theorem List.length_filterMap_congr_isSome {α β γ : Type _}
    (f : α → Option β) (g : α → Option γ) (l : List α)
    (h : ∀ x ∈ l, (f x).isSome = (g x).isSome) :
    (l.filterMap f).length = (l.filterMap g).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    cases hf : f x <;> cases hg : g x <;> simp_all

@[simp] theorem groupedSurvivors_nil (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr) :
    groupedSurvivors db exprEval exprWithAggEval items groupBy having [] = [] := by
  simp [groupedSurvivors]

@[simp] theorem projectGroupsWithWindows_nil (db : Database)
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) :
    projectGroupsWithWindows db selectItemWithAggEval exprWithAggEval items [] = [] := by
  simp [projectGroupsWithWindows, groupWindowRows]

/-- The window projection over groups has one row per group (#429). -/
theorem projectGroupsWithWindows_length (db : Database)
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (groups : List (Table × Row)) :
    (projectGroupsWithWindows db selectItemWithAggEval exprWithAggEval items groups).length =
      groups.length := by
  simp [projectGroupsWithWindows, groupWindowRows, List.length_zip]

/-- The window sort keys over groups align with the window projection (#429). -/
theorem groupWindowOrderKeys_length (db : Database)
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (orderBy : List OrderByItem) (groups : List (Table × Row)) (projected : Table)
    (h : projected.length = groups.length) :
    (groupWindowOrderKeys db exprWithAggEval orderBy groups projected).length =
      projected.length := by
  simp [groupWindowOrderKeys, List.length_zip, h]

/-- The grouped sort keys have one row per group that survives HAVING (#429). -/
theorem evalSelectGroupOrderKeys_length_survivors (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (filteredRows : Table) :
    (evalSelectGroupOrderKeys db exprEval selectItemWithAggEval exprWithAggEval
      items groupBy having orderBy filteredRows).length =
    (groupedSurvivors db exprEval exprWithAggEval items groupBy having filteredRows).length := by
  simp only [evalSelectGroupOrderKeys, groupedSurvivors]
  apply List.length_filterMap_congr_isSome
  intro ⟨_k, groupRows⟩ _
  dsimp only
  cases bareSampleRow (exprEval db) (selectMinMaxCalls items having) groupRows with
  | none => rfl
  | some sampleRow =>
    dsimp only
    split <;> (try split) <;> simp

/-- In the grouped path without DISTINCT, the per-group sort-key rows align
    1:1 with the projected rows (#234): both are a `filterMap` over the same
    groups with the same per-group HAVING test. -/
theorem evalSelectGroupOrderKeys_length_aligned (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderByItem)
    (filteredRows : Table)
    (h : (!distinct && !groupBy.isEmpty) = true) :
    (evalSelectGroupOrderKeys db exprEval selectItemWithAggEval exprWithAggEval
      items groupBy having orderBy filteredRows).length =
    (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg distinct items
      groupBy having filteredRows).length := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hd, hgb⟩ := h
  have hgb' : (!groupBy.isEmpty) = true := by simp [hgb]
  by_cases hw : hasWindowFn items = true
  · simp only [evalSelectProjectDistinct, hd, hgb', hw, Bool.true_or, Bool.and_self, if_true,
      Bool.false_eq_true, if_false, projectGroupsWithWindows_length]
    exact evalSelectGroupOrderKeys_length_survivors _ _ _ _ _ _ _ _ _
  · simp only [evalSelectGroupOrderKeys, evalSelectProjectDistinct, hd, hgb', hw, if_true,
      Bool.false_eq_true, if_false, Bool.and_false]
    apply List.length_filterMap_congr_isSome
    intro ⟨_k, groupRows⟩ _
    dsimp only
    cases bareSampleRow (exprEval db) (selectMinMaxCalls items having) groupRows with
    | none => rfl
    | some sampleRow =>
      dsimp only
      split <;> (try split) <;> simp

/-- The grouped sort keys, with or without window items, align with the grouped projection
    (#234, #429). -/
theorem groupedOrderKeys_length_aligned (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderByItem)
    (filteredRows : Table)
    (hgb : (!groupBy.isEmpty) = true) :
    (if hasWindowFn items || orderByHasWindow orderBy then
      groupWindowOrderKeys db exprWithAggEval orderBy
        (if !groupBy.isEmpty then
          groupedSurvivors db exprEval exprWithAggEval items groupBy having filteredRows
         else aggSurvivors db exprEval exprWithAggEval items having filteredRows)
        (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
          exprWithAggEval exprWithWindowEval hasWindowFn hasAgg false items groupBy having
          filteredRows)
     else
      evalSelectGroupOrderKeys db exprEval selectItemWithAggEval exprWithAggEval
        items groupBy having orderBy filteredRows).length =
    (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg false items groupBy having
      filteredRows).length := by
  have hold := evalSelectGroupOrderKeys_length_aligned db exprEval selectItemEval
    selectItemWithAggEval exprWithAggEval exprWithWindowEval hasWindowFn hasAgg false items
    groupBy having orderBy filteredRows (by simp only [Bool.not_false, Bool.true_and]; exact hgb)
  by_cases hw : (hasWindowFn items || orderByHasWindow orderBy) = true
  · rw [if_pos hw]
    apply groupWindowOrderKeys_length
    by_cases hwi : hasWindowFn items = true
    · simp only [evalSelectProjectDistinct, hgb, hwi, Bool.true_or, Bool.and_self, if_true,
        Bool.false_eq_true, if_false, projectGroupsWithWindows_length]
    · -- window keys only (#435): the grouped projection has one row per surviving group
      rw [← hold, evalSelectGroupOrderKeys_length_survivors]
      simp [hgb]
  · rw [if_neg hw]
    exact hold

/-- `groupedOrderKeys_length_aligned` without window `ORDER BY` keys. -/
theorem groupedOrderKeys_length_aligned_noWinKey (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderByItem)
    (filteredRows : Table)
    (hgb : (!groupBy.isEmpty) = true) (hob : orderByHasWindow orderBy = false) :
    (if hasWindowFn items then
      groupWindowOrderKeys db exprWithAggEval orderBy
        (if !groupBy.isEmpty then
          groupedSurvivors db exprEval exprWithAggEval items groupBy having filteredRows
         else aggSurvivors db exprEval exprWithAggEval items having filteredRows)
        (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
          exprWithAggEval exprWithWindowEval hasWindowFn hasAgg false items groupBy having
          filteredRows)
     else
      evalSelectGroupOrderKeys db exprEval selectItemWithAggEval exprWithAggEval
        items groupBy having orderBy filteredRows).length =
    (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg false items groupBy having
      filteredRows).length := by
  have h := groupedOrderKeys_length_aligned db exprEval selectItemEval selectItemWithAggEval
    exprWithAggEval exprWithWindowEval hasWindowFn hasAgg items groupBy having orderBy
    filteredRows hgb
  simpa only [hob, Bool.or_false] using h

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
  -- the HAVING evaluated: `HAVING TRUE` when the only aggregate is in ORDER BY (#445)
  let having := effectiveHaving groupBy items having orderBy
  let havingRows : Table := match having with
    | some cond =>
      filteredRows.filter fun row =>
        exprEval db row cond == some (Value.bool true)
    | none => filteredRows
  -- Sort sources have the correlated outer-row suffix stripped: outer columns
  -- are constant per query instance, so they can never affect sort order, and
  -- stripping them keeps ground SELECTs row-context independent (#206).
  -- Grouped queries without DISTINCT sort on per-group key rows (#234).
  let groupedSort := !distinct && !groupBy.isEmpty
  -- Plain DISTINCT sorts each distinct row with its first source row as context (#320,
  -- registry row 5): a key that is not selected reads that row, as sqlite and DuckDB do.
  -- Output names come first in the context, so selected keys sort as before; the standard
  -- and postgres dialects reject an unselected key at parse time.
  -- Grouped DISTINCT sorts each distinct row by the key row of the first group that
  -- produced it (#320).
  let groupedDistinct := distinct && !groupBy.isEmpty
  let plainDistinct := distinct && groupBy.isEmpty && !hasAgg items && !hasWindowFn items &&
    !implicitGroup hasWindowFn items having
  let strippedSources := havingRows.map (fun r => r.take (r.length - ctxLen))
  -- Groups that survive HAVING, for the window path over groups (#429).
  let windowGroups : List (Table × Row) :=
    if !groupBy.isEmpty then
      groupedSurvivors db exprEval exprWithAggEval items groupBy having filteredRows
    else aggSurvivors db exprEval exprWithAggEval items having filteredRows
  applyOrderByLimitOffsetAligned compareEval db
    (if groupedSort || groupedDistinct then groupOrderByItems orderBy
     else if orderByHasWindow orderBy then windowOrderByItems orderBy else orderBy) limit offset
    ((!distinct && groupBy.isEmpty && !hasAgg items &&
        !implicitGroup hasWindowFn items having) || groupedSort || groupedDistinct ||
      plainDistinct)
    (if groupedSort then
      (if hasWindowFn items || orderByHasWindow orderBy then
        groupWindowOrderKeys db exprWithAggEval orderBy windowGroups
          (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
            exprWithAggEval exprWithWindowEval hasWindowFn hasAgg false items groupBy having
            filteredRows)
       else
        evalSelectGroupOrderKeys db exprEval selectItemWithAggEval exprWithAggEval
          items groupBy having orderBy filteredRows)
     else if groupedDistinct then
      (dedupByKey (fun p => Row.valueKey p.1)
        ((evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
            exprWithAggEval exprWithWindowEval hasWindowFn hasAgg false items groupBy having
            filteredRows).zip
          (if hasWindowFn items || orderByHasWindow orderBy then
            groupWindowOrderKeys db exprWithAggEval orderBy windowGroups
              (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
                exprWithAggEval exprWithWindowEval hasWindowFn hasAgg false items groupBy having
                filteredRows)
           else
            evalSelectGroupOrderKeys db exprEval selectItemWithAggEval exprWithAggEval
              items groupBy having orderBy filteredRows))).map Prod.snd
     else if plainDistinct then
      (dedupByKey (fun p => Row.valueKey p.1)
        ((havingRows.map fun row => items.flatMap (selectItemEval db row)).zip
          strippedSources)).map Prod.snd
     else if orderByHasWindow orderBy then
      ((List.range havingRows.length).zip havingRows).map fun (i, r) =>
        r.take (r.length - ctxLen) ++ windowOrderKeyCols exprWithWindowEval db r havingRows i orderBy
     else strippedSources)
    (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg distinct items
      groupBy having filteredRows)

/-- ORDER BY never changes the row count of the post-WHERE pipeline: sort
    sources align with the projected rows in both the plain path (#206) and
    the grouped path (#234). Unless it makes the query one group: an aggregate
    only in ORDER BY does (#445), so the two orders must give the same evaluated
    `HAVING` (`effectiveHaving`). -/
theorem evalSelectAfterFilter_orderBy_length (db : Database)
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
    (orderBy1 orderBy2 : List OrderByItem) (limit offset : Option Nat)
    (ctxLen : Nat) (filteredRows : Table)
    (hEH : effectiveHaving groupBy items having orderBy1 =
      effectiveHaving groupBy items having orderBy2) :
    (evalSelectAfterFilter db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      distinct items groupBy having orderBy1 limit offset ctxLen filteredRows).length =
    (evalSelectAfterFilter db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      distinct items groupBy having orderBy2 limit offset ctxLen filteredRows).length := by
  simp only [evalSelectAfterFilter]
  rw [hEH]
  generalize effectiveHaving groupBy items having orderBy2 = having
  apply applyOrderByLimitOffsetAligned_length_eq_general
  all_goals
    intro huse
    by_cases hg : (!distinct && !groupBy.isEmpty) = true
    · rw [if_pos hg]
      have hd : distinct = false := by simp only [Bool.and_eq_true] at hg; simpa using hg.1
      have hgb : (!groupBy.isEmpty) = true := by simp only [Bool.and_eq_true] at hg; exact hg.2
      subst hd
      exact groupedOrderKeys_length_aligned _ _ _ _ _ _ _ _ _ _ _ _ _ hgb
    · rw [if_neg hg]
      by_cases hgd : (distinct && !groupBy.isEmpty) = true
      · -- grouped DISTINCT: one first group key row per distinct row (#320)
        have hgb : (!groupBy.isEmpty) = true := by
          simp only [Bool.and_eq_true] at hgd; exact hgd.2
        rw [if_pos hgd, List.length_map, length_dedupByKey_zip _ _ _
          (groupedOrderKeys_length_aligned _ _ _ _ _ _ _ _ _ _ _ _ _ hgb).symm]
        have hd : distinct = true := by simp only [Bool.and_eq_true] at hgd; exact hgd.1
        subst hd
        rw [evalSelectProjectDistinct_true]
      · rw [if_neg hgd]
        by_cases hpd : (distinct && groupBy.isEmpty && !hasAgg items && !hasWindowFn items &&
            !implicitGroup hasWindowFn items having) = true
        · -- plain DISTINCT: one first source row per distinct row (#320)
          rw [if_pos hpd, List.length_map, length_dedupByKey_zip _ _ _ (by simp)]
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
            List.isEmpty_iff] at hpd
          obtain ⟨⟨⟨⟨hd, hg0⟩, ha⟩, hw⟩, hi⟩ := hpd
          subst hd hg0
          simp [evalSelectProjectDistinct, ha, hw, hi]
        · rw [if_neg hpd]
          have hplain : (!distinct && groupBy.isEmpty && !hasAgg items &&
              !implicitGroup hasWindowFn items having) = true := by
            simpa [hg, hgd, hpd] using huse
          -- the sources (with hidden window-key columns, #435, or without) are one per row
          have hsrc : ∀ (b : Bool) (A B : Table), A.length = B.length →
              (if b = true then A else B).length = B.length := by
            intro b A B h; cases b <;> simp [h]
          rw [hsrc _ _ _ (by simp [List.length_zip, List.length_range]), List.length_map]
          exact (evalSelectProjectDistinct_length_aligned _ _ _ _ _ _ _ _
            _ _ _ _ _ hplain).symm

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
    (hNoAgg : hasAgg items = false)
    (hNoWA : implicitGroup hasWindowFn items having = false) :
    evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg distinct items
      groupBy having [] = [] := by
  simp only [evalSelectProjectDistinct, List.foldl, List.filterMap_nil,
    hNoAgg, hNoWA, Bool.or_false, List.head?_nil, Option.getD]
  cases having <;> simp [List.map_nil] <;> split <;> simp_all

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
    let baseRowsWithContext := baseRows.map fun row => row ++ outerRow
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
    (orderBy1 orderBy2 : List OrderByItem) (limit offset : Option Nat)
    (hEH : effectiveHaving groupBy items having orderBy1 =
      effectiveHaving groupBy items having orderBy2) :
    (evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ where_ groupBy having orderBy1 limit offset)).length =
    (evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ where_ groupBy having orderBy2 limit offset)).length := by
  simp only [evalSelectCore_eq_afterFilter]
  exact evalSelectAfterFilter_orderBy_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEH

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
    implicitGroup hasWindowFn items having = false →
    orderByOnlyAggregates groupBy items having orderBy = false →
    (∀ row : Row, (exprEval db row cond == some (Value.bool true)) = false) →
    evalSelectCore db outerRow fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (SelectStmt.mk distinct items from_ (some cond) groupBy having orderBy limit offset) = [] := by
  intro hNoAgg hNoWA hOB hAllFalse
  -- Unfold evalSelectCore directly (it's a regular def)
  show evalSelectAfterFilter db exprEval selectItemEval selectItemWithAggEval
    exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
    distinct items groupBy having orderBy limit offset outerRow.length
    (List.filter (fun row => exprEval db row cond == some (Value.bool true))
      (List.map (fun row => row ++ outerRow)
        (match from_ with | some f => fromEval db f | none => [[]]))) = []
  -- filteredRows = [] because all rows are rejected
  rw [filter_eq_nil_of_false _ _ hAllFalse]
  -- evalSelectAfterFilter ... [] = aligned-orderBy (evalSelectProjectDistinct ... [])
  simp only [evalSelectAfterFilter, effectiveHaving_of_not hOB]
  -- evalSelectProjectDistinct ... [] = [] (no aggregates); the rows, and since #320 the
  -- grouped DISTINCT sources, hold one such term each
  simp only [evalSelectProjectDistinct_nil _ _ _ _ _ _ _ _ _ _ _ _ hNoAgg hNoWA]
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
    h_hasAgg, h_hasWindowFn, effectiveHaving, orderByOnlyAggregates]
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
    (baseRows.map fun row => row ++ outerRow).filter fun row =>
      exprEval db row p == some (Value.bool true) := by
  simp only [evalSelectCore_eq_afterFilter]
  exact evalSelectAfterFilter_star_identity db exprEval selectItemEval selectItemWithAggEval
    exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg _ h_hasAgg h_hasWindowFn h_star _

/-- Core filter_and: filtering a subquery result is the same as combining WHERE clauses. -/
theorem evalSelectCore_filter_and (db : Database) (alias_ : String)
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
    -- the derived table `(SELECT * FROM from_ WHERE r) AS alias_` evaluates to
    -- its inner result (true when naming it `alias_` renames nothing, #257)
    (h_subquery : ∀ r : Expr,
      fromEval db (.subquery (.simple (.mk false [.star none] from_ (some r) [] none [] none none)) alias_) =
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
        (.mk false [.star none] from_ (some r) [] none [] none none))
    (h_and : ∀ row, (exprEval db row (.binOp .and p q) == some (Value.bool true)) =
      ((exprEval db row p == some (Value.bool true)) && (exprEval db row q == some (Value.bool true)))) :
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items
        (some (.subquery (.simple (.mk false [.star none] from_ (some p) [] none [] none none)) alias_))
        (some q) groupBy having orderBy limit offset) =
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items from_ (some (.binOp .and p q)) groupBy having orderBy limit offset) := by
  simp only [evalSelectCore_eq_afterFilter]
  congr 1
  simp only [h_subquery]
  rw [evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _ h_hasAgg_star h_hasWindowFn_star h_star]
  simp only [List.append_nil, List.map_id']
  rw [← list_filter_and_eq]
  congr 1; funext row; exact (h_and row).symm

/-- Core filter_commute: filtering by p then q equals filtering by q then p. -/
theorem evalSelectCore_filter_commute (db : Database) (alias_ : String)
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
    -- the derived table `(SELECT * FROM from_ WHERE r) AS alias_` evaluates to
    -- its inner result (true when naming it `alias_` renames nothing, #257)
    (h_subquery : ∀ r : Expr,
      fromEval db (.subquery (.simple (.mk false [.star none] from_ (some r) [] none [] none none)) alias_) =
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
        (.mk false [.star none] from_ (some r) [] none [] none none)) :
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items
        (some (.subquery (.simple (.mk false [.star none] from_ (some p) [] none [] none none)) alias_))
        (some q) groupBy having orderBy limit offset) =
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items
        (some (.subquery (.simple (.mk false [.star none] from_ (some q) [] none [] none none)) alias_))
        (some p) groupBy having orderBy limit offset) := by
  simp only [evalSelectCore_eq_afterFilter]
  congr 1
  simp only [h_subquery]
  rw [evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _ h_hasAgg_star h_hasWindowFn_star h_star,
      evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _ h_hasAgg_star h_hasWindowFn_star h_star]
  simp only [List.append_nil, List.map_id']
  exact list_filter_comm _ _ _

/-- Core filter_idempotent: filtering by p then p again equals filtering by p once. -/
theorem evalSelectCore_filter_idempotent (db : Database) (alias_ : String)
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
    -- the derived table `(SELECT * FROM from_ WHERE r) AS alias_` evaluates to
    -- its inner result (true when naming it `alias_` renames nothing, #257)
    (h_subquery : ∀ r : Expr,
      fromEval db (.subquery (.simple (.mk false [.star none] from_ (some r) [] none [] none none)) alias_) =
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
        (.mk false [.star none] from_ (some r) [] none [] none none)) :
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items
        (some (.subquery (.simple (.mk false [.star none] from_ (some p) [] none [] none none)) alias_))
        (some p) groupBy having orderBy limit offset) =
    evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
      (.mk false items from_ (some p) groupBy having orderBy limit offset) := by
  simp only [evalSelectCore_eq_afterFilter]
  congr 1
  simp only [h_subquery]
  rw [evalSelectCore_star_where_eq_filter _ _ _ _ _ _ _ _ _ _ _ _ _ h_hasAgg_star h_hasWindowFn_star h_star]
  simp only [List.append_nil, List.map_id']
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
    -- the derived table `(SELECT * FROM from_ WHERE r) AS alias_` evaluates to
    -- its inner result (true when naming it `alias_` renames nothing, #257)
    (h_subquery : ∀ r : Expr,
      fromEval db (.subquery (.simple (.mk false [.star none] from_ (some r) [] none [] none none)) alias_) =
      evalSelectCore db [] fromEval exprEval selectItemEval selectItemWithAggEval
        exprWithAggEval compareEval exprWithWindowEval hasWindowFn hasAgg
        (.mk false [.star none] from_ (some r) [] none [] none none)) :
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
  simp only [List.append_nil, List.map_id']

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
      (List.map (· ++ outerRow) (fromEval db from_)) := by
  rw [evalSelectCore_eq_afterFilter]
  dsimp only []
  simp [evalSelectAfterFilter, applyOrderByLimitOffsetAligned, evalSelectProjectDistinct,
    hNoAgg, hNoWin, effectiveHaving, orderByOnlyAggregates]

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
        (List.map (· ++ outerRow) (fromEval db from_))) := by
  rw [evalSelectCore_eq_afterFilter]
  dsimp only []
  simp [evalSelectAfterFilter, applyOrderByLimitOffsetAligned, evalSelectProjectDistinct,
    hNoAgg, hNoWin, effectiveHaving, orderByOnlyAggregates]

/-- For SELECT DISTINCT items FROM from_ (no WHERE, no GROUP BY, etc.),
    the result is (projection of each base row), deduplicated by value key (#315) -/
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
    dedupByKey Row.valueKey (List.map (fun row => items.flatMap (selectItemEval db row))
      (List.map (· ++ outerRow) (fromEval db from_))) := by
  rw [evalSelectCore_eq_afterFilter]
  dsimp only []
  simp [evalSelectAfterFilter, applyOrderByLimitOffsetAligned, evalSelectProjectDistinct,
    hNoAgg, hNoWin, effectiveHaving, orderByOnlyAggregates]

/-- For SELECT DISTINCT items FROM from_ WHERE cond (no GROUP BY, etc.),
    the result is (filter then project), deduplicated by value key (#315) -/
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
    dedupByKey Row.valueKey (List.map (fun row => items.flatMap (selectItemEval db row))
      (List.filter (fun row => exprEval db row cond == some (Value.bool true))
        (List.map (· ++ outerRow) (fromEval db from_)))) := by
  rw [evalSelectCore_eq_afterFilter]
  dsimp only []
  simp [evalSelectAfterFilter, applyOrderByLimitOffsetAligned, evalSelectProjectDistinct,
    hNoAgg, hNoWin, effectiveHaving, orderByOnlyAggregates]

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
  let key := groupBy.map (fun e => (exprEval db row e).map Value.setKey)
  match groups.find? (fun (k, _) => k == key) with
  | some _ => groups.map fun (k, rs) => if k == key then (k, rs ++ [row]) else (k, rs)
  | none => groups ++ [(key, [row])]

/-- Accumulator invariant: foldl with constant key on [(k0, acc)] gives [(k0, acc ++ rows)]. -/
private theorem foldl_addToGroupsByKey_const_key_acc
    (exprEval : Database → Row → Expr → Option Value) (db : Database) (groupBy : List Expr)
    (k0 : List (Option Value)) (acc : Table) (rows : Table)
    (hk : ∀ row ∈ rows, groupBy.map (fun e => (exprEval db row e).map Value.setKey) = k0) :
    rows.foldl (addToGroupsByKey exprEval db groupBy) [(k0, acc)] = [(k0, acc ++ rows)] := by
  induction rows generalizing acc with
  | nil => simp [List.append_nil]
  | cons row rest ih =>
    simp only [List.foldl_cons]
    have hk_row : groupBy.map (fun e => (exprEval db row e).map Value.setKey) = k0 := hk row List.mem_cons_self
    have hk_rest : ∀ r ∈ rest, groupBy.map (fun e => (exprEval db r e).map Value.setKey) = k0 :=
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
    (hk_row : groupBy.map (fun e => (exprEval db row e).map Value.setKey) = k0)
    (hk_rest : ∀ r ∈ rest, groupBy.map (fun e => (exprEval db r e).map Value.setKey) = k0) :
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
        exprWithWindowEval db row1 p1 sp1 idx e = exprWithWindowEval db row2 p2 sp2 idx e)
    (h_gwin : ((!groupBy.isEmpty || hasAgg items || implicitGroup hasWindowFn items having) &&
      hasWindowFn items) = false) :
    evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval exprWithAggEval
      exprWithWindowEval hasWindowFn hasAgg distinct items groupBy having fr1 =
    evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval exprWithAggEval
      exprWithWindowEval hasWindowFn hasAgg distinct items groupBy having fr2 := by
  unfold evalSelectProjectDistinct
  -- Split on distinct (eraseDups wrapper)
  cases distinct
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, h_gwin]
  -- Split on the 4 branches
  all_goals {
    split
    · -- GROUP BY branch
      first | apply congrArg (dedupByKey Row.valueKey) | skip
      cases fr1 with
      | nil =>
        cases fr2 with | nil => rfl | cons _ _ => simp at hlen
      | cons row1 rest1 =>
        cases fr2 with
        | nil => simp at hlen
        | cons row2 rest2 =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hk0 : ∀ row, groupBy.map (fun e => (exprEval db row e).map Value.setKey) = groupBy.map (fun e => (exprEval db row1 e).map Value.setKey) :=
            fun row => List.map_congr_left fun e he => by rw [h_gb e he row row1]
          have hfold1 := foldl_addToGroupsByKey_const_key exprEval db groupBy _ row1 rest1
            rfl (fun r _ => hk0 r)
          have hfold2 := foldl_addToGroupsByKey_const_key exprEval db groupBy _ row2 rest2
            (hk0 row2) (fun r _ => hk0 r)
          unfold addToGroupsByKey at hfold1 hfold2
          rw [hfold1, hfold2]
          simp only [List.filterMap_cons, List.filterMap_nil]
          have hlen' : (row1 :: rest1).length = (row2 :: rest2).length := by simp [hlen]
          -- a non-empty group has a sample row (the first, or sqlite's extreme row)
          obtain ⟨s1, hs1⟩ : ∃ r, bareSampleRow (exprEval db) (selectMinMaxCalls items having)
              (row1 :: rest1) = some r :=
            Option.ne_none_iff_exists'.mp (by rw [Ne, bareSampleRow_eq_none_iff]; simp)
          obtain ⟨s2, hs2⟩ : ∃ r, bareSampleRow (exprEval db) (selectMinMaxCalls items having)
              (row2 :: rest2) = some r :=
            Option.ne_none_iff_exists'.mp (by rw [Ne, bareSampleRow_eq_none_iff]; simp)
          rw [hs1, hs2]
          cases having with
          | none =>
            dsimp only []
            simp only [ite_true]
            exact congrArg (fun x => [x]) (flatMap_congr_mem fun item hmem =>
              h_sia item hmem (row1 :: rest1) (row2 :: rest2) _ _ hlen')
          | some hcond =>
            dsimp only []
            have hph : (exprWithAggEval db (row1 :: rest1) s1 hcond == some (Value.bool true)) =
                (exprWithAggEval db (row2 :: rest2) s2 hcond == some (Value.bool true)) := by
              congr 1; exact h_ea hcond rfl (row1 :: rest1) (row2 :: rest2) _ _ hlen'
            simp only [hph]
            by_cases hx : (exprWithAggEval db (row2 :: rest2) s2 hcond == some (Value.bool true)) = true
            · simp only [hx, ite_true]
              exact congrArg (fun x => [x]) (flatMap_congr_mem fun item hmem =>
                h_sia item hmem (row1 :: rest1) (row2 :: rest2) _ _ hlen')
            · simp [hx]
    · split
      · -- Aggregate branch
        first | apply congrArg (dedupByKey Row.valueKey) | skip
        cases having with
        | none =>
          simp only [ite_true]
          exact congrArg (fun x => [x]) (flatMap_congr_mem fun item hmem =>
            h_sia item hmem fr1 fr2 _ _ hlen)
        | some hcond =>
          simp only []
          have hph : (exprWithAggEval db fr1
                ((bareSampleRow (exprEval db) (selectMinMaxCalls items (some hcond)) fr1).getD [])
                hcond == some (Value.bool true)) =
              (exprWithAggEval db fr2
                ((bareSampleRow (exprEval db) (selectMinMaxCalls items (some hcond)) fr2).getD [])
                hcond == some (Value.bool true)) := by
            congr 1; exact h_ea hcond rfl fr1 fr2 _ _ hlen
          simp only [hph]
          split
          · exact congrArg (fun x => [x]) (flatMap_congr_mem fun item hmem =>
              h_sia item hmem fr1 fr2 _ _ hlen)
          · rfl
      · split
        · -- Window branch
          first | apply congrArg (dedupByKey Row.valueKey) | skip
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
          first | apply congrArg (dedupByKey Row.valueKey) | skip
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

/-- With row-independent GROUP BY keys there is at most one group, so the
    grouped projection (without DISTINCT) has at most one row. -/
theorem evalSelectProjectDistinct_grouped_length_le_one
    (db : Database)
    (exprEval : Database → Row → Expr → Option Value)
    (selectItemEval : Database → Row → SelectItem → List (String × Value))
    (selectItemWithAggEval : Database → Table → Row → SelectItem → List (String × Value))
    (exprWithAggEval : Database → Table → Row → Expr → Option Value)
    (exprWithWindowEval : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn : List SelectItem → Bool)
    (hasAgg : List SelectItem → Bool)
    (distinct : Bool) (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr) (fr : Table)
    (h_gb : ∀ e ∈ groupBy, ∀ row1 row2, exprEval db row1 e = exprEval db row2 e)
    (hg : (!distinct && !groupBy.isEmpty) = true) :
    (evalSelectProjectDistinct db exprEval selectItemEval selectItemWithAggEval
      exprWithAggEval exprWithWindowEval hasWindowFn hasAgg distinct items
      groupBy having fr).length ≤ 1 := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨hd, hgb⟩ := hg
  have hgb' : (!groupBy.isEmpty) = true := by simp [hgb]
  by_cases hw : hasWindowFn items = true
  · -- windows over groups (#429): one row per surviving group
    simp only [evalSelectProjectDistinct, hd, hgb', hw, Bool.true_or, Bool.and_self, if_true,
      Bool.false_eq_true, if_false, projectGroupsWithWindows_length, groupedSurvivors]
    cases fr with
    | nil => simp
    | cons row rest =>
      have hk0 : ∀ r, groupBy.map (fun e => (exprEval db r e).map Value.setKey) = groupBy.map (fun e => (exprEval db row e).map Value.setKey) :=
        fun r => List.map_congr_left fun e he => by rw [h_gb e he r row]
      have hfold := foldl_addToGroupsByKey_const_key exprEval db groupBy _ row rest
        rfl (fun r _ => hk0 r)
      unfold addToGroupsByKey at hfold
      rw [hfold]
      simp only [List.filterMap_cons, List.filterMap_nil, List.head?_cons]
      split <;> (try split) <;> simp
  · simp only [evalSelectProjectDistinct, hd, hgb', hw, Bool.and_false, if_true,
      Bool.false_eq_true, if_false]
    cases fr with
    | nil => simp
    | cons row rest =>
      have hk0 : ∀ r, groupBy.map (fun e => (exprEval db r e).map Value.setKey) = groupBy.map (fun e => (exprEval db row e).map Value.setKey) :=
        fun r => List.map_congr_left fun e he => by rw [h_gb e he r row]
      have hfold := foldl_addToGroupsByKey_const_key exprEval db groupBy _ row rest
        rfl (fun r _ => hk0 r)
      unfold addToGroupsByKey at hfold
      rw [hfold]
      simp only [List.filterMap_cons, List.filterMap_nil, List.head?_cons]
      split <;> simp

-- ============================================================================
-- evalSelectCore outer row congruence
-- ============================================================================

/-- Stripping the correlated outer-row suffix recovers the inner row (#253). -/
@[simp] theorem take_inner_of_append (row o : Row) :
    (row ++ o).take ((row ++ o).length - o.length) = row := by
  simp

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
    (h_hv : ∀ e, effectiveHaving sel.groupBy sel.items sel.having sel.orderBy = some e →
        ∀ row1 row2, exprEval db row1 e = exprEval db row2 e)
    (h_items_no_star : ∀ item ∈ sel.items, ∃ e alias_, item = .exprItem e alias_)
    (h_si : ∀ item ∈ sel.items, ∀ row1 row2,
        selectItemEval db row1 item = selectItemEval db row2 item)
    (h_sia : ∀ item ∈ sel.items, ∀ rows1 rows2 s1 s2,
        rows1.length = rows2.length →
        selectItemWithAggEval db rows1 s1 item = selectItemWithAggEval db rows2 s2 item)
    (h_ea : ∀ e, effectiveHaving sel.groupBy sel.items sel.having sel.orderBy = some e → ∀ rows1 rows2 s1 s2,
        rows1.length = rows2.length →
        exprWithAggEval db rows1 s1 e = exprWithAggEval db rows2 s2 e)
    (h_ew : ∀ e alias_, .exprItem e alias_ ∈ sel.items → ∀ row1 row2 p1 p2 sp1 sp2 idx,
        p1.length = p2.length →
        exprWithWindowEval db row1 p1 sp1 idx e = exprWithWindowEval db row2 p2 sp2 idx e)
    (h_gwin : ((!sel.groupBy.isEmpty || hasAgg sel.items ||
      implicitGroup hasWindowFn sel.items (effectiveHaving sel.groupBy sel.items sel.having sel.orderBy)) && hasWindowFn sel.items) = false)
    (h_obw : orderByHasWindow sel.orderBy = false) :
    evalSelectCore db r1 fromEval exprEval selectItemEval selectItemWithAggEval exprWithAggEval
      compareEval exprWithWindowEval hasWindowFn hasAgg sel =
    evalSelectCore db r2 fromEval exprEval selectItemEval selectItemWithAggEval exprWithAggEval
      compareEval exprWithWindowEval hasWindowFn hasAgg sel := by
  obtain ⟨d, items, from_, wc, gb, hv, ob, lim, off⟩ := sel
  simp only [SelectStmt.whereClause, SelectStmt.groupBy, SelectStmt.having,
             SelectStmt.items, SelectStmt.orderBy] at *
  simp only [evalSelectCore_eq_afterFilter, evalSelectAfterFilter, h_obw, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte]
  -- the hypotheses are about the HAVING the pipeline evaluates (#445)
  generalize effectiveHaving gb items hv ob = hv at h_hv h_ea h_gwin ⊢
  by_cases hg : (!d && !gb.isEmpty) = true
  · -- Grouped, no DISTINCT (#234): ORDER BY uses per-group key rows. The
    -- GROUP BY keys are row-independent, so there is at most one group, and
    -- sorting at most one row is the identity whatever the keys are.
    simp only [hg, ↓reduceIte, Bool.or_true]
    have key : ∀ (K1 K2 P1 P2 : Table), P1 = P2 → P1.length ≤ 1 →
        K1.length = P1.length → K2.length = P2.length →
        applyOrderByLimitOffsetAligned compareEval db (groupOrderByItems ob) lim off
          true K1 P1 =
        applyOrderByLimitOffsetAligned compareEval db (groupOrderByItems ob) lim off
          true K2 P2 := by
      intro K1 K2 P1 P2 hP hle hK1 hK2
      subst hP
      exact applyOrderByLimitOffsetAligned_of_length_le_one _ _ _ _ _ _ _ _ _ _ _ hle
        (fun _ => hK1) (fun _ => hK2)
    apply key
    · -- rows: projection congruence (unchanged machinery)
      cases wc with
      | none =>
        exact evalSelectProjectDistinct_eq_of_length_eq db _ _ _ _ _ _ _
          d items gb hv _ _ (by simp [List.length_map])
          h_gb h_hv h_items_no_star h_si h_sia h_ea h_ew h_gwin
      | some wcond =>
        exact evalSelectProjectDistinct_eq_of_length_eq db _ _ _ _ _ _ _
          d items gb hv _ _
          (by apply filter_const_length_eq' _ _ _
                (exprEval db r1 wcond == some (Value.bool true))
              · intro row; congr 1; exact h_wc wcond rfl row r1
              · simp [List.length_map])
          h_gb h_hv h_items_no_star h_si h_sia h_ea h_ew h_gwin
    · exact evalSelectProjectDistinct_grouped_length_le_one _ _ _ _ _ _ _ _ _ _ _ _ _ h_gb hg
    all_goals
      have hd : d = false := by simp only [Bool.and_eq_true] at hg; simpa using hg.1
      have hgb : (!gb.isEmpty) = true := by simp only [Bool.and_eq_true] at hg; exact hg.2
      subst hd
      exact groupedOrderKeys_length_aligned_noWinKey _ _ _ _ _ _ _ _ _ _ _ _ _ hgb h_obw
  · have hg' : (!d && !gb.isEmpty) = false := by simpa using hg
    by_cases hgd : (d && !gb.isEmpty) = true
    · -- Grouped DISTINCT (#320): the GROUP BY keys are row-independent, so there is at most
      -- one group and one output row, and sorting it is the identity whatever the sources.
      have hgb : (!false && !gb.isEmpty) = true := by
        simp only [Bool.and_eq_true] at hgd; simp [hgd.2]
      have key2 : ∀ (o : List OrderByItem) (us : Bool) (K1 K2 P1 P2 : Table), P1 = P2 →
          P1.length ≤ 1 → (us = true → K1.length = P1.length) →
          (us = true → K2.length = P2.length) →
          applyOrderByLimitOffsetAligned compareEval db o lim off us K1 P1 =
          applyOrderByLimitOffsetAligned compareEval db o lim off us K2 P2 := by
        intro o us K1 K2 P1 P2 hP hle h1 h2
        subst hP
        exact applyOrderByLimitOffsetAligned_of_length_le_one _ _ _ _ _ _ _ _ _ _ _ hle h1 h2
      simp only [hg', hgd, Bool.false_eq_true, ↓reduceIte]
      apply key2
      · -- rows: projection congruence (unchanged machinery)
        cases wc with
        | none =>
          exact evalSelectProjectDistinct_eq_of_length_eq db _ _ _ _ _ _ _
            d items gb hv _ _ (by simp [List.length_map])
            h_gb h_hv h_items_no_star h_si h_sia h_ea h_ew h_gwin
        | some wcond =>
          exact evalSelectProjectDistinct_eq_of_length_eq db _ _ _ _ _ _ _
            d items gb hv _ _
            (by apply filter_const_length_eq' _ _ _
                  (exprEval db r1 wcond == some (Value.bool true))
                · intro row; congr 1; exact h_wc wcond rfl row r1
                · simp [List.length_map])
            h_gb h_hv h_items_no_star h_si h_sia h_ea h_ew h_gwin
      · have hd : d = true := by simp only [Bool.and_eq_true] at hgd; exact hgd.1
        subst hd
        rw [evalSelectProjectDistinct_true]
        exact Nat.le_trans (length_dedupByKey_le _ _)
          (evalSelectProjectDistinct_grouped_length_le_one _ _ _ _ _ _ _ _ false _ _ _ _ h_gb hgb)
      all_goals
        intro _
        have hd : d = true := by simp only [Bool.and_eq_true] at hgd; exact hgd.1
        subst hd
        rw [List.length_map, length_dedupByKey_zip _ _ _
          (groupedOrderKeys_length_aligned_noWinKey _ _ _ _ _ _ _ _ _ _ _ _ _
            (by simpa using hgb) h_obw).symm,
          evalSelectProjectDistinct_true]
    have hgd' : (d && !gb.isEmpty) = false := by simpa using hgd
    simp only [hg', hgd', Bool.false_eq_true, ↓reduceIte, Bool.or_false]
    -- The aligned ORDER BY takes (sources, rows); both are row-context
    -- independent: sources because the outer suffix is stripped, rows by the
    -- existing projection congruence.
    have congr2 : ∀ {α β γ : Type} (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β},
        a₁ = a₂ → b₁ = b₂ → f a₁ b₁ = f a₂ b₂ := by
      intro _ _ _ f _ _ _ _ h1 h2; rw [h1, h2]
    -- Plain DISTINCT pairs each projected row with its stripped source row and keeps the first
    -- of each value key (#320): context-independent when both components are.
    have hsrc : ∀ (b : Bool) (P1 P2 S1 S2 : Table), S1 = S2 → (S1.length = S2.length → P1 = P2) →
        (if b = true then (dedupByKey (fun p => Row.valueKey p.1) (P1.zip S1)).map Prod.snd
         else S1) =
        (if b = true then (dedupByKey (fun p => Row.valueKey p.1) (P2.zip S2)).map Prod.snd
         else S2) := by
      intro b P1 P2 S1 S2 hS hP; subst hS; rw [hP rfl]
    apply congr2
    apply hsrc
    · -- sources: (havingRows).map (drop outer.length) is context-independent
      cases wc with
      | none =>
        cases hv with
        | none =>
          simp [List.map_map, Function.comp_def]
        | some hcond =>
          simp only [List.filter_map, List.map_map, Function.comp_def,
            take_inner_of_append, List.map_id']
          exact List.filter_congr (fun row _ => by
            congr 1; exact h_hv hcond rfl (row ++ r1) (row ++ r2))
      | some wcond =>
        cases hv with
        | none =>
          simp only [List.filter_map, List.map_map, Function.comp_def,
            take_inner_of_append, List.map_id']
          exact List.filter_congr (fun row _ => by
            congr 1; exact h_wc wcond rfl (row ++ r1) (row ++ r2))
        | some hcond =>
          simp only [List.filter_map, List.map_map, Function.comp_def,
            take_inner_of_append, List.map_id', List.filter_filter]
          exact List.filter_congr (fun row _ => by
            rw [h_wc wcond rfl (row ++ r1) (row ++ r2),
                h_hv hcond rfl (row ++ r1) (row ++ r2)])
    · -- projected rows (#320): ground items project every row alike, so equal lengths suffice
      intro hlen
      simp only [List.length_map] at hlen
      obtain ⟨r0⟩ : Nonempty Row := ⟨[]⟩
      exact map_const_length_eq' _ _ _ (items.flatMap (selectItemEval db r0))
        (fun row => flatMap_congr_mem (fun item hi => h_si item hi row r0)) hlen
    · -- rows: projection congruence (unchanged machinery)
      cases wc with
      | none =>
        exact evalSelectProjectDistinct_eq_of_length_eq db _ _ _ _ _ _ _
          d items gb hv _ _ (by simp [List.length_map])
          h_gb h_hv h_items_no_star h_si h_sia h_ea h_ew h_gwin
      | some wcond =>
        exact evalSelectProjectDistinct_eq_of_length_eq db _ _ _ _ _ _ _
          d items gb hv _ _
          (by apply filter_const_length_eq' _ _ _
                (exprEval db r1 wcond == some (Value.bool true))
              · intro row; congr 1; exact h_wc wcond rfl row r1
              · simp [List.length_map])
          h_gb h_hv h_items_no_star h_si h_sia h_ea h_ew h_gwin

-- ============================================================================
-- Callback congruence by computable size (#212)
-- ============================================================================

/-- `evalExprCore` only calls its subquery callback on subqueries inside `e`,
    all of which have smaller `size`: callbacks that agree there give the same
    result. Used to remove the termination guards of `evalExprWithDb`. -/
theorem evalExprCore_congr_subq (db : Database) (row : Row) :
    ∀ (n : Nat) (e : Expr), e.size ≤ n → ∀ (f g : Database → Row → SubQuery → Table),
    (∀ sq, sq.size < e.size → f db row sq = g db row sq) →
    evalExprCore db row f e = evalExprCore db row g e := by
  intro n
  induction n with
  | zero => intro e he; have := Expr.size_pos e; omega
  | succ n ih =>
    intro e he f g hfg
    have sub : ∀ x : Expr, x.size < e.size →
        evalExprCore db row f x = evalExprCore db row g x :=
      fun x hx => ih x (by omega) f g (fun sq hsq => hfg sq (by omega))
    cases e with
    | lit v => rw [evalExprCore, evalExprCore]
    | col c => rw [evalExprCore, evalExprCore]
    | binOp op l r =>
      simp only [evalExprCore]
      rw [sub l (by simp [Expr.size]; omega), sub r (by simp [Expr.size]; omega)]
    | unaryOp op a =>
      simp only [evalExprCore]
      rw [sub a (by simp [Expr.size])]
    | func name args =>
      simp only [evalExprCore]
      congr 1
      apply List.map_congr_left
      intro x hx
      exact sub x (by have := Expr.size_le_sizeList_of_mem hx; simp [Expr.size]; omega)
    | agg fn a d => rw [evalExprCore, evalExprCore]
    | countStar => rw [evalExprCore, evalExprCore]
    | «case» ws el =>
      rw [evalExprCore_case, evalExprCore_case]
      apply evalCaseHelper_congr
      · cases el with
        | none => rfl
        | some x => exact sub x (by simp [Expr.size, Expr.sizeOpt]; omega)
      · intro p hp
        obtain ⟨a, b⟩ := p
        have hs := Expr.size_le_sizePairs_of_mem hp
        exact ⟨sub a (by simp [Expr.size]; omega), sub b (by simp [Expr.size]; omega)⟩
    | inList a neg vals =>
      have h_ev := sub a (by simp [Expr.size]; omega)
      have h_vals : ∀ vi, vi ∈ vals → evalExprCore db row f vi = evalExprCore db row g vi :=
        fun vi hvi => sub vi (by have := Expr.size_le_sizeList_of_mem hvi; simp [Expr.size]; omega)
      rw [evalExprCore_inList, evalExprCore_inList]
      dsimp only []
      rw [inList_foldl_eval_independent (evalExprCore db row f) (evalExprCore db row g) _ _ h_ev vals h_vals]
    | inSubquery a neg sq =>
      simp only [evalExprCore]
      rw [sub a (by simp [Expr.size]; omega), hfg sq (by simp [Expr.size]; omega)]
    | «exists» neg sq =>
      simp only [evalExprCore]
      rw [hfg sq (by simp [Expr.size])]
    | subquery sq =>
      simp only [evalExprCore]
      rw [hfg sq (by simp [Expr.size])]
    | between a lo hi =>
      simp only [evalExprCore]
      rw [sub a (by simp [Expr.size]; omega), sub lo (by simp [Expr.size]; omega),
        sub hi (by simp [Expr.size]; omega)]
    | windowFn fn a spec => rw [evalExprCore, evalExprCore]

/-- `evalFromCore` only calls its callbacks on parts of `fc` (join conditions,
    FROM subqueries), all of which have smaller `size`. -/
theorem evalFromCore_congr (db : Database) :
    ∀ (n : Nat) (fc : FromClause), fc.size ≤ n →
    ∀ (f1 f2 : Database → Row → Expr → Option Value) (s1 s2 : Database → SubQuery → Table),
    (∀ e, e.size < fc.size → ∀ r, f1 db r e = f2 db r e) →
    (∀ sq, sq.size < fc.size → s1 db sq = s2 db sq) →
    evalFromCore db f1 s1 fc = evalFromCore db f2 s2 fc := by
  intro n
  induction n with
  | zero => intro fc h; have := FromClause.size_pos fc; omega
  | succ n ih =>
    intro fc hfc f1 f2 s1 s2 hf hs
    cases fc with
    | table t => simp only [evalFromCore]
    | subquery sq a =>
      simp only [evalFromCore]
      rw [hs sq (by simp [FromClause.size])]
    | join l jt r on_ =>
      have hl := ih l (by simp [FromClause.size] at hfc; omega) f1 f2 s1 s2
        (fun e he r => hf e (by simp [FromClause.size]; omega) r)
        (fun sq hsq => hs sq (by simp [FromClause.size]; omega))
      have hr := ih r (by simp [FromClause.size] at hfc; omega) f1 f2 s1 s2
        (fun e he r => hf e (by simp [FromClause.size]; omega) r)
        (fun sq hsq => hs sq (by simp [FromClause.size]; omega))
      simp only [evalFromCore]
      rw [hl, hr]
      cases on_ with
      | none => rfl
      | some cond =>
        have hc : ∀ r, f1 db r cond = f2 db r cond :=
          hf cond (by simp [FromClause.size, Expr.sizeOpt]; omega)
        simp only [hc]

-- ============================================================================
-- evalSelectCore callback congruence (#212 phase 2)
-- ============================================================================


theorem applyOrderByLimitOffsetAligned_congr
    (cA cB : Database → Row → Row → List OrderByItem → Bool)
    (db : Database) (ob : List OrderByItem) (lim off : Option Nat) (us : Bool) (src rows : Table)
    (h : ∀ r1 r2, cA db r1 r2 ob = cB db r1 r2 ob) :
    applyOrderByLimitOffsetAligned cA db ob lim off us src rows =
    applyOrderByLimitOffsetAligned cB db ob lim off us src rows := by
  simp only [applyOrderByLimitOffsetAligned, h]

theorem groupOrderKeyRow_congr (db : Database)
    (aA aB : Database → Table → Row → Expr → Option Value) (ob : List OrderByItem)
    (h : ∀ o ∈ ob, ∀ rows r, aA db rows r o.expr = aB db rows r o.expr)
    (groupRows : Table) (sampleRow projected : Row) :
    groupOrderKeyRow db aA ob groupRows sampleRow projected =
    groupOrderKeyRow db aB ob groupRows sampleRow projected := by
  simp only [groupOrderKeyRow]
  apply filterMap_congr_mem
  intro x hx
  rw [h x.2 (List.of_mem_zip hx).2]

/-- Equal group-by values give equal grouping keys (`Value.setKey`: NULL tags erased and numbers
    compared by value, #315). -/
theorem groupKey_congr {db : Database} {eA eB : Database → Row → Expr → Option Value}
    {gb : List Expr} (hG : ∀ r, gb.map (eA db r) = gb.map (eB db r)) (r : Row) :
    gb.map (fun e => (eA db r e).map Value.setKey) =
      gb.map (fun e => (eB db r e).map Value.setKey) := by
  have h := congrArg (List.map (Option.map Value.setKey)) (hG r)
  simpa [List.map_map, Function.comp_def] using h

theorem evalSelectGroupOrderKeys_congr (db : Database)
    (eA eB : Database → Row → Expr → Option Value)
    (siaA siaB : Database → Table → Row → SelectItem → List (String × Value))
    (aA aB : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (gb : List Expr) (hv : Option Expr) (ob : List OrderByItem)
    (rows : Table)
    (hG : ∀ r, gb.map (eA db r) = gb.map (eB db r))
    (hSIA : ∀ rs r, items.flatMap (siaA db rs r) = items.flatMap (siaB db rs r))
    (hHa : ∀ c, hv = some c → ∀ rs r, aA db rs r c = aB db rs r c)
    (hOK : ∀ o ∈ ob, ∀ rs r, aA db rs r o.expr = aB db rs r o.expr)
    (hB : ∀ rs, bareSampleRow (eA db) (selectMinMaxCalls items hv) rs =
      bareSampleRow (eB db) (selectMinMaxCalls items hv) rs) :
    evalSelectGroupOrderKeys db eA siaA aA items gb hv ob rows =
    evalSelectGroupOrderKeys db eB siaB aB items gb hv ob rows := by
  have hK := groupOrderKeyRow_congr db aA aB ob hOK
  have hG' := groupKey_congr hG
  cases hv with
  | none => simp only [evalSelectGroupOrderKeys, hG', hSIA, hK, hB]
  | some c =>
    have hc := hHa c rfl
    simp only [evalSelectGroupOrderKeys, hG', hSIA, hK, hc, hB]


theorem groupedSurvivors_congr (db : Database)
    (eA eB : Database → Row → Expr → Option Value)
    (aA aB : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (gb : List Expr) (hv : Option Expr) (rows : Table)
    (hG : ∀ r, gb.map (eA db r) = gb.map (eB db r))
    (hHa : ∀ c, hv = some c → ∀ rs r, aA db rs r c = aB db rs r c)
    (hB : ∀ rs, bareSampleRow (eA db) (selectMinMaxCalls items hv) rs =
      bareSampleRow (eB db) (selectMinMaxCalls items hv) rs) :
    groupedSurvivors db eA aA items gb hv rows = groupedSurvivors db eB aB items gb hv rows := by
  have hG' := groupKey_congr hG
  cases hv with
  | none => simp only [groupedSurvivors, hG', hB]
  | some c =>
    have hc := hHa c rfl
    simp only [groupedSurvivors, hG', hc, hB]

theorem aggSurvivors_congr (db : Database)
    (eA eB : Database → Row → Expr → Option Value)
    (aA aB : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (hv : Option Expr) (rows : Table)
    (hHa : ∀ c, hv = some c → ∀ rs r, aA db rs r c = aB db rs r c)
    (hB : ∀ rs, bareSampleRow (eA db) (selectMinMaxCalls items hv) rs =
      bareSampleRow (eB db) (selectMinMaxCalls items hv) rs) :
    aggSurvivors db eA aA items hv rows = aggSurvivors db eB aB items hv rows := by
  cases hv with
  | none => simp only [aggSurvivors, hB]
  | some c =>
    have hc := hHa c rfl
    simp only [aggSurvivors, hc, hB]

/-- The window projection over groups only uses the aggregate evaluator through the window
    evaluator on the items' expressions, and the item evaluator on the items (#429). -/
theorem projectGroupsWithWindows_congr (db : Database)
    (siaA siaB : Database → Table → Row → SelectItem → List (String × Value))
    (aA aB : Database → Table → Row → Expr → Option Value)
    (items : List SelectItem) (gs : List (Table × Row))
    (hSIA1 : ∀ item ∈ items, ∀ rs r, siaA db rs r item = siaB db rs r item)
    (hGW : ∀ e a, SelectItem.exprItem e a ∈ items → ∀ r p sp i,
      evalExprWithWindowParam (groupWindowEval aA gs) db r p sp i e =
      evalExprWithWindowParam (groupWindowEval aB gs) db r p sp i e) :
    projectGroupsWithWindows db siaA aA items gs = projectGroupsWithWindows db siaB aB items gs := by
  simp only [projectGroupsWithWindows]
  apply List.map_congr_left
  intro x _
  apply flatMap_congr_mem
  intro item hmem
  cases item with
  | star t => exact hSIA1 _ hmem _ _
  | exprItem e a =>
    simp only []
    split
    · rw [hGW e a hmem]
    · exact hSIA1 _ hmem _ _

theorem groupWindowOrderKeys_congr (db : Database)
    (aA aB : Database → Table → Row → Expr → Option Value) (ob : List OrderByItem)
    (hOK : ∀ o ∈ ob, ∀ rs r, aA db rs r o.expr = aB db rs r o.expr)
    (gs : List (Table × Row))
    (hOW : ∀ o ∈ ob, ∀ r p sp i,
      evalExprWithWindowParam (groupWindowEval aA gs) db r p sp i o.expr =
      evalExprWithWindowParam (groupWindowEval aB gs) db r p sp i o.expr)
    (projected : Table) :
    groupWindowOrderKeys db aA ob gs projected = groupWindowOrderKeys db aB ob gs projected := by
  simp only [groupWindowOrderKeys, groupWindowKeyRow]
  apply List.map_congr_left
  intro x _
  apply filterMap_congr_mem
  intro y hy
  have hm := (List.of_mem_zip hy).2
  by_cases hw : exprHasWindowFn y.2.expr = true
  · simp only [hw, if_true, hOW _ hm]
  · simp only [hw, Bool.false_eq_true, if_false, hOK _ hm]

/-- The hidden window-key columns only use the window evaluator on the `ORDER BY` keys (#435). -/
theorem windowOrderKeyCols_congr
    (wA wB : Database → Row → Table → Table → Nat → Expr → Option Value)
    (db : Database) (row : Row) (rows : Table) (idx : Nat) (ob : List OrderByItem)
    (h : ∀ o ∈ ob, ∀ r p sp i, wA db r p sp i o.expr = wB db r p sp i o.expr) :
    windowOrderKeyCols wA db row rows idx ob = windowOrderKeyCols wB db row rows idx ob := by
  simp only [windowOrderKeyCols]
  apply filterMap_congr_mem
  intro y hy
  rw [h _ (List.of_mem_zip hy).2]


/-- `evalSelectCore` congruence over its callbacks: two callback tuples that
    agree wherever `evalSelectCore` uses them on `sel` give the same result. -/
theorem evalSelectCore_callbacks_congr (db : Database) (outerRow : Row)
    (fA fB : Database → FromClause → Table)
    (eA eB : Database → Row → Expr → Option Value)
    (siA siB : Database → Row → SelectItem → List (String × Value))
    (siaA siaB : Database → Table → Row → SelectItem → List (String × Value))
    (aA aB : Database → Table → Row → Expr → Option Value)
    (cA cB : Database → Row → Row → List OrderByItem → Bool)
    (wA wB : Database → Row → Table → Table → Nat → Expr → Option Value)
    (hasWindowFn hasAgg : List SelectItem → Bool) (sel : SelectStmt)
    (hF : ∀ f, sel.fromClause = some f → fA db f = fB db f)
    (hW : ∀ c, sel.whereClause = some c → ∀ r, eA db r c = eB db r c)
    (hHe : ∀ c, effectiveHaving sel.groupBy sel.items sel.having sel.orderBy = some c → ∀ r, eA db r c = eB db r c)
    (hHa : ∀ c, effectiveHaving sel.groupBy sel.items sel.having sel.orderBy = some c → ∀ rs r, aA db rs r c = aB db rs r c)
    (hG : ∀ r, sel.groupBy.map (eA db r) = sel.groupBy.map (eB db r))
    (hSI : ∀ r, sel.items.flatMap (siA db r) = sel.items.flatMap (siB db r))
    (hSIA : ∀ rs r, sel.items.flatMap (siaA db rs r) = sel.items.flatMap (siaB db rs r))
    (hEW : ∀ e a, SelectItem.exprItem e a ∈ sel.items →
      ∀ r p sp i, wA db r p sp i e = wB db r p sp i e)
    (hC1 : ∀ r1 r2, cA db r1 r2 sel.orderBy = cB db r1 r2 sel.orderBy)
    (hC2 : ∀ r1 r2, cA db r1 r2 (groupOrderByItems sel.orderBy) =
      cB db r1 r2 (groupOrderByItems sel.orderBy))
    (hOK : ∀ o ∈ sel.orderBy, ∀ rs r, aA db rs r o.expr = aB db rs r o.expr)
    (hB : ∀ rs, bareSampleRow (eA db) (selectMinMaxCalls sel.items (effectiveHaving sel.groupBy sel.items sel.having sel.orderBy)) rs =
      bareSampleRow (eB db) (selectMinMaxCalls sel.items (effectiveHaving sel.groupBy sel.items sel.having sel.orderBy)) rs)
    (hSIA1 : ∀ item ∈ sel.items, ∀ rs r, siaA db rs r item = siaB db rs r item)
    (hGW : ∀ e a, SelectItem.exprItem e a ∈ sel.items → ∀ gs r p sp i,
      evalExprWithWindowParam (groupWindowEval aA gs) db r p sp i e =
      evalExprWithWindowParam (groupWindowEval aB gs) db r p sp i e)
    (hOWp : ∀ o ∈ sel.orderBy, ∀ r p sp i, wA db r p sp i o.expr = wB db r p sp i o.expr)
    (hOWg : ∀ o ∈ sel.orderBy, ∀ gs r p sp i,
      evalExprWithWindowParam (groupWindowEval aA gs) db r p sp i o.expr =
      evalExprWithWindowParam (groupWindowEval aB gs) db r p sp i o.expr)
    (hC3 : ∀ r1 r2, cA db r1 r2 (windowOrderByItems sel.orderBy) =
      cB db r1 r2 (windowOrderByItems sel.orderBy)) :
    evalSelectCore db outerRow fA eA siA siaA aA cA wA hasWindowFn hasAgg sel =
    evalSelectCore db outerRow fB eB siB siaB aB cB wB hasWindowFn hasAgg sel := by
  obtain ⟨d, items, from_, w, gb, hv, ob, lim, off⟩ := sel
  simp only [SelectStmt.fromClause, SelectStmt.whereClause, SelectStmt.having,
    SelectStmt.groupBy, SelectStmt.items, SelectStmt.orderBy] at *
  -- the hypotheses are about the HAVING the pipeline evaluates (#445)
  obtain ⟨hv', hhv'⟩ : ∃ x, effectiveHaving gb items hv ob = x := ⟨_, rfl⟩
  simp only [hhv'] at hHe hHa hB
  have hGK : ∀ rows, evalSelectGroupOrderKeys db eA siaA aA items gb hv' ob rows =
      evalSelectGroupOrderKeys db eB siaB aB items gb hv' ob rows :=
    fun rows => evalSelectGroupOrderKeys_congr db eA eB siaA siaB aA aB items gb hv' ob rows
      hG hSIA hHa hOK hB
  have hWin : ∀ r p sp i, projectWindowItems wA db r p sp i items =
      projectWindowItems wB db r p sp i items :=
    fun r p sp i => projectWindowItems_congr wA wB db r p sp i items
      (fun e a ha => hEW e a ha r p sp i)
  have hOrd : ∀ (us : Bool) (src rows : Table),
      applyOrderByLimitOffsetAligned cA db
        (if (!d && !gb.isEmpty || d && !gb.isEmpty) = true then groupOrderByItems ob
         else if orderByHasWindow ob = true then windowOrderByItems ob else ob)
        lim off us src rows =
      applyOrderByLimitOffsetAligned cB db
        (if (!d && !gb.isEmpty || d && !gb.isEmpty) = true then groupOrderByItems ob
         else if orderByHasWindow ob = true then windowOrderByItems ob else ob)
        lim off us src rows := by
    intro us src rows
    split
    · exact applyOrderByLimitOffsetAligned_congr cA cB db _ lim off us src rows hC2
    · split
      · exact applyOrderByLimitOffsetAligned_congr cA cB db _ lim off us src rows hC3
      · exact applyOrderByLimitOffsetAligned_congr cA cB db _ lim off us src rows hC1
  have hFrom : (match from_ with | some f => fA db f | none => [[]]) =
      (match from_ with | some f => fB db f | none => [[]]) := by
    cases from_ with
    | none => rfl
    | some f => exact hF f rfl
  simp only [evalSelectCore, hhv', SelectStmt.distinct, SelectStmt.items, SelectStmt.fromClause,
    SelectStmt.whereClause, SelectStmt.groupBy, SelectStmt.having, SelectStmt.orderBy,
    SelectStmt.limitVal, SelectStmt.offsetVal, groupKey_congr hG, hSI, hSIA, hWin, hGK, hB,
    groupedSurvivors_congr db eA eB aA aB items gb hv' _ hG hHa hB,
    aggSurvivors_congr db eA eB aA aB items hv' _ hHa hB,
    projectGroupsWithWindows_congr db siaA siaB aA aB items _ hSIA1 (fun e a h => hGW e a h _),
    groupWindowOrderKeys_congr db aA aB ob hOK _ (fun o ho => hOWg o ho _),
    windowOrderKeyCols_congr wA wB db _ _ _ ob hOWp]
  erw [hOrd]
  cases from_ <;> cases w <;> cases hv' <;>
    (try simp only [hF _ rfl]) <;> (try simp only [hW _ rfl]) <;>
    (try simp only [hHe _ rfl, hHa _ rfl]) <;> rfl

end SqlEquiv
