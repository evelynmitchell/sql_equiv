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

end SqlEquiv
