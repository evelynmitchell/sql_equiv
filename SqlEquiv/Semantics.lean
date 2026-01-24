/-
  SQL Semantics: Evaluation Model

  Defines what SQL statements *mean* using a relational algebra model.
  This enables formal equivalence proofs.
-/
import SqlEquiv.Ast

namespace SqlEquiv

-- ============================================================================
-- Core Types
-- ============================================================================

/-- A row is a mapping from column names to values -/
abbrev Row := List (String × Value)

/-- A table is a list of rows (bag semantics for now) -/
abbrev Table := List Row

/-- A database maps table names to tables -/
abbrev Database := String → Table

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Check if string contains substring (simple implementation) -/
def stringContains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else go h n
where
  go : List Char → List Char → Bool
  | [], _ => false
  | h :: hs, needle =>
    if needle.isPrefixOf (h :: hs) then true
    else go hs needle

/-- Enumerate a list with indices -/
def listEnumerate {α : Type} (xs : List α) : List (Nat × α) :=
  go 0 xs
where
  go (i : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (i, x) :: go (i + 1) xs

-- ============================================================================
-- Row Operations
-- ============================================================================

/-- Get value from row by column name -/
def Row.get (row : Row) (col : String) : Option Value :=
  row.lookup col

/-- Get value from row by qualified column name -/
def Row.getQualified (row : Row) (table : Option String) (col : String) : Option Value :=
  match table with
  | some t => row.lookup s!"{t}.{col}"
  | none =>
    -- Try unqualified first, then any qualified match
    match row.lookup col with
    | some v => some v
    | none =>
      match row.find? (fun (k, _) => k.endsWith s!".{col}") with
      | some (_, v) => some v
      | none => none

-- ============================================================================
-- Value Operations
-- ============================================================================

/-- Compare two values for equality -/
def Value.eq : Value → Value → Option Bool
  | .null, _ => none  -- NULL = anything is NULL
  | _, .null => none
  | .int a, .int b => some (a == b)
  | .string a, .string b => some (a == b)
  | .bool a, .bool b => some (a == b)
  | _, _ => none  -- type mismatch

/-- Compare two values for ordering -/
def Value.compare : Value → Value → Option Ordering
  | .null, _ => none
  | _, .null => none
  | .int a, .int b => some (Ord.compare a b)
  | .string a, .string b => some (Ord.compare a b)
  | _, _ => none

/-- Convert value to boolean for WHERE clauses -/
def Value.toBool : Value → Option Bool
  | .bool b => some b
  | .null => none
  | .int n => some (n != 0)
  | _ => none

-- ============================================================================
-- Expression Evaluation
-- ============================================================================

/-- Evaluate expression against a row -/
partial def evalExpr (row : Row) : Expr → Option Value
  | .lit v => some v
  | .col c => row.getQualified c.table c.column
  | .binOp op l r => evalBinOp op (evalExpr row l) (evalExpr row r)
  | .unaryOp op e => evalUnaryOp op (evalExpr row e)
  | .func name args => evalFunc name (args.map (evalExpr row))
  | .case branches else_ => evalCase row branches else_
  | .inList e vals =>
    match evalExpr row e with
    | none => none
    | some v =>
      let hasMatch := vals.filterMap (evalExpr row) |>.any fun v' =>
        v.eq v' == some true
      some (Value.bool hasMatch)
  | .between e lo hi =>
    match evalExpr row e, evalExpr row lo, evalExpr row hi with
    | some v, some vlo, some vhi =>
      match v.compare vlo, v.compare vhi with
      | some .lt, _ => some (Value.bool false)
      | _, some .gt => some (Value.bool false)
      | some _, some _ => some (Value.bool true)
      | _, _ => none
    | _, _, _ => none

where
  evalBinOp (op : BinOp) (l r : Option Value) : Option Value :=
    match op, l, r with
    | .add, some (.int a), some (.int b) => some (.int (a + b))
    | .sub, some (.int a), some (.int b) => some (.int (a - b))
    | .mul, some (.int a), some (.int b) => some (.int (a * b))
    | .div, some (.int a), some (.int b) =>
      if b == 0 then none else some (.int (a / b))
    | .mod, some (.int a), some (.int b) =>
      if b == 0 then none else some (.int (a % b))
    | .eq, some a, some b => (a.eq b).map Value.bool
    | .ne, some a, some b => (a.eq b).map (fun b => Value.bool (!b))
    | .lt, some a, some b => (a.compare b).map (fun o => Value.bool (o == .lt))
    | .le, some a, some b => (a.compare b).map (fun o => Value.bool (o != .gt))
    | .gt, some a, some b => (a.compare b).map (fun o => Value.bool (o == .gt))
    | .ge, some a, some b => (a.compare b).map (fun o => Value.bool (o != .lt))
    | .and, some (.bool a), some (.bool b) => some (.bool (a && b))
    | .and, some (.bool false), _ => some (.bool false)  -- short-circuit
    | .and, _, some (.bool false) => some (.bool false)
    | .or, some (.bool a), some (.bool b) => some (.bool (a || b))
    | .or, some (.bool true), _ => some (.bool true)  -- short-circuit
    | .or, _, some (.bool true) => some (.bool true)
    | .concat, some (.string a), some (.string b) => some (.string (a ++ b))
    | .like, some (.string s), some (.string pat) =>
      -- Simplified LIKE: only handles % as wildcard
      some (.bool (simpleLike s pat))
    | _, _, _ => none

  simpleLike (s pat : String) : Bool :=
    -- Very simplified: % matches anything, _ matches one char
    let patChars := pat.toList
    if pat == "%" then true
    else if pat.startsWith "%" && pat.endsWith "%" then
      let inner := patChars.drop 1 |>.dropLast |> String.ofList
      stringContains s inner
    else if pat.startsWith "%" then
      let suffix := patChars.drop 1 |> String.ofList
      s.endsWith suffix
    else if pat.endsWith "%" then
      let patPrefix := patChars.dropLast |> String.ofList
      s.startsWith patPrefix
    else
      s == pat

  evalUnaryOp (op : UnaryOp) (e : Option Value) : Option Value :=
    match op, e with
    | .not, some (.bool b) => some (.bool (!b))
    | .neg, some (.int n) => some (.int (-n))
    | .isNull, v => some (.bool (v.isNone || v == some .null))
    | .isNotNull, v => some (.bool (v.isSome && v != some .null))
    | _, _ => none

  evalFunc (name : String) (args : List (Option Value)) : Option Value :=
    match name.toUpper, args with
    | "COALESCE", vals =>
      vals.find? (fun v => v.isSome && v != some .null) |>.join
    | "NULLIF", [some a, some b] =>
      if a.eq b == some true then some .null else some a
    | "ABS", [some (.int n)] => some (.int n.natAbs)
    | "LENGTH", [some (.string s)] => some (.int s.length)
    | "UPPER", [some (.string s)] => some (.string s.toUpper)
    | "LOWER", [some (.string s)] => some (.string s.toLower)
    | _, _ => none

  evalCase (row : Row) (branches : List (Expr × Expr)) (else_ : Option Expr) : Option Value :=
    match branches with
    | [] => else_.bind (evalExpr row)
    | (cond, result) :: rest =>
      match evalExpr row cond with
      | some (.bool true) => evalExpr row result
      | some (.bool false) => evalCase row rest else_
      | _ => none  -- NULL condition treated as false

-- ============================================================================
-- SELECT Evaluation
-- ============================================================================

/-- Evaluate FROM clause to get source rows -/
partial def evalFrom (db : Database) : FromClause → Table
  | .table t =>
    let baseTable := db t.name
    -- Qualify column names with table alias
    let qualifier := t.alias.getD t.name
    baseTable.map fun row =>
      row.map fun (col, val) => (s!"{qualifier}.{col}", val)
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
            match evalExpr combined cond with
            | some (.bool true) => some combined
            | _ => none
    | .left =>
      leftRows.flatMap fun lr =>
        let matchingRows := rightRows.filterMap fun rr =>
          let combined := lr ++ rr
          match on_ with
          | none => some combined
          | some cond =>
            match evalExpr combined cond with
            | some (.bool true) => some combined
            | _ => none
        if matchingRows.isEmpty then
          -- Return left row with NULLs for right columns
          match rightRows.head? with
          | some rightRow => [lr ++ rightRow.map fun (k, _) => (k, .null)]
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
            match evalExpr combined cond with
            | some (.bool true) => some combined
            | _ => none
        if matchingRows.isEmpty then
          match leftRows.head? with
          | some leftRow => [leftRow.map (fun (k, _) => (k, .null)) ++ rr]
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
              match evalExpr combined cond with
              | some (.bool true) => true
              | _ => false
          if hasMatch then none
          else match leftRows.head? with
            | some leftRow => some (leftRow.map (fun (k, _) => (k, .null)) ++ rr)
            | none => some rr)

/-- Evaluate SELECT item to extract columns from row -/
partial def evalSelectItem (row : Row) : SelectItem → List (String × Value)
  | .star none =>
    -- Return all columns
    row
  | .star (some t) =>
    -- Return columns from specific table
    row.filter fun (k, _) => k.startsWith s!"{t}."
  | .exprItem e alias =>
    match evalExpr row e with
    | some v =>
      let colName := alias.getD (exprToName e)
      [(colName, v)]
    | none =>
      let colName := alias.getD (exprToName e)
      [(colName, .null)]
where
  exprToName : Expr → String
    | .col c => c.column
    | .func name _ => name
    | _ => "expr"

/-- Evaluate full SELECT statement -/
partial def evalSelect (db : Database) (sel : SelectStmt) : Table :=
  -- 1. FROM clause
  let baseRows : Table := match sel.fromClause with
    | some f => evalFrom db f
    | none => [[]]  -- Single empty row for SELECT without FROM

  -- 2. WHERE clause
  let filteredRows : Table := match sel.whereClause with
    | some cond =>
      baseRows.filter fun row =>
        evalExpr row cond == some (Value.bool true)
    | none => baseRows

  -- 3. GROUP BY - simplified: just pass through (no aggregation support)
  let groupedRows : Table := filteredRows

  -- 4. HAVING clause
  let havingRows : Table := match sel.having with
    | some cond =>
      groupedRows.filter fun row =>
        evalExpr row cond == some (Value.bool true)
    | none => groupedRows

  -- 5. SELECT items (projection)
  let projectedRows : Table := havingRows.map fun row =>
    sel.items.flatMap (evalSelectItem row)

  -- 6. DISTINCT
  let distinctRows : Table := if sel.distinct then
    projectedRows.eraseDups
  else
    projectedRows

  -- 7. ORDER BY
  let orderedRows : Table := if sel.orderBy.isEmpty then distinctRows else
    distinctRows.mergeSort fun r1 r2 =>
      compareByOrderItems r1 r2 sel.orderBy

  -- 8. OFFSET and LIMIT
  let offsetRows : Table := match sel.offsetVal with
    | some n => orderedRows.drop n
    | none => orderedRows
  let limitRows : Table := match sel.limitVal with
    | some n => offsetRows.take n
    | none => offsetRows

  limitRows

where
  compareByOrderItems (r1 r2 : Row) : List OrderByItem → Bool
    | [] => true
    | item :: rest =>
      let v1 := evalExpr r1 item.expr
      let v2 := evalExpr r2 item.expr
      match v1, v2 with
      | some a, some b =>
        match a.compare b with
        | some .lt => item.dir == .asc
        | some .gt => item.dir == .desc
        | _ => compareByOrderItems r1 r2 rest
      | _, _ => compareByOrderItems r1 r2 rest

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
          cols.zip (exprs.map fun e => (evalExpr [] e).getD .null)
        | none =>
          (listEnumerate exprs).map fun (i, e) =>
            (s!"col{i}", (evalExpr [] e).getD .null)
    | .select sel =>
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
          | some cond => evalExpr row cond == some (Value.bool true)
          | none => true
        if shouldUpdate then
          upd.assignments.foldl (fun r a =>
            r.map fun (k, v) =>
              if k == a.column || k.endsWith s!".{a.column}" then
                (k, (evalExpr r a.value).getD .null)
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
        | some cond => evalExpr row cond != some (Value.bool true)
        | none => false  -- DELETE without WHERE deletes all
    else
      db name

/-- Evaluate any statement -/
def evalStmt (db : Database) : Stmt → Database × Option Table
  | .select s => (db, some (evalSelect db s))
  | .insert i => (evalInsert db i, none)
  | .update u => (evalUpdate db u, none)
  | .delete d => (evalDelete db d, none)

end SqlEquiv
