/-
  Pretty Printer: AST → SQL String

  Converts AST back to SQL text for debugging and round-trip testing.
  Extended for Spider benchmark compatibility.
-/
import SqlEquiv.Ast

namespace SqlEquiv

-- ============================================================================
-- Helper Functions
-- ============================================================================

def Value.toSql : Value → String
  | .int n    => toString n
  | .string s => s!"'{s}'"  -- TODO: escape quotes
  | .bool b   => if b then "TRUE" else "FALSE"
  | .null     => "NULL"

def ColumnRef.toSql (c : ColumnRef) : String :=
  match c.table with
  | some t => s!"{t}.{c.column}"
  | none   => c.column

def BinOp.toSql : BinOp → String
  | .add    => "+"
  | .sub    => "-"
  | .mul    => "*"
  | .div    => "/"
  | .mod    => "%"
  | .eq     => "="
  | .ne     => "<>"
  | .lt     => "<"
  | .le     => "<="
  | .gt     => ">"
  | .ge     => ">="
  | .and    => "AND"
  | .or     => "OR"
  | .concat => "||"
  | .like   => "LIKE"

def UnaryOp.toSql : UnaryOp → String
  | .not       => "NOT"
  | .neg       => "-"
  | .isNull    => "IS NULL"
  | .isNotNull => "IS NOT NULL"

def AggFunc.toSql : AggFunc → String
  | .count => "COUNT"
  | .sum   => "SUM"
  | .avg   => "AVG"
  | .min   => "MIN"
  | .max   => "MAX"

def JoinType.toSql : JoinType → String
  | .inner => "INNER JOIN"
  | .left  => "LEFT JOIN"
  | .right => "RIGHT JOIN"
  | .full  => "FULL JOIN"
  | .cross => "CROSS JOIN"

def OrderDir.toSql : OrderDir → String
  | .asc  => "ASC"
  | .desc => "DESC"

def SetOp.toSql : SetOp → String
  | .union     => "UNION"
  | .unionAll  => "UNION ALL"
  | .intersect => "INTERSECT"
  | .exceptOp  => "EXCEPT"

-- ============================================================================
-- Expression Pretty Printing
-- ============================================================================

mutual

partial def Expr.toSql : Expr → String
  | .lit v => v.toSql
  | .col c => c.toSql
  | .binOp op l r => s!"({l.toSql} {op.toSql} {r.toSql})"
  | .unaryOp op e =>
    match op with
    | .isNull | .isNotNull => s!"({e.toSql} {op.toSql})"
    | _ => s!"({op.toSql} {e.toSql})"
  | .func name args =>
    let argStr := ", ".intercalate (args.map Expr.toSql)
    s!"{name}({argStr})"
  | .agg fn arg distinct =>
    let distinctStr := if distinct then "DISTINCT " else ""
    match arg with
    | some e => s!"{fn.toSql}({distinctStr}{e.toSql})"
    | none => s!"{fn.toSql}({distinctStr}*)"  -- shouldn't happen normally
  | .countStar => "COUNT(*)"
  | .case branches else_ =>
    let branchStr := branches.map fun (cond, result) =>
      s!"WHEN {cond.toSql} THEN {result.toSql}"
    let elseStr := match else_ with
      | some e => s!" ELSE {e.toSql}"
      | none => ""
    s!"CASE {" ".intercalate branchStr}{elseStr} END"
  | .inList e neg vals =>
    let notStr := if neg then "NOT " else ""
    let valStr := ", ".intercalate (vals.map Expr.toSql)
    s!"({e.toSql} {notStr}IN ({valStr}))"
  | .inSubquery e neg sel =>
    let notStr := if neg then "NOT " else ""
    s!"({e.toSql} {notStr}IN ({sel.toSql}))"
  | .exists neg sel =>
    let notStr := if neg then "NOT " else ""
    s!"({notStr}EXISTS ({sel.toSql}))"
  | .subquery sel =>
    s!"({sel.toSql})"
  | .between e lo hi =>
    s!"({e.toSql} BETWEEN {lo.toSql} AND {hi.toSql})"
  | .windowFn fn arg spec =>
    let fnName := match fn with
      | .rowNumber => "ROW_NUMBER"
      | .rank => "RANK"
      | .denseRank => "DENSE_RANK"
      | .sum => "SUM"
      | .avg => "AVG"
      | .min => "MIN"
      | .max => "MAX"
      | .count => "COUNT"
    let argStr := match arg with
      | some e => e.toSql
      | none => ""
    let partStr := if spec.partitionBy.isEmpty then ""
      else s!"PARTITION BY {", ".intercalate (spec.partitionBy.map Expr.toSql)} "
    let orderStr := if spec.orderBy.isEmpty then ""
      else s!"ORDER BY {", ".intercalate (spec.orderBy.map OrderByItem.toSql)}"
    s!"{fnName}({argStr}) OVER ({partStr}{orderStr})"

-- ============================================================================
-- SELECT Components Pretty Printing
-- ============================================================================

partial def SelectItem.toSql : SelectItem → String
  | .star none     => "*"
  | .star (some t) => s!"{t}.*"
  | .exprItem e none     => e.toSql
  | .exprItem e (some a) => s!"{e.toSql} AS {a}"

partial def TableRef.toSql (t : TableRef) : String :=
  match t.alias with
  | some a => s!"{t.name} AS {a}"
  | none   => t.name

partial def FromClause.toSql : FromClause → String
  | .table t => t.toSql
  | .subquery sel alias => s!"({sel.toSql}) AS {alias}"
  | .join left jtype right on_ =>
    let onStr := match on_ with
      | some e => s!" ON {e.toSql}"
      | none   => ""
    s!"{left.toSql} {jtype.toSql} {right.toSql}{onStr}"

partial def OrderByItem.toSql (o : OrderByItem) : String :=
  s!"{o.expr.toSql} {o.dir.toSql}"

-- ============================================================================
-- Statement Pretty Printing
-- ============================================================================

partial def SelectStmt.toSql (s : SelectStmt) : String :=
  let parts : List String := [
    "SELECT",
    if s.distinct then "DISTINCT" else "",
    ", ".intercalate (s.items.map SelectItem.toSql),
    match s.fromClause with
    | some f => s!"FROM {f.toSql}"
    | none => "",
    match s.whereClause with
    | some w => s!"WHERE {w.toSql}"
    | none => "",
    if s.groupBy.isEmpty then ""
    else s!"GROUP BY {", ".intercalate (s.groupBy.map Expr.toSql)}",
    match s.having with
    | some h => s!"HAVING {h.toSql}"
    | none => "",
    if s.orderBy.isEmpty then ""
    else s!"ORDER BY {", ".intercalate (s.orderBy.map OrderByItem.toSql)}",
    match s.limitVal with
    | some n => s!"LIMIT {n}"
    | none => "",
    match s.offsetVal with
    | some n => s!"OFFSET {n}"
    | none => ""
  ]
  " ".intercalate (parts.filter (· ≠ ""))

partial def Query.toSql : Query → String
  | .simple sel => sel.toSql
  | .compound left op right => s!"{left.toSql} {op.toSql} {right.toSql}"
  | .withCTE ctes query =>
    let cteStrs := ctes.map fun cte => s!"{cte.name} AS ({cte.query.toSql})"
    s!"WITH {", ".intercalate cteStrs} {query.toSql}"

end

def InsertStmt.toSql (i : InsertStmt) : String :=
  let colStr := match i.columns with
    | some cols => s!" ({", ".intercalate cols})"
    | none => ""
  let sourceStr := match i.source with
    | .values rows =>
      let rowStrs := rows.map fun (row : List Expr) =>
        s!"({", ".intercalate (row.map Expr.toSql)})"
      s!"VALUES {", ".intercalate rowStrs}"
    | .selectStmt sel => sel.toSql
  s!"INSERT INTO {i.table}{colStr} {sourceStr}"

def UpdateStmt.toSql (u : UpdateStmt) : String :=
  let setStr := u.assignments.map fun a =>
    s!"{a.column} = {a.value.toSql}"
  let whereStr := match u.whereClause with
    | some w => s!" WHERE {w.toSql}"
    | none => ""
  s!"UPDATE {u.table} SET {", ".intercalate setStr}{whereStr}"

def DeleteStmt.toSql (d : DeleteStmt) : String :=
  let whereStr := match d.whereClause with
    | some w => s!" WHERE {w.toSql}"
    | none => ""
  s!"DELETE FROM {d.table}{whereStr}"

def Stmt.toSql : Stmt → String
  | .query q  => q.toSql
  | .insert i => i.toSql
  | .update u => u.toSql
  | .delete d => d.toSql

end SqlEquiv
