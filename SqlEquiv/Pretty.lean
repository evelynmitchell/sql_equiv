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

/-- Escape single quotes in SQL strings by doubling them -/
def escapeSqlString (s : String) : String :=
  s.replace "'" "''"

def Value.toSql : Value → String
  | .int n    => toString n
  | .string s => s!"'{escapeSqlString s}'"
  | .bool b   => if b then "TRUE" else "FALSE"
  | .decimal u s =>
    -- u / 10^s with exactly s fractional digits: decimal 12345 2 → "123.45"
    if s == 0 then toString u
    else
      let sign := if u < 0 then "-" else ""
      let abs := u.natAbs
      let intPart := abs / 10 ^ s
      let fracPart := abs % 10 ^ s
      let fracStr := toString fracPart
      let padded := String.ofList (List.replicate (s - fracStr.length) '0') ++ fracStr
      s!"{sign}{intPart}.{padded}"
  | .null _   => "NULL"  -- All NULLs print as NULL regardless of type

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
  | .likeCI => "LIKE"

def UnaryOp.toSql : UnaryOp → String
  | .not       => "NOT"
  | .neg       => "-"
  | .isNull    => "IS NULL"
  | .isNotNull => "IS NOT NULL"

def AggFunc.toSql : AggFunc → String
  | .count => "COUNT"
  | .sum _ => "SUM"
  | .avg _ => "AVG"
  | .min _ => "MIN"
  | .max _ => "MAX"

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

/-- What the printer needs to know about its target dialect. `toSql` prints for the default
    (`standard`) dialect; `toSqlWith (PrintCfg.of d)` prints for `d`, and `Stmt.toSqlIn`
    (`SqlEquiv.PrettyDialect`) checks that the result parses back to the same choices (#267).
    - `nullOrdering`: NULLS FIRST/LAST is printed only where it differs from this rule.
    - `likeCase`: how the target reads `LIKE`. A case-insensitive `likeCI` printed for a
      case-sensitive target is spelled `LOWER(x) LIKE LOWER(p)` (our `LOWER`, like sqlite's,
      folds ASCII letters only, the letters `likeCI` folds).
    - `annotate`: also print, as `/*…*/` comments, the dialect choices recorded on aggregate
      and LIKE nodes that SQL cannot spell (MIN/MAX mode, SUM/AVG over booleans, LIKE case).
      Used to compare two ASTs' choices; not meant to be run. -/
structure PrintCfg where
  nullOrdering : NullOrdering
  likeCase : LikeCase
  annotate : Bool := false
  deriving Repr, Inhabited

/-- Print for dialect `d`. -/
def PrintCfg.of (d : Dialect) : PrintCfg :=
  { nullOrdering := d.config.nullOrdering, likeCase := d.config.likeCase }

private def MixedMinMax.tag : MixedMinMax → String
  | .error => "error" | .typeClass => "typeClass"

private def BoolMinMax.tag : BoolMinMax → String
  | .error => "error" | .asInt => "asInt" | .ordered => "ordered"

private def BoolSumAvg.tag : BoolSumAvg → String
  | .error => "error" | .asInt => "asInt"

/-- The annotation of a MIN/MAX mode. -/
def MinMaxMode.tag (m : MinMaxMode) : String :=
  s!"mixed={m.mixed.tag},bools={m.bools.tag},bareRow={m.bareRow}"

/-- The annotation of a SUM/AVG boolean rule. -/
def BoolSumAvg.annotation (b : BoolSumAvg) : String := s!"bools={b.tag}"

/-- An aggregate's name, with its dialect choices when annotating. -/
def AggFunc.toSqlWith (cfg : PrintCfg) (fn : AggFunc) : String :=
  let note (t : String) := if cfg.annotate then s!"/*{t}*/" else ""
  match fn with
  | .count => "COUNT"
  | .sum b => "SUM" ++ note b.annotation
  | .avg b => "AVG" ++ note b.annotation
  | .min m => "MIN" ++ note m.tag
  | .max m => "MAX" ++ note m.tag

-- ============================================================================
-- Expression Pretty Printing
-- ============================================================================

mutual

partial def Expr.toSqlWith (cfg : PrintCfg) : Expr → String
  | .lit v => v.toSql
  | .col c => c.toSql
  | .binOp .likeCI l r =>
    let note := if cfg.annotate then "/*ci*/" else ""
    match cfg.likeCase with
    | .asciiInsensitive => s!"({l.toSqlWith cfg} LIKE{note} {r.toSqlWith cfg})"
    -- A case-sensitive target: fold both sides explicitly (the `like` it re-parses as is
    -- printed with the case-sensitive note, so the annotated forms agree).
    | .sensitive =>
      let cs := if cfg.annotate then "/*cs*/" else ""
      s!"(LOWER({l.toSqlWith cfg}) LIKE{cs} LOWER({r.toSqlWith cfg}))"
  | .binOp .like l r =>
    let note := if cfg.annotate then "/*cs*/" else ""
    s!"({l.toSqlWith cfg} LIKE{note} {r.toSqlWith cfg})"
  | .binOp op l r => s!"({l.toSqlWith cfg} {op.toSql} {r.toSqlWith cfg})"
  | .unaryOp op e =>
    match op with
    | .isNull | .isNotNull => s!"({e.toSqlWith cfg} {op.toSql})"
    | _ => s!"({op.toSql} {e.toSqlWith cfg})"
  | .func name args =>
    let argStr := ", ".intercalate (args.map (Expr.toSqlWith cfg))
    s!"{name}({argStr})"
  | .agg fn arg distinct =>
    let distinctStr := if distinct then "DISTINCT " else ""
    match arg with
    | some e => s!"{fn.toSqlWith cfg}({distinctStr}{e.toSqlWith cfg})"
    | none => s!"{fn.toSqlWith cfg}({distinctStr}*)"  -- shouldn't happen normally
  | .countStar => "COUNT(*)"
  | .case branches else_ =>
    let branchStr := branches.map fun (cond, result) =>
      s!"WHEN {cond.toSqlWith cfg} THEN {result.toSqlWith cfg}"
    let elseStr := match else_ with
      | some e => s!" ELSE {e.toSqlWith cfg}"
      | none => ""
    s!"CASE {" ".intercalate branchStr}{elseStr} END"
  | .inList e neg vals =>
    let notStr := if neg then "NOT " else ""
    let valStr := ", ".intercalate (vals.map (Expr.toSqlWith cfg))
    s!"({e.toSqlWith cfg} {notStr}IN ({valStr}))"
  | .inSubquery e neg sel =>
    let notStr := if neg then "NOT " else ""
    s!"({e.toSqlWith cfg} {notStr}IN ({sel.toSqlWith cfg}))"
  | .exists neg sel =>
    let notStr := if neg then "NOT " else ""
    s!"({notStr}EXISTS ({sel.toSqlWith cfg}))"
  | .subquery sel =>
    s!"({sel.toSqlWith cfg})"
  | .between e lo hi =>
    s!"({e.toSqlWith cfg} BETWEEN {lo.toSqlWith cfg} AND {hi.toSqlWith cfg})"
  | .windowFn fn arg spec =>
    let note (t : String) := if cfg.annotate then s!"/*{t}*/" else ""
    let fnName := match fn with
      | .rowNumber => "ROW_NUMBER"
      | .rank => "RANK"
      | .denseRank => "DENSE_RANK"
      | .sum b => "SUM" ++ note b.annotation
      | .avg b => "AVG" ++ note b.annotation
      | .min m => "MIN" ++ note m.tag
      | .max m => "MAX" ++ note m.tag
      | .count => "COUNT"
    let argStr := match arg with
      | some e => e.toSqlWith cfg
      -- COUNT with no argument is COUNT(*) (the parser maps COUNT(*) OVER to
      -- windowFn .count none, #214); ranking functions take no argument.
      | none => if fn == WindowFunc.count then "*" else ""
    let partStr := if spec.partitionBy.isEmpty then ""
      else s!"PARTITION BY {", ".intercalate (spec.partitionBy.map (Expr.toSqlWith cfg))} "
    let orderStr := if spec.orderBy.isEmpty then ""
      else s!"ORDER BY {", ".intercalate (spec.orderBy.map (OrderByItem.toSqlWith cfg))}"
    s!"{fnName}({argStr}) OVER ({partStr}{orderStr})"

/-- Subquery body (#218): a SELECT or a set operation over subqueries.
    Mirrors Query.toSqlWith's compound printing. -/
partial def SubQuery.toSqlWith (cfg : PrintCfg) : SubQuery → String
  | .simple sel => sel.toSqlWith cfg
  | .compound l op r => s!"{l.toSqlWith cfg} {op.toSql} {r.toSqlWith cfg}"

-- ============================================================================
-- SELECT Components Pretty Printing
-- ============================================================================

partial def SelectItem.toSqlWith (cfg : PrintCfg) : SelectItem → String
  | .star none     => "*"
  | .star (some t) => s!"{t}.*"
  | .exprItem e none     => e.toSqlWith cfg
  | .exprItem e (some a) => s!"{e.toSqlWith cfg} AS {a}"

partial def TableRef.toSqlWith (_cfg : PrintCfg) (t : TableRef) : String :=
  match t.alias with
  | some a => s!"{t.name} AS {a}"
  | none   => t.name

partial def FromClause.toSqlWith (cfg : PrintCfg) : FromClause → String
  | .table t => t.toSqlWith cfg
  | .subquery sel alias => s!"({sel.toSqlWith cfg}) AS {alias}"
  | .join left jtype right on_ =>
    let onStr := match on_ with
      | some e => s!" ON {e.toSqlWith cfg}"
      | none   => ""
    s!"{left.toSqlWith cfg} {jtype.toSql} {right.toSqlWith cfg}{onStr}"

/-- Prints `NULLS FIRST/LAST` only when it differs from the target's rule
    (`cfg.nullOrdering`), so re-parsing in the target dialect gives back the same NULL
    positions whatever dialect the AST was parsed in. -/
partial def OrderByItem.toSqlWith (cfg : PrintCfg) (o : OrderByItem) : String :=
  let nullsStr :=
    if o.nulls == cfg.nullOrdering.resolve o.dir then ""
    else match o.nulls with
      | .first => " NULLS FIRST"
      | .last => " NULLS LAST"
  s!"{o.expr.toSqlWith cfg} {o.dir.toSql}{nullsStr}"

-- ============================================================================
-- Statement Pretty Printing
-- ============================================================================

partial def SelectStmt.toSqlWith (cfg : PrintCfg) (s : SelectStmt) : String :=
  let parts : List String := [
    "SELECT",
    if s.distinct then "DISTINCT" else "",
    ", ".intercalate (s.items.map (SelectItem.toSqlWith cfg)),
    match s.fromClause with
    | some f => s!"FROM {f.toSqlWith cfg}"
    | none => "",
    match s.whereClause with
    | some w => s!"WHERE {w.toSqlWith cfg}"
    | none => "",
    if s.groupBy.isEmpty then ""
    else s!"GROUP BY {", ".intercalate (s.groupBy.map (Expr.toSqlWith cfg))}",
    match s.having with
    | some h => s!"HAVING {h.toSqlWith cfg}"
    | none => "",
    if s.orderBy.isEmpty then ""
    else s!"ORDER BY {", ".intercalate (s.orderBy.map (OrderByItem.toSqlWith cfg))}",
    match s.limitVal with
    | some n => s!"LIMIT {n}"
    | none => "",
    match s.offsetVal with
    | some n => s!"OFFSET {n}"
    | none => ""
  ]
  " ".intercalate (parts.filter (· ≠ ""))

partial def Query.toSqlWith (cfg : PrintCfg) : Query → String
  | .simple sel => sel.toSqlWith cfg
  | .compound left op right => s!"{left.toSqlWith cfg} {op.toSql} {right.toSqlWith cfg}"
  | .withCTE ctes query =>
    let recursiveKw := if ctes.any (·.isRecursive) then "RECURSIVE " else ""
    let cteStrs := ctes.map fun cte => s!"{cte.name} AS ({cte.query.toSqlWith cfg})"
    s!"WITH {recursiveKw}{", ".intercalate cteStrs} {query.toSqlWith cfg}"
  | .ordered query ob lim off =>
    let parts := [query.toSqlWith cfg,
      if ob.isEmpty then "" else
        s!"ORDER BY {", ".intercalate (ob.map (OrderByItem.toSqlWith cfg))}",
      match lim with | some n => s!"LIMIT {n}" | none => "",
      match off with | some n => s!"OFFSET {n}" | none => ""]
    " ".intercalate (parts.filter (· ≠ ""))

end

def InsertStmt.toSqlWith (cfg : PrintCfg) (i : InsertStmt) : String :=
  let colStr := match i.columns with
    | some cols => s!" ({", ".intercalate cols})"
    | none => ""
  let sourceStr := match i.source with
    | .values rows =>
      let rowStrs := rows.map fun (row : List Expr) =>
        s!"({", ".intercalate (row.map (Expr.toSqlWith cfg))})"
      s!"VALUES {", ".intercalate rowStrs}"
    | .selectStmt sel => sel.toSqlWith cfg
  s!"INSERT INTO {i.table}{colStr} {sourceStr}"

def UpdateStmt.toSqlWith (cfg : PrintCfg) (u : UpdateStmt) : String :=
  let setStr := u.assignments.map fun a =>
    s!"{a.column} = {a.value.toSqlWith cfg}"
  let whereStr := match u.whereClause with
    | some w => s!" WHERE {w.toSqlWith cfg}"
    | none => ""
  s!"UPDATE {u.table} SET {", ".intercalate setStr}{whereStr}"

def DeleteStmt.toSqlWith (cfg : PrintCfg) (d : DeleteStmt) : String :=
  let whereStr := match d.whereClause with
    | some w => s!" WHERE {w.toSqlWith cfg}"
    | none => ""
  s!"DELETE FROM {d.table}{whereStr}"

def Stmt.toSqlWith (cfg : PrintCfg) : Stmt → String
  | .query q  => q.toSqlWith cfg
  | .insert i => i.toSqlWith cfg
  | .update u => u.toSqlWith cfg
  | .delete d => d.toSqlWith cfg

-- ============================================================================
-- Default-dialect printing
-- ============================================================================

/-- The default dialect's print configuration (`toSql` prints for it). -/
def PrintCfg.default : PrintCfg := PrintCfg.of defaultDialect

/-- SQL for the default (`standard`) dialect. Re-parsing it in the default dialect gives
    back the same NULL positions and LIKE case (a sqlite `likeCI` prints as
    `LOWER(x) LIKE LOWER(p)`). MIN/MAX modes and SUM/AVG boolean rules have no SQL
    spelling; `Stmt.toSqlIn` refuses when they would not survive. -/
def Expr.toSql (e : Expr) : String := e.toSqlWith PrintCfg.default
def SubQuery.toSql (s : SubQuery) : String := s.toSqlWith PrintCfg.default
def SelectItem.toSql (s : SelectItem) : String := s.toSqlWith PrintCfg.default
def TableRef.toSql (t : TableRef) : String := t.toSqlWith PrintCfg.default
def FromClause.toSql (f : FromClause) : String := f.toSqlWith PrintCfg.default
def OrderByItem.toSql (o : OrderByItem) : String := o.toSqlWith PrintCfg.default
def SelectStmt.toSql (s : SelectStmt) : String := s.toSqlWith PrintCfg.default
def Query.toSql (q : Query) : String := q.toSqlWith PrintCfg.default
def InsertStmt.toSql (i : InsertStmt) : String := i.toSqlWith PrintCfg.default
def UpdateStmt.toSql (u : UpdateStmt) : String := u.toSqlWith PrintCfg.default
def DeleteStmt.toSql (d : DeleteStmt) : String := d.toSqlWith PrintCfg.default
def Stmt.toSql (s : Stmt) : String := s.toSqlWith PrintCfg.default

end SqlEquiv
