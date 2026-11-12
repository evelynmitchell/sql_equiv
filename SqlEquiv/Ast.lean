/-
  SQL Abstract Syntax Tree

  This module defines the core types for representing SQL statements.
  Built bottom-up: literals → expressions → clauses → statements
  Extended for Spider benchmark compatibility: subqueries, aggregates, set operations
-/

namespace SqlEquiv

-- ============================================================================
-- SQL Type System
-- ============================================================================

/-- SQL data types for typed NULLs and type checking -/
inductive SqlType where
  | int
  | string
  | bool
  | decimal  -- NUMERIC/DECIMAL: exact scaled-integer arithmetic (#201)
  | unknown  -- for untyped NULL or expressions with indeterminate type
  deriving Repr, BEq, Inhabited, DecidableEq, ReflBEq, LawfulBEq

-- ============================================================================
-- Three-Valued Logic (Trilean)
-- ============================================================================

/-- SQL's three-valued logic: TRUE, FALSE, UNKNOWN
    UNKNOWN represents NULL in boolean context -/
inductive Trilean where
  | true
  | false
  | unknown
  deriving Repr, BEq, Inhabited, DecidableEq

namespace Trilean

/-- NOT in three-valued logic -/
def not : Trilean → Trilean
  | .true => .false
  | .false => .true
  | .unknown => .unknown

/-- AND in three-valued logic (truth table):
    T ∧ T = T, T ∧ F = F, T ∧ U = U
    F ∧ T = F, F ∧ F = F, F ∧ U = F  (FALSE dominates UNKNOWN)
    U ∧ T = U, U ∧ F = F, U ∧ U = U -/
def and : Trilean → Trilean → Trilean
  | .false, _ => .false
  | _, .false => .false
  | .true, .true => .true
  | .true, .unknown => .unknown
  | .unknown, .true => .unknown
  | .unknown, .unknown => .unknown

/-- OR in three-valued logic (truth table):
    T ∨ T = T, T ∨ F = T, T ∨ U = T  (TRUE dominates UNKNOWN)
    F ∨ T = T, F ∨ F = F, F ∨ U = U
    U ∨ T = T, U ∨ F = U, U ∨ U = U -/
def or : Trilean → Trilean → Trilean
  | .true, _ => .true
  | _, .true => .true
  | .false, .false => .false
  | .false, .unknown => .unknown
  | .unknown, .false => .unknown
  | .unknown, .unknown => .unknown

/-- Convert Bool to Trilean -/
def ofBool : Bool → Trilean
  | Bool.true => .true
  | Bool.false => .false

/-- Convert Trilean to Bool (UNKNOWN → false, as in WHERE clause) -/
def toBool : Trilean → Bool
  | .true => Bool.true
  | .false => Bool.false
  | .unknown => Bool.false

/-- Check if Trilean is definitely true -/
def isTrue : Trilean → Bool
  | .true => Bool.true
  | _ => Bool.false

/-- Check if Trilean is definitely false -/
def isFalse : Trilean → Bool
  | .false => Bool.true
  | _ => Bool.false

/-- Check if Trilean is unknown -/
def isUnknown : Trilean → Bool
  | .unknown => Bool.true
  | _ => Bool.false

end Trilean

-- ============================================================================
-- Value Types
-- ============================================================================

/-- SQL value literals with typed NULLs -/
inductive Value where
  | int    : Int → Value
  | string : String → Value
  | bool   : Bool → Value
  /-- NUMERIC/DECIMAL as exact scaled integer: `decimal u s` denotes u / 10^s
      (e.g. `decimal 12345 2` = 123.45). Construct via `Value.mkDecimal` to
      keep values in canonical form (no trailing zeros: 1.10 is stored as
      `decimal 11 1`, never `decimal 110 2`), so structural BEq (DISTINCT,
      GROUP BY) agrees with numeric equality. -/
  | decimal : Int → Nat → Value
  | null   : Option SqlType → Value  -- typed NULL (none = unknown type)
  deriving Repr, BEq, Inhabited, DecidableEq, ReflBEq, LawfulBEq

namespace Value

/-- Get the SQL type of a value -/
def sqlType : Value → SqlType
  | .int _ => .int
  | .string _ => .string
  | .bool _ => .bool
  | .decimal _ _ => .decimal
  | .null (some t) => t
  | .null none => .unknown

/-- Canonical decimal constructor: strips trailing zeros so numerically equal
    decimals are structurally equal (`mkDecimal 110 2 = mkDecimal 11 1`).
    A whole number normalizes to scale 0 but stays `.decimal` (1.0 → decimal
    1 0), preserving the value's declared type. -/
def mkDecimal (u : Int) (s : Nat) : Value :=
  match s with
  | 0 => .decimal u 0
  | s' + 1 => if u % 10 == 0 then mkDecimal (u / 10) s' else .decimal u (s' + 1)

/-- Check if value is NULL (any type) -/
def isNull : Value → Bool
  | .null _ => true
  | _ => false

/-- Check if value is not NULL -/
def isNotNull : Value → Bool
  | .null _ => false
  | _ => true

/-- Create typed NULL values -/
def nullInt : Value := .null (some .int)
def nullString : Value := .null (some .string)
def nullBool : Value := .null (some .bool)
def nullDecimal : Value := .null (some .decimal)
def nullUntyped : Value := .null none

/-- Convert boolean value to Trilean -/
def toTrilean : Value → Trilean
  | .bool true => .true
  | .bool false => .false
  | .null _ => .unknown
  | _ => .unknown  -- non-boolean treated as unknown in boolean context

/-- Convert Trilean back to Value -/
def ofTrilean : Trilean → Value
  | .true => .bool true
  | .false => .bool false
  | .unknown => .null none

end Value

/-- Convert Trilean to Option Value (for bridge theorems) -/
def Trilean.toOptionValue (t : Trilean) : Option Value :=
  some (Value.ofTrilean t)

/-- Column reference: optionally qualified with table name -/
structure ColumnRef where
  table  : Option String
  column : String
  deriving Repr, BEq, Inhabited, DecidableEq

-- ============================================================================
-- Operators
-- ============================================================================

/-- Binary operators -/
inductive BinOp where
  -- Arithmetic
  | add | sub | mul | div | mod
  -- Comparison
  | eq | ne | lt | le | gt | ge
  -- Logical
  | and | or
  -- String
  | concat
  | like
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Unary operators -/
inductive UnaryOp where
  | not
  | neg
  | isNull
  | isNotNull
  deriving Repr, BEq, Inhabited, DecidableEq

/-- How MIN/MAX treat input that mixes numbers and strings. Implementation-
    defined (docs/IMPLEMENTATION_DEFINED.md, row 13); chosen by the dialect at
    parse time and recorded on each MIN/MAX node.
    - `error`: the aggregate is an error (standard, DuckDB, Postgres).
    - `typeClass`: numbers order before strings, so MAX is the greatest string
      and MIN the least number (sqlite). -/
inductive MixedMinMax where
  | error
  | typeClass
  deriving Repr, BEq, Inhabited, DecidableEq

/-- How MIN/MAX treat boolean inputs. Implementation-defined
    (docs/IMPLEMENTATION_DEFINED.md, row 14); chosen by the dialect at parse
    time.
    - `error`: booleans are not orderable by MIN/MAX (standard, Postgres:
      `max(boolean)` does not exist); any boolean input is an error.
    - `asInt`: booleans are the integers 1/0 (sqlite).
    - `ordered`: booleans only → false < true, result is a boolean; with
      numbers they act as 1/0 (DuckDB). -/
inductive BoolMinMax where
  | error
  | asInt
  | ordered
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The dialect choices a MIN/MAX node records. -/
structure MinMaxMode where
  mixed : MixedMinMax
  bools : BoolMinMax
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Aggregate functions (MIN/MAX carry the dialect's mixed-type mode) -/
inductive AggFunc where
  | count
  | sum
  | avg
  | min (mode : MinMaxMode)
  | max (mode : MinMaxMode)
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Table reference with optional alias -/
structure TableRef where
  name  : String
  alias : Option String
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Join types -/
inductive JoinType where
  | inner
  | left
  | right
  | full
  | cross
  deriving Repr, BEq, Inhabited, DecidableEq

/-- ORDER BY direction -/
inductive OrderDir where
  | asc
  | desc
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Position of NULL sort keys in an ORDER BY item (`NULLS FIRST` / `NULLS LAST`).
    Absolute: independent of the sort direction. -/
inductive NullsOrder where
  | first
  | last
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Engine-wide rule for where NULLs sort when a query doesn't say `NULLS
    FIRST/LAST`. The SQL standard leaves this to the implementation.
    - `nullsSmallest`: NULL sorts below every value (sqlite, MySQL, SQL Server):
      ASC → NULLS FIRST, DESC → NULLS LAST.
    - `nullsLargest`: NULL sorts above every value (PostgreSQL, Oracle):
      ASC → NULLS LAST, DESC → NULLS FIRST.
    - `nullsAlwaysLast`: DuckDB's default: NULLS LAST in both directions. -/
inductive NullOrdering where
  | nullsSmallest
  | nullsLargest
  | nullsAlwaysLast
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The explicit NULL position a `NullOrdering` assigns to a sort direction. -/
def NullOrdering.resolve : NullOrdering → OrderDir → NullsOrder
  | .nullsSmallest, .asc => .first
  | .nullsSmallest, .desc => .last
  | .nullsLargest, .asc => .last
  | .nullsLargest, .desc => .first
  | .nullsAlwaysLast, _ => .last

/-- The database engine whose implementation-defined behaviour a query is
    checked against (docs/IMPLEMENTATION_DEFINED.md). Resolved at parse time:
    the parser writes each choice into the AST (e.g. the NULL position of every
    ORDER BY item, the mixed-type mode of every MIN/MAX), so evaluation and
    proofs never depend on the dialect, and every equivalence theorem holds for
    every dialect.
    - `standard`: the SQL standard; where it says error, we error. Where it
      leaves a choice to the implementation, see `Dialect.config`.
    - `sqlite`, `duckdb`, `postgres`: that engine's behaviour, as observed and
      recorded in the registry. -/
inductive Dialect where
  | standard
  | sqlite
  | duckdb
  | postgres
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The per-behaviour choices of a dialect (one field per configurable row of
    the implementation-defined registry). -/
structure DialectConfig where
  /-- Where NULLs sort when an ORDER BY item has no NULLS FIRST/LAST (row 1) -/
  nullOrdering : NullOrdering
  /-- MIN/MAX over mixed numbers and strings (row 13) -/
  mixedMinMax : MixedMinMax
  /-- MIN/MAX over booleans (row 14) -/
  boolMinMax : BoolMinMax
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Each dialect's choices. `standard` has to pick a NULL position (the standard
    leaves it to the implementation): it takes NULL-largest, the rule of the
    Postgres standards tiebreaker. -/
def Dialect.config : Dialect → DialectConfig
  | .standard => { nullOrdering := .nullsLargest,    mixedMinMax := .error,     boolMinMax := .error }
  | .sqlite   => { nullOrdering := .nullsSmallest,   mixedMinMax := .typeClass, boolMinMax := .asInt }
  | .duckdb   => { nullOrdering := .nullsAlwaysLast, mixedMinMax := .error,     boolMinMax := .ordered }
  | .postgres => { nullOrdering := .nullsLargest,    mixedMinMax := .error,     boolMinMax := .error }

/-- The MIN/MAX mode a dialect configuration records on each MIN/MAX node. -/
def DialectConfig.minMaxMode (c : DialectConfig) : MinMaxMode :=
  { mixed := c.mixedMinMax, bools := c.boolMinMax }

/-- Parse a dialect name (case-insensitive): standard, sqlite, duckdb, postgres
    (or postgresql). -/
def Dialect.ofString? (s : String) : Option Dialect :=
  match s.toLower with
  | "standard" => some .standard
  | "sqlite" => some .sqlite
  | "duckdb" => some .duckdb
  | "postgres" | "postgresql" => some .postgres
  | _ => none

/-- The dialect used when none is given. -/
def defaultDialect : Dialect := .standard

/-- The default dialect's NULL rule. Each ORDER BY item carries an explicit
    `NullsOrder`, so evaluation and proofs never depend on this choice; the
    pretty-printer omits NULLS FIRST/LAST when an item matches it. -/
def defaultNullOrdering : NullOrdering := defaultDialect.config.nullOrdering

/-- Set operations -/
inductive SetOp where
  | union
  | unionAll
  | intersect
  | exceptOp  -- 'except' is reserved in Lean
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Window function types -/
inductive WindowFunc where
  | rowNumber
  | rank
  | denseRank
  | sum
  | avg
  | min (mode : MinMaxMode)
  | max (mode : MinMaxMode)
  | count
  deriving Repr, BEq, Inhabited, DecidableEq

-- ============================================================================
-- Core Types (mutually recursive for subquery support)
-- ============================================================================

mutual

/-- Window frame specification -/
inductive WindowSpec where
  | mk : List Expr →        -- partitionBy
         List OrderByItem → -- orderBy
         WindowSpec

/-- SQL expression AST -/
inductive Expr where
  | lit       : Value → Expr
  | col       : ColumnRef → Expr
  | binOp     : BinOp → Expr → Expr → Expr
  | unaryOp   : UnaryOp → Expr → Expr
  | func      : String → List Expr → Expr              -- scalar function call
  | agg       : AggFunc → Option Expr → Bool → Expr    -- aggregate(expr, distinct?)
  | countStar : Expr                                    -- COUNT(*)
  | «case»    : List (Expr × Expr) → Option Expr → Expr
  | inList    : Expr → Bool → List Expr → Expr         -- expr [NOT] IN (values)
  | inSubquery : Expr → Bool → SubQuery → Expr         -- expr [NOT] IN (subquery)
  | exists    : Bool → SubQuery → Expr                 -- [NOT] EXISTS (subquery)
  | subquery  : SubQuery → Expr                        -- scalar subquery
  | between   : Expr → Expr → Expr → Expr
  | windowFn  : WindowFunc → Option Expr → WindowSpec → Expr  -- window function with OVER clause

/-- ORDER BY item -/
inductive OrderByItem where
  | mk : Expr → OrderDir → NullsOrder → OrderByItem

/-- SELECT item: an expression with optional alias, or * -/
inductive SelectItem where
  | star      : Option String → SelectItem           -- * or table.*
  | exprItem  : Expr → Option String → SelectItem    -- expr AS alias

/-- FROM clause source: can be a table, join, or subquery -/
inductive FromClause where
  | table     : TableRef → FromClause
  | subquery  : SubQuery → String → FromClause       -- (SELECT ...) AS alias
  | join      : FromClause → JoinType → FromClause → Option Expr → FromClause

/-- Subquery body: a SELECT or a set operation over subqueries (#218).
    CTEs are deliberately not permitted inside subqueries — `Query.withCTE`
    remains top-level only (Option B of the design on issue #218). -/
inductive SubQuery where
  | simple   : SelectStmt → SubQuery
  | compound : SubQuery → SetOp → SubQuery → SubQuery

/-- Full SELECT statement -/
inductive SelectStmt where
  | mk : Bool →                    -- distinct
         List SelectItem →         -- items
         Option FromClause →       -- fromClause
         Option Expr →             -- whereClause
         List Expr →               -- groupBy
         Option Expr →             -- having
         List OrderByItem →        -- orderBy
         Option Nat →              -- limitVal
         Option Nat →              -- offsetVal
         SelectStmt

end

-- Accessor functions for SelectStmt
def SelectStmt.distinct : SelectStmt → Bool
  | .mk d _ _ _ _ _ _ _ _ => d

def SelectStmt.items : SelectStmt → List SelectItem
  | .mk _ i _ _ _ _ _ _ _ => i

def SelectStmt.fromClause : SelectStmt → Option FromClause
  | .mk _ _ f _ _ _ _ _ _ => f

def SelectStmt.whereClause : SelectStmt → Option Expr
  | .mk _ _ _ w _ _ _ _ _ => w

def SelectStmt.groupBy : SelectStmt → List Expr
  | .mk _ _ _ _ g _ _ _ _ => g

def SelectStmt.having : SelectStmt → Option Expr
  | .mk _ _ _ _ _ h _ _ _ => h

def SelectStmt.orderBy : SelectStmt → List OrderByItem
  | .mk _ _ _ _ _ _ o _ _ => o

def SelectStmt.limitVal : SelectStmt → Option Nat
  | .mk _ _ _ _ _ _ _ l _ => l

def SelectStmt.offsetVal : SelectStmt → Option Nat
  | .mk _ _ _ _ _ _ _ _ o => o

-- Accessor functions for OrderByItem
def OrderByItem.expr : OrderByItem → Expr
  | .mk e _ _ => e

def OrderByItem.dir : OrderByItem → OrderDir
  | .mk _ d _ => d

def OrderByItem.nulls : OrderByItem → NullsOrder
  | .mk _ _ n => n

/-- ORDER BY item with the NULL position chosen by a `NullOrdering`
    (default: the default dialect's rule). -/
def OrderByItem.ofDir (e : Expr) (d : OrderDir)
    (ordering : NullOrdering := defaultNullOrdering) : OrderByItem :=
  .mk e d (ordering.resolve d)

-- Accessor functions for WindowSpec
def WindowSpec.partitionBy : WindowSpec → List Expr
  | .mk p _ => p

def WindowSpec.orderBy : WindowSpec → List OrderByItem
  | .mk _ o => o

-- Note: CTEDef and Query are mutually recursive
mutual
/-- Common Table Expression definition: name, query, and recursion flag -/
inductive CTEDef where
  | mk : (name : String) → (query : Query) → (isRecursive : Bool := false) → CTEDef

/-- Query with optional set operations -/
inductive Query where
  | simple : SelectStmt → Query
  | compound : Query → SetOp → Query → Query
  | withCTE : List CTEDef → Query → Query  -- WITH cte1 AS (...), cte2 AS (...) query
end

-- Accessor functions for CTEDef
def CTEDef.name : CTEDef → String
  | .mk n _ _ => n

def CTEDef.query : CTEDef → Query
  | .mk _ q _ => q

def CTEDef.isRecursive : CTEDef → Bool
  | .mk _ _ r => r

/-- Values source for INSERT -/
inductive InsertSource where
  | values : List (List Expr) → InsertSource  -- multiple rows
  | selectStmt : SelectStmt → InsertSource

/-- Column assignment: column = expr -/
structure Assignment where
  column : String
  value  : Expr

/-- INSERT statement -/
structure InsertStmt where
  table   : String
  columns : Option (List String)  -- None means all columns
  source  : InsertSource

/-- UPDATE statement -/
structure UpdateStmt where
  table       : String
  assignments : List Assignment
  whereClause : Option Expr

/-- DELETE statement -/
structure DeleteStmt where
  table  : String
  whereClause : Option Expr

/-- Any SQL DML statement -/
inductive Stmt where
  | query  : Query → Stmt
  | insert : InsertStmt → Stmt
  | update : UpdateStmt → Stmt
  | delete : DeleteStmt → Stmt

-- ============================================================================
-- ToString instances (simpler than Repr for debugging)
-- ============================================================================

mutual
  partial def Expr.toReprStr : Expr → String
    | .lit v => s!"Expr.lit {repr v}"
    | .col c => s!"Expr.col {repr c}"
    | .binOp op l r => s!"Expr.binOp {repr op} ({l.toReprStr}) ({r.toReprStr})"
    | .unaryOp op e => s!"Expr.unaryOp {repr op} ({e.toReprStr})"
    | .func name args => s!"Expr.func {repr name} [{", ".intercalate (args.map Expr.toReprStr)}]"
    | .agg fn e dist => s!"Expr.agg {repr fn} {e.map Expr.toReprStr} {dist}"
    | .countStar => "Expr.countStar"
    | .case branches else_ =>
      let brStr := branches.map fun (c, r) => s!"({c.toReprStr}, {r.toReprStr})"
      s!"Expr.case [{", ".intercalate brStr}] {else_.map Expr.toReprStr}"
    | .inList e neg vals => s!"Expr.inList ({e.toReprStr}) {neg} [{", ".intercalate (vals.map Expr.toReprStr)}]"
    | .inSubquery e neg sel => s!"Expr.inSubquery ({e.toReprStr}) {neg} ({sel.toReprStr})"
    | .exists neg sel => s!"Expr.exists {neg} ({sel.toReprStr})"
    | .subquery sel => s!"Expr.subquery ({sel.toReprStr})"
    | .between e lo hi => s!"Expr.between ({e.toReprStr}) ({lo.toReprStr}) ({hi.toReprStr})"
    | .windowFn fn arg spec => s!"Expr.windowFn {repr fn} {arg.map Expr.toReprStr} ({WindowSpec.toReprStr spec})"

  partial def SubQuery.toReprStr : SubQuery → String
    | .simple sel => s!"SubQuery.simple ({sel.toReprStr})"
    | .compound l op r => s!"SubQuery.compound ({l.toReprStr}) {repr op} ({r.toReprStr})"

  partial def WindowSpec.toReprStr : WindowSpec → String
    | .mk partBy orderBy =>
      s!"WindowSpec.mk [{", ".intercalate (partBy.map Expr.toReprStr)}] [{", ".intercalate (orderBy.map OrderByItem.toReprStr)}]"

  partial def SelectItem.toReprStr : SelectItem → String
    | .star t => s!"SelectItem.star {repr t}"
    | .exprItem e a => s!"SelectItem.exprItem ({Expr.toReprStr e}) {repr a}"

  partial def FromClause.toReprStr : FromClause → String
    | .table t => s!"FromClause.table {repr t}"
    | .subquery sel alias => s!"FromClause.subquery ({sel.toReprStr}) {repr alias}"
    | .join l jt r on_ =>
      s!"FromClause.join ({FromClause.toReprStr l}) {repr jt} ({FromClause.toReprStr r}) {on_.map Expr.toReprStr}"

  partial def OrderByItem.toReprStr : OrderByItem → String
    | .mk e d n => s!"OrderByItem.mk ({Expr.toReprStr e}) {repr d} {repr n}"

  partial def SelectStmt.toReprStr : SelectStmt → String
    | .mk d items f w g h o l off =>
      s!"SelectStmt.mk {d} [{", ".intercalate (items.map SelectItem.toReprStr)}] {f.map FromClause.toReprStr} {w.map Expr.toReprStr} [{", ".intercalate (g.map Expr.toReprStr)}] {h.map Expr.toReprStr} [{", ".intercalate (o.map OrderByItem.toReprStr)}] {l} {off}"

  partial def Query.toReprStr : Query → String
    | .simple sel => s!"Query.simple ({sel.toReprStr})"
    | .compound l op r => s!"Query.compound ({l.toReprStr}) {repr op} ({r.toReprStr})"
    | .withCTE ctes q =>
      let cteStrs := ctes.map fun cte => s!"CTEDef.mk {repr cte.name} ({Query.toReprStr cte.query}) {cte.isRecursive}"
      s!"Query.withCTE [{", ".intercalate cteStrs}] ({q.toReprStr})"

  partial def InsertSource.toReprStr : InsertSource → String
    | .values rows =>
      let rowStrs := rows.map fun row => s!"[{", ".intercalate (row.map Expr.toReprStr)}]"
      s!"InsertSource.values [{", ".intercalate rowStrs}]"
    | .selectStmt sel => s!"InsertSource.selectStmt ({SelectStmt.toReprStr sel})"

  partial def Assignment.toReprStr : Assignment → String
    | ⟨c, v⟩ => s!"Assignment.mk {repr c} ({Expr.toReprStr v})"
end

instance : Repr Expr where reprPrec e _ := e.toReprStr
instance : Repr WindowSpec where reprPrec s _ := s.toReprStr
instance : Repr SelectItem where reprPrec i _ := i.toReprStr
instance : Repr FromClause where reprPrec f _ := f.toReprStr
instance : Repr OrderByItem where reprPrec o _ := o.toReprStr
instance : Repr SelectStmt where reprPrec s _ := s.toReprStr
instance : Repr Query where reprPrec q _ := q.toReprStr
instance : Repr InsertSource where reprPrec s _ := s.toReprStr
instance : Repr Assignment where reprPrec a _ := a.toReprStr

instance : Repr InsertStmt where
  reprPrec i _ := s!"InsertStmt.mk {repr i.table} {repr i.columns} ({InsertSource.toReprStr i.source})"

instance : Repr UpdateStmt where
  reprPrec u _ := s!"UpdateStmt.mk {repr u.table} [{", ".intercalate (u.assignments.map Assignment.toReprStr)}] {u.whereClause.map Expr.toReprStr}"

instance : Repr DeleteStmt where
  reprPrec d _ := s!"DeleteStmt.mk {repr d.table} {d.whereClause.map Expr.toReprStr}"

instance : Repr Stmt where
  reprPrec s _ := match s with
    | .query q => s!"Stmt.query ({Query.toReprStr q})"
    | .insert ins => s!"Stmt.insert ({repr ins})"
    | .update upd => s!"Stmt.update ({repr upd})"
    | .delete del => s!"Stmt.delete ({repr del})"

-- CTEDef instances (defined after SelectStmt toReprStr is available)
instance : Repr CTEDef where
  reprPrec cte _ := s!"CTEDef.mk {repr cte.name} ({Query.toReprStr cte.query}) {cte.isRecursive}"

-- ============================================================================
-- BEq instances
-- ============================================================================

mutual
  partial def Expr.beq : Expr → Expr → Bool
    | .lit v1, .lit v2 => v1 == v2
    | .col c1, .col c2 => c1 == c2
    | .binOp op1 l1 r1, .binOp op2 l2 r2 => op1 == op2 && Expr.beq l1 l2 && Expr.beq r1 r2
    | .unaryOp op1 e1, .unaryOp op2 e2 => op1 == op2 && Expr.beq e1 e2
    | .func n1 a1, .func n2 a2 => n1 == n2 && a1.length == a2.length && (a1.zip a2).all (fun (x, y) => Expr.beq x y)
    | .agg f1 e1 d1, .agg f2 e2 d2 =>
      f1 == f2 && d1 == d2 &&
      match e1, e2 with
      | none, none => true
      | some x, some y => Expr.beq x y
      | _, _ => false
    | .countStar, .countStar => true
    | .case b1 e1, .case b2 e2 =>
      b1.length == b2.length &&
      (b1.zip b2).all (fun ((c1, r1), (c2, r2)) => Expr.beq c1 c2 && Expr.beq r1 r2) &&
      match e1, e2 with
      | none, none => true
      | some x, some y => Expr.beq x y
      | _, _ => false
    | .inList e1 n1 v1, .inList e2 n2 v2 =>
      Expr.beq e1 e2 && n1 == n2 && v1.length == v2.length && (v1.zip v2).all (fun (x, y) => Expr.beq x y)
    | .inSubquery e1 n1 s1, .inSubquery e2 n2 s2 =>
      Expr.beq e1 e2 && n1 == n2 && SubQuery.beq s1 s2
    | .exists n1 s1, .exists n2 s2 => n1 == n2 && SubQuery.beq s1 s2
    | .subquery s1, .subquery s2 => SubQuery.beq s1 s2
    | .between e1 l1 h1, .between e2 l2 h2 => Expr.beq e1 e2 && Expr.beq l1 l2 && Expr.beq h1 h2
    | .windowFn fn1 arg1 spec1, .windowFn fn2 arg2 spec2 =>
      fn1 == fn2 && WindowSpec.beq spec1 spec2 &&
      match arg1, arg2 with
      | none, none => true
      | some x, some y => Expr.beq x y
      | _, _ => false
    | _, _ => false

  partial def WindowSpec.beq : WindowSpec → WindowSpec → Bool
    | .mk part1 ord1, .mk part2 ord2 =>
      part1.length == part2.length && (part1.zip part2).all (fun (x, y) => Expr.beq x y) &&
      ord1.length == ord2.length && (ord1.zip ord2).all (fun (x, y) => OrderByItem.beq x y)

  partial def SelectItem.beq : SelectItem → SelectItem → Bool
    | .star t1, .star t2 => t1 == t2
    | .exprItem e1 a1, .exprItem e2 a2 => Expr.beq e1 e2 && a1 == a2
    | _, _ => false

  partial def SubQuery.beq : SubQuery → SubQuery → Bool
    | .simple s1, .simple s2 => SelectStmt.beq s1 s2
    | .compound l1 o1 r1, .compound l2 o2 r2 =>
      SubQuery.beq l1 l2 && o1 == o2 && SubQuery.beq r1 r2
    | _, _ => false

  partial def FromClause.beq : FromClause → FromClause → Bool
    | .table t1, .table t2 => t1 == t2
    | .subquery s1 a1, .subquery s2 a2 => SubQuery.beq s1 s2 && a1 == a2
    | .join l1 jt1 r1 on1, .join l2 jt2 r2 on2 =>
      FromClause.beq l1 l2 && jt1 == jt2 && FromClause.beq r1 r2 &&
      match on1, on2 with
      | none, none => true
      | some x, some y => Expr.beq x y
      | _, _ => false
    | _, _ => false

  partial def OrderByItem.beq : OrderByItem → OrderByItem → Bool
    | .mk e1 d1 n1, .mk e2 d2 n2 => Expr.beq e1 e2 && d1 == d2 && n1 == n2

  partial def SelectStmt.beq : SelectStmt → SelectStmt → Bool
    | .mk d1 i1 f1 w1 g1 h1 o1 l1 off1, .mk d2 i2 f2 w2 g2 h2 o2 l2 off2 =>
      d1 == d2 &&
      i1.length == i2.length && (i1.zip i2).all (fun (x, y) => SelectItem.beq x y) &&
      (match f1, f2 with | none, none => true | some x, some y => FromClause.beq x y | _, _ => false) &&
      (match w1, w2 with | none, none => true | some x, some y => Expr.beq x y | _, _ => false) &&
      g1.length == g2.length && (g1.zip g2).all (fun (x, y) => Expr.beq x y) &&
      (match h1, h2 with | none, none => true | some x, some y => Expr.beq x y | _, _ => false) &&
      o1.length == o2.length && (o1.zip o2).all (fun (x, y) => OrderByItem.beq x y) &&
      l1 == l2 && off1 == off2

  partial def Query.beq : Query → Query → Bool
    | .simple s1, .simple s2 => SelectStmt.beq s1 s2
    | .compound l1 op1 r1, .compound l2 op2 r2 =>
      Query.beq l1 l2 && op1 == op2 && Query.beq r1 r2
    | .withCTE ctes1 q1, .withCTE ctes2 q2 =>
      ctes1.length == ctes2.length &&
      (ctes1.zip ctes2).all (fun (c1, c2) => c1.name == c2.name && Query.beq c1.query c2.query && c1.isRecursive == c2.isRecursive) &&
      Query.beq q1 q2
    | _, _ => false

  partial def InsertSource.beq : InsertSource → InsertSource → Bool
    | .values r1, .values r2 =>
      r1.length == r2.length &&
      (r1.zip r2).all (fun (row1, row2) =>
        row1.length == row2.length && (row1.zip row2).all (fun (x, y) => Expr.beq x y))
    | .selectStmt s1, .selectStmt s2 => SelectStmt.beq s1 s2
    | _, _ => false

  partial def Assignment.beq : Assignment → Assignment → Bool
    | ⟨c1, v1⟩, ⟨c2, v2⟩ => c1 == c2 && Expr.beq v1 v2
end

instance : BEq Expr where beq := Expr.beq
instance : BEq WindowSpec where beq := WindowSpec.beq
instance : BEq SelectItem where beq := SelectItem.beq
instance : BEq FromClause where beq := FromClause.beq
instance : BEq OrderByItem where beq := OrderByItem.beq
instance : BEq SelectStmt where beq := SelectStmt.beq
instance : BEq SubQuery where beq := SubQuery.beq
instance : BEq Query where beq := Query.beq
instance : BEq InsertSource where beq := InsertSource.beq
instance : BEq Assignment where beq := Assignment.beq
instance : BEq CTEDef where beq c1 c2 := c1.name == c2.name && Query.beq c1.query c2.query && c1.isRecursive == c2.isRecursive

instance : BEq InsertStmt where
  beq i1 i2 := i1.table == i2.table && i1.columns == i2.columns && InsertSource.beq i1.source i2.source

instance : BEq UpdateStmt where
  beq u1 u2 :=
    u1.table == u2.table &&
    u1.assignments.length == u2.assignments.length &&
    (u1.assignments.zip u2.assignments).all (fun (x, y) => Assignment.beq x y) &&
    match u1.whereClause, u2.whereClause with
    | none, none => true
    | some x, some y => Expr.beq x y
    | _, _ => false

instance : BEq DeleteStmt where
  beq d1 d2 :=
    d1.table == d2.table &&
    match d1.whereClause, d2.whereClause with
    | none, none => true
    | some x, some y => Expr.beq x y
    | _, _ => false

instance : BEq Stmt where
  beq s1 s2 := match s1, s2 with
    | .query x, .query y => Query.beq x y
    | .insert x, .insert y => x == y
    | .update x, .update y => x == y
    | .delete x, .delete y => x == y
    | _, _ => false

-- ============================================================================
-- DecidableEq instance for Expr
-- ============================================================================
--
-- Why this is needed:
--   `syntacticEquiv_implies_equiv` needs to derive `normalizeExpr e1 = normalizeExpr e2`
--   from `syntacticEquiv e1 e2 = true`. This requires `DecidableEq Expr`.
--
-- Why we can't use standard approaches:
--   1. `deriving instance DecidableEq` — unsupported for Lean 4 mutual inductives
--   2. Manual WFR mutual block — fails with "Cannot derive unfold equation" even at
--      maxHeartbeats 4000000 (it's a structural rfl failure, not a timeout)
--   3. `noncomputable instance : DecidableEq Expr := Classical.decEq _` — sound, but
--      makes `syntacticEquiv` noncomputable, breaking `native_decide` in the
--      `sql_equiv!` tactic (Tactics.lean) which is the main user-facing API
--
-- Soundness assumption:
--   The `unsafe` impl assumes `Expr.BEq` is lawful: `(a == b) = true ↔ a = b`.
--   The BEq instance (lines 476-567) is a structural recursive comparison over all
--   14 Expr constructors and 5 mutual types. It is `partial def` only because Lean 4
--   can't verify termination for the mutual block — NOT because it's non-terminating.
--   Converting BEq to WFR would eliminate this assumption but hits the same eq_def
--   size limit.
--
-- What would eliminate the unsafe code:
--   - Lean adding `deriving DecidableEq` support for mutual inductives, OR
--   - Lean raising the eq_def size limit for mutual WFR blocks, OR
--   - Proving `LawfulBEq Expr` (requires non-partial BEq first)

private unsafe def Expr.decEqUnsafe (a b : Expr) : Decidable (a = b) :=
  if a == b then .isTrue lcProof else .isFalse lcProof

@[implemented_by Expr.decEqUnsafe]
opaque Expr.decEqOpaque (a b : Expr) : Decidable (a = b)

instance : DecidableEq Expr := Expr.decEqOpaque

-- ============================================================================
-- Inhabited instances
-- ============================================================================

instance : Inhabited Expr where default := .lit (.null none)
instance : Inhabited WindowSpec where default := .mk [] []
instance : Inhabited SelectItem where default := .star none
instance : Inhabited FromClause where default := .table ⟨"", none⟩
instance : Inhabited OrderByItem where default := .mk default .asc .first
instance : Inhabited SelectStmt where
  default := .mk false [] none none [] none [] none none
instance : Inhabited SubQuery where default := .simple default
instance : Inhabited CTEDef where default := ⟨"", .simple default, false⟩
instance : Inhabited Query where default := .simple default
instance : Inhabited InsertSource where default := .values []
instance : Inhabited Assignment where default := ⟨"", default⟩
instance : Inhabited InsertStmt where default := ⟨"", none, default⟩
instance : Inhabited UpdateStmt where default := ⟨"", [], none⟩
instance : Inhabited DeleteStmt where default := ⟨"", none⟩
instance : Inhabited Stmt where default := .query default

end SqlEquiv
