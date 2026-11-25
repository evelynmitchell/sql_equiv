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
  /-- LIKE that ignores ASCII letter case (sqlite's default LIKE). The parser
      emits it instead of `like` when the dialect's `likeCase` is
      `asciiInsensitive` (docs/IMPLEMENTATION_DEFINED.md, row 8). -/
  | likeCI
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

/-- SUM/AVG over booleans (registry row 18), chosen per dialect and per function at parse time.
    - `error`: a boolean input is a type error (standard, Postgres; DuckDB's AVG).
    - `asInt`: booleans are the integers 1/0 (sqlite; DuckDB's SUM). -/
inductive BoolSumAvg where
  | error
  | asInt
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

/-- LIKE letter-case rule (registry row 8), chosen by the dialect at parse time.
    - `sensitive`: `'abc' LIKE 'ABC'` is false (standard, DuckDB, Postgres).
    - `asciiInsensitive`: ASCII letters match regardless of case; other
      characters are compared exactly (sqlite). -/
inductive LikeCase where
  | sensitive
  | asciiInsensitive
  deriving Repr, BEq, Inhabited, DecidableEq

/-- `SELECT DISTINCT` with an `ORDER BY` key that is not selected (row 5):
    `SELECT DISTINCT a FROM t ORDER BY b`.
    - `reject`: a parse error, as the standard and Postgres require ("for
      SELECT DISTINCT, ORDER BY expressions must appear in select list").
    - `firstRow`: accepted; each output row sorts by the key of its first
      source row (sqlite and DuckDB; DuckDB plans it as `first(b)`). -/
inductive DistinctOrderBy where
  | reject
  | firstRow
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A column that is neither grouped nor inside an aggregate, next to aggregates (`SELECT max(a), b
    FROM t`; registry T9).
    - `reject`: an error, as the standard, Postgres and DuckDB require.
    - `sqlite`: accepted. With one `MIN`/`MAX` call, the bare column takes its value from the first
      row where that aggregate's argument is extreme (the last row if every argument is NULL);
      otherwise from the group's first row.
    Used by the typed-core bridge (`SqlBridge`); `SqlEquiv`'s evaluator accepts bare columns in
    every dialect and reads them from the group's first row. -/
inductive BareColumns where
  | reject
  | sqlite
  deriving Repr, BEq, Inhabited, DecidableEq

/-- `INSERT` without a column list and fewer values than the table has columns
    (`INSERT INTO t VALUES (6, 'x')` into a three-column table; registry T19, typed-core bridge).
    - `reject`: an error, as the standard, sqlite and DuckDB do.
    - `padNull`: the missing trailing columns are `NULL` (Postgres).
    More values than columns is an error in every dialect. -/
inductive ShortInsert where
  | reject
  | padNull
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A scalar subquery that returns several rows (`WHERE x > (SELECT a FROM t)` with two rows in
    `t`).
    - `error`: an evaluation error, as the standard, Postgres and DuckDB do.
    - `firstRow`: the first row's value (sqlite).
    Used by the typed-core bridge (`SqlBridge`), which records it on each subquery node. -/
inductive ScalarSubqueryRows where
  | error
  | firstRow
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The dialect choices a MIN/MAX node records. -/
structure MinMaxMode where
  mixed : MixedMinMax
  bools : BoolMinMax
  /-- A bare column next to this MIN/MAX, when it is the statement's only one, reads the row
      where its argument is extreme (sqlite; registry T9). Otherwise bare columns read the
      group's first row. -/
  bareRow : Bool := false
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Aggregate functions (MIN/MAX carry the dialect's mixed-type mode) -/
inductive AggFunc where
  | count
  | sum (bools : BoolSumAvg)
  | avg (bools : BoolSumAvg)
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

/-- A query without `GROUP BY` and without an aggregate in its select list that has a `HAVING`
    (`SELECT 1 FROM t HAVING COUNT(*) > 1`; registry row 22, #440).
    - `oneGroup`: the whole input is one group, as the standard, DuckDB and Postgres do.
    - `reject`: an error, as sqlite does ("HAVING clause on a non-aggregate query"). -/
inductive ImplicitGroup where
  | oneGroup
  | reject
  deriving Repr, BEq, Inhabited, DecidableEq

/-- What a quiet evaluation error (`none`: a type mismatch, a missing column, a division by zero)
    means in a dialect (registry row 23, #270). The evaluator and every theorem are quiet: an
    error drops the row in `WHERE` and shows as NULL in the select list. `evalQueryIn`
    (`SqlEquiv.Strict`) layers the dialect's choice on top.
    - `quiet`: nothing changes, as sqlite mostly does.
    - `strict`: the statement fails when a clause it evaluates yields an error, as Postgres and
      the standard do.
    - `strictDivZeroNull`: `strict`, except that division and modulo by zero are not errors, as in
      DuckDB (`5 % 0` is NULL; `1 / 0` is a float infinity, registry row 6). -/
inductive ErrorMode where
  | quiet
  | strict
  | strictDivZeroNull
  deriving Repr, BEq, Inhabited, DecidableEq

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
  /-- LIKE letter case (row 8) -/
  likeCase : LikeCase
  /-- DISTINCT with an unselected ORDER BY key (row 5) -/
  distinctOrderBy : DistinctOrderBy
  /-- Bare columns next to aggregates (registry T9; typed-core bridge) -/
  bareColumns : BareColumns := .reject
  /-- A scalar subquery with several rows (registry T17; typed-core bridge) -/
  scalarSubqueryRows : ScalarSubqueryRows := .error
  /-- SUM over booleans (row 18) -/
  boolSum : BoolSumAvg := .error
  /-- AVG over booleans (row 18) -/
  boolAvg : BoolSumAvg := .error
  /-- `HAVING` without `GROUP BY` and without an aggregate in the select list (row 22) -/
  implicitGroup : ImplicitGroup := .oneGroup
  /-- What an evaluation error means (row 23, #270) -/
  errors : ErrorMode := .strict
  /-- `INSERT` with fewer values than columns and no column list (registry T19; typed-core
      bridge) -/
  shortInsert : ShortInsert := .reject
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Each dialect's choices. `standard` has to pick a NULL position (the standard
    leaves it to the implementation): it takes NULL-largest, the rule of the
    Postgres standards tiebreaker. -/
def Dialect.config : Dialect → DialectConfig
  | .standard => { nullOrdering := .nullsLargest,    mixedMinMax := .error,
                   boolMinMax := .error,   likeCase := .sensitive,
                   distinctOrderBy := .reject }
  | .sqlite   => { nullOrdering := .nullsSmallest,   mixedMinMax := .typeClass,
                   boolMinMax := .asInt,   likeCase := .asciiInsensitive,
                   distinctOrderBy := .firstRow, bareColumns := .sqlite,
                   scalarSubqueryRows := .firstRow, boolSum := .asInt, boolAvg := .asInt,
                   implicitGroup := .reject, errors := .quiet }
  | .duckdb   => { nullOrdering := .nullsAlwaysLast, mixedMinMax := .error,
                   boolMinMax := .ordered, likeCase := .sensitive,
                   distinctOrderBy := .firstRow, boolSum := .asInt,
                   errors := .strictDivZeroNull }
  | .postgres => { nullOrdering := .nullsLargest,    mixedMinMax := .error,
                   boolMinMax := .error,   likeCase := .sensitive,
                   distinctOrderBy := .reject, shortInsert := .padNull }

/-- The MIN/MAX mode a dialect configuration records on each MIN/MAX node. -/
def DialectConfig.minMaxMode (c : DialectConfig) : MinMaxMode :=
  { mixed := c.mixedMinMax, bools := c.boolMinMax, bareRow := c.bareColumns == .sqlite }

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
  | sum (bools : BoolSumAvg)
  | avg (bools : BoolSumAvg)
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

/-- The SELECT items of the leftmost branch of a subquery body (#340). -/
def SubQuery.leftmostItems : SubQuery → List SelectItem
  | .simple s => s.items
  | .compound l _ _ => l.leftmostItems

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
  /-- `q ORDER BY … LIMIT … OFFSET …` over a whole compound query (#317): `A UNION B ORDER BY k`
      sorts the union, not branch `B`. Keys refer to output columns. -/
  | ordered : Query → List OrderByItem → Option Nat → Option Nat → Query
end

/-- The SELECT items of the leftmost branch of a query: they name a compound query's output
    columns (#317, #340). -/
def Query.leftmostItems : Query → List SelectItem
  | .simple s => s.items
  | .compound l _ _ => l.leftmostItems
  | .withCTE _ q => q.leftmostItems
  | .ordered q _ _ _ => q.leftmostItems

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
    | .ordered q ob l off =>
      s!"Query.ordered ({q.toReprStr}) [{", ".intercalate (ob.map OrderByItem.toReprStr)}] {l} {off}"

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
-- Decidable equality (total, structurally recursive; #278)
-- ============================================================================
--
-- `deriving DecidableEq` does not support nested inductives (Lean 4.27–4.36)
-- (`List Expr`, `Option Expr`, … inside the mutual block), so the deciders
-- are hand-written. They are generated by `tools/gen_ast_deceq.py`; edit the
-- generator, not this block, when the AST changes.
--
-- Shape: match on the first argument (so structural recursion unfolds), then
-- check `b.ctorIdx` before matching `b`; the other constructors are ruled out
-- by the index hypothesis. Nested `List`/`Option`/pair fields get their own
-- mutual helpers. Everything is total and kernel-reducible, so `decide` works,
-- and `BEq` on these types is `instBEqOfDecidableEq`, hence `LawfulBEq`.
-- This replaces the earlier partial `Expr.beq` + `unsafe`/`implemented_by`
-- `DecidableEq` (which assumed `Expr.beq` was lawful).

-- Structural orders on the AST's leaf types, used only by the generated
-- `*.cmp` below (canonical operand order in `normalizeExpr`). `Value` gets no
-- `Ord` instance on purpose: SQL ordering is `Value.compare`, and a structural
-- `compare` on values would be easy to pick up by mistake.
deriving instance Ord for SqlType, ColumnRef, BinOp, UnaryOp, MixedMinMax, BoolMinMax, BoolSumAvg,
  MinMaxMode, AggFunc, TableRef, JoinType, OrderDir, NullsOrder, SetOp, WindowFunc

/-- Structural total order on values (by constructor, then fields). Not SQL
    order (that is `Value.compare`): `1` and `1.0` differ here. -/
def Value.structCmp : Value → Value → Ordering
  | .int a, .int b => compare a b
  | .string a, .string b => compare a b
  | .bool a, .bool b => compare a b
  | .decimal u s, .decimal u' s' => (compare u u').then (compare s s')
  | .null t, .null t' => compare t t'
  | a, b => compare a.ctorIdx b.ctorIdx

-- BEGIN GENERATED (tools/gen_ast_deceq.py)
mutual
def WindowSpec.decEq (a b : WindowSpec) : Decidable (a = b) :=
  match a, b with
  | @WindowSpec.mk a0 a1, @WindowSpec.mk b0 b1 =>
    let _ : Decidable (a0 = b0) := Expr.decEqList a0 b0
      if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := OrderByItem.decEqList a1 b1
      if h : a1 = b1 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
termination_by structural a

def Expr.decEq (a b : Expr) : Decidable (a = b) :=
  match a with
  | @Expr.lit a0 =>
    if hb : b.ctorIdx = 0 then
      match b, hb with
      | @Expr.lit b0, _ =>
        if h : a0 = b0 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.col a0 =>
    if hb : b.ctorIdx = 1 then
      match b, hb with
      | @Expr.col b0, _ =>
        if h : a0 = b0 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.binOp a0 a1 a2 =>
    if hb : b.ctorIdx = 2 then
      match b, hb with
      | @Expr.binOp b0 b1 b2, _ =>
        if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := Expr.decEq a1 b1
      if h : a1 = b1 then by subst h; exact (let _ : Decidable (a2 = b2) := Expr.decEq a2 b2
      if h : a2 = b2 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.unaryOp a0 a1 =>
    if hb : b.ctorIdx = 3 then
      match b, hb with
      | @Expr.unaryOp b0 b1, _ =>
        if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := Expr.decEq a1 b1
      if h : a1 = b1 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.func a0 a1 =>
    if hb : b.ctorIdx = 4 then
      match b, hb with
      | @Expr.func b0 b1, _ =>
        if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := Expr.decEqList a1 b1
      if h : a1 = b1 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.agg a0 a1 a2 =>
    if hb : b.ctorIdx = 5 then
      match b, hb with
      | @Expr.agg b0 b1 b2, _ =>
        if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := Expr.decEqOpt a1 b1
      if h : a1 = b1 then by subst h; exact (if h : a2 = b2 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.countStar =>
    if hb : b.ctorIdx = 6 then
      match b, hb with
      | @Expr.countStar, _ =>
        isTrue rfl
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.«case» a0 a1 =>
    if hb : b.ctorIdx = 7 then
      match b, hb with
      | @Expr.«case» b0 b1, _ =>
        let _ : Decidable (a0 = b0) := Expr.decEqPairs a0 b0
      if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := Expr.decEqOpt a1 b1
      if h : a1 = b1 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.inList a0 a1 a2 =>
    if hb : b.ctorIdx = 8 then
      match b, hb with
      | @Expr.inList b0 b1 b2, _ =>
        let _ : Decidable (a0 = b0) := Expr.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (if h : a1 = b1 then by subst h; exact (let _ : Decidable (a2 = b2) := Expr.decEqList a2 b2
      if h : a2 = b2 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.inSubquery a0 a1 a2 =>
    if hb : b.ctorIdx = 9 then
      match b, hb with
      | @Expr.inSubquery b0 b1 b2, _ =>
        let _ : Decidable (a0 = b0) := Expr.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (if h : a1 = b1 then by subst h; exact (let _ : Decidable (a2 = b2) := SubQuery.decEq a2 b2
      if h : a2 = b2 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.exists a0 a1 =>
    if hb : b.ctorIdx = 10 then
      match b, hb with
      | @Expr.exists b0 b1, _ =>
        if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := SubQuery.decEq a1 b1
      if h : a1 = b1 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.subquery a0 =>
    if hb : b.ctorIdx = 11 then
      match b, hb with
      | @Expr.subquery b0, _ =>
        let _ : Decidable (a0 = b0) := SubQuery.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.between a0 a1 a2 =>
    if hb : b.ctorIdx = 12 then
      match b, hb with
      | @Expr.between b0 b1 b2, _ =>
        let _ : Decidable (a0 = b0) := Expr.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := Expr.decEq a1 b1
      if h : a1 = b1 then by subst h; exact (let _ : Decidable (a2 = b2) := Expr.decEq a2 b2
      if h : a2 = b2 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Expr.windowFn a0 a1 a2 =>
    if hb : b.ctorIdx = 13 then
      match b, hb with
      | @Expr.windowFn b0 b1 b2, _ =>
        if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := Expr.decEqOpt a1 b1
      if h : a1 = b1 then by subst h; exact (let _ : Decidable (a2 = b2) := WindowSpec.decEq a2 b2
      if h : a2 = b2 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
termination_by structural a

def Expr.decEqList (a b : List Expr) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match Expr.decEq x y, Expr.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (by subst h1 h2; rfl)
    | isFalse h1, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h2 => isFalse (fun e => by injection e; contradiction)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
termination_by structural a

def Expr.decEqOpt (a b : Option Expr) : Decidable (a = b) :=
  match a, b with
  | none, none => isTrue rfl
  | some x, some y =>
    match Expr.decEq x y with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by injection e; contradiction)
  | none, some _ => isFalse (fun e => by cases e)
  | some _, none => isFalse (fun e => by cases e)
termination_by structural a

def Expr.decEqPairs (a b : List (Expr × Expr)) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | (x1, x2) :: xs, (y1, y2) :: ys =>
    match Expr.decEq x1 y1, Expr.decEq x2 y2, Expr.decEqPairs xs ys with
    | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1 h2 h3; rfl)
    | isFalse h1, _, _ => isFalse (fun e => by injection e with e1; injection e1; contradiction)
    | _, isFalse h2, _ => isFalse (fun e => by injection e with e1; injection e1; contradiction)
    | _, _, isFalse h3 => isFalse (fun e => by injection e; contradiction)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
termination_by structural a

def OrderByItem.decEq (a b : OrderByItem) : Decidable (a = b) :=
  match a, b with
  | @OrderByItem.mk a0 a1 a2, @OrderByItem.mk b0 b1 b2 =>
    let _ : Decidable (a0 = b0) := Expr.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (if h : a1 = b1 then by subst h; exact (if h : a2 = b2 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
termination_by structural a

def OrderByItem.decEqList (a b : List OrderByItem) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match OrderByItem.decEq x y, OrderByItem.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (by subst h1 h2; rfl)
    | isFalse h1, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h2 => isFalse (fun e => by injection e; contradiction)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
termination_by structural a

def SelectItem.decEq (a b : SelectItem) : Decidable (a = b) :=
  match a with
  | @SelectItem.star a0 =>
    if hb : b.ctorIdx = 0 then
      match b, hb with
      | @SelectItem.star b0, _ =>
        if h : a0 = b0 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @SelectItem.exprItem a0 a1 =>
    if hb : b.ctorIdx = 1 then
      match b, hb with
      | @SelectItem.exprItem b0 b1, _ =>
        let _ : Decidable (a0 = b0) := Expr.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (if h : a1 = b1 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
termination_by structural a

def SelectItem.decEqList (a b : List SelectItem) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match SelectItem.decEq x y, SelectItem.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (by subst h1 h2; rfl)
    | isFalse h1, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h2 => isFalse (fun e => by injection e; contradiction)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
termination_by structural a

def FromClause.decEq (a b : FromClause) : Decidable (a = b) :=
  match a with
  | @FromClause.table a0 =>
    if hb : b.ctorIdx = 0 then
      match b, hb with
      | @FromClause.table b0, _ =>
        if h : a0 = b0 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @FromClause.subquery a0 a1 =>
    if hb : b.ctorIdx = 1 then
      match b, hb with
      | @FromClause.subquery b0 b1, _ =>
        let _ : Decidable (a0 = b0) := SubQuery.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (if h : a1 = b1 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @FromClause.join a0 a1 a2 a3 =>
    if hb : b.ctorIdx = 2 then
      match b, hb with
      | @FromClause.join b0 b1 b2 b3, _ =>
        let _ : Decidable (a0 = b0) := FromClause.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (if h : a1 = b1 then by subst h; exact (let _ : Decidable (a2 = b2) := FromClause.decEq a2 b2
      if h : a2 = b2 then by subst h; exact (let _ : Decidable (a3 = b3) := Expr.decEqOpt a3 b3
      if h : a3 = b3 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
termination_by structural a

def FromClause.decEqOpt (a b : Option FromClause) : Decidable (a = b) :=
  match a, b with
  | none, none => isTrue rfl
  | some x, some y =>
    match FromClause.decEq x y with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by injection e; contradiction)
  | none, some _ => isFalse (fun e => by cases e)
  | some _, none => isFalse (fun e => by cases e)
termination_by structural a

def SubQuery.decEq (a b : SubQuery) : Decidable (a = b) :=
  match a with
  | @SubQuery.simple a0 =>
    if hb : b.ctorIdx = 0 then
      match b, hb with
      | @SubQuery.simple b0, _ =>
        let _ : Decidable (a0 = b0) := SelectStmt.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @SubQuery.compound a0 a1 a2 =>
    if hb : b.ctorIdx = 1 then
      match b, hb with
      | @SubQuery.compound b0 b1 b2, _ =>
        let _ : Decidable (a0 = b0) := SubQuery.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (if h : a1 = b1 then by subst h; exact (let _ : Decidable (a2 = b2) := SubQuery.decEq a2 b2
      if h : a2 = b2 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
termination_by structural a

def SelectStmt.decEq (a b : SelectStmt) : Decidable (a = b) :=
  match a, b with
  | @SelectStmt.mk a0 a1 a2 a3 a4 a5 a6 a7 a8, @SelectStmt.mk b0 b1 b2 b3 b4 b5 b6 b7 b8 =>
    if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := SelectItem.decEqList a1 b1
      if h : a1 = b1 then by subst h; exact (let _ : Decidable (a2 = b2) := FromClause.decEqOpt a2 b2
      if h : a2 = b2 then by subst h; exact (let _ : Decidable (a3 = b3) := Expr.decEqOpt a3 b3
      if h : a3 = b3 then by subst h; exact (let _ : Decidable (a4 = b4) := Expr.decEqList a4 b4
      if h : a4 = b4 then by subst h; exact (let _ : Decidable (a5 = b5) := Expr.decEqOpt a5 b5
      if h : a5 = b5 then by subst h; exact (let _ : Decidable (a6 = b6) := OrderByItem.decEqList a6 b6
      if h : a6 = b6 then by subst h; exact (if h : a7 = b7 then by subst h; exact (if h : a8 = b8 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
termination_by structural a
end

instance : DecidableEq WindowSpec := WindowSpec.decEq
instance : DecidableEq Expr := Expr.decEq
instance : DecidableEq OrderByItem := OrderByItem.decEq
instance : DecidableEq SelectItem := SelectItem.decEq
instance : DecidableEq FromClause := FromClause.decEq
instance : DecidableEq SubQuery := SubQuery.decEq
instance : DecidableEq SelectStmt := SelectStmt.decEq

mutual
def CTEDef.decEq (a b : CTEDef) : Decidable (a = b) :=
  match a, b with
  | @CTEDef.mk a0 a1 a2, @CTEDef.mk b0 b1 b2 =>
    if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := Query.decEq a1 b1
      if h : a1 = b1 then by subst h; exact (if h : a2 = b2 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
termination_by structural a

def CTEDef.decEqList (a b : List CTEDef) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match CTEDef.decEq x y, CTEDef.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (by subst h1 h2; rfl)
    | isFalse h1, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h2 => isFalse (fun e => by injection e; contradiction)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
termination_by structural a

def Query.decEq (a b : Query) : Decidable (a = b) :=
  match a with
  | @Query.simple a0 =>
    if hb : b.ctorIdx = 0 then
      match b, hb with
      | @Query.simple b0, _ =>
        if h : a0 = b0 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Query.compound a0 a1 a2 =>
    if hb : b.ctorIdx = 1 then
      match b, hb with
      | @Query.compound b0 b1 b2, _ =>
        let _ : Decidable (a0 = b0) := Query.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (if h : a1 = b1 then by subst h; exact (let _ : Decidable (a2 = b2) := Query.decEq a2 b2
      if h : a2 = b2 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Query.withCTE a0 a1 =>
    if hb : b.ctorIdx = 2 then
      match b, hb with
      | @Query.withCTE b0 b1, _ =>
        let _ : Decidable (a0 = b0) := CTEDef.decEqList a0 b0
      if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := Query.decEq a1 b1
      if h : a1 = b1 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
  | @Query.ordered a0 a1 a2 a3 =>
    if hb : b.ctorIdx = 3 then
      match b, hb with
      | @Query.ordered b0 b1 b2 b3, _ =>
        let _ : Decidable (a0 = b0) := Query.decEq a0 b0
      if h : a0 = b0 then by subst h; exact (let _ : Decidable (a1 = b1) := OrderByItem.decEqList a1 b1
      if h : a1 = b1 then by subst h; exact (if h : a2 = b2 then by subst h; exact (if h : a3 = b3 then by subst h; exact (isTrue rfl) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))) else isFalse (fun n => h (by injection n <;> assumption))
    else isFalse (fun e => hb (by subst e; rfl))
termination_by structural a
end

instance : DecidableEq CTEDef := CTEDef.decEq
instance : DecidableEq Query := Query.decEq

/-! Structural total order on expressions (not SQL order): used by
`normalizeExpr` to put commutative operands in a canonical order. -/
mutual
def WindowSpec.cmp (a b : WindowSpec) : Ordering :=
  match a, b with
  | @WindowSpec.mk a0 a1, @WindowSpec.mk b0 b1 => (Expr.cmpList a0 b0).then (OrderByItem.cmpList a1 b1)
termination_by structural a

def Expr.cmp (a b : Expr) : Ordering :=
  match a with
  | @Expr.lit a0 =>
    match b with
    | @Expr.lit b0 => Value.structCmp a0 b0
    | b => compare 0 b.ctorIdx
  | @Expr.col a0 =>
    match b with
    | @Expr.col b0 => compare a0 b0
    | b => compare 1 b.ctorIdx
  | @Expr.binOp a0 a1 a2 =>
    match b with
    | @Expr.binOp b0 b1 b2 => (compare a0 b0).then ((Expr.cmp a1 b1).then (Expr.cmp a2 b2))
    | b => compare 2 b.ctorIdx
  | @Expr.unaryOp a0 a1 =>
    match b with
    | @Expr.unaryOp b0 b1 => (compare a0 b0).then (Expr.cmp a1 b1)
    | b => compare 3 b.ctorIdx
  | @Expr.func a0 a1 =>
    match b with
    | @Expr.func b0 b1 => (compare a0 b0).then (Expr.cmpList a1 b1)
    | b => compare 4 b.ctorIdx
  | @Expr.agg a0 a1 a2 =>
    match b with
    | @Expr.agg b0 b1 b2 => (compare a0 b0).then ((Expr.cmpOpt a1 b1).then (compare a2 b2))
    | b => compare 5 b.ctorIdx
  | @Expr.countStar =>
    match b with
    | @Expr.countStar => .eq
    | b => compare 6 b.ctorIdx
  | @Expr.«case» a0 a1 =>
    match b with
    | @Expr.«case» b0 b1 => (Expr.cmpPairs a0 b0).then (Expr.cmpOpt a1 b1)
    | b => compare 7 b.ctorIdx
  | @Expr.inList a0 a1 a2 =>
    match b with
    | @Expr.inList b0 b1 b2 => (Expr.cmp a0 b0).then ((compare a1 b1).then (Expr.cmpList a2 b2))
    | b => compare 8 b.ctorIdx
  | @Expr.inSubquery a0 a1 a2 =>
    match b with
    | @Expr.inSubquery b0 b1 b2 => (Expr.cmp a0 b0).then ((compare a1 b1).then (SubQuery.cmp a2 b2))
    | b => compare 9 b.ctorIdx
  | @Expr.exists a0 a1 =>
    match b with
    | @Expr.exists b0 b1 => (compare a0 b0).then (SubQuery.cmp a1 b1)
    | b => compare 10 b.ctorIdx
  | @Expr.subquery a0 =>
    match b with
    | @Expr.subquery b0 => SubQuery.cmp a0 b0
    | b => compare 11 b.ctorIdx
  | @Expr.between a0 a1 a2 =>
    match b with
    | @Expr.between b0 b1 b2 => (Expr.cmp a0 b0).then ((Expr.cmp a1 b1).then (Expr.cmp a2 b2))
    | b => compare 12 b.ctorIdx
  | @Expr.windowFn a0 a1 a2 =>
    match b with
    | @Expr.windowFn b0 b1 b2 => (compare a0 b0).then ((Expr.cmpOpt a1 b1).then (WindowSpec.cmp a2 b2))
    | b => compare 13 b.ctorIdx
termination_by structural a

def OrderByItem.cmp (a b : OrderByItem) : Ordering :=
  match a, b with
  | @OrderByItem.mk a0 a1 a2, @OrderByItem.mk b0 b1 b2 => (Expr.cmp a0 b0).then ((compare a1 b1).then (compare a2 b2))
termination_by structural a

def SelectItem.cmp (a b : SelectItem) : Ordering :=
  match a with
  | @SelectItem.star a0 =>
    match b with
    | @SelectItem.star b0 => compare a0 b0
    | b => compare 0 b.ctorIdx
  | @SelectItem.exprItem a0 a1 =>
    match b with
    | @SelectItem.exprItem b0 b1 => (Expr.cmp a0 b0).then (compare a1 b1)
    | b => compare 1 b.ctorIdx
termination_by structural a

def FromClause.cmp (a b : FromClause) : Ordering :=
  match a with
  | @FromClause.table a0 =>
    match b with
    | @FromClause.table b0 => compare a0 b0
    | b => compare 0 b.ctorIdx
  | @FromClause.subquery a0 a1 =>
    match b with
    | @FromClause.subquery b0 b1 => (SubQuery.cmp a0 b0).then (compare a1 b1)
    | b => compare 1 b.ctorIdx
  | @FromClause.join a0 a1 a2 a3 =>
    match b with
    | @FromClause.join b0 b1 b2 b3 => (FromClause.cmp a0 b0).then ((compare a1 b1).then ((FromClause.cmp a2 b2).then (Expr.cmpOpt a3 b3)))
    | b => compare 2 b.ctorIdx
termination_by structural a

def SubQuery.cmp (a b : SubQuery) : Ordering :=
  match a with
  | @SubQuery.simple a0 =>
    match b with
    | @SubQuery.simple b0 => SelectStmt.cmp a0 b0
    | b => compare 0 b.ctorIdx
  | @SubQuery.compound a0 a1 a2 =>
    match b with
    | @SubQuery.compound b0 b1 b2 => (SubQuery.cmp a0 b0).then ((compare a1 b1).then (SubQuery.cmp a2 b2))
    | b => compare 1 b.ctorIdx
termination_by structural a

def SelectStmt.cmp (a b : SelectStmt) : Ordering :=
  match a, b with
  | @SelectStmt.mk a0 a1 a2 a3 a4 a5 a6 a7 a8, @SelectStmt.mk b0 b1 b2 b3 b4 b5 b6 b7 b8 => (compare a0 b0).then ((SelectItem.cmpList a1 b1).then ((FromClause.cmpOpt a2 b2).then ((Expr.cmpOpt a3 b3).then ((Expr.cmpList a4 b4).then ((Expr.cmpOpt a5 b5).then ((OrderByItem.cmpList a6 b6).then ((compare a7 b7).then (compare a8 b8))))))))
termination_by structural a

def Expr.cmpList (a b : List Expr) : Ordering :=
  match a, b with
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => (Expr.cmp x y).then (Expr.cmpList xs ys)
termination_by structural a

def Expr.cmpOpt (a b : Option Expr) : Ordering :=
  match a, b with
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some x, some y => Expr.cmp x y
termination_by structural a

def Expr.cmpPairs (a b : List (Expr × Expr)) : Ordering :=
  match a, b with
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (x1, x2) :: xs, (y1, y2) :: ys =>
    (Expr.cmp x1 y1).then ((Expr.cmp x2 y2).then (Expr.cmpPairs xs ys))
termination_by structural a

def OrderByItem.cmpList (a b : List OrderByItem) : Ordering :=
  match a, b with
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => (OrderByItem.cmp x y).then (OrderByItem.cmpList xs ys)
termination_by structural a

def SelectItem.cmpList (a b : List SelectItem) : Ordering :=
  match a, b with
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => (SelectItem.cmp x y).then (SelectItem.cmpList xs ys)
termination_by structural a

def FromClause.cmpOpt (a b : Option FromClause) : Ordering :=
  match a, b with
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some x, some y => FromClause.cmp x y
termination_by structural a
end
-- END GENERATED

deriving instance DecidableEq for InsertSource, Assignment, InsertStmt, UpdateStmt, DeleteStmt, Stmt

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
