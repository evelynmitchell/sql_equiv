# SELECT Statement

## Cleanroom Specification

**Module:** `SqlEquiv/Ast.lean` (SelectStmt, FromClause, SelectItem, Query, etc.)
**Status:** Implemented ✅
**Lines:** 252-335

---

## 1. Intended Function

The SELECT statement types represent the full structure of SQL queries, including:
- SELECT items (columns, expressions, *)
- FROM clause (tables, joins, subqueries)
- WHERE, GROUP BY, HAVING clauses
- ORDER BY, LIMIT, OFFSET
- Set operations (UNION, INTERSECT, EXCEPT)
- Common Table Expressions (WITH)

### 1.1 Black-Box Specification

```
SelectStmt : Type
  Represents a single SELECT statement with all clauses.

FromClause : Type
  Represents the source of data: tables, joins, or subqueries.

Query : Type
  Represents a complete query including set operations and CTEs.
```

---

## 2. Data Types

### 2.1 SELECT Item

```lean
inductive SelectItem where
  | star      : Option String → SelectItem    -- * or table.*
  | exprItem  : Expr → Option String → SelectItem  -- expr AS alias
```

**Examples:**
| SQL | AST |
|-----|-----|
| `*` | `star none` |
| `t.*` | `star (some "t")` |
| `x` | `exprItem (col "x") none` |
| `x AS y` | `exprItem (col "x") (some "y")` |
| `1 + 2 AS sum` | `exprItem (binOp .add ...) (some "sum")` |

### 2.2 Table Reference

```lean
structure TableRef where
  name  : String          -- Table name
  alias : Option String   -- Optional alias
  deriving Repr, BEq, Inhabited, DecidableEq
```

**Examples:**
| SQL | AST |
|-----|-----|
| `users` | `⟨"users", none⟩` |
| `users u` | `⟨"users", some "u"⟩` |
| `users AS u` | `⟨"users", some "u"⟩` |

### 2.3 Join Type

```lean
inductive JoinType where
  | inner  -- INNER JOIN (or just JOIN)
  | left   -- LEFT [OUTER] JOIN
  | right  -- RIGHT [OUTER] JOIN
  | full   -- FULL [OUTER] JOIN
  | cross  -- CROSS JOIN
  deriving Repr, BEq, Inhabited, DecidableEq
```

### 2.4 FROM Clause

```lean
inductive FromClause where
  | table    : TableRef → FromClause
  | subquery : SelectStmt → String → FromClause  -- (SELECT ...) AS alias
  | join     : FromClause → JoinType → FromClause → Option Expr → FromClause
```

**Examples:**
| SQL | AST |
|-----|-----|
| `users` | `table ⟨"users", none⟩` |
| `users u` | `table ⟨"users", some "u"⟩` |
| `(SELECT 1) AS s` | `subquery stmt "s"` |
| `a JOIN b ON c` | `join (table a) .inner (table b) (some c)` |
| `a LEFT JOIN b ON c` | `join (table a) .left (table b) (some c)` |
| `a CROSS JOIN b` | `join (table a) .cross (table b) none` |

**Join nesting:**
```sql
a JOIN b ON x JOIN c ON y
```
Parses as left-associative:
```lean
join (join (table a) .inner (table b) x) .inner (table c) y
```

### 2.5 ORDER BY Item

```lean
inductive OrderByItem where
  | mk : Expr → OrderDir → OrderByItem

inductive OrderDir where
  | asc
  | desc
```

**Examples:**
| SQL | AST |
|-----|-----|
| `x ASC` | `OrderByItem.mk (col "x") .asc` |
| `x DESC` | `OrderByItem.mk (col "x") .desc` |
| `x` | `OrderByItem.mk (col "x") .asc` (default) |

### 2.6 SELECT Statement

```lean
inductive SelectStmt where
  | mk : Bool →              -- DISTINCT
         List SelectItem →    -- SELECT items
         Option FromClause →  -- FROM clause (optional for SELECT 1)
         Option Expr →        -- WHERE clause
         List Expr →          -- GROUP BY expressions
         Option Expr →        -- HAVING clause
         List OrderByItem →   -- ORDER BY
         Option Nat →         -- LIMIT
         Option Nat →         -- OFFSET
         SelectStmt
```

**Accessor Functions:**
```lean
def SelectStmt.distinct : SelectStmt → Bool
def SelectStmt.items : SelectStmt → List SelectItem
def SelectStmt.fromClause : SelectStmt → Option FromClause
def SelectStmt.whereClause : SelectStmt → Option Expr
def SelectStmt.groupBy : SelectStmt → List Expr
def SelectStmt.having : SelectStmt → Option Expr
def SelectStmt.orderBy : SelectStmt → List OrderByItem
def SelectStmt.limitVal : SelectStmt → Option Nat
def SelectStmt.offsetVal : SelectStmt → Option Nat
```

### 2.7 Set Operations

```lean
inductive SetOp where
  | union      -- UNION (removes duplicates)
  | unionAll   -- UNION ALL (keeps duplicates)
  | intersect  -- INTERSECT
  | exceptOp   -- EXCEPT (Lean reserves 'except')
```

### 2.8 Common Table Expressions

```lean
inductive CTEDef where
  | mk : (name : String) →
         (query : Query) →
         (isRecursive : Bool := false) →
         CTEDef
```

**Accessor functions:**
```lean
def CTEDef.name : CTEDef → String
def CTEDef.query : CTEDef → Query
def CTEDef.isRecursive : CTEDef → Bool
```

### 2.9 Query

```lean
inductive Query where
  | simple   : SelectStmt → Query
  | compound : Query → SetOp → Query → Query
  | withCTE  : List CTEDef → Query → Query
```

**Examples:**
| SQL | AST |
|-----|-----|
| `SELECT * FROM t` | `simple (SelectStmt.mk ...)` |
| `q1 UNION q2` | `compound q1 .union q2` |
| `q1 UNION ALL q2` | `compound q1 .unionAll q2` |
| `WITH x AS (q) SELECT ...` | `withCTE [CTEDef.mk "x" q false] mainQuery` |

---

## 3. Clause Specifications

### 3.1 SELECT Clause

```
Purpose: Define the output columns/expressions

Syntax: SELECT [DISTINCT] item1 [AS alias1], item2 [AS alias2], ...

Semantics:
  - Items evaluated for each row
  - DISTINCT removes duplicate rows from result
  - Aliases provide output column names
  - * expands to all columns from all tables
  - table.* expands to all columns from specific table
```

### 3.2 FROM Clause

```
Purpose: Define the data sources

Syntax: FROM source1 [join_type] JOIN source2 ON condition ...

Semantics:
  - Tables provide base data
  - JOINs combine tables
  - Subqueries provide derived tables
  - Aliases provide table references

Join Types:
  INNER:  Only matching rows from both
  LEFT:   All left rows + matching right (NULL for non-matching)
  RIGHT:  All right rows + matching left (NULL for non-matching)
  FULL:   All rows from both (NULL for non-matching)
  CROSS:  Cartesian product (all combinations)
```

### 3.3 WHERE Clause

```
Purpose: Filter rows based on condition

Syntax: WHERE condition

Semantics:
  - Evaluated for each row
  - Only rows where condition is TRUE are included
  - UNKNOWN (from NULLs) treated as FALSE
  - No aggregates allowed in WHERE
```

### 3.4 GROUP BY Clause

```
Purpose: Group rows for aggregation

Syntax: GROUP BY expr1, expr2, ...

Semantics:
  - Rows with equal GROUP BY values form groups
  - Each group produces one output row
  - Non-aggregated SELECT items must be in GROUP BY
  - Empty input produces zero groups
```

### 3.5 HAVING Clause

```
Purpose: Filter groups based on aggregate conditions

Syntax: HAVING condition

Semantics:
  - Evaluated after grouping
  - Can reference aggregates
  - Only groups where condition is TRUE are included
```

### 3.6 ORDER BY Clause

```
Purpose: Sort output rows

Syntax: ORDER BY expr1 [ASC|DESC], expr2 [ASC|DESC], ...

Semantics:
  - Applied after all other clauses
  - ASC = ascending (default)
  - DESC = descending
  - NULL handling is implementation-defined
  - Can reference aliases from SELECT
```

### 3.7 LIMIT and OFFSET

```
Purpose: Restrict number of output rows

Syntax: LIMIT n [OFFSET m]

Semantics:
  - OFFSET m: Skip first m rows
  - LIMIT n: Return at most n rows
  - Applied after ORDER BY
  - Without ORDER BY, result is arbitrary
```

---

## 4. Correctness Conditions

### 4.1 Well-Formedness

```lean
-- All column references must be valid
theorem columns_valid (s : SelectStmt) (env : Env) :
  s.wellFormed env → ∀ col ∈ s.columns, env.hasColumn col

-- GROUP BY columns must exist
theorem groupby_valid (s : SelectStmt) (env : Env) :
  s.wellFormed env → ∀ e ∈ s.groupBy, e.validIn env

-- HAVING requires GROUP BY
theorem having_needs_groupby (s : SelectStmt) :
  s.having.isSome → s.groupBy.length > 0 ∨ hasAggregates s.items
```

### 4.2 Join Equivalences

```lean
-- INNER JOIN commutativity
theorem inner_join_comm (a b : FromClause) (cond : Expr) :
  eval (join a .inner b (some cond)) =
  eval (join b .inner a (some cond))

-- INNER JOIN associativity
theorem inner_join_assoc (a b c : FromClause) (c1 c2 : Expr) :
  -- Note: condition rewriting needed
```

### 4.3 Set Operation Properties

```lean
-- UNION commutativity
theorem union_comm (q1 q2 : Query) :
  eval (compound q1 .union q2) = eval (compound q2 .union q1)

-- UNION ALL commutativity (bag semantics)
theorem union_all_comm (q1 q2 : Query) :
  bagEquiv (eval (compound q1 .unionAll q2)) (eval (compound q2 .unionAll q1))
```

---

## 5. Execution Order

Standard SQL execution order:

```
1. FROM     - Compute cross product of tables
2. WHERE    - Filter rows
3. GROUP BY - Group rows
4. HAVING   - Filter groups
5. SELECT   - Compute output expressions
6. DISTINCT - Remove duplicates
7. ORDER BY - Sort results
8. OFFSET   - Skip rows
9. LIMIT    - Limit output
```

Note: Optimizers may reorder internally while preserving semantics.

---

## 6. Integration Points

### 6.1 Parser

```lean
def parseSelectStmt : String → Except String SelectStmt
def parseQuery : String → Except String Query
```

### 6.2 Evaluator

```lean
def evalSelectStmt : Env → SelectStmt → List Row
def evalQuery : Env → Query → List Row
```

### 6.3 Optimizer

```lean
def optimizeQuery : Query → Query
```

Transformations:
- Predicate pushdown
- Join reordering
- Subquery flattening

---

## 7. Testing Strategy

### 7.1 Parsing Tests

```lean
-- Simple SELECT
#guard parseQuery "SELECT * FROM t" = ok expectedAst

-- With WHERE
#guard parseQuery "SELECT x FROM t WHERE y > 5" = ok expectedAst

-- With JOIN
#guard parseQuery "SELECT * FROM a JOIN b ON a.id = b.id" = ok expectedAst
```

### 7.2 Evaluation Tests

```lean
-- Empty table
#guard evalQuery env "SELECT * FROM empty_table" = []

-- Simple filter
#guard evalQuery env "SELECT x FROM t WHERE x > 5" = expectedRows

-- Aggregation
#guard evalQuery env "SELECT COUNT(*) FROM t" = [[count]]
```

### 7.3 Equivalence Tests

```lean
-- Join commutativity
#guard queryEquiv
  "SELECT * FROM a JOIN b ON c"
  "SELECT * FROM b JOIN a ON c"

-- Filter order
#guard queryEquiv
  "SELECT * FROM t WHERE a AND b"
  "SELECT * FROM t WHERE b AND a"
```

---

## 8. Design Decisions

### 8.1 Optional FROM Clause

```lean
fromClause : Option FromClause  -- None for "SELECT 1"
```

Allows queries like:
```sql
SELECT 1 + 1 AS result
SELECT CURRENT_TIMESTAMP
```

### 8.2 Separate SelectStmt and Query

```
SelectStmt - Single SELECT with all clauses
Query      - Adds set operations and CTEs
```

This separation:
- Simplifies SelectStmt structure
- Makes mutual recursion cleaner
- Matches logical SQL structure

### 8.3 Left-Associative Join Parsing

```sql
a JOIN b ON x JOIN c ON y
-- Parses as: (a JOIN b ON x) JOIN c ON y
```

Matches standard SQL precedence rules.

---

## 9. DML Statements

The AST also supports data manipulation (not SELECT):

### 9.1 INSERT

```lean
inductive InsertSource where
  | values : List (List Expr) → InsertSource
  | selectStmt : SelectStmt → InsertSource

structure InsertStmt where
  table   : String
  columns : Option (List String)
  source  : InsertSource
```

### 9.2 UPDATE

```lean
structure Assignment where
  column : String
  value  : Expr

structure UpdateStmt where
  table       : String
  assignments : List Assignment
  whereClause : Option Expr
```

### 9.3 DELETE

```lean
structure DeleteStmt where
  table  : String
  whereClause : Option Expr
```

### 9.4 Statement Type

```lean
inductive Stmt where
  | query  : Query → Stmt
  | insert : InsertStmt → Stmt
  | update : UpdateStmt → Stmt
  | delete : DeleteStmt → Stmt
```

---

## 10. References

- ISO/IEC 9075 SQL Standard, Section 7 (Query expressions)
- ISO/IEC 9075 SQL Standard, Section 14 (Data manipulation)
- Ramakrishnan & Gehrke, "Database Management Systems", Chapters 3-5
