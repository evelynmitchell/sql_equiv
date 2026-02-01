# Semantic Evaluation

## Cleanroom Specification

**Module:** `SqlEquiv/Semantics.lean`
**Status:** Implemented ✅
**Lines:** 1-851

---

## 1. Intended Function

The semantic evaluator defines the meaning of SQL queries by computing their results. This executable semantics enables:
- Testing correctness of queries
- Formal equivalence proofs
- Understanding SQL behavior precisely

### 1.1 Black-Box Specification

```
evalQuery : Database → Query → Table
  Given a database state, compute the result table of a query.

evalExpr : Row → Expr → Option Value
  Evaluate an expression against a row context.

evalStmt : Database → Stmt → Database × Option Table
  Execute a SQL statement, returning updated database and optional result.
```

---

## 2. Core Types

### 2.1 Row

```lean
abbrev Row := List (String × Value)
```

A row is an association list mapping column names to values.

**Example:**
```lean
[("id", Value.int 1), ("name", Value.string "Alice")]
```

### 2.2 Table

```lean
abbrev Table := List Row
```

A table is a list of rows (bag semantics—order matters for ORDER BY, duplicates allowed).

### 2.3 Database

```lean
abbrev Database := String → Table
```

A database maps table names to tables.

---

## 3. Expression Evaluation

### 3.1 Core Evaluator

```
Function: evalExprWithDb
Signature: Database → Row → Expr → Option Value

Purpose: Evaluate expression with database context (for subqueries)

Semantics by constructor:
  lit v         → some v
  col c         → lookup column in row
  binOp op l r  → evalBinOp op (eval l) (eval r)
  unaryOp op e  → evalUnaryOp op (eval e)
  func name args → evalFunc name (map eval args)
  agg fn arg d  → none (needs group context)
  countStar     → none (needs group context)
  case b e      → first true branch or else
  inList e n vs → check if value in list
  inSubquery e n s → check if value in subquery result
  exists n s    → check if subquery returns rows
  subquery s    → return single value from subquery
  between e l h → check if l ≤ e ≤ h
  windowFn f a s → none (needs partition context)
```

### 3.2 Binary Operator Evaluation

```lean
def evalBinOp (op : BinOp) (l r : Option Value) : Option Value
```

| Operation | Behavior |
|-----------|----------|
| add/sub/mul | Integer arithmetic, NULL propagates |
| div/mod | Integer division, NULL or div-by-zero → none |
| eq/ne/lt/le/gt/ge | Three-valued comparison |
| and/or | Three-valued logic with short-circuit |
| concat | String concatenation |
| like | Pattern matching |

**Short-circuit evaluation:**
```
FALSE AND anything → FALSE
TRUE OR anything   → TRUE
```

### 3.3 Unary Operator Evaluation

```lean
def evalUnaryOp (op : UnaryOp) (e : Option Value) : Option Value
```

| Operation | Behavior |
|-----------|----------|
| not | Three-valued NOT |
| neg | Integer negation |
| isNull | TRUE iff value is NULL or missing |
| isNotNull | TRUE iff value is present and not NULL |

### 3.4 Function Evaluation

```lean
def evalFunc (name : String) (args : List (Option Value)) : Option Value
```

**Supported functions:**
| Function | Behavior |
|----------|----------|
| COALESCE | First non-NULL argument |
| NULLIF | NULL if arguments equal, else first |
| ABS | Absolute value |
| LENGTH | String length |
| UPPER | Uppercase |
| LOWER | Lowercase |

---

## 4. Aggregate Evaluation

### 4.1 Aggregate Over Table

```
Function: evalAggOverTable
Signature: Database → AggFunc → Option Expr → Bool → Table → Option Value

Purpose: Compute aggregate function over a group of rows

Parameters:
  db       - Database context
  fn       - Aggregate function (COUNT, SUM, AVG, MIN, MAX)
  argExpr  - Expression to aggregate (None for COUNT(*))
  distinct - Apply DISTINCT before aggregating
  rows     - Group of rows
```

**Aggregate semantics:**

| Function | NULL handling | Empty group |
|----------|---------------|-------------|
| COUNT(col) | Ignores NULLs | 0 |
| COUNT(*) | Counts all | 0 |
| SUM | Ignores NULLs | NULL |
| AVG | Ignores NULLs | NULL |
| MIN | Ignores NULLs | NULL |
| MAX | Ignores NULLs | NULL |

### 4.2 Expression with Aggregates

```lean
partial def evalExprWithAgg (db : Database) (rows : Table) (row : Row) : Expr → Option Value
```

For expressions containing aggregates, evaluate aggregates over the entire group while using a sample row for non-aggregate references.

---

## 5. FROM Clause Evaluation

### 5.1 Core Evaluator

```
Function: evalFrom
Signature: Database → FromClause → Table

Purpose: Compute source rows from FROM clause
```

**By constructor:**

| FromClause | Behavior |
|------------|----------|
| table t | Fetch table, qualify columns with alias |
| subquery s a | Evaluate subquery, qualify with alias |
| join l type r cond | Combine according to join type |

### 5.2 Join Semantics

```
CROSS JOIN: Cartesian product
  |result| = |left| × |right|

INNER JOIN: Matching pairs only
  result = {l ++ r | l ∈ left, r ∈ right, cond(l ++ r) = TRUE}

LEFT JOIN: All left rows, matching right (or NULL)
  For each left row:
    If any right rows match: include all matches
    Else: include left row with NULLs for right columns

RIGHT JOIN: Symmetric to LEFT
  Equivalent to reversing tables and using LEFT JOIN

FULL OUTER JOIN: All rows from both sides
  = LEFT JOIN ∪ (unmatched right rows with NULL left)
```

### 5.3 Column Qualification

When fetching tables, columns are qualified with table name or alias:
```
FROM users u  →  columns become "u.id", "u.name", etc.
FROM users    →  columns become "users.id", "users.name", etc.
```

---

## 6. SELECT Statement Evaluation

### 6.1 Execution Order

```lean
partial def evalSelectWithContext (db : Database) (outerRow : Row) (sel : SelectStmt) : Table
```

**Processing steps:**

```
1. FROM     → Compute base rows from tables/joins
2. WHERE    → Filter rows where condition is TRUE
3. GROUP BY → Partition rows by grouping expressions
4. HAVING   → Filter groups where condition is TRUE
5. SELECT   → Project and compute output columns
6. DISTINCT → Remove duplicate rows
7. ORDER BY → Sort rows
8. OFFSET   → Skip first N rows
9. LIMIT    → Take at most N rows
```

### 6.2 Aggregation Paths

```
Has GROUP BY?
├─ YES → Partition rows into groups
│        Evaluate aggregates per group
│        One output row per group
│
└─ NO → Has aggregates in SELECT?
        ├─ YES → Treat entire result as one group
        │        One output row total (or zero if HAVING fails)
        │
        └─ NO → Has window functions?
                ├─ YES → Compute windows over partitions
                │        One output row per input row
                │
                └─ NO → Simple projection
                        One output row per input row
```

### 6.3 Correlated Subqueries

For correlated subqueries, the outer row context is merged with each base row:

```lean
let baseRowsWithContext : Table := baseRows.map fun row => outerRow ++ row
```

This allows subqueries to reference columns from outer queries.

---

## 7. Window Function Evaluation

### 7.1 Partition and Sort

```lean
partial def partitionRows (db : Database) (rows : Table) (partExprs : List Expr) : List Table
partial def sortPartition (db : Database) (rows : Table) (orderBy : List OrderByItem) : Table
```

**Process:**
1. Partition rows by PARTITION BY expressions
2. Sort each partition by ORDER BY
3. Compute window function for each row within its partition

### 7.2 Ranking Functions

```lean
ROW_NUMBER(): Position in sorted partition (1, 2, 3, ...)
RANK():       Same rank for ties, gaps after (1, 1, 3, ...)
DENSE_RANK(): Same rank for ties, no gaps (1, 1, 2, ...)
```

### 7.3 Aggregate Windows

Window versions of SUM, AVG, MIN, MAX, COUNT compute over the entire partition for each row.

---

## 8. Set Operations

### 8.1 Query Evaluation

```lean
partial def evalQuery (db : Database) : Query → Table
  | .simple sel     → evalSelect db sel
  | .compound l op r → combine (eval l) (eval r) by op
  | .withCTE ctes q → evaluate CTEs, then query
```

### 8.2 Set Operation Semantics

| Operation | Behavior |
|-----------|----------|
| UNION | Concatenate, remove duplicates |
| UNION ALL | Concatenate, keep duplicates |
| INTERSECT | Rows in both results |
| EXCEPT | Rows in left but not right |

### 8.3 Common Table Expressions

```lean
| .withCTE ctes query =>
    let dbWithCtes := ctes.foldl (fun db' cte =>
      fun name =>
        if name == cte.name then evalQuery db' cte.query
        else db' name
    ) db
    evalQuery dbWithCtes query
```

CTEs are evaluated and added to database context before main query.

### 8.4 Recursive CTEs

```lean
partial def evalRecursiveCTE (db : Database) (cteName : String) (cteQuery : Query) : Table
```

Uses fixed-point iteration:
1. Start with empty table
2. Evaluate CTE query with current table
3. If result unchanged, stop (fixed point)
4. Otherwise, repeat with new result
5. Maximum 1000 iterations to prevent infinite loops

---

## 9. DML Statement Evaluation

### 9.1 INSERT

```lean
partial def evalInsert (db : Database) (ins : InsertStmt) : Database
```

**Semantics:**
- Evaluate VALUES expressions or SELECT query
- Append new rows to target table
- Return updated database

### 9.2 UPDATE

```lean
partial def evalUpdate (db : Database) (upd : UpdateStmt) : Database
```

**Semantics:**
- For each row in target table
- If WHERE condition is TRUE (or no WHERE)
- Apply SET assignments to row
- Return updated database

### 9.3 DELETE

```lean
def evalDelete (db : Database) (del : DeleteStmt) : Database
```

**Semantics:**
- Remove rows where condition is TRUE
- No WHERE → delete all rows
- Return updated database

---

## 10. Correctness Conditions

### 10.1 Determinism

```lean
-- Same inputs produce same outputs
theorem eval_deterministic (db : Database) (q : Query) :
  evalQuery db q = evalQuery db q
```

Note: ORDER BY without LIMIT on ties may produce different orderings (implementation-defined).

### 10.2 NULL Handling

```lean
-- NULL comparisons yield UNKNOWN
theorem null_comparison (v : Value) :
  Value.eq (Value.null t) v = none

-- IS NULL correctly detects NULLs
theorem is_null_correct (v : Value) :
  evalUnaryOp .isNull (some v) = some (Value.bool v.isNull)
```

### 10.3 Join Properties

```lean
-- INNER JOIN commutativity (modulo column ordering)
theorem inner_join_comm_rows (db : Database) (a b : FromClause) (cond : Expr) :
  bagEquiv (evalFrom db (join a .inner b cond))
           (evalFrom db (join b .inner a cond))

-- LEFT JOIN + WHERE on right col = INNER JOIN
theorem left_join_filter_inner (db : Database) (a b : FromClause) (joinCond rightPred : Expr) :
  rightPred references right table →
  evalFrom db (join a .left b joinCond) filtered by rightPred =
  evalFrom db (join a .inner b (joinCond AND rightPred))
```

### 10.4 Axioms for Proofs

```lean
-- Evaluation unfolds for literals
axiom evalExprWithDb_lit (db : Database) (row : Row) (v : Value) :
  evalExprWithDb db row (Expr.lit v) = some v

-- Evaluation unfolds for binary operations
axiom evalExprWithDb_binOp (db : Database) (row : Row) (op : BinOp) (l r : Expr) :
  evalExprWithDb db row (Expr.binOp op l r) =
  evalBinOp op (evalExprWithDb db row l) (evalExprWithDb db row r)
```

---

## 11. Testing Strategy

### 11.1 Unit Tests

```lean
-- Literal evaluation
#guard evalExpr [] (Expr.lit (Value.int 42)) = some (Value.int 42)

-- Arithmetic
#guard evalExpr [] (binOp .add (lit (int 1)) (lit (int 2))) = some (Value.int 3)

-- NULL propagation
#guard evalExpr [] (binOp .add (lit (int 1)) (lit (null none))) = none
```

### 11.2 Integration Tests

```lean
-- Full query evaluation
let db := fun name => if name == "t" then [[("x", int 1), ("y", int 2)]] else []
#guard evalQuery db (parse "SELECT x + y FROM t") = [[("expr", int 3)]]
```

### 11.3 Property Tests

```lean
-- WHERE TRUE is identity
∀ db q, evalQuery db (addWhere q TRUE) = evalQuery db q

-- WHERE FALSE yields empty
∀ db q, evalQuery db (addWhere q FALSE) = []
```

---

## 12. Integration Points

### 12.1 With AST

Uses all AST types: `Expr`, `SelectStmt`, `Query`, `Value`, etc.

### 12.2 With Equivalence Checker

```lean
def queryEquiv (db : Database) (q1 q2 : Query) : Bool :=
  evalQuery db q1 == evalQuery db q2
```

### 12.3 With Optimizer

Optimizer transformations must preserve:
```lean
evalQuery db (optimize q) = evalQuery db q
```

---

## 13. Design Decisions

### 13.1 Bag vs Set Semantics

**Choice:** Bag semantics (duplicates allowed)

**Rationale:**
- Matches SQL default behavior (SELECT without DISTINCT)
- UNION ALL preserves duplicates
- DISTINCT explicitly removes duplicates

### 13.2 Partial Functions

Many evaluators return `Option Value` because:
- NULL propagation
- Type mismatches
- Division by zero
- Missing columns

### 13.3 Mutual Recursion

`evalExprWithDb` and `evalSelect` are mutually recursive due to subqueries:
- Expression can contain subquery
- Subquery evaluation uses expression evaluation

The `mutual` block and `partial` keyword handle this.

---

## 14. References

- ISO/IEC 9075 SQL Standard, Section 7 (Query expressions)
- Ramakrishnan & Gehrke, "Database Management Systems", Chapter 5
- Garcia-Molina, Ullman, Widom, "Database Systems: The Complete Book"
