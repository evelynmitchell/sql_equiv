# Expression AST

## Cleanroom Specification

**Module:** `SqlEquiv/Ast.lean` (Expr, BinOp, UnaryOp, AggFunc, etc.)
**Status:** Implemented ✅
**Lines:** 152-250

---

## 1. Intended Function

The Expression AST represents all SQL expressions: literals, column references, operators, function calls, aggregates, subqueries, and more. This is the core building block for WHERE clauses, SELECT lists, and JOIN conditions.

### 1.1 Black-Box Specification

```
Expr : Type
  Abstract syntax tree for SQL expressions, supporting:
  - Literals and column references
  - Binary and unary operators
  - Aggregate and scalar functions
  - CASE expressions
  - IN lists and subqueries
  - EXISTS predicates
  - BETWEEN expressions
  - Window functions
```

---

## 2. Supporting Types

### 2.1 Column Reference

```lean
structure ColumnRef where
  table  : Option String   -- Optional table qualifier
  column : String          -- Column name
  deriving Repr, BEq, Inhabited, DecidableEq
```

**Examples:**
- `ColumnRef.mk none "id"` → `id`
- `ColumnRef.mk (some "users") "name"` → `users.name`

### 2.2 Binary Operators

```lean
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
```

**Operator Mapping:**
| BinOp | SQL Syntax | Returns |
|-------|------------|---------|
| add | `+` | Numeric |
| sub | `-` | Numeric |
| mul | `*` | Numeric |
| div | `/` | Numeric |
| mod | `%` | Numeric |
| eq | `=` | Trilean |
| ne | `<>`, `!=` | Trilean |
| lt | `<` | Trilean |
| le | `<=` | Trilean |
| gt | `>` | Trilean |
| ge | `>=` | Trilean |
| and | `AND` | Trilean |
| or | `OR` | Trilean |
| concat | `\|\|` | String |
| like | `LIKE` | Trilean |

### 2.3 Unary Operators

```lean
inductive UnaryOp where
  | not       -- Logical NOT
  | neg       -- Arithmetic negation
  | isNull    -- IS NULL predicate
  | isNotNull -- IS NOT NULL predicate
  deriving Repr, BEq, Inhabited, DecidableEq
```

### 2.4 Aggregate Functions

```lean
inductive AggFunc where
  | count | sum | avg | min | max
  deriving Repr, BEq, Inhabited, DecidableEq
```

### 2.5 Window Functions

```lean
inductive WindowFunc where
  | rowNumber | rank | denseRank
  | sum | avg | min | max | count
  deriving Repr, BEq, Inhabited, DecidableEq
```

---

## 3. Expression Type

### 3.1 Full Definition

```lean
inductive Expr where
  | lit       : Value → Expr
  | col       : ColumnRef → Expr
  | binOp     : BinOp → Expr → Expr → Expr
  | unaryOp   : UnaryOp → Expr → Expr
  | func      : String → List Expr → Expr
  | agg       : AggFunc → Option Expr → Bool → Expr
  | countStar : Expr
  | «case»    : List (Expr × Expr) → Option Expr → Expr
  | inList    : Expr → Bool → List Expr → Expr
  | inSubquery : Expr → Bool → SelectStmt → Expr
  | exists    : Bool → SelectStmt → Expr
  | subquery  : SelectStmt → Expr
  | between   : Expr → Expr → Expr → Expr
  | windowFn  : WindowFunc → Option Expr → WindowSpec → Expr
```

### 3.2 Constructor Specifications

#### 3.2.1 Literals

```
Constructor: Expr.lit
Arguments: Value → Expr

Purpose: Embed a literal value in an expression

Examples:
  lit (Value.int 42)       -- 42
  lit (Value.string "hi")  -- 'hi'
  lit (Value.bool true)    -- TRUE
  lit (Value.null none)    -- NULL
```

#### 3.2.2 Column References

```
Constructor: Expr.col
Arguments: ColumnRef → Expr

Purpose: Reference a column (optionally table-qualified)

Examples:
  col ⟨none, "id"⟩              -- id
  col ⟨some "t", "name"⟩        -- t.name
```

#### 3.2.3 Binary Operations

```
Constructor: Expr.binOp
Arguments: BinOp → Expr → Expr → Expr

Purpose: Binary operation on two expressions

Examples:
  binOp .add (lit (int 1)) (lit (int 2))        -- 1 + 2
  binOp .eq (col ⟨none, "x"⟩) (lit (int 5))     -- x = 5
  binOp .and expr1 expr2                         -- expr1 AND expr2
```

#### 3.2.4 Unary Operations

```
Constructor: Expr.unaryOp
Arguments: UnaryOp → Expr → Expr

Purpose: Unary operation on an expression

Examples:
  unaryOp .not (col ⟨none, "flag"⟩)              -- NOT flag
  unaryOp .neg (lit (int 5))                     -- -5
  unaryOp .isNull (col ⟨none, "x"⟩)              -- x IS NULL
  unaryOp .isNotNull (col ⟨none, "x"⟩)           -- x IS NOT NULL
```

#### 3.2.5 Function Calls

```
Constructor: Expr.func
Arguments: String → List Expr → Expr

Purpose: Scalar function call with arguments

Examples:
  func "UPPER" [col ⟨none, "name"⟩]              -- UPPER(name)
  func "COALESCE" [col ⟨none, "x"⟩, lit (int 0)] -- COALESCE(x, 0)
  func "LENGTH" [lit (string "hello")]           -- LENGTH('hello')
```

#### 3.2.6 Aggregate Functions

```
Constructor: Expr.agg
Arguments: AggFunc → Option Expr → Bool → Expr
           (function)  (expression)  (distinct?)

Purpose: Aggregate function call

Examples:
  agg .count (some (col ⟨none, "id"⟩)) false     -- COUNT(id)
  agg .count (some (col ⟨none, "id"⟩)) true      -- COUNT(DISTINCT id)
  agg .sum (some (col ⟨none, "amount"⟩)) false   -- SUM(amount)
  agg .avg (some (col ⟨none, "price"⟩)) false    -- AVG(price)
  agg .max (some (col ⟨none, "score"⟩)) false    -- MAX(score)
```

#### 3.2.7 COUNT(*)

```
Constructor: Expr.countStar
Arguments: (none)

Purpose: COUNT(*) - counts all rows including NULLs

Example:
  countStar                                       -- COUNT(*)
```

**Note:** Separate constructor because `COUNT(*)` has no expression argument and counts NULLs, unlike `COUNT(column)`.

#### 3.2.8 CASE Expressions

```
Constructor: Expr.case
Arguments: List (Expr × Expr) → Option Expr → Expr
           (when/then pairs)    (else branch)

Purpose: CASE WHEN ... THEN ... ELSE ... END

Examples:
  case [(cond1, result1), (cond2, result2)] (some default)
  -- CASE WHEN cond1 THEN result1 WHEN cond2 THEN result2 ELSE default END

  case [(cond, result)] none
  -- CASE WHEN cond THEN result END (no ELSE → NULL)
```

#### 3.2.9 IN List

```
Constructor: Expr.inList
Arguments: Expr → Bool → List Expr → Expr
           (expr)  (negated?)  (values)

Purpose: expr [NOT] IN (value1, value2, ...)

Examples:
  inList (col ⟨none, "x"⟩) false [lit (int 1), lit (int 2)]
  -- x IN (1, 2)

  inList (col ⟨none, "x"⟩) true [lit (int 1), lit (int 2)]
  -- x NOT IN (1, 2)
```

#### 3.2.10 IN Subquery

```
Constructor: Expr.inSubquery
Arguments: Expr → Bool → SelectStmt → Expr
           (expr)  (negated?)  (subquery)

Purpose: expr [NOT] IN (SELECT ...)

Examples:
  inSubquery (col ⟨none, "id"⟩) false subq
  -- id IN (SELECT ...)

  inSubquery (col ⟨none, "id"⟩) true subq
  -- id NOT IN (SELECT ...)
```

#### 3.2.11 EXISTS

```
Constructor: Expr.exists
Arguments: Bool → SelectStmt → Expr
           (negated?)  (subquery)

Purpose: [NOT] EXISTS (SELECT ...)

Examples:
  exists false subq    -- EXISTS (SELECT ...)
  exists true subq     -- NOT EXISTS (SELECT ...)
```

#### 3.2.12 Scalar Subquery

```
Constructor: Expr.subquery
Arguments: SelectStmt → Expr

Purpose: Scalar subquery (must return exactly one row, one column)

Example:
  subquery subq        -- (SELECT max(x) FROM t)
```

**Runtime constraint:** Subquery must return at most one row.

#### 3.2.13 BETWEEN

```
Constructor: Expr.between
Arguments: Expr → Expr → Expr → Expr
           (value)  (low)   (high)

Purpose: value BETWEEN low AND high

Equivalent to: value >= low AND value <= high

Example:
  between (col ⟨none, "x"⟩) (lit (int 1)) (lit (int 10))
  -- x BETWEEN 1 AND 10
```

#### 3.2.14 Window Functions

```
Constructor: Expr.windowFn
Arguments: WindowFunc → Option Expr → WindowSpec → Expr
           (function)   (argument)    (OVER clause)

Purpose: Window function with OVER clause

Examples:
  windowFn .rowNumber none (WindowSpec.mk [] [orderBy])
  -- ROW_NUMBER() OVER (ORDER BY ...)

  windowFn .sum (some (col ⟨none, "amount"⟩)) (WindowSpec.mk [partition] [])
  -- SUM(amount) OVER (PARTITION BY ...)
```

---

## 4. Window Specification

```lean
inductive WindowSpec where
  | mk : List Expr →        -- PARTITION BY expressions
         List OrderByItem → -- ORDER BY items
         WindowSpec
```

**Example:**
```sql
SUM(amount) OVER (PARTITION BY customer_id ORDER BY date ASC)
```
becomes:
```lean
windowFn .sum (some amount) (WindowSpec.mk [customer_id] [OrderByItem.mk date .asc])
```

---

## 5. Correctness Conditions

### 5.1 Well-Formedness

```lean
-- Column references must be valid for evaluation context
def Expr.wellFormed (ctx : Context) : Expr → Bool

-- Aggregates only in appropriate contexts (SELECT, HAVING, not WHERE)
def Expr.noAggregates : Expr → Bool

-- Subqueries must be valid SelectStmts
def SelectStmt.valid : SelectStmt → Bool
```

### 5.2 Expression Equivalence

```lean
-- Structural equality
theorem expr_eq_refl (e : Expr) : e = e

-- Semantic equivalence (evaluated to same value in all contexts)
def Expr.semanticEquiv (e1 e2 : Expr) : Prop :=
  ∀ env row, eval env row e1 = eval env row e2
```

### 5.3 Normalization Properties

```lean
-- De Morgan's laws preserved
theorem demorgan_and (a b : Expr) :
  normalize (unaryOp .not (binOp .and a b)) =
  normalize (binOp .or (unaryOp .not a) (unaryOp .not b))

-- Double negation elimination
theorem double_neg (e : Expr) :
  normalize (unaryOp .not (unaryOp .not e)) = normalize e

-- BETWEEN expansion
theorem between_expand (v lo hi : Expr) :
  semanticEquiv (between v lo hi) (binOp .and (binOp .ge v lo) (binOp .le v hi))
```

---

## 6. SQL Semantics

### 6.1 Evaluation Order

Binary operators evaluate left-to-right:
```
binOp op e1 e2  →  first evaluate e1, then e2, then apply op
```

Short-circuit evaluation for AND/OR:
```
binOp .and false _ → false (don't evaluate right)
binOp .or true _   → true (don't evaluate right)
```

### 6.2 NULL Propagation

Most operations propagate NULL:
```
NULL + 1     → NULL
NULL = NULL  → UNKNOWN
NULL AND x   → FALSE or UNKNOWN (depends on x)
```

Exceptions:
- `IS NULL`, `IS NOT NULL` — always return TRUE/FALSE
- `COALESCE` — returns first non-NULL
- `AND FALSE` — always FALSE
- `OR TRUE` — always TRUE

### 6.3 Aggregate NULL Handling

| Function | NULL behavior |
|----------|---------------|
| COUNT(col) | Ignores NULLs |
| COUNT(*) | Counts all rows |
| SUM/AVG | Ignores NULLs |
| MIN/MAX | Ignores NULLs |
| All | Empty group → NULL (except COUNT → 0) |

---

## 7. Integration Points

### 7.1 Parser

```lean
-- Parser produces Expr from SQL text
def parseExpr : String → Except String Expr
```

### 7.2 Evaluator

```lean
-- Evaluator computes Value from Expr
def evalExpr : Env → Row → Expr → Value
```

### 7.3 Normalizer

```lean
-- Normalizer simplifies expressions
def normalize : Expr → Expr
```

### 7.4 Optimizer

```lean
-- Optimizer transforms for efficiency
def optimizeExpr : Expr → Expr
```

---

## 8. Testing Strategy

### 8.1 Constructor Tests

```lean
-- Each constructor parses and prints correctly
#guard parseExpr "42" = ok (lit (int 42))
#guard parseExpr "x" = ok (col ⟨none, "x"⟩)
#guard parseExpr "1 + 2" = ok (binOp .add (lit (int 1)) (lit (int 2)))
#guard parseExpr "NOT x" = ok (unaryOp .not (col ⟨none, "x"⟩))
```

### 8.2 Semantic Tests

```lean
-- Evaluation produces correct values
#guard evalExpr env row (lit (int 42)) = Value.int 42
#guard evalExpr env row (binOp .add (lit (int 1)) (lit (int 2))) = Value.int 3
```

### 8.3 Equivalence Tests

```lean
-- Known equivalences hold
#guard semanticEquiv (between x lo hi) (binOp .and (binOp .ge x lo) (binOp .le x hi))
#guard semanticEquiv (inList x false [a, b]) (binOp .or (binOp .eq x a) (binOp .eq x b))
```

---

## 9. Mutual Recursion Note

`Expr` is mutually recursive with `SelectStmt` through:
- `Expr.inSubquery` — contains SelectStmt
- `Expr.exists` — contains SelectStmt
- `Expr.subquery` — contains SelectStmt

This requires Lean's `mutual` block:
```lean
mutual
  inductive Expr where ...
  inductive SelectStmt where ...
end
```

The `partial` keyword is used for recursive functions over these types.

---

## 10. References

- ISO/IEC 9075 SQL Standard, Section 6 (Scalar expressions)
- ISO/IEC 9075 SQL Standard, Section 7 (Query expressions)
- Ramakrishnan & Gehrke, "Database Management Systems", Chapter 5
