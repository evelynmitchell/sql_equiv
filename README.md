# SQL Equiv

A SQL parser and semantic equivalence prover written in Lean 4. This project provides formal verification of SQL query equivalences, enabling you to prove that two SQL queries produce identical results for all possible databases.

## Overview

SQL Equiv is a comprehensive toolkit for:

- **Parsing SQL** - Full DML support with a hand-rolled recursive descent parser
- **Evaluating queries** - A relational algebra-based semantic model
- **Proving equivalences** - Formal proofs that two SQL expressions/queries are semantically equivalent
- **Custom tactics** - Lean 4 tactics specifically designed for SQL equivalence proofs

The project is designed for compatibility with the Spider benchmark and supports complex SQL features including subqueries, aggregates, joins, and set operations.

## Features

### Full SQL DML Support

- **SELECT statements**: `*`, column lists, aliases, DISTINCT
- **Expressions**: arithmetic, comparisons, boolean logic, CASE/WHEN, BETWEEN, IN, LIKE
- **NULL handling**: Typed NULLs, IS NULL/IS NOT NULL, three-valued logic, NULL propagation
- **Joins**: INNER, LEFT, RIGHT, FULL, CROSS
- **Aggregates**: COUNT, SUM, AVG, MIN, MAX (with DISTINCT support)
- **Subqueries**: Scalar subqueries, IN subqueries, EXISTS, correlated subqueries
- **Set operations**: UNION, UNION ALL, INTERSECT, EXCEPT
- **Clauses**: WHERE, GROUP BY, HAVING, ORDER BY, LIMIT, OFFSET
- **INSERT statements**: VALUES, INSERT...SELECT
- **UPDATE statements**: SET with WHERE conditions
- **DELETE statements**: With WHERE conditions

### Semantic Equivalence Proofs

Define and prove equivalences at multiple levels:

```lean
-- Expression equivalence
def ExprEquiv (e1 e2 : Expr) : Prop :=
  forall row : Row, evalExpr row e1 = evalExpr row e2

-- SELECT statement equivalence
def SelectEquiv (s1 s2 : SelectStmt) : Prop :=
  forall db : Database, evalSelect db s1 = evalSelect db s2

-- Full statement equivalence
def StmtEquiv (s1 s2 : Stmt) : Prop :=
  forall db : Database, evalStmt db s1 = evalStmt db s2
```

### Custom Tactics for SQL Proofs

```lean
-- Automated equivalence proving
example : Expr.binOp .and a b =~e Expr.binOp .and b a := by sql_equiv

-- SQL-specific simplification
example : ... := by sql_simp

-- Reflexivity, symmetry, transitivity
example : a =~e a := by sql_refl
example (h : a =~e b) : b =~e a := by sql_symm; exact h
example (h1 : a =~e b) (h2 : b =~e c) : a =~e c := by sql_trans b <;> assumption
```

### Property-Based Testing

QuickCheck-style testing with random expression generation to validate equivalence properties:

- Random expression generation with depth limits
- Random row/database generation
- Property verification for commutativity, associativity, etc.

## Installation

### Prerequisites

Install Lean 4 using elan:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### Build

```bash
# Clone the repository
git clone <repository-url>
cd sql_equiv

# Build the project
lake build
```

### Run Tests

```bash
# Run the complete test suite
lake exe sql_equiv_test

# Run the demo
lake exe sql_equiv
```

## Usage Examples

### Parsing SQL

```lean
import SqlEquiv

open SqlEquiv

-- Parse a SQL string to AST
def example1 : IO Unit := do
  match parse "SELECT * FROM users WHERE age > 18" with
  | .ok stmt => IO.println s!"Parsed: {stmt.toSql}"
  | .error e => IO.println s!"Error: {e}"

-- Parse specifically a SELECT statement
def example2 : IO Unit := do
  match parseSelectStr "SELECT name, age FROM users" with
  | .ok sel => IO.println s!"Columns: {sel.items.length}"
  | .error e => IO.println s!"Error: {e}"
```

### Evaluating Queries

```lean
import SqlEquiv

open SqlEquiv

def example3 : IO Unit := do
  -- Define a simple database
  let usersTable : Table := [
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30)],
    [("id", .int 2), ("name", .string "Bob"), ("age", .int 25)],
    [("id", .int 3), ("name", .string "Carol"), ("age", .int 35)]
  ]

  let db : Database := fun name =>
    if name == "users" then usersTable else []

  -- Parse and evaluate
  match parseSelectStr "SELECT name FROM users WHERE age > 25" with
  | .ok sel =>
    let result := evalSelect db sel
    IO.println s!"Found {result.length} rows"
    for row in result do
      IO.println s!"  {row}"
  | .error e =>
    IO.println s!"Error: {e}"
```

### Proving Equivalences

```lean
import SqlEquiv

open SqlEquiv

-- Prove AND is commutative
theorem my_and_comm (a b : Expr) :
    Expr.binOp .and a b =~e Expr.binOp .and b a := by
  sql_equiv

-- Prove double negation elimination
theorem my_not_not (e : Expr) :
    Expr.unaryOp .not (Expr.unaryOp .not e) =~e e := by
  sql_equiv

-- Prove WHERE TRUE is equivalent to no WHERE clause
theorem my_where_true (db : Database) (items : List SelectItem) (from_ : Option FromClause) :
    evalSelect db (.mk false items from_ (some (.lit (.bool true))) [] none [] none none) =
    evalSelect db (.mk false items from_ none [] none [] none none) := by
  exact where_true_elim db items from_ [] none [] none none
```

### Using the sql_equiv Tactic

```lean
import SqlEquiv
import SqlEquiv.Tactics

open SqlEquiv

variable (a b c : Expr)

-- Basic commutativity
example : Expr.binOp .and a b =~e Expr.binOp .and b a := by sql_equiv
example : Expr.binOp .or a b =~e Expr.binOp .or b a := by sql_equiv
example : Expr.binOp .add a b =~e Expr.binOp .add b a := by sql_equiv
example : Expr.binOp .mul a b =~e Expr.binOp .mul b a := by sql_equiv

-- Double negation
example : Expr.unaryOp .not (Expr.unaryOp .not a) =~e a := by sql_equiv

-- Using transitivity
example (h1 : a =~e b) (h2 : b =~e c) : a =~e c := by
  sql_trans b
  . exact h1
  . exact h2
```

## Architecture

### Module Overview

| Module | Description |
|--------|-------------|
| `SqlEquiv.Ast` | Abstract Syntax Tree definitions for all SQL constructs |
| `SqlEquiv.Parser` | Hand-rolled recursive descent parser with tokenizer |
| `SqlEquiv.Pretty` | Pretty printer for converting AST back to SQL strings |
| `SqlEquiv.Semantics` | Relational algebra-based evaluation model |
| `SqlEquiv.Equiv` | Equivalence definitions and core theorems |
| `SqlEquiv.Tactics` | Custom Lean 4 tactics for SQL proofs |
| `SqlEquiv.Basic` | Re-exports all modules for convenience |

### Key Types

```lean
-- SQL types for typed NULLs
inductive SqlType where
  | int | string | bool | unknown

-- Three-valued logic (TRUE, FALSE, UNKNOWN)
inductive Trilean where
  | true | false | unknown

-- Values with typed NULLs
inductive Value where
  | int    : Int -> Value
  | string : String -> Value
  | bool   : Bool -> Value
  | null   : Option SqlType -> Value  -- typed NULL (none = unknown type)

-- Expressions
inductive Expr where
  | lit       : Value -> Expr
  | col       : ColumnRef -> Expr
  | binOp     : BinOp -> Expr -> Expr -> Expr
  | unaryOp   : UnaryOp -> Expr -> Expr
  | func      : String -> List Expr -> Expr
  | agg       : AggFunc -> Option Expr -> Bool -> Expr
  | countStar : Expr
  | case      : List (Expr * Expr) -> Option Expr -> Expr
  | inList    : Expr -> Bool -> List Expr -> Expr
  | inSubquery: Expr -> Bool -> SelectStmt -> Expr
  | exists    : Bool -> SelectStmt -> Expr
  | subquery  : SelectStmt -> Expr
  | between   : Expr -> Expr -> Expr -> Expr

-- Statements
inductive Stmt where
  | query  : Query -> Stmt
  | insert : InsertStmt -> Stmt
  | update : UpdateStmt -> Stmt
  | delete : DeleteStmt -> Stmt
```

### Semantic Model

- **Row**: `List (String * Value)` - A mapping from column names to values
- **Table**: `List Row` - A collection of rows (bag semantics)
- **Database**: `String -> Table` - A mapping from table names to tables

## Available Theorems

### Expression Equivalence Properties

| Theorem | Description |
|---------|-------------|
| `expr_equiv_refl` | Reflexivity: `e =~e e` |
| `expr_equiv_symm` | Symmetry: `e1 =~e e2 -> e2 =~e e1` |
| `expr_equiv_trans` | Transitivity: `e1 =~e e2 -> e2 =~e e3 -> e1 =~e e3` |

### Commutativity

| Theorem | Description |
|---------|-------------|
| `and_comm` | `(a AND b) =~e (b AND a)` |
| `or_comm` | `(a OR b) =~e (b OR a)` |
| `add_comm` | `(a + b) =~e (b + a)` |
| `mul_comm` | `(a * b) =~e (b * a)` |
| `eq_comm` | `(a = b) =~e (b = a)` |

### Associativity

| Theorem | Description |
|---------|-------------|
| `and_assoc` | `((a AND b) AND c) =~e (a AND (b AND c))` |
| `or_assoc` | `((a OR b) OR c) =~e (a OR (b OR c))` |

### De Morgan's Laws

| Theorem | Description |
|---------|-------------|
| `not_and` | `NOT (a AND b) =~e (NOT a OR NOT b)` |
| `not_or` | `NOT (a OR b) =~e (NOT a AND NOT b)` |

### Distributivity

| Theorem | Description |
|---------|-------------|
| `and_or_distrib_left` | `a AND (b OR c) =~e (a AND b) OR (a AND c)` |
| `and_or_distrib_right` | `(a OR b) AND c =~e (a AND c) OR (b AND c)` |
| `or_and_distrib_left` | `a OR (b AND c) =~e (a OR b) AND (a OR c)` |
| `or_and_distrib_right` | `(a AND b) OR c =~e (a OR c) AND (b OR c)` |

### Absorption Laws

| Theorem | Description |
|---------|-------------|
| `and_absorb_or` | `a AND (a OR b) =~e a` |
| `or_absorb_and` | `a OR (a AND b) =~e a` |

### Identity Laws

| Theorem | Description |
|---------|-------------|
| `and_true` | `a AND TRUE =~e a` |
| `or_false` | `a OR FALSE =~e a` |
| `and_false` | `a AND FALSE =~e FALSE` |
| `or_true` | `a OR TRUE =~e TRUE` |

### NULL Handling (IS NULL Laws)

| Theorem | Description |
|---------|-------------|
| `is_null_on_null` | `IS NULL` on NULL returns TRUE |
| `is_null_on_int/string/bool` | `IS NULL` on non-NULL returns FALSE |
| `is_not_null_on_null` | `IS NOT NULL` on NULL returns FALSE |
| `is_not_null_on_int/string/bool` | `IS NOT NULL` on non-NULL returns TRUE |
| `is_null_is_not_null_complement` | `IS NULL` and `IS NOT NULL` are complementary |

### NULL Propagation

| Theorem | Description |
|---------|-------------|
| `null_add_left/right` | `NULL + x = NULL`, `x + NULL = NULL` |
| `null_sub_left/right` | `NULL - x = NULL`, `x - NULL = NULL` |
| `null_mul_left/right` | `NULL * x = NULL`, `x * NULL = NULL` |
| `null_div_left/right` | `NULL / x = NULL`, `x / NULL = NULL` |
| `null_eq_left/right` | `NULL = x = NULL` (comparison returns unknown) |
| `null_ne_left/right` | `NULL <> x = NULL` |
| `null_lt_left/right` | `NULL < x = NULL` |

### Three-Valued Logic (NULL in Boolean Operations)

| Theorem | Description |
|---------|-------------|
| `false_and_null` | `FALSE AND NULL = FALSE` (FALSE dominates) |
| `null_and_false` | `NULL AND FALSE = FALSE` |
| `true_and_null` | `TRUE AND NULL = NULL` (propagates unknown) |
| `true_or_null` | `TRUE OR NULL = TRUE` (TRUE dominates) |
| `false_or_null` | `FALSE OR NULL = NULL` (propagates unknown) |
| `null_and_null` | `NULL AND NULL = NULL` |
| `null_or_null` | `NULL OR NULL = NULL` |

### Trilean Properties

| Theorem | Description |
|---------|-------------|
| `trilean_not_not` | Trilean NOT is self-inverse |
| `trilean_and_comm` | Trilean AND is commutative |
| `trilean_or_comm` | Trilean OR is commutative |
| `trilean_and_true/false` | Identity and annihilation laws |
| `trilean_or_true/false` | Identity and annihilation laws |
| `trilean_de_morgan_and` | `NOT (a AND b) = (NOT a) OR (NOT b)` |
| `trilean_de_morgan_or` | `NOT (a OR b) = (NOT a) AND (NOT b)` |

### Other

| Theorem | Description |
|---------|-------------|
| `not_not` | `NOT (NOT e) =~e e` |
| `where_true_elim` | `SELECT ... WHERE TRUE` equals `SELECT ...` |
| `where_false_empty` | `SELECT ... WHERE FALSE` returns empty |
| `join_comm` | INNER JOIN is commutative (row membership) |

## Contributing

### Adding New Equivalences

1. **Define the theorem** in `SqlEquiv/Equiv.lean`:

```lean
theorem my_new_theorem (a b : Expr) :
    Expr.binOp .someOp a b =~e Expr.binOp .someOp b a := by
  intro row
  -- Your proof here
  sorry
```

2. **Add tests** in `Test/EquivTest.lean`:

```lean
-- Compile-time verification
#check @my_new_theorem

-- Runtime test
def myTests : List TestResult := [
  testSyntacticEquiv "my_test"
    (.binOp .someOp (col "x") (col "y"))
    (.binOp .someOp (col "y") (col "x"))
]
```

3. **Add property tests** in `Test/PropertyTest.lean` for random testing.

### Adding New SQL Features

1. **Extend the AST** in `SqlEquiv/Ast.lean`
2. **Extend the parser** in `SqlEquiv/Parser.lean`
3. **Extend the pretty printer** in `SqlEquiv/Pretty.lean`
4. **Extend the semantics** in `SqlEquiv/Semantics.lean`
5. **Add tests** in the appropriate test file

### Running Tests

```bash
# Build and run all tests
lake build && lake exe sql_equiv_test
```

## Project Structure

```
sql_equiv/
+-- SqlEquiv/
|   +-- Ast.lean          # AST definitions
|   +-- Parser.lean       # SQL parser
|   +-- Pretty.lean       # Pretty printer
|   +-- Semantics.lean    # Evaluation model
|   +-- Equiv.lean        # Equivalence proofs
|   +-- Tactics.lean      # Custom tactics
|   +-- Basic.lean        # Re-exports
+-- Test/
|   +-- Common.lean       # Test infrastructure
|   +-- ParserTest.lean   # Parser tests
|   +-- SemanticsTest.lean# Semantics tests
|   +-- EquivTest.lean    # Equivalence tests
|   +-- PropertyTest.lean # Property-based tests
|   +-- Main.lean         # Test runner
+-- Main.lean             # Demo application
+-- lakefile.toml         # Lake build config
+-- README.md             # This file
```

## Dependencies

- [Lean 4](https://lean-lang.org/) - The programming language and theorem prover
- [Batteries](https://github.com/leanprover-community/batteries) - Standard library extensions

## License

MIT License

Copyright (c) 2024

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
