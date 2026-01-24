# SQL Parser & Equivalence Prover in Lean 4

A formally verified SQL parser and semantic equivalence prover written in Lean 4. This project demonstrates how to use dependent types and theorem proving to reason about SQL query equivalence.

## Features

### SQL Parser
- Full DML support: SELECT, INSERT, UPDATE, DELETE
- JOIN types: INNER, LEFT, RIGHT, FULL, CROSS
- Clauses: WHERE, GROUP BY, HAVING, ORDER BY, LIMIT, OFFSET
- Expressions: arithmetic, comparison, logical operators
- Advanced: CASE, IN, BETWEEN, LIKE, function calls
- Hand-rolled recursive descent parser with proper operator precedence

### Semantic Evaluation Model
- Relational algebra semantics with bag (multiset) model
- Full SQL evaluation pipeline
- NULL handling following SQL semantics
- Expression evaluation with short-circuit logic

### Formal Equivalence Framework
- **Expression Equivalence**: `e1 ≃ₑ e2` iff they evaluate the same for all rows
- **Select Equivalence**: `s1 ≃ₛ s2` iff they produce same results for all databases
- **Statement Equivalence**: `s1 ≃ s2` iff they have same effect on all databases
- Proven reflexivity, symmetry, and transitivity for all equivalence relations

### Syntactic Equivalence via Normalization
- Canonical form normalization for decidable equivalence checking
- Detects commutativity of AND, OR, +, *
- Double negation elimination

## Project Structure

```
sql_equiv/
├── SqlEquiv/
│   ├── Ast.lean        # Core AST types (Value, Expr, SelectStmt, etc.)
│   ├── Parser.lean     # Tokenizer + recursive descent parser
│   ├── Pretty.lean     # AST → SQL string pretty printer
│   ├── Semantics.lean  # Evaluation model (Row, Table, Database, eval*)
│   ├── Equiv.lean      # Equivalence definitions and proofs
│   └── Basic.lean      # Module re-exports
├── SqlEquiv.lean       # Main library module
├── Main.lean           # Demo program
├── lakefile.toml       # Lake build configuration
└── lean-toolchain      # Lean version specification
```

## Building

Requires [Lean 4](https://lean-lang.org/) installed via [elan](https://github.com/leanprover/elan).

```bash
# Build the project
lake build

# Run the demo
.lake/build/bin/sql_equiv
```

## Demo Output

```
╔═══════════════════════════════════╗
║  SQL Parser & Equivalence Prover  ║
║          in Lean 4                ║
╚═══════════════════════════════════╝

Input:  SELECT * FROM users WHERE age > 18
Output: SELECT * FROM users WHERE (age > 18)

Input:  SELECT u.name, o.total FROM users u INNER JOIN orders o ON u.id = o.user_id
Output: SELECT u.name, o.total FROM users AS u INNER JOIN orders AS o ON (u.id = o.user_id)

═══════════════════════════════════
SQL Evaluation Demo
═══════════════════════════════════
Query: SELECT name, age FROM users WHERE age > 25
Result: 2 rows
  name='Alice', age=30
  name='Carol', age=35

═══════════════════════════════════
Syntactic Equivalence via Normalization
═══════════════════════════════════
Is '(x AND y)' ≡ '(y AND x)'? true
Is '(x + 1)' ≡ '(1 + x)'? true
```

## Key Types

```lean
-- SQL Values
inductive Value where
  | int : Int → Value
  | string : String → Value
  | bool : Bool → Value
  | null : Value

-- SQL Expressions
inductive Expr where
  | lit : Value → Expr
  | col : ColumnRef → Expr
  | binOp : BinOp → Expr → Expr → Expr
  | unaryOp : UnaryOp → Expr → Expr
  | func : String → List Expr → Expr
  | case : List (Expr × Expr) → Option Expr → Expr
  | inList : Expr → List Expr → Expr
  | between : Expr → Expr → Expr → Expr

-- Semantic types
abbrev Row := List (String × Value)
abbrev Table := List Row
abbrev Database := String → Table

-- Equivalence definition
def ExprEquiv (e1 e2 : Expr) : Prop :=
  ∀ row : Row, evalExpr row e1 = evalExpr row e2
```

## License

MIT
