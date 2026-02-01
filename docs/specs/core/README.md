# Core Cleanroom Specifications

This directory contains Cleanroom-style specifications for the implemented SQL features in sql_equiv.

## Purpose

These specifications document:
- **What** each module does (black-box behavior)
- **How** it's implemented (data structures, algorithms)
- **Why** design decisions were made
- **Correctness conditions** that must hold
- **Testing strategies** for verification

## Specification Index

| Spec | Module | Description |
|------|--------|-------------|
| [THREE_VALUED_LOGIC.md](THREE_VALUED_LOGIC.md) | `Ast.lean` (Trilean) | SQL's TRUE/FALSE/UNKNOWN logic |
| [SQL_VALUE_SYSTEM.md](SQL_VALUE_SYSTEM.md) | `Ast.lean` (Value) | Typed values and NULL representation |
| [EXPRESSION_AST.md](EXPRESSION_AST.md) | `Ast.lean` (Expr) | Expression abstract syntax tree |
| [SELECT_STATEMENT.md](SELECT_STATEMENT.md) | `Ast.lean` (SelectStmt) | SELECT, FROM, JOIN, Query types |
| [SEMANTIC_EVALUATION.md](SEMANTIC_EVALUATION.md) | `Semantics.lean` | Query evaluation engine |
| [PARSER.md](PARSER.md) | `Parser.lean` | SQL text to AST transformation |

## Reading Order

For understanding the codebase, read in this order:

1. **THREE_VALUED_LOGIC** - Foundation for NULL handling
2. **SQL_VALUE_SYSTEM** - How values are represented
3. **EXPRESSION_AST** - Building blocks for queries
4. **SELECT_STATEMENT** - Query structure
5. **SEMANTIC_EVALUATION** - How queries execute
6. **PARSER** - How SQL text becomes AST

## Specification Format

Each spec follows the Cleanroom methodology:

```
1. Intended Function    - What the module does
2. Data Types          - Core type definitions
3. Operations          - Function specifications
4. Correctness         - Theorems that must hold
5. Integration         - How it connects to other modules
6. Testing Strategy    - How to verify correctness
7. Design Decisions    - Rationale for choices
8. References          - SQL standards, papers
```

## Related Documentation

- **Future features**: See `docs/specs/` for optimizer feature specifications
- **Tutorials**: See `docs/tutorials/` for guided learning
- **Coverage matrix**: See `docs/COVERAGE_MATRIX.md` for documentation status
