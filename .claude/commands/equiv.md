# /equiv

Test SQL query equivalence.

## Usage

- `/equiv` - Describe two queries to test for equivalence
- `/equiv check` - Check a specific equivalence claim in the codebase

## Instructions

Help the user test whether two SQL expressions are equivalent.

### Interactive Mode

1. Ask the user to describe the two SQL queries or expressions
2. Help formulate them in the project's AST representation
3. Either:
   - Write a test case to check equivalence
   - Attempt to prove equivalence if it holds
   - Find a counterexample if it doesn't hold

### Checking Existing Claims

1. Find equivalence theorems in the codebase:
   ```
   Look in SQLEquiv/ for theorems about expression equivalence
   ```

2. Verify they typecheck:
   ```bash
   source ~/.elan/env && lake build
   ```

### Common Equivalences

- Filter commutativity: `filter p (filter q t) = filter q (filter p t)`
- Filter-project: When filter doesn't use projected-away columns
- Join commutativity: For inner joins
- Predicate pushdown: Moving filters closer to base tables

### Example

User: "Is `SELECT * FROM t WHERE a=1 AND b=2` equivalent to `SELECT * FROM t WHERE b=2 AND a=1`?"

This is filter commutativity - the order of AND conditions doesn't matter.
Look for a theorem like `filter_and_comm` or help prove it.
