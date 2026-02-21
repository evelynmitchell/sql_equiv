# /lspec-test

Add LSpec property tests for existing theorems using SlimCheck generators.

## Usage

- `/lspec-test <theorem-name>` — Generate a property test for the specified theorem

## Instructions

### Background

LSpec property tests live in `LSpecTests/` and use SlimCheck for random generation. Each test checks that a theorem's statement holds on random inputs by evaluating both sides and comparing with `==`.

### Steps

1. **Find the theorem** in `SqlEquiv/Equiv/`. Read its statement to understand:
   - What types are involved (Expr, Value, Option Value, etc.)
   - What preconditions exist (if any)
   - What the equality/property claims

2. **Choose the right generator** from `LSpecTests/Generators.lean`:

   | Type | Generator | Use when |
   |------|-----------|----------|
   | `BoundedGroundExpr` | General ground expressions (no columns) | Boolean algebra, general properties |
   | `BoolGroundExpr` | Boolean-valued ground expressions | AND/OR/NOT properties |
   | `IntGroundExpr` | Integer-valued ground expressions | Arithmetic identity properties |
   | `ColumnGroundExpr` | Expressions with column refs x/y/z | Row-dependent properties |
   | `Value` | Random values (int/string/bool/null) | Value-level properties (evalBinOp, evalFunc) |
   | `Option SqlType` | Random typed nulls | NULL propagation with typed nulls |

3. **Choose the right test file:**

   | Category | File |
   |----------|------|
   | Boolean algebra, arithmetic, expression equivalence | `LSpecTests/ExprAlgebra.lean` |
   | NULL propagation, three-valued logic, IS NULL | `LSpecTests/NullSemantics.lean` |
   | Database/query-level properties | `LSpecTests/EdgeCaseDb.lean` |

4. **Write the test** using this pattern:
   ```lean
   check (cfg := cfg) "theorem_name description" (∀ v1 : Gen1, v2 : Gen2,
     LHS == RHS) $
   ```

   - For expression-level theorems, use `evalExpr [] expr` (empty row for ground exprs)
   - For value-level theorems, use `evalBinOp`/`evalUnaryOp`/`evalFunc` directly
   - Chain tests with `$` operator

5. **Add the test to the group function** in the same file. Tests are organized in named groups:
   ```lean
   def myTests (cfg : Configuration) : TestSeq :=
     check (cfg := cfg) "test1" (...) $
     check (cfg := cfg) "test2" (...) $
     done
   ```

6. **Wire the group into `allTests`** if it's a new group:
   ```lean
   def allTests (cfg : Configuration) : TestSeq :=
     group "Existing Group" (existingTests cfg) $
     group "New Group" (myTests cfg) $
     done
   ```

7. **Build and run:**
   ```bash
   lake build lspec_tests && lake exe lspec_tests
   ```
   For quick iteration: `LSPEC_SAMPLES=100 lake exe lspec_tests`

### Examples

**Value-level NULL propagation (NullSemantics.lean):**
```lean
check (cfg := cfg) "NULL + x = NULL" (∀ v : Value,
  evalBinOp .add (some (.null none)) (some v) == some (.null none)) $
```

**Expression-level boolean algebra (ExprAlgebra.lean):**
```lean
check (cfg := cfg) "AND commutes" (∀ a b : BoundedGroundExpr,
  evalExpr [] (.binOp .and a.expr b.expr) == evalExpr [] (.binOp .and b.expr a.expr)) $
```

**Three-valued logic with typed nulls (NullSemantics.lean):**
```lean
check (cfg := cfg) "FALSE AND NULL = FALSE" (∀ t : Option SqlType,
  evalBinOp .and (some (.bool false)) (some (.null t)) == some (.bool false)) $
```

### Important Notes

- The `$` operator chains tests — the last test in a group uses `done` (no trailing `$`)
- `BoundedGroundExpr` has a `.expr` field to extract the `Expr`
- Ground expressions have no column references, so `evalExpr [] e` works (empty row)
- For theorems with preconditions, the generator must produce values satisfying them, or the test should filter/skip invalid inputs
- Default sample count is 10,000 (`LSPEC_SAMPLES` env var overrides)
- `evalExpr row e` is shorthand for `evalExprWithDb (fun _ => []) row e`

### Related Commands

- `/test` — Run the main test suite
- `/coverage` — Check which theorems have test coverage
