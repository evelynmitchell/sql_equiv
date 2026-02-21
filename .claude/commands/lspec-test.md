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

4. **Write the test with a `-- covers:` annotation:**
   ```lean
   -- covers: theorem_name
   check (cfg := cfg) "human-readable description" (∀ v1 : Gen1, v2 : Gen2,
     LHS == RHS) $
   ```

   The `-- covers:` comment is **required** for every new `check` statement. It links the test to one or more theorems for coverage tracking.

   For tests covering multiple theorems:
   ```lean
   -- covers: and_comm, evalBinOp_and_comm
   check (cfg := cfg) "AND commutes" (∀ a b : BoundedGroundExpr, ...)
   ```

   - For expression-level theorems, use `evalExpr [] expr` (empty row for ground exprs)
   - For value-level theorems, use `evalBinOp`/`evalUnaryOp`/`evalFunc` directly
   - Chain tests with `$` operator

5. **Add the test to the group function** in the same file. Tests are organized in named groups:
   ```lean
   def myTests (cfg : Configuration) : TestSeq :=
     -- covers: theorem_a
     check (cfg := cfg) "test1" (...) $
     -- covers: theorem_b
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
   lake build sql_equiv_lspec && lake exe sql_equiv_lspec
   ```
   For quick iteration: `LSPEC_SAMPLES=100 lake exe sql_equiv_lspec`

8. **Verify coverage** after adding tests:
   ```bash
   uv run python tools/axiom_coverage_validator.py --runtime --theorems
   ```

### Examples

**Value-level NULL propagation (NullSemantics.lean):**
```lean
-- covers: null_add_left
check (cfg := cfg) "NULL + x = NULL" (∀ v : Value,
  evalBinOp .add (some (.null none)) (some v) == some (.null none)) $
```

**Expression-level boolean algebra (ExprAlgebra.lean):**
```lean
-- covers: and_comm, evalBinOp_and_comm
check (cfg := cfg) "AND commutes" (∀ a b : BoundedGroundExpr,
  evalExpr [] (.binOp .and a.expr b.expr) == evalExpr [] (.binOp .and b.expr a.expr)) $
```

**Three-valued logic with typed nulls (NullSemantics.lean):**
```lean
-- covers: false_and_null, trilean_and_false
check (cfg := cfg) "FALSE AND NULL = FALSE" (∀ t : Option SqlType,
  evalBinOp .and (some (.bool false)) (some (.null t)) == some (.bool false)) $
```

### Important Notes

- **Every `check` statement MUST have a `-- covers:` annotation** on the line above it
- The `$` operator chains tests — the last test in a group uses `done` (no trailing `$`)
- `BoundedGroundExpr` has a `.expr` field to extract the `Expr`
- Ground expressions have no column references, so `evalExpr [] e` works (empty row)
- For theorems with preconditions, the generator must produce values satisfying them, or the test should filter/skip invalid inputs
- Default sample count is 10,000 (`LSPEC_SAMPLES` env var overrides)
- `evalExpr row e` is shorthand for `evalExprWithDb (fun _ => []) row e`

### Related Commands

- `/test` — Run the main test suite
- `/coverage` — Check which theorems have test coverage
