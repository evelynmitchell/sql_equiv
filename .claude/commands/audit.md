# /audit

Type-aware soundness checking for optimizer rewrite functions.

## Usage

- `/audit` — Full scan: audit all rewrite functions in the optimizer pipeline
- `/audit <function>` — Targeted: audit a specific rewrite function (e.g., `/audit applyIdentityLaws`)

## Philosophy

A rewrite `lhs => rhs` is sound only if `eval(lhs) = eval(rhs)` for **every
possible runtime type** of each free variable. SQL expressions are untyped at
the AST level — a variable `a` in a pattern could evaluate to `int`, `string`,
`bool`, `null`, or `none` (error). The evaluator (`evalBinOp`, `evalUnaryOp`)
dispatches on concrete types and has catch-all arms that return `none`. If a
rewrite removes an operator, a type combination that previously hit the catch-all
might now take a different path, or vice versa. This is where soundness bugs hide.

Copilot found the identity law bug (`a AND TRUE => a`) exactly this way: when
`a` evaluates to a non-boolean (e.g., `int 42`), the original expression
hits the `evalBinOp` catch-all and returns `none`, but the rewritten expression
returns `some (.int 42)`.

## Instructions — Full Scan

When the user runs `/audit` with no arguments:

1. **Find all Expr-to-Expr rewrite functions** in the optimizer pipeline.
   Read these files and identify every function with signature `Expr → Expr`
   that pattern-matches on expression structure and returns a different expression:
   - `SqlEquiv/Optimizer.lean` — `applyDeMorgan`, `eliminateDoubleNegation`,
     `applyIdentityLaws`, `applyIdempotentLaws`, `applyComplementLaws`,
     `simplifyArithmetic`, `constantFoldBinOp`, `constantFoldUnaryOp`
   - `SqlEquiv/ExprNormalization.lean` — normalization functions
   - `SqlEquiv/PredicatePushdown.lean` — predicate rewrite functions
   - `SqlEquiv/OptimizerUtils.lean` — utility rewrite functions

2. **Apply the audit protocol** (see below) to each rewrite arm of each function.

3. **Report findings** using the output format described below.

## Instructions — Targeted Audit

When the user runs `/audit <function>`:

1. **Read the specified function** from the optimizer files.
2. **Apply the audit protocol** to each arm.
3. **Report findings** or "No issues found" if all arms are sound.

## The Audit Protocol

This is the core reasoning procedure. Apply it to each rewrite arm.

### Step 1: Identify the rewrite

For each pattern-match arm that returns a structurally different expression,
extract the rewrite rule. Example:

```
applyIdentityLaws:
  .binOp .and a (.lit (.bool true)) => a
```

### Step 2: List free expression variables

Identify the unbound variables that represent arbitrary sub-expressions.
In the example above: `a` is free.

### Step 3: Enumerate Value types for each variable

For each free variable, consider what `evalExprWithDb` might return at runtime.
The possible results are (from `SqlEquiv/Ast.lean:100-105`):

| Result | Description |
|--------|-------------|
| `some (.int n)` | Integer value |
| `some (.string s)` | String value |
| `some (.bool b)` | Boolean value (true or false) |
| `some (.null t)` | SQL NULL |
| `none` | Evaluation error |

For variables appearing in binary operators, consider all combinations of these
5 types for both operands. For single-variable rewrites, consider all 5 types.

### Step 4: Trace the evaluator — BEFORE rewrite

For each type combination, trace what the evaluator does with the **original**
expression (before the rewrite). Key dispatch tables:

- **`evalBinOp`** (`SqlEquiv/Semantics.lean:124-182`): Pattern-matches on
  `(op, l, r)`. Check which arm fires for each type combination. The catch-all
  at line 182 (`| _, _, _ => none`) fires for type mismatches.

- **`evalUnaryOp`** (`SqlEquiv/Semantics.lean:192-200`): Pattern-matches on
  `(op, e)`. The catch-all at line 200 (`| _, _ => none`) fires for type
  mismatches (e.g., `NOT` on an integer).

### Step 5: Trace the evaluator — AFTER rewrite

For each type combination, trace what the evaluator does with the **rewritten**
expression (after the rewrite). This may be:
- A different operator application (trace the new operator's dispatch)
- A bare variable (result is whatever the variable evaluates to)
- A literal (result is the literal value)

### Step 6: Compare results

For each type combination, compare the BEFORE and AFTER results:

- **Match**: Both produce the same `Option Value` — this type combination is sound.
- **Mismatch**: Different results — **soundness bug**. Record the counterexample.

Pay special attention to these high-risk patterns:
- **Identity elimination** (`a OP identity => a`): Removing the operator means
  `a`'s raw value flows through. If `a` is the wrong type, the original would
  have returned `none` but the rewrite returns the raw value.
- **Annihilation** (`a OP absorb => absorb`): Replacing with a constant is
  usually safe because the result is independent of `a`'s type.
- **Double negation** (`NOT NOT a => a`): Safe only if `a` is boolean.
  For non-boolean `a`, `NOT a` returns `none`, and `NOT none` also returns
  `none`, matching the rewritten `a` only if `a` itself is `none`.
- **Arithmetic identities** (`a + 0 => a`, `a * 1 => a`): Only sound when
  `a` is an integer. For string/bool/null, `a + 0` returns `none` but `a`
  returns the raw value.

### Step 7: Check guards

If the function already has type guards (like `isDefinitelyNonBool`), evaluate
whether the guard is sufficient:
- Does it catch ALL non-boolean/non-integer types?
- Does it handle `none` (error) correctly?
- Is the guard conservative enough? (False negatives are safe; false positives are bugs.)

## Key Files to Read

Always read these files during an audit — they contain the evaluator dispatch
tables that determine correctness:

| File | Lines | Contains |
|------|-------|----------|
| `SqlEquiv/Semantics.lean` | 124-182 | `evalBinOp` — binary operator type dispatch |
| `SqlEquiv/Semantics.lean` | 192-200 | `evalUnaryOp` — unary operator type dispatch |
| `SqlEquiv/Semantics.lean` | 203-213 | `evalFunc` — function dispatch |
| `SqlEquiv/Ast.lean` | 100-105 | `Value` type definition |
| `SqlEquiv/Optimizer.lean` | 80-230 | All rewrite functions |
| `SqlEquiv/ExprNormalization.lean` | all | Normalization rewrites |
| `SqlEquiv/PredicatePushdown.lean` | all | Predicate pushdown rewrites |
| `SqlEquiv/OptimizerUtils.lean` | all | Utility rewrites |

## Output Format

Structure the report as follows:

```
## Audit Report: [function name or "Full Scan"]

### [function_name] (file:line)

#### Arm 1: `pattern => result`
- Free variables: a, b
- Type analysis:
  | a type | b type | BEFORE | AFTER | Status |
  |--------|--------|--------|-------|--------|
  | int    | -      | none   | some (.int n) | MISMATCH |
  | bool   | -      | some (.bool b) | some (.bool b) | ok |
  | string | -      | none   | some (.string s) | MISMATCH |
  | null   | -      | some (.null none) | some (.null none) | ok |
  | none   | -      | none   | none  | ok |
- Verdict: UNSOUND — returns raw value when original returns none for non-boolean a
- Guard check: isDefinitelyNonBool catches int/string literals but NOT
  column refs, function calls, or subqueries that return non-boolean values
- Suggested fix: [description]

#### Arm 2: `pattern => result`
- Free variables: ...
- Verdict: SOUND

### Summary
- Functions audited: N
- Arms checked: M
- Issues found: K
  - [function:arm] — brief description
  - ...
```

Use these status markers:
- `ok` — sound for this type combination
- `MISMATCH` — different results before vs after (soundness bug)
- `GUARD` — would be unsound but existing guard catches it

## After Audit

If issues are found:

1. **Suggest a fix approach** for each issue. Common fixes:
   - Add a type guard (like `isDefinitelyNonBool`)
   - Restrict the pattern match to only fire on known-safe types
   - Add a runtime type check in the rewritten expression

2. **Offer to add regression tests** via `/counterexample` for each
   concrete counterexample found.

3. **Offer to add LSpec property tests** via `/lspec` that would catch
   similar issues automatically in the future.

## Related Commands

- `/investigate` — investigate anomalies in project health signals
- `/counterexample` — add a counterexample as a regression test
- `/lspec` — run LSpec property-based tests
- `/equiv` — prove equivalence between SQL expressions
