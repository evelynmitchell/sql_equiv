# /audit

Type-aware soundness checking for expression rewrite functions.

## Usage

- `/audit` — Full scan: audit every `Expr → Expr` rewriter in the codebase
- `/audit <function>` — Targeted: audit one rewrite function (e.g., `/audit simplifyBinOp`)

## Philosophy

A rewrite `lhs => rhs` is sound only if `eval(lhs) = eval(rhs)` for **every
possible runtime type** of each free variable, **every row, and every
database**. SQL expressions are untyped at the AST level — a variable `a` in a
pattern could evaluate to any `Value` kind, to NULL, or to `none` (error).
The evaluator (`evalBinOp`, `evalUnaryOp`, `evalFunc`) dispatches on concrete
types and has catch-all arms that return `none`. If a rewrite removes an
operator, a type combination that previously hit the catch-all might now take
a different path, or vice versa. This is where soundness bugs hide.

Copilot found the identity law bug (`a AND TRUE => a`) exactly this way: when
`a` evaluates to a non-boolean (e.g., `int 42`), the original expression
hits the `evalBinOp` catch-all and returns `none`, but the rewritten expression
returns `some (.int 42)`.

### Proven rewriters: what is left to audit

Every rewriter in the tree today is **certified**: each arm returns a subtype
`{ e' // e ≃ₑ e' }` whose proof the Lean kernel checks. For these, the
per-type hand-trace below largely re-derives what the kernel already checked.
The audit's job shifts to the things the kernel does *not* check:

1. **The trust base** — `#print axioms` on the top-level theorem. Expected:
   `[propext, sorryAx, Classical.choice, Quot.sound]` (`sorryAx` comes from
   the evaluator's `decreasing_by sorry` in `Semantics.lean`). Anything else
   (`Lean.ofReduceBool` / `Lean.trustCompiler` from `native_decide`, or a
   project `axiom`) is a finding. `Test/RewriterTest.lean` pins this with a
   `#guard_msgs` guard.
2. **Runtime/proof divergence** — `@[implemented_by]`, `@[extern]`, `unsafe`,
   or `partial def` on the rewriter's or evaluator's path mean the compiled
   code is not the code that was proved.
3. **The scope of the relation** — `≃ₑ` (`SqlEquiv/Equiv/Defs.lean`)
   quantifies over every database and row (#242). The weaker `≃ₑ₀`
   (`ExprEquivEmptyDb`) only covers the empty database; a rewrite justified
   only by `≃ₑ₀` is **not** sound for subquery-bearing expressions
   (`EXISTS`, `IN (subquery)`, scalar subqueries) on real tables. Check which
   relation each proof concludes. Likewise, `Expr.isGround` admits
   `EXISTS (SELECT 1 FROM t)` (database-dependent); only `Expr.isClosed`
   implies database independence.
4. **Guard bridges** — static guards (`isDefinitelyBool`, `isDefinitelyInt`)
   must have bridge theorems to the semantic preconditions
   (`isBoolValued`, `isIntValued`), quantified over all databases.

For an **unproven** rewriter (any new `Expr → Expr` without a `≃ₑ` proof),
the full protocol below is the primary check.

## Instructions — Full Scan

When the user runs `/audit` with no arguments:

1. **Find all Expr-to-Expr rewrite functions.** Do not trust a fixed list —
   files move. Search:
   ```bash
   grep -rn "Expr → Expr\|: Expr :=\|{ e' : Expr //" SqlEquiv --include=*.lean | grep "def "
   ```
   As of #242 these are:
   - `SqlEquiv/Rewriter.lean` — `certifiedRewriteAux` / `certifiedRewrite`,
     built from `simplifyBinOp`, `simplifyUnaryOp`, `simplifyInList`,
     `simplifyCaseExpr`, `simplifyBetween` (34 arms; proof
     `certifiedRewriteAux_equiv`)
   - `SqlEquiv/Equiv/ExprAxioms.lean` — `normalizeExpr` (operand reordering
     for AND/OR/+/×; proof `normalizeExpr_equiv` in `Equiv/Decidable.lean`)

2. **Check the trust base and runtime path** (items 1–2 above):
   ```lean
   import SqlEquiv
   #print axioms SqlEquiv.certifiedRewrite
   #print axioms SqlEquiv.normalizeExpr_equiv
   #print axioms SqlEquiv.checkEquivFull
   ```
   and `grep -rn "implemented_by\|@\[extern\|unsafe" SqlEquiv`.

3. **Apply the audit protocol** (below) to each rewrite arm. For proven arms,
   it is enough to confirm the arm's proof concludes `≃ₑ` (not `≃ₑ₀`) and
   that any guard has a bridge theorem.

4. **Probe empirically** — compare `evalExprWithDb db row e` against
   `evalExprWithDb db row (certifiedRewrite e).val` across operand kinds,
   rows, and both an empty and a non-empty database. The permanent version
   is the "Context Sweep" group in `LSpecTests/RewriterProperties.lean`
   (`sweepCases`, ~52k expressions); run it with
   `lake exe sql_equiv_lspec`. When adding a rewriter, extend `sweepCases`
   with its shapes. Verify a probe is non-vacuous by pointing it at a known
   unsound mutant and confirming it fails.

5. **Report findings** using the output format below.

## Instructions — Targeted Audit

When the user runs `/audit <function>`:

1. **Read the specified function** (find it with `grep -rn "def <function>" SqlEquiv`).
2. **Apply the audit protocol** to each arm.
3. **Report findings** or "No issues found" if all arms are sound.

## The Audit Protocol

This is the core reasoning procedure. Apply it to each rewrite arm.

### Step 1: Identify the rewrite

For each pattern-match arm that returns a structurally different expression,
extract the rewrite rule. Example:

```
simplifyBinOp:
  .and, l, .lit (.bool true) => l      -- guarded by l.isDefinitelyBool
```

### Step 2: List free expression variables

Identify the unbound variables that represent arbitrary sub-expressions.
In the example above: `l` is free.

### Step 3: Enumerate Value types for each variable

For each free variable, consider what `evalExprWithDb db row` might return at
runtime. The possible results (see `inductive Value` in `SqlEquiv/Ast.lean`):

| Result | Description |
|--------|-------------|
| `some (.int n)` | Integer value |
| `some (.string s)` | String value |
| `some (.bool b)` | Boolean value (true or false) |
| `some (.decimal u s)` | Exact decimal `u / 10^s` (canonical via `Value.mkDecimal`) |
| `some (.null t)` | SQL NULL, typed (`some .int`, …) or untyped (`none`) |
| `none` | Evaluation error (type mismatch, missing column, div by zero) |

For variables appearing in binary operators, consider all combinations of
these 6 results for both operands. For single-variable rewrites, consider all 6.
Distinguish typed vs untyped NULL where an arm could propagate one and not the
other.

If `Value` gains a constructor, update this table in the same PR (CLAUDE.md:
"Docs ship with behavior").

### Step 4: Trace the evaluator — BEFORE rewrite

For each type combination, trace what the evaluator does with the **original**
expression. Key dispatch tables (all in `SqlEquiv/SemanticsBase.lean`; find
them with `grep -n "^def evalBinOp\|^def evalUnaryOp\|^def evalFunc"`):

- **`evalBinOp`**: pattern-matches on `(op, l, r)`. Check which arm fires for
  each type combination; the final catch-all returns `none` for type mismatches.
- **`evalUnaryOp`**: pattern-matches on `(op, e)`; catch-all returns `none`
  (e.g., `NOT` on an integer).
- **`evalFunc`**: dispatch by upper-cased function name.

For subquery-bearing operands, also vary the database: `EXISTS`, `IN (subquery)`
and scalar subqueries give different results on an empty vs non-empty table.

### Step 5: Trace the evaluator — AFTER rewrite

For each type combination, trace what the evaluator does with the **rewritten**
expression. This may be:
- A different operator application (trace the new operator's dispatch)
- A bare variable (result is whatever the variable evaluates to)
- A literal (result is the literal value)

### Step 6: Compare results

For each type combination (and database), compare BEFORE and AFTER:

- **Match**: Both produce the same `Option Value` — sound for this combination.
- **Mismatch**: Different results — **soundness bug**. Record the counterexample.

Pay special attention to these high-risk patterns:
- **Identity elimination** (`a OP identity => a`): Removing the operator means
  `a`'s raw value flows through. If `a` is the wrong type, the original would
  have returned `none` but the rewrite returns the raw value.
- **Annihilation** (`a OP absorb => absorb`): Replacing with a constant is
  usually safe because the result is independent of `a`'s type — but check
  that the evaluator really short-circuits (e.g., `a AND FALSE` when `a` is
  `none`).
- **Double negation** (`NOT NOT a => a`): Safe only if `a` is boolean.
  For non-boolean `a`, `NOT a` returns `none`, and `NOT none` also returns
  `none`, matching the rewritten `a` only if `a` itself is `none`.
- **Arithmetic identities** (`a + 0 => a`, `a * 1 => a`): Only sound when
  `a` is an integer. For string/bool/null/decimal, `a + 0` may return `none`
  or a different representation, while `a` returns the raw value.
- **Subquery rewrites** (`NOT EXISTS` flips, `IN (subquery)` expansions): sound
  only if the proof holds for every database — check it concludes `≃ₑ`.

### Step 7: Check guards

If the arm has a type guard (`isDefinitelyBool`, `isDefinitelyInt`), evaluate
whether it is sufficient:
- Does it catch ALL wrong-typed inputs, including `none` (error)?
- Is there a bridge theorem from the guard to the semantic precondition
  (`isDefinitelyBool_implies_isBoolValued`, `isDefinitelyInt_implies_isIntValued`
  in `SqlEquiv/Rewriter.lean`)? Is that precondition quantified over all
  databases?
- Is the guard conservative? (False negatives are safe; false positives are bugs.)
  `isDefinitelyInt` deliberately excludes `/` and `%` (division by zero → `none`).

## Key Files to Read

Locate definitions by name (`grep -n "^def <name>"`), not by line number.

| File | Contains |
|------|----------|
| `SqlEquiv/SemanticsBase.lean` | `evalBinOp`, `evalUnaryOp`, `evalFunc` — type dispatch |
| `SqlEquiv/Ast.lean` | `inductive Value` |
| `SqlEquiv/Equiv/Defs.lean` | `ExprEquiv` (`≃ₑ`), `ExprEquivEmptyDb` (`≃ₑ₀`), type preconditions |
| `SqlEquiv/Rewriter.lean` | Certified rewriter, static guards, bridge theorems |
| `SqlEquiv/Equiv/ExprAxioms.lean` | `normalizeExpr` and the algebraic laws the rewriter uses |
| `SqlEquiv/Equiv/Decidable.lean` | `normalizeExpr_equiv`, `isGround` / `isClosed`, `checkEquivFull` |
| `LSpecTests/RewriterProperties.lean` | Context sweep (empirical probe) |
| `Test/RewriterTest.lean` | `#guard_msgs` axiom guard |

## Output Format

Structure the report as follows:

```
## Audit Report: [function name or "Full Scan"]

### Trust base
- #print axioms <theorem>: [...]   (expected: propext, sorryAx, Classical.choice, Quot.sound)
- Runtime overrides on path: none / [list]

### [function_name] (file:line)

#### Arm 1: `pattern => result`
- Free variables: a, b
- Proof: <theorem name> concludes ≃ₑ / ≃ₑ₀ / none
- Type analysis (unproven arms, or where the proof's scope is in doubt):
  | a type | b type | BEFORE | AFTER | Status |
  |--------|--------|--------|-------|--------|
  | int    | -      | none   | some (.int n) | MISMATCH |
  | bool   | -      | some (.bool b) | some (.bool b) | ok |
  | string | -      | none   | some (.string s) | MISMATCH |
  | decimal| -      | none   | some (.decimal u s) | MISMATCH |
  | null   | -      | some (.null none) | some (.null none) | ok |
  | none   | -      | none   | none  | ok |
- Verdict: UNSOUND — returns raw value when original returns none for non-boolean a
- Guard check: isDefinitelyBool / bridge theorem present / missing
- Suggested fix: [description]

#### Arm 2: `pattern => result`
- Free variables: ...
- Verdict: SOUND (proved: <theorem>, ≃ₑ)

### Empirical probe
- Expressions: N, rewritten: M, contexts: rows × {empty, non-empty} db, mismatches: K
- Vacuity check: mutant <description> caught? yes/no

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
   - Add a type guard (like `isDefinitelyBool`) plus a bridge theorem
   - Restrict the pattern match to only fire on known-safe types
   - Restate a proof from `≃ₑ₀` to `≃ₑ`, or restrict the arm to closed
     (`Expr.isClosed`) operands

2. **Offer to add regression tests** via `/counterexample` for each
   concrete counterexample found.

3. **Offer to add LSpec property tests** via `/lspec` (or extend `sweepCases`)
   that would catch similar issues automatically in the future.

## Related Commands

- `/investigate` — investigate anomalies in project health signals
- `/counterexample` — add a counterexample as a regression test
- `/lspec` — run LSpec property-based tests
- `/equiv` — prove equivalence between SQL expressions
- `/sorry-audit` — track `sorry` / `sorryAx` in the trust base
