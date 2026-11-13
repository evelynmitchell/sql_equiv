# /audit

Type-aware soundness audit of this repository's expression rewriters.

This is a thin adapter over the general **rewrite-audit** skill in
`tools/rewrite-audit/` (extracted from this command; plan:
`docs/AUDIT_EXTRACTION_PLAN.md`).

## Usage

- `/audit`: full scan of every rewriter
- `/audit <function>`: targeted audit of one rewrite function (e.g.
  `/audit simplifyBinOp`)

## Instructions

1. **Read `tools/rewrite-audit/SKILL.md` and follow it**, loading its
   `references/` files as it directs. Do not re-discover: this repo's project
   map is `.claude/rewrite-audit.json`. It names:
   - the rewriters: `certifiedRewrite`, `normalizeExpr`, `checkEquivFull`;
   - the evaluator dispatch: `evalBinOp`, `evalUnaryOp`, `evalFunc` in
     `SqlEquiv/SemanticsBase.lean`;
   - the value type: `Value`;
   - the relation: `≃ₑ` over every database and row. Reject the weaker
     `≃ₑ₀`;
   - the guards and their bridges;
   - the probe (LSpec Context Sweep);
   - the trust guard (`Test/TrustBaseTest.lean`).
2. **This is a Lean project**, so the Lean layer
   (`tools/rewrite-audit/references/lean.md`) applies. Run the scripts from
   the repo root:
   ```bash
   tools/rewrite-audit/scripts/lean/print_axioms.sh SqlEquiv SqlEquiv.certifiedRewrite SqlEquiv.certifiedRewriteAux_equiv SqlEquiv.normalizeExpr_equiv SqlEquiv.checkEquivFull
   ```
   ```bash
   tools/rewrite-audit/scripts/lean/check_trust_base.sh SqlEquiv SqlEquiv
   ```
   Expected: `[propext, Classical.choice, Quot.sound]` everywhere, and
   "trust base OK" over every theorem. The build already enforces the latter
   through `Test/TrustBaseTest.lean`.
3. **Run the repo-only checks** listed in `projectSpecificChecks` of the
   config. In particular, `checkEquivFull` may conclude `≃ₑ` from ground
   evaluation only for `Expr.isClosed` operands; `Expr.isGround` admits
   database-dependent `EXISTS (SELECT 1 FROM t)`.
4. **Probe:** `lake exe sql_equiv_lspec`, group "Context Sweep". Report the
   expression and rewrite counts and the mismatch count, and confirm the
   built-in oracle self-check (unguarded `a AND TRUE → a`) passes. When adding
   a rewriter, extend `sweepCases` in `LSpecTests/RewriterProperties.lean` with
   its shapes.
5. **Report** in the skill's format (`references/output-format.md`).
   `tools/rewrite-audit/examples/sql_equiv.md` is the baseline from
   13 Nov 2026. A full scan on an unchanged tree should match it.

## This repository's value domain

Results of `evalExprWithDb db row e`, from `inductive Value` in
`SqlEquiv/Ast.lean`:

| Result | Description |
|--------|-------------|
| `some (.int n)` | Integer value |
| `some (.string s)` | String value |
| `some (.bool b)` | Boolean value (true or false) |
| `some (.decimal u s)` | Exact decimal `u / 10^s` (canonical via `Value.mkDecimal`) |
| `some (.null t)` | SQL NULL, typed (`some .int`, …) or untyped (`none`) |
| `none` | Evaluation error (type mismatch, missing column, division by zero) |

If `Value` gains a constructor, update this table, the LSpec generators and
`tools/definition_coverage_matrix.py` in the same PR (CLAUDE.md: "Docs ship
with behavior").

Dialect choices are recorded in the AST at parse time (`BinOp.likeCI`, the
MIN/MAX `MinMaxMode`). A rewrite arm must match only the operator or mode its
proof covers.

## Related commands

- `/investigate`: investigate anomalies in project health signals
- `/counterexample`: add a counterexample as a regression test
- `/lspec`: run LSpec property-based tests
- `/equiv`: prove equivalence between SQL expressions
- `/sorry-audit`: track `sorry` / `sorryAx` in the trust base
