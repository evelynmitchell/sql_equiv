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
   `references/` files as it directs. Start from this repo's project
   map, `.claude/rewrite-audit.json`, but on a full scan **also re-run the
   skill's discovery searches** and report any rewriter or decision procedure
   that is not in the config. A new one may not be listed. The config names:
   - the rewriters: `certifiedRewrite`, `normalizeExpr`, `checkEquivFull`, the statement
     checkers, and the typed core's `SqlCore.Expr.simplify`, `SqlCore.Query.simplify` and
     checkers `Expr.checkEquiv` / `Query.checkEquiv` (relations `Expr.Equiv Γ` and
     `Query.Equiv .ordered`, over conforming rows and instances);
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
   ```bash
   tools/rewrite-audit/scripts/lean/print_axioms.sh SqlCore SqlCore.Expr.equiv_simplify SqlCore.Query.equiv_simplify SqlCore.Expr.checkEquiv SqlCore.Query.checkEquiv SqlCore.Expr.equiv_of_check SqlCore.Query.equiv_of_check
   ```
   ```bash
   tools/rewrite-audit/scripts/lean/check_trust_base.sh SqlCore SqlCore
   ```
   `SqlBridge` has no root module, so the script cannot import it;
   `SqlCoreTest/TrustBaseTest.lean` asserts its trust base (built with `sqlcore_test`).
   Expected: `[propext, Classical.choice, Quot.sound]` everywhere, and
   "trust base OK" over every theorem, definition and opaque constant. Always
   run the script: `Test/TrustBaseTest.lean` enforces the same check only when
   `sql_equiv_test` is built (as CI does). Plain `lake build` (default target
   `sql_equiv`) does not import it.

   When judging runtime/proof divergence, say which rewriter or decision
   procedure an override is on the path of. Since #278 no `partial def` is
   on a proof or checker path: the remaining ones (66 on 23 Nov 2026: 48 parser, 8 pretty-printer, 10 `toReprStr`) are
   the parser, the SQL pretty-printer and `toReprStr`. The count grows with
   the parser; what matters is where they are. Count declarations, not
   comments that mention them:
   ```bash
   grep -rnE "^\s*(private |protected )?partial def" SqlEquiv/ | cut -d: -f1 | sort | uniq -c
   ```
   Every hit must be in `Parser.lean`, `Pretty.lean` or a `toReprStr`. Run the same count
   over `SqlCore/ SqlBridge/`: the only hits allowed there are the Spider coverage reporter,
   `SqlBridge/Coverage.lean` (9 on 23 Nov 2026), which no theorem or checker uses. A
   `partial def` anywhere else, or reachable from the evaluator, a rewriter
   or a checker, is a finding. Since #278 there are no
   overrides left in `SqlEquiv/`: the AST's `DecidableEq` is a total generated
   decider (`tools/gen_ast_deceq.py`), and `sql_equiv!` uses `decide +kernel`
   instead of `native_decide`. `Test/TrustBaseTest.lean` enforces both
   (`#assert_no_runtime_overrides`, and `Test/TacticTest.lean` pins the
   tactic's axioms). Report any reappearance as a finding.

   Also check for vacuous theorems, whose two sides are the same text (#307):
   ```bash
   python3 tools/rewrite-audit/scripts/lean/find_identical_sides.py SqlEquiv SqlCore SqlBridge
   ```
   Expected: "OK". CI runs it too.
3. **Run the repo-only checks** listed in `projectSpecificChecks` of the
   config. In particular, `checkEquivFull` may conclude `≃ₑ` from ground
   evaluation only for `Expr.isClosed` operands; `Expr.isGround` admits
   database-dependent `EXISTS (SELECT 1 FROM t)`.
4. **Probe:** `lake exe sql_equiv_lspec`, group "Context Sweep". Report the
   expression and rewrite counts and the mismatch count, and confirm the
   built-in mutant check passes. It runs an unguarded `a AND TRUE → a`
   rewriter through the same mismatch function and must catch cases. When adding
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
