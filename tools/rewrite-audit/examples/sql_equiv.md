# Worked example: sql_equiv, 13 Nov 2026

A full-scan report on master `2a67c43` (after PR #273), produced with this
repository's config (`.claude/rewrite-audit.json`). This is the acceptance
baseline for the adapter: a full scan on an unchanged tree must reproduce it.

## Rewrite Audit: Full Scan (sql_equiv, 2a67c43)

### Trust base
- `#print axioms`: `[propext, Classical.choice, Quot.sound]` for each of:
  - `certifiedRewrite`, `certifiedRewriteAux_equiv`;
  - `normalizeExpr_equiv`;
  - `checkEquivFull`;
  - `evalSelect_eq_evalSelectCore`, `select_where_congr`.
- Whole-library guard (`Test/TrustBaseTest.lean`): OK, 1258 theorems.
- Runtime overrides:
  - `DecidableEq Expr` is `@[implemented_by]` an `unsafe` BEq
    (`Ast.lean:833`). This is **off-path**: rewriter arms branch on
    `isDefinitelyBool`/`isDefinitelyInt`, not on `Expr` equality.
  - `partial def hasAggregate` / `exprHasWindowFn` are **on-path** but opaque.
    SELECT theorems take "no aggregate / no window function" as hypotheses.

### certifiedRewriteAux / certifiedRewrite (SqlEquiv/Rewriter.lean:430, :701)
- All 34 arms: the result type `{ e' // e ≃ₑ e' }` forces the full relation
  (all databases and rows). No arm uses `≃ₑ₀`.
- Guards:
  - `isDefinitelyBool` has the bridge `isDefinitelyBool_implies_isBoolValued`;
  - `isDefinitelyInt` has the bridge `isDefinitelyInt_implies_isIntValued`.
    This guard excludes `/` and `%`.

  Both bridges are quantified over `db` and `row`.
- Dialect operator `BinOp.likeCI`: no arms. The LIKE rules match only
  case-sensitive `.like`.
- Verdict: SOUND.

### normalizeExpr (SqlEquiv/Equiv/ExprAxioms.lean:231)
- `normalizeExpr_equiv` concludes `≃ₑ`. The `likeCI` congruence case is
  present.
- Verdict: SOUND.

### checkEquivFull (SqlEquiv/Equiv/Decidable.lean:1167)
- The ground-evaluation path concludes `≃ₑ` only when both sides are
  `isClosed` (project-specific check).
- Verdict: SOUND.

### Empirical probe
- Context Sweep: 54,876 expressions, of which 7,850 were rewritten. Contexts
  were rows × {empty, non-empty} database × subqueries. Mismatches: 0.
- Vacuity: the built-in oracle self-check catches the unguarded mutant
  `a AND TRUE → a`.

### Summary
- Rewriters audited: 3.
- Issues: 0.
- Observations:
  - `hasAggregate` / `exprHasWindowFn` are partial and opaque to proofs;
  - the legacy non-`Param` partial evaluators (`evalExprWithAgg`,
    `compareByOrderItems`, `computeRanks`, `computeDenseRanks`,
    `evalExprWithWindow`) look unused;
  - the off-path `unsafe` `DecidableEq Expr` is documented in `Ast.lean`.
