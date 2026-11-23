# Plan: Increase LSpec Property Test Coverage

> **Note (23 Nov 2026):** the optimizer (`Optimizer.lean`, `OptimizerUtils.lean`,
> `LSpecTests/OptimizerEquiv.lean`) was removed in PR #156. The optimizer items below are
> historical; the certified rewriter `certifiedRewrite` (`SqlEquiv/Rewriter.lean`) took its place.

## Current State (after 100→1000 sample bump)
- **76 property checks** across 3 suites (ExprAlgebra, NullSemantics, OptimizerEquiv)
- **1000 samples** per check (76,000 total) — previously 100 samples (7,600 total)
- Sample count configurable via `LSPEC_SAMPLES` env var (e.g., `LSPEC_SAMPLES=100` for CI)
- Run seed configurable via `LSPEC_SEED` (default 0, used by pull-request CI); a daily workflow
  runs a new seed and files failures as issues (#395)
- Coverage limited to: expression algebra identities, NULL propagation, and 8 optimizer passes

## Coverage Gaps (prioritized)

---

### Tier 1 — Easy wins (existing generators, no new infrastructure)

These use `BoundedGroundExpr`, `IntGroundExpr`, `BoolGroundExpr`, `Value` directly.

#### 1A. Constant folding preserves semantics
New file: `LSpecTests/ConstantFolding.lean`

Properties:
- `constantFoldBinOp op l r` preserves semantics for all BinOp × BoundedGroundExpr pairs
- `constantFoldUnaryOp op e` preserves semantics for all UnaryOp × BoundedGroundExpr pairs
- `simplifyExprOnce e` preserves semantics (the composed single-pass pipeline)
- `foldArithmetic` agrees with `evalBinOp` on literal inputs
- `foldComparison` agrees with `evalBinOp` on literal inputs
- `foldLogical` agrees with `evalBinOp` on literal inputs

Estimated: **~8 new check properties**

#### 1B. Flatten/unflatten roundtrip
New file: `LSpecTests/FlattenRoundtrip.lean`

Properties:
- `unflattenAnd (flattenAnd e) == some e'` where `evalExpr [] e' == evalExpr [] e`
- `unflattenOr (flattenOr e) == some e'` where `evalExpr [] e' == evalExpr [] e`
- `flattenAnd e` is always non-empty (proven, but validate at runtime)
- `flattenOr e` is always non-empty (proven, but validate at runtime)
- Idempotency: flatten after unflatten-then-flatten is stable

Estimated: **~6 new check properties**

#### 1C. evalFunc — remaining scalar functions
Add to `LSpecTests/NullSemantics.lean` (new group):

Properties:
- `NULLIF(a, a) == NULL` for all non-null Values
- `NULLIF(a, b) == a` when a ≠ b
- `ABS(n) >= 0` for all Int
- `ABS(-n) == ABS(n)` for all Int
- `LENGTH(s) >= 0` for all String
- `UPPER(LOWER(s)) == UPPER(s)` idempotence-like
- `LOWER(UPPER(s)) == LOWER(s)`
- `CONCAT(s, "") == s` identity
- NULL propagation for each function (ABS(NULL) == NULL, etc.)

Estimated: **~12 new check properties**

#### 1D. Ordering / comparison consistency
New file: `LSpecTests/ExprOrdering.lean`

Properties on `exprCompare` / `exprStructuralCmp`:
- Reflexivity: `cmp e e == .eq`
- Antisymmetry: `cmp a b == .lt → cmp b a == .gt`
- Transitivity: `cmp a b ≠ .gt ∧ cmp b c ≠ .gt → cmp a c ≠ .gt`
- Consistency with `exprLt`: `exprLt a b == (exprCompare a b == .lt)`

Properties on `valueCompare`:
- Same three ordering laws

Estimated: **~8 new check properties**

#### 1E. Normalization convergence
Add to `LSpecTests/OptimizerEquiv.lean` (new group):

Properties:
- Commutative normal form: `normalizeExprCanonical (a AND b) == normalizeExprCanonical (b AND a)` for BoolGroundExpr
- Same for OR, ADD, MUL, EQ
- `optimizeExpr` is idempotent: `optimizeExpr (optimizeExpr e) == optimizeExpr e`
- `simplifyExprOnce` is idempotent (may not hold — good to test!)

Estimated: **~7 new check properties**

**Tier 1 total: ~41 new properties → ~41,000 new samples**

---

### Tier 2 — Moderate (need new generators)

#### 2A. Column-aware expression generator
Add to `LSpecTests/Generators.lean`:

New type: `ColumnGroundExpr` — expressions that reference columns from a fixed schema
(e.g., columns `x : Int`, `y : Int`, `z : Bool` with a matching sample Row).

This enables testing functions that involve column references with a known evaluation row.

#### 2B. Predicate pushdown safety invariants
New file: `LSpecTests/PredicatePushdown.lean`

Requires: Generator for simple `FromClause` (single table, join of two tables).

Properties:
- `pushPredicateDown pred from` reconstructs: remaining AND pushed ≈ original semantics
- `canPushPastProjection` is conservative (pushed predicates still evaluate correctly)
- `canPushLeftThroughJoin` / `canPushRightThroughJoin` respect join semantics

Estimated: **~6 new check properties**

#### 2C. transformColumnRefs correctness
Properties:
- Transformed expression evaluates the same against inner row as original against outer row
- Round-trip: transform then reverse-transform recovers original (for simple cases)

Estimated: **~3 new check properties**

**Tier 2 total: ~9 new properties, requires new generator infrastructure**

---

### Tier 3 — Hard (need database/table fixtures)

#### 3A. Query-level optimizer equivalence
Would need: `Database`, `Table`, `SelectStmt` generators (complex).

Properties:
- `optimizeSelectStmt s` produces same result set as `s` for random databases
- `optimizeQuery q` produces same result set as `q`
- `optimize stmt` produces same result set as `stmt`

#### 3B. Aggregate and window function semantics
Would need: Row group generators, partition generators.

Properties:
- `evalAggOverTable` correctness for COUNT, SUM, AVG, MIN, MAX
- Window function ranking consistency (ROW_NUMBER unique, RANK monotone, DENSE_RANK gap-free)

**Tier 3: Deferred — high effort, lower marginal value given axiom coverage**

---

## Implementation Order

| Step | What | New checks | Effort |
|------|------|-----------|--------|
| 1 | Constant folding (1A) | +8 | Small |
| 2 | Flatten/unflatten (1B) | +6 | Small |
| 3 | evalFunc coverage (1C) | +12 | Small |
| 4 | Normalization convergence (1E) | +7 | Small |
| 5 | Ordering laws (1D) | +8 | Small |
| 6 | Column-aware generator (2A) | +0 | Medium |
| 7 | Predicate pushdown (2B+2C) | +9 | Medium |

**After Tier 1: 76 + 41 = 117 checks × 1000 = 117,000 samples**
**After Tier 2: 117 + 9 = 126 checks × 1000 = 126,000 samples**

## Files Changed

New files:
- `LSpecTests/ConstantFolding.lean`
- `LSpecTests/FlattenRoundtrip.lean`
- `LSpecTests/ExprOrdering.lean`
- (Tier 2) `LSpecTests/PredicatePushdown.lean`

Modified files:
- `LSpecTests/Generators.lean` — new generators (ColumnGroundExpr for Tier 2)
- `LSpecTests/NullSemantics.lean` — add evalFunc group
- `LSpecTests/OptimizerEquiv.lean` — add normalization convergence group
- `LSpecTests/Main.lean` — register new suites
- `lakefile.toml` — no changes needed (globs already cover `LSpecTests.*`)
