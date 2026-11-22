# Mutual Recursion Audit and Refactoring Plan

> **Historical snapshot.** Axiom/theorem counts in this document are as of when it was written. As of 2026-11 the codebase has **0 axioms** (all proved since PR #173) and **697 theorems**; run `python3 tools/count_axioms_theorems.py` for the live count. Category D below is out of date: see the correction there.

This document catalogs every `mutual` block in the codebase, classifies each by
whether the mutual recursion is necessary, and proposes a prioritized refactoring
plan based on the lessons learned from the Semantics.lean conversion (PR #153).

## Background: Why Mutual Blocks Matter

In Lean 4, `partial def` functions are **opaque to the kernel** — they cannot be
unfolded in proofs. When functions are placed in a `mutual` / `partial def` block,
*every* function in the block inherits this opacity, even if it is not truly
mutually recursive with the others.

PR #153 demonstrated the cost of this: a 21-function `partial def` mutual block in
`Semantics.lean` prevented 6 bridge axioms from being proved as theorems. By
identifying that only 3 functions were truly mutual, extracting the rest, and
converting the core block to WFR (`def` with `termination_by`), we reduced the
axiom count from 28 to 22 — the single largest axiom reduction in the project.

### The `partial def` Tax

For any function `f` in a `partial def` mutual block:
- `f` is opaque: `simp [f]`, `unfold f`, `rfl` — none work in proofs
- Bridge axioms (`f_eq_fCore`) must remain as `axiom` declarations
- Every additional function in the block multiplies this cost

### The Refactoring Pattern (from PR #153)

1. **Identify the minimal mutual core** — which functions actually call each other
   in a cycle?
2. **Parameterize the rest** — extract non-mutual functions outside the block,
   passing the mutual core functions as callbacks where needed.
3. **Convert to WFR if possible** — use `def` with `termination_by` /
   `decreasing_by sorry` instead of `partial def`. Even with `sorry` in
   termination proofs, `def` produces kernel-unfoldable equations.
4. **Accept `partial def` where genuinely non-terminating** — e.g., CTE
   fixed-point iteration.

---

## Inventory of Mutual Blocks

### Category A: Mutual Inductive Types (No Action Needed)

These define the grammar of SQL and are inherently mutually recursive. They
produce no axioms and require no changes.

| File | Lines | Types | Notes |
|------|-------|-------|-------|
| `Ast.lean` | 227–280 | `Expr`, `WindowSpec`, `SelectItem`, `FromClause`, `OrderByItem` | Core AST; `Expr` embeds `SelectItem`/`FromClause` via subqueries |
| `Ast.lean` | 325–335 | `Query`, `CTEDef` | `Query` embeds `CTEDef` which embeds `Query` |

**Verdict:** Necessary. Mutual inductive types are the canonical use case for
`mutual` in Lean 4.

---

### Category B: Type-Structural Mirrors (Low Priority)

These blocks exist because each mutually recursive AST type needs a corresponding
function. They mirror the shape of the Category A inductives. In languages with
deriving mechanisms (Haskell's `deriving Eq, Show`) these would be auto-generated.

| File | Lines | Functions | Type | Purpose |
|------|-------|-----------|------|---------|
| `Ast.lean` | 385–440 | 9 | `partial def` | `toReprStr` for all AST types |
| `Ast.lean` | 476–567 | 9 | `partial def` | `BEq` for all AST types |
| `Pretty.lean` | 81–206 | 7 | `partial def` | `toSql` pretty printer |
| `Equiv/Decidable.lean` | 28–128 | 5 | `partial def` | `decideExprEq` and friends |

> **Update (Nov 2026, #278):** the `BEq` block and `decideExprEq` and friends
> are gone, replaced by a total generated `DecidableEq`
> (`tools/gen_ast_deceq.py`); see `docs/PROVING_LOG.md`. Only `toReprStr` and
> `toSql` remain partial, and both are off the proof path.

**Verdict:** Structurally forced by the mutual inductive types. Low priority for
refactoring because:
- We are unlikely to prove theorems about `toReprStr` or `toSql`
- `BEq` and `DecidableEq` could benefit from WFR conversion if we need to
  reason about equality decisions in proofs, but this is not currently blocking
  any axiom reductions

**Potential future action:** If Lean 4 gains better `deriving` support for mutual
inductives, these blocks could be replaced entirely.

---

### Category C: Already Refactored (Done)

| File | Lines | Functions | Type | Notes |
|------|-------|-----------|------|-------|
| `Semantics.lean` | 278–310 | 3 | `def` (WFR) | `evalExprWithDb`, `evalFrom`, `evalSelectWithContext` — converted in PR #153 |
| `Equiv/Decidable.lean` | 193–268 | 3 | `def` (WFR) | `isGround` family — already using WFR |

**Verdict:** No action needed. These are the result of prior refactoring work.

---

### Category D: Genuinely Non-Terminating (Accept `partial def`)

| File | Lines | Functions | Type | Notes |
|------|-------|-----------|------|-------|
| `Semantics.lean` | 839–881 | 2 | `partial def` | `evalRecursiveCTE` (fixed-point iteration), `evalQuery` |

**Verdict:** `partial def` is the honest choice here. `evalRecursiveCTE` iterates
until a fixed point is reached or a fuel limit is hit — this is genuinely
non-terminating in the general case. `evalQuery` must remain mutual with it
because queries can contain recursive CTEs.

The single remaining axiom `evalQuery_eq_evalQueryCore` is a direct consequence
of this block and cannot be eliminated without fundamentally changing the CTE
evaluation strategy (e.g., bounded fuel as a `Nat` parameter).

> **Correction (PR #174):** this block was since converted: `evalQuery` and
> `evalRecursiveCTE` are now plain `def`s (`SqlEquiv/Semantics.lean`), the CTE
> iteration being bounded by `maxCTEIterations` (1000), and the bridge to
> `evalQueryCore` is proved (`evalQuery_eq_evalQueryCore_simple` /
> `_compound`). The codebase has no axioms.

---

### Category E: Refactoring Candidates (High Priority)

These blocks contain functions that are `partial def` but are not all truly
mutually recursive. They follow the same anti-pattern as the original
Semantics.lean block and would benefit from the same treatment.

#### E1. Parser.lean — 16+ functions, ~803 lines

**Location:** Lines 582–1384

**Functions in the block:**
```
parsePrimary, parseOperand, parseMulDiv, parseAddSub, parsePred,
parseComparison, parseAnd, parseOr, parseExpr,
parseSelectItem, parseTableRef, parseJoinType,
parseFromSource, parseFromClause, parseOrderByItem,
parseSelectStmt, parseSetOp, parseQueryRest,
parseQueryBody, parseCTEDef, parseCTEList, parseQuery,
parseInsert, parseUpdate, parseDelete, parseStmt
```

**Dependency analysis:**

The true mutual cycle is between expressions and statements — `parseExpr` can
encounter subqueries (which call `parseSelectStmt`), and `parseSelectStmt`
contains expressions. This gives us a minimal mutual core of roughly:
- `parseExpr` (or its entry point `parseOr`)
- `parseSelectStmt`
- `parseFromSource` (subqueries in FROM)
- `parseQueryBody` / `parseQuery` (compound queries)

The operator precedence chain is **not mutual** — it is a linear call chain:
```
parseOr → parseAnd → parseComparison → parsePred → parseAddSub → parseMulDiv → parseOperand → parsePrimary
```

Similarly, `parseInsert`, `parseUpdate`, `parseDelete`, `parseStmt`,
`parseJoinType`, `parseOrderByItem` likely only call into the expression
parser, not back up to statement-level parsers.

**Priority: Low.** We do not prove theorems about parsing, so the `partial def`
tax has no practical impact on axiom counts. However, this refactoring would
improve readability and compile times by reducing the mutual block size.

**Estimated effort:** Medium. The parser is large but the extraction pattern is
straightforward — pull the linear chain out and parameterize the subquery entry
point.

---

#### E2. Optimizer.lean (main) — 6 functions, ~142 lines

**Location:** Lines 320–461

**Functions in the block:**
```
optimizeExpr, optimizeWindowSpec, optimizeSelectItem,
optimizeFromClause, optimizeOrderByItem, optimizeSelectStmt
```

**Dependency analysis:**

The true mutual cycle is:
- `optimizeExpr` ↔ `optimizeSelectStmt` (subqueries in expressions)
- `optimizeFromClause` → `optimizeExpr` (join conditions) and
  `optimizeFromClause` → `optimizeSelectStmt` (subqueries in FROM)

Likely extractable:
- `optimizeWindowSpec` — calls `optimizeExpr` only
- `optimizeOrderByItem` — calls `optimizeExpr` only

After extraction, the minimal mutual core would be ~4 functions:
`optimizeExpr`, `optimizeSelectItem`, `optimizeFromClause`,
`optimizeSelectStmt`.

**Priority: High.** The `PROVING_AXIOMS_PLAN.md` identifies optimizer
preservation theorems as Level 4 targets. If we want to prove that
`optimizeExpr` preserves semantics, it must be kernel-unfoldable, which
requires converting this block from `partial def` to WFR.

**Estimated effort:** Medium-High. The optimizer has more complex internal
logic than Semantics.lean (constant folding, boolean simplification, predicate
pushdown into JOINs), so the parameterization and WFR conversion will require
careful handling of the rewrite rules.

**Proposed approach:**
1. Extract `optimizeWindowSpec` and `optimizeOrderByItem` as standalone
   functions parameterized on an `exprOpt : Expr → Expr` callback
2. Attempt WFR conversion of the remaining 4-function core using structural
   recursion on the AST
3. If WFR conversion succeeds, prove bridge lemmas connecting `optimizeExpr`
   to its specification

---

#### E3. Optimizer.lean (query level) — 2 functions, ~13 lines

**Location:** Lines 467–479

**Functions:** `optimizeCTE`, `optimizeQuery`

**Dependency analysis:** `optimizeQuery` calls `optimizeSelectStmt` (from E2)
and `optimizeCTE`. `optimizeCTE` calls `optimizeQuery`. This is truly mutual
but tiny.

**Priority: Medium.** Should be addressed together with E2. If E2 is converted
to WFR, this block could potentially be merged into it or converted alongside.

---

#### E4. Optimizer.lean (cost estimation) — 4 functions, ~66 lines

**Location:** Lines 549–614

**Functions:**
```
estimateExprCost, estimateFromCost,
estimateSelectCost, estimateQueryCost
```

**Dependency analysis:** Same mutual pattern as the optimizer — expressions
contain subqueries. `estimateExprCost` ↔ `estimateSelectCost` form the core
cycle.

**Priority: Low-Medium.** Cost estimation correctness properties (e.g.,
"estimated cost is always positive") could be useful but are not on the current
proving roadmap.

---

## Prioritized Refactoring Roadmap

### Phase 1: Optimizer Core (E2 + E3)
**Goal:** Make `optimizeExpr` and `optimizeSelectStmt` kernel-unfoldable.
**Axiom impact:** Enables proving optimizer preservation theorems (Level 4 in
`PROVING_AXIOMS_PLAN.md`).
**Approach:** Same parameterization + WFR strategy as Semantics.lean PR #153.

### Phase 2: Cost Estimation (E4)
**Goal:** Make cost functions provable for property-based verification.
**Axiom impact:** Minor — enables properties like monotonicity and positivity.
**Approach:** Straightforward WFR conversion; cost functions are structurally
recursive on AST depth.

### Phase 3: Parser (E1)
**Goal:** Improve readability and compile times.
**Axiom impact:** None — no theorems about parsing.
**Approach:** Extract operator precedence chain; parameterize subquery entry
point.

### Phase 4: Type-Structural Mirrors (Category B)
**Goal:** Convert `BEq`/`DecidableEq` to WFR if needed for proofs.
**Axiom impact:** Only relevant if equality reasoning becomes necessary.
**Approach:** Defer until needed.

---

## Design Principles

Based on experience from PR #153 and this audit:

1. **Minimize mutual block membership.** Every function in a `partial def`
   mutual block pays the opacity tax. Only include functions that participate
   in an actual call cycle.

2. **Parameterize to break false dependencies.** If function `f` calls
   function `g` which is in a mutual block, but `f` itself is not called by
   anything in the block, extract `f` and pass `g` as a callback parameter.

3. **Prefer `def` + `sorry` over `partial def`.** A `def` with
   `decreasing_by sorry` in its termination proof is still kernel-unfoldable.
   A `partial def` is not. The `sorry` is a termination obligation, not a
   correctness hole — the function still computes correctly at runtime.

4. **Accept `partial def` for genuinely non-terminating code.** Fixed-point
   iteration, REPL loops, and other inherently non-terminating computations
   should use `partial def` honestly rather than faking termination.

5. **SQL's grammar drives mutual recursion.** The root cause of all mutual
   blocks in this codebase is that SQL expressions can contain subqueries
   (SELECT statements), and SELECT statements contain expressions. This
   single cycle (`Expr ↔ SelectStmt`) propagates through every layer:
   parsing, evaluation, optimization, pretty-printing, and equality. Accept
   this as a fundamental property of the domain, and focus on keeping the
   mutual cores minimal.
