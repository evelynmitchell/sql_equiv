# Concrete Plan: Proving the Complete List of SQL Types

This plan turns the type expansion roadmap (`PLAN_expand_types.md`) into a concrete,
ordered checklist of implementation and proof tasks.

> **Status (2026-11):** Batch 1a (DECIMAL/NUMERIC) has shipped (#201; PRs #205,
> #207, #208), so `Value` now has five constructors: `int`, `string`, `bool`,
> `decimal`, `null`. The optimizer steps are struck through because that module
> was removed (PR #156). The "Current State" section below describes the plan's
> starting point; counts in it are as of writing (now: 0 axioms, 622 theorems).

---

## Current State

**4 types today:**

| SqlType   | Value constructor       | Lean backing | Proofs affected |
|-----------|-------------------------|--------------|-----------------|
| `int`     | `int : Int -> Value`    | `Int`        | All theorems in `Equiv/` modules |
| `string`  | `string : String -> Value` | `String`  | All theorems in `Equiv/` modules |
| `bool`    | `bool : Bool -> Value`  | `Bool`       | All theorems in `Equiv/` modules |
| `unknown` | `null : Option SqlType -> Value` | -   | All theorems in `Equiv/` modules |

**Proof case counts:** Each binary-op commutativity theorem currently does
exhaustive case analysis over `Option Value x Option Value`. With 4 value
constructors + `none`, that's 5x5 = 25 cases per theorem. Many resolve by `rfl`.

> **Refresh (2026-06, #200):** All axioms are now proven theorems (561 theorems,
> ratchet at 0), so adding a constructor means extending *proofs*, not just
> statements. Measured blast radius — `.null` match-arm sites that need a sibling
> arm per new constructor: `Equiv/Comparison.lean` 57, `Equiv/ValueLemmas.lean` 55,
> `SemanticsBase.lean` 43, `Semantics.lean` 21, all other files ≤ 4 each (~190
> total). The statement-level theorem files (`Equiv/StatementAxioms.lean`: 2) are
> insulated because they work at expression level. The `first | rfl | ...`
> fallback combinators in `Comparison.lean` absorb new same-shape cases
> automatically. The optimizer module was removed in PR #156; optimizer steps
> below are struck. Tracking issues: #200 (this refresh), #201 (decimal),
> #202 (float decision), #203 (DuckDB oracle).

---

## Target State

**11 types total** (4 existing + 5 high + 1 medium + 1 low):

| SqlType     | Value constructor                    | Lean backing          | Priority |
|-------------|--------------------------------------|-----------------------|----------|
| `int`       | `int : Int -> Value`                 | `Int`                 | Have     |
| `string`    | `string : String -> Value`           | `String`              | Have     |
| `bool`      | `bool : Bool -> Value`               | `Bool`                | Have     |
| `unknown`   | `null : Option SqlType -> Value`     | -                     | Have     |
| `float`     | `float : Float -> Value`             | `Float`               | High     |
| `decimal`   | `decimal : Int -> Nat -> Value`      | `Int` (scaled)        | High     |
| `date`      | `date : String -> Value`             | `String` (ISO-8601)   | High     |
| `time`      | `time : String -> Value`             | `String` (ISO-8601)   | High     |
| `timestamp` | `timestamp : String -> Value`        | `String` (ISO-8601)   | High     |
| `interval`  | `interval : Int -> IntervalKind -> Value` | `Int` + kind tag | Medium   |
| `binary`    | `binary : ByteArray -> Value`        | `ByteArray`           | Low      |

**New proof case counts:** With 11 Value constructors (10 non-null types + null) +
`none`, each binary-op theorem grows to 12x12 = 144 cases. The cross-type cases are
overwhelmingly trivial (`rfl`), but they need to be written.

---

## NULL Semantics Invariant (binding on every batch)

NULLs are **never** errors. Per the SQL standard:

- **NULL propagation:** any arithmetic/comparison/string op with a NULL operand
  yields SQL NULL (`some (.null none)`) — never `none`.
- **Three-valued logic:** AND/OR follow the standard's truth tables, including
  the dominance rules `FALSE AND NULL = FALSE` and `TRUE OR NULL = TRUE`
  (short-circuit arms fire before null propagation).
- **Aggregates:** SUM/AVG/MIN/MAX ignore NULL inputs; empty input yields NULL.
- `none` is reserved for what the standard rejects as a *type error*
  (e.g. `1 + 'abc'`) or a genuine evaluation error (missing column).

**Mechanism:** the null-propagation arms in `evalBinOp` use wildcards
(`| op, some (.null _), some _ => some (.null none)` and its mirror), so every
new `Value` constructor inherits standard NULL behavior automatically — e.g.
`decimal + NULL = NULL` holds by construction with zero new arms. When adding a
type, keep its arms *below* the null-propagation arms and never add a
constructor-specific null arm. The differential tests against sqlite3 (and
DuckDB once #203 lands) validate this end-to-end; extend them with
NULL-with-new-type cases in every batch.

---

## Implementation Batches

The work is divided into 4 batches, each independently shippable.

### Batch 1: Float and Decimal (highest value, unblocks numeric proofs)

**Why first:** These two types are needed for the widest range of SQL equivalence
proofs: arithmetic commutativity/associativity, comparison flips, aggregate
semantics (AVG returns float per SQL standard), and type coercion rules.

> **Status (2026-06): Batch 1a (decimal) SHIPPED** — PR #205 (constructor,
> scale-aligned arithmetic, int↔decimal promotion, parser, proofs, tests),
> PR #207 (aggregates over decimal + DuckDB oracle), PR #208 (ORDER BY).
> Checkboxes below: decimal halves are done; float halves await #202.
> Remaining decimal items tracked on #201: div/mod scale policy, denotation
> lemmas (IsCanonical/mkDecimal), CAST.
>
> **Refresh (2026-06, #200): Batch 1 is split.** Do **decimal first (#201)** —
> scaled-integer arithmetic is exact, so existing proof patterns carry over.
> **Float is gated on a design decision (#202)**: IEEE `Float` falsifies theorems
> this library proves (`NaN ≠ NaN` vs `eq_reflexive`; NaN unordered vs
> `Value.compare` totality; `-0.0 + 0 = +0.0` vs `x + 0 = x`). Decide
> IEEE-with-preconditions vs rationals vs defer before touching float.
> Float-specific checklist items below are deferred with it.

#### Step 1.1: AST changes (`Ast.lean`)

- [ ] Add `float` and `decimal` to `SqlType` inductive
- [ ] Add `float : Float -> Value` and `decimal : Int -> Nat -> Value` to `Value`
- [ ] Update `Value.sqlType` with new match arms
- [ ] Add `nullFloat`, `nullDecimal` helpers
- [ ] Update `Value.toTrilean` (float/decimal -> `.unknown`)
- [ ] Fix all exhaustiveness errors (Lean will flag every incomplete match)

**Risk:** This step alone breaks the build because every `match` on `Value` becomes
incomplete. Plan to fix all modules in one pass.

#### Step 1.2: Semantics (`Semantics.lean`)

- [ ] `Value.eq`: float=float (IEEE `==`), decimal=decimal (normalize scales, compare)
- [ ] `Value.compare`: float (`Float.lt`), decimal (normalize then compare scaled ints)
- [ ] `Value.toBool`: float (`f ≠ 0.0 -> some true`), decimal (`n ≠ 0 -> some true`)
- [ ] `evalBinOp`: arithmetic for float and decimal
  - [ ] float +/-/*/div float
  - [ ] decimal +/-/* decimal (scale alignment: `max(s1,s2)` for +/-, `s1+s2` for *)
  - [ ] decimal / decimal (scale handling TBD -- return float? or fixed scale?)
- [ ] Type coercion: `int op float -> promote int`, `int op decimal -> promote int`, `decimal op float -> promote decimal`
- [ ] `evalUnaryOp`: neg for float (`-f`) and decimal (`-n, s`)
- [ ] Aggregates: extend SUM/AVG/MIN/MAX for float and decimal values

#### Step 1.3: Parser (`Parser.lean`)

- [ ] Tokenizer: recognize decimal point in number literals (`.` without `e/E` -> decimal, with `e/E` -> float)
- [ ] Add `floatLit` token variant if not present
- [ ] `parsePrimary`: handle float/decimal literal -> `Expr.lit`
- [ ] Parse `CAST(expr AS FLOAT)` and `CAST(expr AS DECIMAL(p,s))` (requires CAST infrastructure)

#### Step 1.4: Pretty printer (`Pretty.lean`)

- [ ] `Value.toSql` for float and decimal
- [ ] Decimal display: `formatDecimal 12345 2 = "123.45"`

#### ~~Step 1.5: Optimizer (`Optimizer.lean`)~~ — module removed in PR #156

The certified rewriter (`Rewriter.lean`) replaced the optimizer. If decimal/float
constant-folding rules are added there, each rule carries its own proof, so this
is covered by Step 1.6 rather than a separate step. (Note: `x + 0.0 = x` is
**false** for IEEE float when `x = -0.0` — see #202.)

#### Step 1.6: Proofs (`Equiv/` modules — primarily `Comparison.lean`, `ValueLemmas.lean`)

This is the bulk of the work. Each existing commutativity/associativity theorem
needs new case arms for float and decimal.

**Strategy to manage proof explosion:**

1. **Factor out a "mismatched types" lemma.** ⚠️ As originally drafted this
   lemma is **false** under the Option 3 semantics that landed (PR #125):
   a cross-type operation on non-null operands is an *error* (`none`), not
   SQL NULL — `Value.eq`/`Value.compare` return `none` on mismatch and
   `evalBinOp`'s catch-all returns `none`. The correct statement is:
   ```lean
   theorem mismatched_types_error (op : BinOp) (v1 v2 : Value)
     (h1 : ¬ v1.isNull) (h2 : ¬ v2.isNull)
     (h : v1.sqlType ≠ v2.sqlType)
     (hop : op ∈ [.add, .sub, .mul, .div, .mod, .lt, .le, .gt, .ge]) :
     evalBinOp op (some v1) (some v2) = none := by ...
   ```
   (Null operands are excluded — they take the null-propagation arms first.
   `.eq`/`.ne` also satisfy this today, but keep them out of `hop` if numeric
   coercion is added, since `1 = 1.0` should then be `true`, not an error.)
   **Coercion caveat:** SQL promotes `INT op DECIMAL` rather than erroring.
   If #201 adds int↔decimal promotion, those pairs are carved out of this
   lemma's `hop`/type hypotheses — decide promotion *before* proving it.
   This one lemma collapses the remaining cross-type cases to a single invocation.

2. **Use `simp` + `decide` aggressively** for same-type arithmetic cases.

3. **Batch the case arms** -- Lean's `match` can handle wildcards; use `| _, _ => rfl`
   for the trivial cross-type fallthrough where possible.

**Affected proofs (non-exhaustive):**

| Theorem | Current cases | After batch 1 |
|---------|:------------:|:--------------:|
| `evalBinOp_and_comm` | 25 | 49 |
| `evalBinOp_or_comm` | 25 | 49 |
| `evalBinOp_add_comm` | 25 | 49 |
| `evalBinOp_mul_comm` | 25 | 49 |
| `evalBinOp_eq_comm` | 25 | 49 |
| (all other binary-op theorems) | 25 | 49 |

New proofs to add:
- [ ] `float_add_comm`: `a + b = b + a` for floats (IEEE caveats: NaN)
- [ ] `float_mul_comm`: `a * b = b * a` for floats
- [ ] `decimal_add_comm`: `a + b = b + a` for decimals
- [ ] `decimal_mul_comm`: `a * b = b * a` for decimals
- [ ] `decimal_eq_normalized`: `decimal 10 1 = decimal 1 0` (1.0 = 1)
- [ ] `int_float_coerce_comm`: coercion is order-independent
- [ ] `int_decimal_coerce_comm`: coercion is order-independent

#### Step 1.7: Tests

- [ ] Float literal parsing: `3.14e2`, `1.5`, `-0.001`
- [ ] Decimal literal parsing: `123.45` (no exponent)
- [ ] Float arithmetic evaluation
- [ ] Decimal arithmetic with scale alignment
- [ ] Type coercion: `1 + 1.5`, `1 + DECIMAL '2.50'`
- [ ] Aggregates: `AVG` over ints returns float

---

### Batch 2: Date, Time, Timestamp (unblocks temporal queries)

**Why second:** Datetime types are the second most impactful gap. They appear in
nearly every business-domain query. The ISO-8601 string representation means
comparisons come "for free" via `String.compare`.

#### Step 2.1: AST changes (`Ast.lean`)

- [ ] Add `date`, `time`, `timestamp` to `SqlType`
- [ ] Add corresponding `Value` constructors (all `String`-backed)
- [ ] Update helpers: `nullDate`, `nullTime`, `nullTimestamp`
- [ ] Update `Value.sqlType`, `Value.toTrilean`

#### Step 2.2: Semantics (`Semantics.lean`)

- [ ] `Value.eq`: string equality for same datetime types
- [ ] `Value.compare`: `String.compare` (ISO order = chrono order)
- [ ] No arithmetic ops (date + interval deferred to Batch 3)
- [ ] Aggregates: MIN/MAX for datetime types via string comparison

#### Step 2.3: Parser (`Parser.lean`)

- [ ] Recognize typed literals: `DATE 'yyyy-mm-dd'`, `TIME 'hh:mm:ss'`, `TIMESTAMP '...'`
- [ ] Add `DATE`, `TIME`, `TIMESTAMP` keywords

#### Step 2.4: Pretty printer (`Pretty.lean`)

- [ ] `Value.toSql`: `DATE '2024-01-15'`, `TIME '14:30:00'`, `TIMESTAMP '...'`

#### ~~Step 2.5: Optimizer (`Optimizer.lean`)~~ — module removed in PR #156

Datetime constant-folding, if wanted, goes in the certified rewriter
(`Rewriter.lean`) with per-rule proofs; covered by Step 2.6.

#### Step 2.6: Proofs (`Equiv/` modules — primarily `Comparison.lean`, `ValueLemmas.lean`)

Case count grows from 49 (post-batch-1) to 100. Again, all new cross-type cases
resolve by `rfl`. The same "mismatched types" lemma applies.

New proofs:
- [ ] `date_eq_comm`: `DATE 'a' = DATE 'b'  <=>  DATE 'b' = DATE 'a'`
- [ ] `timestamp_compare_flip`: `a < b  <=>  b > a` for timestamps
- [ ] `datetime_min_max_comm`: MIN/MAX commutativity for temporal values
- [ ] `datetime_null_propagation`: NULL date comparisons yield UNKNOWN

#### Step 2.7: Tests

- [ ] Date literal parsing and round-trip
- [ ] Time literal parsing and round-trip
- [ ] Timestamp literal parsing and round-trip
- [ ] Datetime comparison evaluation
- [ ] MIN/MAX over date columns

---

### Batch 3: Interval (unblocks date arithmetic)

#### Step 3.1: AST changes

- [ ] Add `IntervalKind` enum: `yearMonth | daySecond`
- [ ] Add `interval` to `SqlType`
- [ ] Add `interval : Int -> IntervalKind -> Value` to `Value`
- [ ] Helpers: `nullInterval`

#### Step 3.2: Semantics

- [ ] `Value.eq`: same-kind integer equality
- [ ] `Value.compare`: same-kind integer comparison (cross-kind = incomparable)
- [ ] Date arithmetic: `date + interval yearMonth -> date`, `timestamp + interval daySecond -> timestamp`
- [ ] Interval arithmetic: `interval + interval` (same kind), `n * interval`

#### Step 3.3: Parser

- [ ] Recognize: `INTERVAL '3' DAY`, `INTERVAL '1-6' YEAR TO MONTH`
- [ ] Keywords: `INTERVAL`, `YEAR`, `MONTH`, `DAY`, `HOUR`, `MINUTE`, `SECOND`

#### Step 3.4: Pretty printer

- [ ] `Value.toSql` for interval values

#### Step 3.5: Proofs

New proofs:
- [ ] `interval_add_comm`: same-kind interval addition is commutative
- [ ] `date_interval_assoc`: `(d + i1) + i2 = d + (i1 + i2)`
- [ ] `interval_null_propagation`

#### Step 3.6: Tests

- [ ] Interval literal parsing
- [ ] Date + interval arithmetic
- [ ] Cross-kind interval rejection

---

### Batch 4: Binary (low priority, completeness)

#### Step 4.1: AST

- [ ] Add `binary` to `SqlType`
- [ ] Add `binary : ByteArray -> Value` to `Value`

#### Step 4.2: Semantics

- [ ] `Value.eq`: byte-level equality
- [ ] `Value.compare`: lexicographic byte comparison
- [ ] No arithmetic ops

#### Step 4.3: Parser

- [ ] Recognize hex literals: `X'48656C6C6F'`

#### Step 4.4: Proofs

- [ ] `binary_eq_comm`: equality is symmetric
- [ ] All cross-type cases (trivial `rfl`)

#### Step 4.5: Tests

- [ ] Hex literal parsing
- [ ] Binary equality and comparison

---

## Proof Explosion Mitigation Strategy

This is the single biggest risk. Adding types multiplies case arms quadratically.

### Approach 1: Cross-type elimination lemma (recommended)

Most binary operations return NULL when operand types don't match. Factor this out:

```lean
/-- For arithmetic/comparison ops, mismatched types always yield NULL -/
lemma mismatched_types_null (op : BinOp) (v1 v2 : Value)
  (h : v1.sqlType ≠ v2.sqlType)
  (hop : op ∈ [.add, .sub, .mul, .div, .mod, .eq, .ne, .lt, .le, .gt, .ge]) :
  evalBinOp op (some v1) (some v2) = some (Value.null none) := by
  cases v1 <;> cases v2 <;> simp_all [evalBinOp, Value.sqlType]
```

With this, a commutativity proof becomes:
1. Same-type cases (one per non-null value type) -- each needs type-specific reasoning
2. Cross-type cases -- single invocation of `mismatched_types_null` + `rfl`
3. NULL cases -- a few arms as today

This reduces per-theorem effort from 144 explicit cases to ~20-25.

### Approach 2: Custom tactic

The `Tactics.lean` module already has custom tactics. Add:

```lean
/-- Tactic that handles all cross-type cases in binary op proofs -/
macro "cross_type_cases" : tactic => ...
```

### Approach 3: Decision procedure

For commutativity of pure arithmetic, `native_decide` or `omega` may close goals
automatically. Worth testing on a few theorems before committing to manual cases.

**Recommendation:** Implement Approach 1 first (the elimination lemma), then layer
Approach 2 on top if manual proof burden is still high.

---

## Dependency Graph

```
Batch 1 (float, decimal)
  ├── Unblocks: numeric equivalence proofs, AVG return type, type coercion
  │
  ├── Batch 2 (date, time, timestamp)  [can start in parallel for AST/parser]
  │     ├── Unblocks: temporal query proofs, MIN/MAX over dates
  │     │
  │     └── Batch 3 (interval)  [depends on Batch 2 for date arithmetic]
  │           └── Unblocks: date arithmetic proofs
  │
  └── Batch 4 (binary)  [independent, can happen any time]
        └── Unblocks: completeness vs SQL standard
```

Batches 1 and 2 can proceed in parallel for AST/Parser/Pretty changes, but
proofs must be done sequentially (each batch's proof work depends on the
`mismatched_types_null` lemma being updated for all types added so far).

---

## Design Decisions (need resolution before starting)

These were identified in `PLAN_expand_types.md` and remain open:

| # | Question | Recommendation | Impact |
|---|----------|---------------|--------|
| 1 | Is `3.14` a float or decimal? | **Decimal** (SQL standard). Use `3.14e0` for float. | Parser, tests |
| 2 | Is `decimal 10 1` equal to `decimal 1 0`? | **Yes** -- normalize before comparison. | `Value.eq`, proofs |
| 3 | What does `decimal / decimal` return? | **Float** (matches PostgreSQL behavior). | Semantics, proofs |
| 4 | Does `AVG(int_col)` return float? | **Yes** (SQL standard). | Aggregates |
| 5 | IEEE NaN handling in float equality? | **NaN = NaN is false** (SQL follows IEEE). Commutativity of `=` still holds since both sides return false. | Float proofs |
| 6 | Float associativity? | **Do NOT prove** `(a+b)+c = a+(b+c)` for floats (false in IEEE). Only prove commutativity. | Proof scope |

---

## Estimated Effort per Batch

| Batch | AST + Semantics | Parser + Pretty | Proofs | Tests | Total |
|-------|:--------------:|:---------------:|:------:|:-----:|:-----:|
| 1: float + decimal | Medium | Medium | **High** | Medium | **Large** |
| 2: date/time/timestamp | Low | Medium | Medium | Low | **Medium** |
| 3: interval | Low | Medium | Medium | Low | **Medium** |
| 4: binary | Low | Low | Low | Low | **Small** |

The proof work in Batch 1 is the hardest because it's where we establish the
cross-type elimination pattern. Once that's solid, Batches 2-4 are incremental.

---

## Success Criteria

After all 4 batches:

- [ ] `SqlType` covers all 11 types (int, string, bool, unknown, float, decimal, date, time, timestamp, interval, binary)
- [ ] `lake build` succeeds with no errors
- [ ] All existing theorems in the `Equiv/` modules re-proven with expanded case analysis
- [ ] New type-specific theorems proven (commutativity, null propagation, comparison flips)
- [ ] `mismatched_types_null` lemma proven for all type pairs
- [ ] Parser handles float literals, decimal literals, typed datetime literals, interval literals, hex binary literals
- [ ] Pretty printer round-trips all new value types
- [ ] Certified rewriter (`Rewriter.lean`) constant-folds arithmetic for float and decimal (with per-rule proofs)
- [ ] Test suite covers all new types
- [ ] Axiom count does not increase (new theorems should be proven, not axiomatized)

---

## Relationship to Other Plans

| Plan | Relationship |
|------|-------------|
| `PLAN_expand_types.md` | This plan **concretizes** that plan with proof-level detail |
| `SQL_GAP_ANALYSIS.md` | Type expansion closes the "Data Types" section gaps |
| `PROVING_AXIOMS_PLAN.md` | Proof work here is orthogonal -- type expansion doesn't add new axioms |
| `CERTIFIED_REWRITER.md` | Rewriter rules carry their own proofs; new-type folding rules go there (optimizer removed in PR #156) |
| `COVERAGE_MATRIX.md` | Updates needed after each batch ships |

---

*Created: 2026-02-06*
