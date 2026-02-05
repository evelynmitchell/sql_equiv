# Plan: Expand SQL Value/Type System

## New Types to Add

| SqlType      | Value Constructor             | Lean Backing Type | SQL Literal Examples                  |
|--------------|-------------------------------|--------------------|---------------------------------------|
| `float`      | `float : Float → Value`      | `Float`            | `1.5`, `3.14`, `1e-10`               |
| `date`       | `date : String → Value`      | `String` (ISO)     | `DATE '2024-01-15'`                   |
| `time`       | `time : String → Value`      | `String` (ISO)     | `TIME '14:30:00'`                     |
| `timestamp`  | `timestamp : String → Value` | `String` (ISO)     | `TIMESTAMP '2024-01-15 14:30:00'`     |

Dates/times stored as ISO-8601 strings — lexicographic ordering matches chronological ordering, so `String.compare` works for comparisons without needing a dedicated date library.

---

## Phase 1: Core Type Definitions (`Ast.lean`)

**Scope:** Add new variants, update helpers. No downstream breakage yet since Lean's exhaustiveness checker will flag every incomplete match for us.

- Add `float | date | time | timestamp` to `SqlType` inductive
- Add `float | date | time | timestamp` constructors to `Value` inductive
- Update `Value.sqlType` — 4 new match arms
- Add `nullFloat`, `nullDate`, `nullTime`, `nullTimestamp` helpers
- Update `Value.toTrilean` — new types return `.unknown` (non-boolean)

---

## Phase 2: Semantics (`Semantics.lean`)

**Value operations:**

| Function        | Changes Needed                                                     |
|-----------------|--------------------------------------------------------------------|
| `Value.eq`      | Add same-type equality for float, date, time, timestamp            |
| `Value.compare` | Add ordering for float (Float.compare), date/time/timestamp (String.compare) |
| `Value.toBool`  | Float: `some (f != 0.0)`. Date/time/timestamp: `none` (not boolean-coercible) |

**Expression evaluation:**

| Function        | Changes Needed                                                     |
|-----------------|--------------------------------------------------------------------|
| `evalBinOp`     | Arithmetic (`+`,`-`,`*`,`/`,`%`): add float cases. Comparisons already delegate to `Value.eq`/`Value.compare` so they come for free. |
| `evalUnaryOp`   | Add `(.neg, .float f) => .float (-f)`                             |
| `evalFunc`      | Add `ABS` for float. Consider `CAST` between int/float. Date functions (EXTRACT, DATE_ADD, etc.) can be deferred to a later phase. |

**Aggregates (SUM, AVG, MIN, MAX):**
- Extend to handle `.float` values alongside `.int`
- AVG over ints could remain int (truncating) or return float — decide based on SQL standard (standard says float)
- MIN/MAX for date/time/timestamp: use string comparison

---

## Phase 3: Parser & Lexer (`Parser.lean`)

**Lexer changes:**
- Extend number tokenization: if digits contain `.` or `e`/`E`, produce a `.floatLit` token instead of `.intLit`
- Add `.floatLit : Float → Token` variant

**Parser changes:**
- `parsePrimary`: handle `.floatLit f => .lit (.float f)`
- Recognize typed literals: `DATE 'yyyy-mm-dd'`, `TIME 'hh:mm:ss'`, `TIMESTAMP 'yyyy-mm-dd hh:mm:ss'`
  - These are keyword + string-literal pairs

---

## Phase 4: Pretty Printer (`Pretty.lean`)

- `Value.toSql`:
  - `.float f => toString f`
  - `.date s => s!"DATE '{s}'"`
  - `.time s => s!"TIME '{s}'"`
  - `.timestamp s => s!"TIMESTAMP '{s}'"`

---

## Phase 5: Optimizer (`Optimizer.lean`, `OptimizerUtils.lean`)

**Constant folding (`Optimizer.lean`):**
- `foldArithmetic`: add float cases for `+`, `-`, `*`, `/` (no `%` for float, or use `Float.mod`)
- `constantFoldUnaryOp`: add `.neg` for float
- Simplification identities: `x + 0.0 => x`, `x * 1.0 => x`, `x * 0.0 => 0.0`

**Value ordering (`OptimizerUtils.lean`):**
- Expand `valueCompare` with new type tag ordering
- Suggested order: `int < float < string < date < time < timestamp < bool < null`

---

## Phase 6: Equivalence Proofs (`Equiv.lean`)

This is the highest-effort phase. Each binary-op commutativity theorem does exhaustive case analysis over `Value × Value`. Adding 4 types takes case count from 4x4=16 to 8x8=64 per theorem.

**Strategy to manage proof explosion:**
- Most new cases are trivial (cross-type ops return `null`) — use `simp` or `decide` tactics
- Factor out a helper lemma: "mismatched types always yield null" to collapse cross-type cases
- Consider using `omega` or `native_decide` for numeric cases
- Existing theorems affected: `evalBinOp_and_comm`, `evalBinOp_or_comm`, `evalBinOp_add_comm`, `evalBinOp_mul_comm`, plus any added since

---

## Phase 7: Tests

- `Test/Common.lean`: add `floatLit`, `dateLit`, `timeLit`, `timestampLit` helpers
- `Test/ParserTest.lean`: float literal parsing, typed date/time/timestamp literal parsing
- `Test/SemanticsTest.lean`: arithmetic with floats, date/time comparisons, aggregates with mixed numeric types

---

## Suggested Implementation Order

1. **Phase 1** (Ast.lean) — everything else follows from this
2. **Phase 4** (Pretty.lean) — quick, unblocks readable test output
3. **Phase 2** (Semantics.lean) — core behavior
4. **Phase 3** (Parser.lean) — can now round-trip
5. **Phase 7** (Tests) — verify everything works
6. **Phase 5** (Optimizer.lean) — constant folding for new types
7. **Phase 6** (Equiv.lean) — proofs last, since they depend on stable semantics

---

## Design Decisions to Make Before Starting

1. **Float representation:** Lean's `Float` is IEEE 754 double. Good enough? (Yes for Spider benchmark.)
2. **Date/time backing type:** ISO-8601 strings vs. structured types? (Strings are simpler, lex-order works.)
3. **Mixed int/float arithmetic:** Should `int + float` auto-coerce? (SQL standard: yes, promote int to float.)
4. **AVG return type:** `AVG(int_col)` returns float? (SQL standard: yes.)
5. **Date arithmetic:** Support `date + int` (add days)? (Defer — not needed for equivalence proofs.)
