# Plan: Expand SQL Value/Type System

## SQL Standard Type Inventory (ISO/IEC 9075)

Complete list of predefined data types from the SQL standard, with our mapping strategy.

### Exact Numeric Types

| SQL Standard Type            | Our SqlType   | Value Constructor                  | Lean Backing Type | Priority | Notes                                      |
|------------------------------|---------------|------------------------------------|--------------------|----------|--------------------------------------------|
| **SMALLINT**                 | `int`         | `int : Int → Value`               | `Int`              | Have     | Lean `Int` is arbitrary precision — covers all three |
| **INTEGER / INT**            | `int`         | `int : Int → Value`               | `Int`              | Have     | ^                                          |
| **BIGINT**                   | `int`         | `int : Int → Value`               | `Int`              | Have     | ^                                          |
| **NUMERIC(p,s)**             | `decimal`     | `decimal : Int → Nat → Value`     | `Int` (scaled)     | High     | Store as scaled integer: value=12345, scale=2 means 123.45 |
| **DECIMAL(p,s) / DEC(p,s)** | `decimal`     | `decimal : Int → Nat → Value`     | `Int` (scaled)     | High     | Same representation as NUMERIC             |

### Approximate Numeric Types

| SQL Standard Type            | Our SqlType   | Value Constructor                  | Lean Backing Type | Priority | Notes                                      |
|------------------------------|---------------|------------------------------------|--------------------|----------|--------------------------------------------|
| **REAL**                     | `float`       | `float : Float → Value`           | `Float`            | High     | Lean `Float` is IEEE 754 double — covers all three |
| **DOUBLE PRECISION**         | `float`       | `float : Float → Value`           | `Float`            | High     | ^                                          |
| **FLOAT(p)**                 | `float`       | `float : Float → Value`           | `Float`            | High     | ^                                          |

### Character String Types

| SQL Standard Type            | Our SqlType   | Value Constructor                  | Lean Backing Type | Priority | Notes                                      |
|------------------------------|---------------|------------------------------------|--------------------|----------|--------------------------------------------|
| **CHAR(n)**                  | `string`      | `string : String → Value`         | `String`           | Have     | Collapse fixed/variable into one — padding semantics ignorable for equivalence |
| **VARCHAR(n)**               | `string`      | `string : String → Value`         | `String`           | Have     | ^                                          |
| **CLOB**                     | `string`      | `string : String → Value`         | `String`           | Have     | ^                                          |

### National Character String Types

| SQL Standard Type            | Our SqlType   | Value Constructor                  | Lean Backing Type | Priority | Notes                                      |
|------------------------------|---------------|------------------------------------|--------------------|----------|--------------------------------------------|
| **NCHAR(n)**                 | `string`      | `string : String → Value`         | `String`           | Low      | Lean `String` is UTF-8 — no distinction needed |
| **NVARCHAR(n)**              | `string`      | `string : String → Value`         | `String`           | Low      | ^                                          |
| **NCLOB**                    | `string`      | `string : String → Value`         | `String`           | Low      | ^                                          |

### Binary String Types

| SQL Standard Type            | Our SqlType   | Value Constructor                  | Lean Backing Type | Priority | Notes                                      |
|------------------------------|---------------|------------------------------------|--------------------|----------|--------------------------------------------|
| **BINARY(n)**                | `binary`      | `binary : ByteArray → Value`      | `ByteArray`        | Low      | Rarely appears in Spider queries           |
| **VARBINARY(n)**             | `binary`      | `binary : ByteArray → Value`      | `ByteArray`        | Low      | ^                                          |
| **BLOB**                     | `binary`      | `binary : ByteArray → Value`      | `ByteArray`        | Low      | ^                                          |

### Boolean Type

| SQL Standard Type            | Our SqlType   | Value Constructor                  | Lean Backing Type | Priority | Notes                                      |
|------------------------------|---------------|------------------------------------|--------------------|----------|--------------------------------------------|
| **BOOLEAN**                  | `bool`        | `bool : Bool → Value`             | `Bool`             | Have     | Already implemented                        |

### Datetime Types

| SQL Standard Type            | Our SqlType       | Value Constructor                      | Lean Backing Type | Priority | Notes                                      |
|------------------------------|-------------------|----------------------------------------|--------------------|----------|--------------------------------------------|
| **DATE**                     | `date`            | `date : String → Value`               | `String` (ISO)     | High     | `'2024-01-15'` — lex order = chrono order  |
| **TIME**                     | `time`            | `time : String → Value`               | `String` (ISO)     | High     | `'14:30:00'`                               |
| **TIME WITH TIME ZONE**      | `time`            | `time : String → Value`               | `String` (ISO)     | Low      | Collapse into `time` — TZ handling deferred |
| **TIMESTAMP**                | `timestamp`       | `timestamp : String → Value`          | `String` (ISO)     | High     | `'2024-01-15 14:30:00'`                    |
| **TIMESTAMP WITH TIME ZONE** | `timestamp`       | `timestamp : String → Value`          | `String` (ISO)     | Low      | Collapse into `timestamp` — TZ handling deferred |

### Interval Types

| SQL Standard Type            | Our SqlType       | Value Constructor                      | Lean Backing Type | Priority | Notes                                      |
|------------------------------|-------------------|----------------------------------------|--------------------|----------|--------------------------------------------|
| **INTERVAL YEAR TO MONTH**   | `interval`        | `interval : Int → IntervalKind → Value`| `Int` + kind tag   | Medium   | Months count (e.g. 14 = 1 year 2 months)  |
| **INTERVAL DAY TO SECOND**   | `interval`        | `interval : Int → IntervalKind → Value`| `Int` + kind tag   | Medium   | Seconds count (possibly with fractional)   |

### XML Type (SQL:2003+)

| SQL Standard Type            | Our SqlType   | Value Constructor                  | Lean Backing Type | Priority | Notes                                      |
|------------------------------|---------------|------------------------------------|--------------------|----------|--------------------------------------------|
| **XML**                      | —             | —                                  | —                  | Skip     | Not relevant for equivalence proofs        |

### JSON (SQL:2016+)

| SQL Standard Type            | Our SqlType   | Value Constructor                  | Lean Backing Type | Priority | Notes                                      |
|------------------------------|---------------|------------------------------------|--------------------|----------|--------------------------------------------|
| **JSON** (not a formal type) | —             | —                                  | —                  | Skip     | Stored in strings per standard; functions not type |

### Collection / Composite Types

| SQL Standard Type            | Our SqlType   | Value Constructor                  | Lean Backing Type | Priority | Notes                                      |
|------------------------------|---------------|------------------------------------|--------------------|----------|--------------------------------------------|
| **ARRAY**                    | —             | —                                  | —                  | Skip     | Not in Spider benchmark                    |
| **MULTISET**                 | —             | —                                  | —                  | Skip     | ^                                          |
| **ROW**                      | —             | —                                  | —                  | Skip     | ^                                          |

### Summary: Our Type Mapping

Many SQL standard types collapse into fewer `SqlType` variants because Lean's types are more general:

| Our SqlType    | SQL Standard Types Covered                                         | Status   |
|----------------|--------------------------------------------------------------------|----------|
| `int`          | SMALLINT, INTEGER, BIGINT                                          | **Have** |
| `string`       | CHAR, VARCHAR, CLOB, NCHAR, NVARCHAR, NCLOB                       | **Have** |
| `bool`         | BOOLEAN                                                            | **Have** |
| `unknown`      | Untyped NULL / indeterminate                                       | **Have** |
| `float`        | REAL, DOUBLE PRECISION, FLOAT(p)                                   | **To add — High** |
| `decimal`      | NUMERIC(p,s), DECIMAL(p,s)                                        | **To add — High** |
| `date`         | DATE                                                               | **To add — High** |
| `time`         | TIME, TIME WITH TIME ZONE                                          | **To add — High** |
| `timestamp`    | TIMESTAMP, TIMESTAMP WITH TIME ZONE                                | **To add — High** |
| `interval`     | INTERVAL YEAR TO MONTH, INTERVAL DAY TO SECOND                    | **To add — Medium** |
| `binary`       | BINARY, VARBINARY, BLOB                                            | **To add — Low** |
| —              | XML, JSON, ARRAY, MULTISET, ROW                                   | **Skip** |

---

## New Types to Add

### High Priority

| SqlType      | Value Constructor                    | Lean Backing Type     | SQL Literal Examples                  |
|--------------|--------------------------------------|-----------------------|---------------------------------------|
| `float`      | `float : Float → Value`             | `Float`               | `1.5`, `3.14`, `1e-10`               |
| `decimal`    | `decimal : Int → Nat → Value`       | `Int` (scaled) + `Nat` (scale) | `DECIMAL '123.45'` or via CAST |
| `date`       | `date : String → Value`             | `String` (ISO)        | `DATE '2024-01-15'`                   |
| `time`       | `time : String → Value`             | `String` (ISO)        | `TIME '14:30:00'`                     |
| `timestamp`  | `timestamp : String → Value`        | `String` (ISO)        | `TIMESTAMP '2024-01-15 14:30:00'`     |

### Medium Priority

| SqlType      | Value Constructor                    | Lean Backing Type     | SQL Literal Examples                  |
|--------------|--------------------------------------|-----------------------|---------------------------------------|
| `interval`   | `interval : Int → IntervalKind → Value` | `Int` + kind tag  | `INTERVAL '3' DAY`, `INTERVAL '1-6' YEAR TO MONTH` |

### Low Priority

| SqlType      | Value Constructor                    | Lean Backing Type     | SQL Literal Examples                  |
|--------------|--------------------------------------|-----------------------|---------------------------------------|
| `binary`     | `binary : ByteArray → Value`        | `ByteArray`           | `X'48656C6C6F'`                       |

### Representation Notes

- **Dates/times** stored as ISO-8601 strings — lexicographic ordering matches chronological ordering, so `String.compare` works for comparisons without needing a dedicated date library.
- **Decimal** stored as scaled integer + scale: `decimal 12345 2` represents `123.45`. This preserves exact arithmetic without floating-point error.
- **Interval** needs a kind tag to distinguish year-month from day-time intervals (they are not interchangeable per the standard). Could be a simple enum: `inductive IntervalKind | yearMonth | daySecond`.

---

## Phase 1: Core Type Definitions (`Ast.lean`)

**Scope:** Add new variants, update helpers. No downstream breakage yet since Lean's exhaustiveness checker will flag every incomplete match for us.

- Add `float | decimal | date | time | timestamp` to `SqlType` inductive (high priority)
- Add `interval | binary` to `SqlType` inductive (medium/low priority, can defer)
- Add `IntervalKind` enum: `yearMonth | daySecond`
- Add corresponding constructors to `Value` inductive
- Update `Value.sqlType` — new match arms per type
- Add null helpers: `nullFloat`, `nullDecimal`, `nullDate`, `nullTime`, `nullTimestamp`, `nullInterval`, `nullBinary`
- Update `Value.toTrilean` — new types return `.unknown` (non-boolean)

---

## Phase 2: Semantics (`Semantics.lean`)

**Value operations:**

| Function        | Changes Needed                                                     |
|-----------------|--------------------------------------------------------------------|
| `Value.eq`      | Add same-type equality for all new types. Decimal: compare scaled values (normalize scales first). Float: IEEE equality. Date/time/timestamp: string equality. Binary: byte equality. Interval: same-kind integer equality. |
| `Value.compare` | Float: `Float.compare`. Decimal: normalize then compare scaled ints. Date/time/timestamp: `String.compare` (ISO order = chrono order). Interval: compare within same kind. Binary: lexicographic byte comparison. |
| `Value.toBool`  | Float: `some (f != 0.0)`. Decimal: `some (n != 0)`. All others: `none` (not boolean-coercible). |

**Expression evaluation:**

| Function        | Changes Needed                                                     |
|-----------------|--------------------------------------------------------------------|
| `evalBinOp`     | Arithmetic (`+`,`-`,`*`,`/`,`%`): add float and decimal cases. Decimal arithmetic must handle scale alignment. Comparisons already delegate to `Value.eq`/`Value.compare` so they come for free. Date + interval arithmetic (deferred). |
| `evalUnaryOp`   | Add negation for float (`-f`) and decimal (`-n, scale`)           |
| `evalFunc`      | `ABS` for float and decimal. `CAST` between int/float/decimal/string. Date functions (EXTRACT, DATE_ADD, etc.) deferred to later phase. |

**Aggregates (SUM, AVG, MIN, MAX):**
- Extend to handle `.float` and `.decimal` values alongside `.int`
- AVG over ints returns float (per SQL standard)
- AVG over decimals returns decimal (preserving precision)
- MIN/MAX for date/time/timestamp: use string comparison
- SUM/AVG not defined for binary or interval-across-kinds

**Type coercion rules (SQL standard):**
- `int` op `float` → promote int to float
- `int` op `decimal` → promote int to decimal (scale 0)
- `decimal` op `float` → promote decimal to float
- Date/time/interval arithmetic deferred

---

## Phase 3: Parser & Lexer (`Parser.lean`)

**Lexer changes:**
- Extend number tokenization: if digits contain `.` or `e`/`E`, produce a `.floatLit` token instead of `.intLit`
- Add `.floatLit : Float → Token` variant
- Add keywords: `DATE`, `TIME`, `TIMESTAMP`, `INTERVAL`, `YEAR`, `MONTH`, `DAY`, `HOUR`, `MINUTE`, `SECOND`

**Parser changes:**
- `parsePrimary`: handle `.floatLit f => .lit (.float f)`
- Recognize typed literals:
  - `DATE 'yyyy-mm-dd'` → `.lit (.date "yyyy-mm-dd")`
  - `TIME 'hh:mm:ss'` → `.lit (.time "hh:mm:ss")`
  - `TIMESTAMP 'yyyy-mm-dd hh:mm:ss'` → `.lit (.timestamp "...")`
  - `INTERVAL 'n' DAY` / `INTERVAL 'n-n' YEAR TO MONTH` → `.lit (.interval n kind)`
  - `X'hex'` → `.lit (.binary bytes)` (low priority)
- Decimal literals: numbers with `.` but no `e`/`E` could be parsed as decimal instead of float (design decision — see below)

---

## Phase 4: Pretty Printer (`Pretty.lean`)

- `Value.toSql`:
  - `.float f => toString f`
  - `.decimal n s => formatDecimal n s` (e.g. 12345 with scale 2 → `"123.45"`)
  - `.date s => s!"DATE '{s}'"`
  - `.time s => s!"TIME '{s}'"`
  - `.timestamp s => s!"TIMESTAMP '{s}'"`
  - `.interval n .yearMonth => s!"INTERVAL '{formatYM n}' YEAR TO MONTH"`
  - `.interval n .daySecond => s!"INTERVAL '{n}' SECOND"`
  - `.binary bs => s!"X'{bytesToHex bs}'"` (low priority)

---

## Phase 5: Optimizer (`Optimizer.lean`, `OptimizerUtils.lean`)

**Constant folding (`Optimizer.lean`):**
- `foldArithmetic`: add float cases for `+`, `-`, `*`, `/` (no `%` for float, or use `Float.mod`)
- `constantFoldUnaryOp`: add `.neg` for float
- Simplification identities: `x + 0.0 => x`, `x * 1.0 => x`, `x * 0.0 => 0.0`

**Value ordering (`OptimizerUtils.lean`):**
- Expand `valueCompare` with new type tag ordering
- Suggested order: `int < float < decimal < string < date < time < timestamp < interval < binary < bool < null`

---

## Phase 6: Equivalence Proofs (`Equiv.lean`)

This is the highest-effort phase. Each binary-op commutativity theorem does exhaustive case analysis over `Value × Value`. Adding all types takes case count from 4x4=16 to potentially 11x11=121 per theorem (though binary/interval can likely be deferred).

**Strategy to manage proof explosion:**
- Most new cases are trivial (cross-type ops return `null`) — use `simp` or `decide` tactics
- Factor out a helper lemma: "mismatched types always yield null" to collapse cross-type cases
- Consider using `omega` or `native_decide` for numeric cases
- Existing theorems affected: `evalBinOp_and_comm`, `evalBinOp_or_comm`, `evalBinOp_add_comm`, `evalBinOp_mul_comm`, plus any added since

---

## Phase 7: Tests

- `Test/Common.lean`: add helpers — `floatLit`, `decimalLit`, `dateLit`, `timeLit`, `timestampLit`, `intervalLit`, `binaryLit`
- `Test/ParserTest.lean`: float literal parsing, decimal literal parsing, typed date/time/timestamp/interval literal parsing, hex binary literals
- `Test/SemanticsTest.lean`: arithmetic with floats, decimal scale alignment, date/time comparisons, aggregates with mixed numeric types, type coercion (int+float, int+decimal, decimal+float)

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
4. **Mixed int/decimal arithmetic:** Should `int + decimal` auto-coerce? (SQL standard: yes, promote int to decimal with scale 0.)
5. **Mixed decimal/float arithmetic:** Should `decimal + float` auto-coerce? (SQL standard: yes, promote decimal to float — loses precision.)
6. **AVG return type:** `AVG(int_col)` returns float? (SQL standard: yes.)
7. **Date arithmetic:** Support `date + interval` → date? (Defer — not needed for equivalence proofs.)
8. **Numeric literal parsing:** Is `3.14` a float or a decimal? (SQL standard: it's exact numeric, i.e. decimal. But many DBs treat it as float. Suggest: parse as decimal, use `CAST` or scientific notation for float.)
9. **Decimal normalization:** Is `decimal 10 1` (= 1.0) equal to `decimal 1 0` (= 1)? (Should be yes — normalize before comparison.)
10. **Interval representation:** Single `Int` for both kinds? Year-month as total months, day-second as total seconds? (Simplest approach, sufficient for equivalence.)
