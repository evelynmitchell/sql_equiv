# PostgreSQL as a Testing Oracle for sql_equiv

> **Historical snapshot.** Axiom/theorem counts in this document are as of when it was written. As of 2026-11 the codebase has **0 axioms** (all proved since PR #173) and **689 theorems**; run `python3 tools/count_axioms_theorems.py` for the live count. The optimizer and its axioms that it mentions were removed in PR #156.

## Motivation

The project already uses SQLite as a differential testing oracle
(`LSpecTests/DiffSqlite.lean`). This works well for basic queries but
SQLite diverges from the SQL standard in areas that matter to our
equivalence proofs:

| Feature | sql_equiv model | PostgreSQL | SQLite |
|---------|----------------|------------|--------|
| Three-valued logic | Full (Trilean) | Full | Partial (NULL = falsy) |
| FULL OUTER JOIN | Modeled | Yes | No |
| RIGHT JOIN | Modeled | Yes | Since 3.39 only |
| INTERSECT ALL / EXCEPT ALL | Modeled as SetOp | Yes | No |
| Boolean type | Native (`Value.bool`) | Native | Integer (0/1) |
| Type strictness | 3 types + typed NULL | Strong typing | Type affinity |
| Window functions | Modeled (WindowFunc) | Full support | Partial |
| Recursive CTEs | Modeled | Yes | Yes |
| NULLS FIRST/LAST | Not yet modeled | Yes | No |

PostgreSQL's standard-compliant NULL handling, boolean type, and full
JOIN/set-operation support make it a more faithful oracle for validating
our formal semantics.

## Architecture

```
                    ┌──────────────────────────────────────┐
                    │         Test Harness (Lean)          │
                    │                                      │
                    │  1. Generate (AST₁, AST₂) pair      │
                    │  2. Emit SQL via Pretty.toSql        │
                    │  3. Eval locally via evalSelect      │
                    │  4. Send SQL to PostgreSQL            │
                    │  5. Parse PG result                   │
                    │  6. Compare (bag or exact)            │
                    └─────┬──────────┬──────────┬──────────┘
                          │          │          │
                    ┌─────▼──┐ ┌─────▼──┐ ┌────▼───┐
                    │ Local  │ │ Pretty │ │  PG    │
                    │ eval   │ │ printer│ │ subprocess│
                    └────────┘ └────────┘ └────────┘
```

### Three comparison modes

1. **Semantics validation** — Run one query against both our evaluator and
   PostgreSQL. Detects bugs in `evalExpr`, `evalSelect`, `evalFrom`, etc.
   This is what `DiffSqlite.lean` already does.

2. **Equivalence validation** — Run *two* queries (left and right side of a
   theorem) against PostgreSQL and confirm they produce the same result.
   Detects false equivalence claims (unsound axioms or wrong theorems).

3. **Counterexample search** — For each unproven axiom, generate random
   databases and check whether the axiom's claim holds in PostgreSQL.
   Prioritizes the 13 axioms in `Equiv/` and the 3 optimizer axioms.

## Implementation Plan

### Phase 1: PostgreSQL subprocess driver

Mirror the existing `DiffSqlite.lean` pattern.

```
LSpecTests/
  DiffSqlite.lean      -- existing (keep as-is)
  DiffPostgres.lean     -- new: PG driver + comparison
  DiffPostgresTests.lean -- new: test definitions
```

**`DiffPostgres.lean`** provides:

```lean
namespace DiffPostgres

/-- Run SQL against a disposable PostgreSQL database.
    Uses `psql` subprocess with pipe-separated output. -/
def runPgRaw (setupSql querySql : String) : IO (Except String String)

/-- Parse psql pipe-separated output into Table. -/
def parsePgOutput (output : String) : Table

/-- Compare evaluator result against PostgreSQL result (bag semantics). -/
def resultsMatchBag (ours pg : Table) : Bool

/-- Compare evaluator result against PostgreSQL result (exact, with ordering). -/
def resultsMatchExact (ours pg : Table) : Bool

end DiffPostgres
```

The subprocess call:

```lean
private def runPgRaw (setupSql querySql : String) : IO (Except String String) := do
  let fullSql := setupSql ++ querySql ++ ";\n"
  let child ← IO.Process.spawn {
    cmd := "psql"
    args := #["-h", "localhost", "-U", "sql_equiv_test",
              "-d", "sql_equiv_test",
              "--no-psqlrc",
              "-t",           -- tuples only (no header/footer)
              "-A",           -- unaligned output
              "-F", "|",      -- pipe separator
              "--pset", "null=NULL"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  child.stdin.putStr fullSql
  child.stdin.flush
  let (_stdin, child) ← child.takeStdin
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode != 0 then return .error s!"psql error: {stderr}"
  return .ok stdout
```

### Phase 2: Schema and data translation

Translate the `Database` type to PostgreSQL DDL + DML.

```lean
/-- Generate CREATE TABLE + INSERT statements from a Database value.
    Maps Value.int → INTEGER, Value.string → TEXT, Value.bool → BOOLEAN,
    Value.null → NULL. -/
def databaseToSetupSql (db : Database) (tableNames : List String) : String
```

Key type mappings:

| `Value` | PostgreSQL type | Notes |
|---------|----------------|-------|
| `.int n` | `INTEGER` or `BIGINT` | Use `BIGINT` if `n` overflows 32-bit |
| `.string s` | `TEXT` | No length limit |
| `.bool b` | `BOOLEAN` | Native, unlike SQLite's 0/1 |
| `.null (some .int)` | `NULL::INTEGER` | Typed NULL via cast |
| `.null (some .string)` | `NULL::TEXT` | |
| `.null (some .bool)` | `NULL::BOOLEAN` | |
| `.null none` | `NULL` | Untyped |

Each test runs inside a transaction that is rolled back, or uses
`CREATE TEMPORARY TABLE` so the database stays clean between tests.

### Phase 3: Equivalence pair testing

For each equivalence theorem/axiom, test both sides:

```lean
/-- Test that two SQL expressions produce the same result on a given
    database in PostgreSQL. -/
def diffEquivTest (description : String)
    (left right : SelectStmt)
    (db : Database) (tables : List String) : IO (String × Bool) := do
  let setupSql := databaseToSetupSql db tables
  let leftSql := left.toSql
  let rightSql := right.toSql
  match ← runPgRaw setupSql leftSql, ← runPgRaw setupSql rightSql with
  | .ok lOut, .ok rOut =>
    let lResult := parsePgOutput lOut
    let rResult := parsePgOutput rOut
    return (description, resultsMatchBag lResult rResult)
  | .error e, _ | _, .error e =>
    return (description ++ " [PG error: " ++ e ++ "]", false)
```

### Phase 4: Property-based testing with random databases

Reuse the existing SlimCheck generators from `LSpecTests/Generators.lean`
to produce random expressions, then test equivalences against PostgreSQL:

```lean
/-- Generate a random database with the standard schema but random data.
    Reuse the pattern from LSpecTests/RandomDb.lean. -/
def genRandomDatabase (seed : Nat) : Database

/-- For a generated expression pair (e, optimizeExpr e), verify
    both sides produce the same result in PostgreSQL. -/
def propOptimizeExprPg (seed : Nat) : IO Bool := do
  let db := genRandomDatabase seed
  let e := genExpr seed 3  -- depth-bounded random expression
  let oe := optimizeExpr e
  -- Wrap in SELECT <expr> FROM <table> for evaluation context
  let leftSel := wrapExprInSelect e
  let rightSel := wrapExprInSelect oe
  let (_, passed) ← diffEquivTest "optimizeExpr" leftSel rightSel db ["users"]
  return passed
```

### Phase 5: Axiom-targeted testing

Systematically test each axiom with PostgreSQL. Priority order:

**Unproven axioms in Equiv/ (13 total):**
1. `join_comm` — INNER JOIN commutativity
2. `join_assoc` — INNER JOIN associativity
3. `filter_join_left` / `filter_join_right` — predicate pushdown into joins
4. `normalizeExpr_equiv` — expression normalization soundness
5. `syntacticEquiv_implies_equiv` — syntactic check correctness
6. `selectStmtGround_eval_independent` — ground query context independence
7. `in_subquery_as_exists` / `not_in_subquery_as_not_exists` — IN ↔ EXISTS
8. `in_subquery_unnest_to_join` — IN → semi-join
9. `not_in_subquery_unnest_to_antijoin` — NOT IN → anti-join
10. `in_subquery_implies_join_match` / `join_match_implies_in_subquery`

**Unproven axioms in Optimizer.lean (3 total):**
1. `optimizeExpr_equiv`
2. `optimizeSelectStmt_equiv`
3. `optimize_equiv`

For each axiom, create a test that instantiates the quantified variables
with random values and checks the claim in PostgreSQL.

## Pretty Printer Adjustments

The existing `Pretty.lean` emits standard SQL that PostgreSQL accepts,
with minor exceptions:

| Issue | Current output | PostgreSQL needs | Fix |
|-------|---------------|-----------------|-----|
| Boolean literals | `TRUE` / `FALSE` | `TRUE` / `FALSE` | Already correct |
| Boolean in WHERE | `WHERE 0` | `WHERE FALSE` | Already correct (we emit `FALSE`) |
| LIKE | `LIKE` | `LIKE` | Already correct |
| Integer division | `/` | `/` | Correct (integer division in PG for integer operands) |
| Modulo | `%` | `%` | Already correct |
| Concat | `\|\|` | `\|\|` | Already correct |

No changes to `Pretty.lean` are expected. If edge cases arise, add a
`toPgSql` variant rather than modifying the existing printer.

## Comparison Logic

### Bag comparison (for most equivalences)

PostgreSQL does not guarantee row order without ORDER BY. Most of our
equivalence relations (`≃ᵇ`, `≃ˢ`) don't require order either. Use
sorted multiset comparison:

```lean
def resultsMatchBag (ours pg : Table) : Bool :=
  sortTable (ours.map normalizeRow) == sortTable (pg.map normalizeRow)
```

### Exact comparison (for `≃ₛ` and `≃ᵩ`)

When testing exact `SelectEquiv` or `QueryEquiv`, add `ORDER BY` to
both queries to force deterministic output, then compare directly.

### Column name normalization

Our evaluator produces qualified column names (`users.age`); PostgreSQL
produces unqualified names (`age`). Reuse the existing `stripQualifier`
function from `DiffSqlite.lean`.

## Null Semantics Validation

This is the highest-value area for PostgreSQL over SQLite. Test cases:

1. **NULL propagation in arithmetic**: `NULL + 1 = NULL`
2. **NULL in comparisons**: `NULL = NULL` is `NULL`, not `TRUE`
3. **NULL in boolean logic**: `TRUE AND NULL = NULL`, `FALSE AND NULL = FALSE`
4. **NULL in IN lists**: `1 IN (1, NULL)` is `TRUE`, `2 IN (1, NULL)` is `NULL`
5. **NULL in NOT IN**: `2 NOT IN (1, NULL)` is `NULL` (not `FALSE`)
6. **IS NULL / IS NOT NULL**: always returns boolean, never NULL
7. **COALESCE-like behavior**: CASE WHEN x IS NULL THEN ...
8. **NULL in aggregates**: COUNT skips NULLs, SUM of all NULLs is NULL
9. **NULL in DISTINCT**: all NULLs are treated as equal
10. **NULL in ORDER BY**: PostgreSQL puts NULLs last (ASC) or first (DESC)

Generate tables with strategic NULL placement and verify our `evalBinOp`,
`evalUnaryOp`, and aggregate logic matches PostgreSQL.

## Infrastructure Requirements

### Local development

```bash
# One-time setup
createdb sql_equiv_test
psql -d sql_equiv_test -c "CREATE ROLE sql_equiv_test LOGIN;"

# Or use Docker
docker run -d --name sql_equiv_pg \
  -e POSTGRES_DB=sql_equiv_test \
  -e POSTGRES_USER=sql_equiv_test \
  -e POSTGRES_HOST_AUTH_METHOD=trust \
  -p 5432:5432 postgres:16
```

### CI integration

Add a PostgreSQL service to CI. The test suite should gracefully skip
PG tests when `psql` is unavailable (same pattern as `DiffSqlite.lean`
with `sqlite3Available`):

```lean
private def psqlAvailable : IO Bool := do
  try
    let result ← IO.Process.output {
      cmd := "psql", args := #["--version"]
    }
    return result.exitCode == 0
  catch _ => return false
```

### Environment configuration

```bash
# Connection settings (with defaults)
PG_HOST=localhost     # or from env
PG_PORT=5432
PG_USER=sql_equiv_test
PG_DB=sql_equiv_test
```

## File Layout

```
LSpecTests/
  DiffSqlite.lean           -- existing, unchanged
  DiffPostgres.lean          -- PG subprocess driver + parsing
  DiffPostgresSemantics.lean -- mode 1: evaluator vs PG
  DiffPostgresEquiv.lean     -- mode 2: equivalence pair testing
  DiffPostgresAxioms.lean    -- mode 3: axiom-targeted tests
  DiffPostgresNull.lean      -- NULL semantics deep tests
```

## Success Criteria

1. **All existing proven theorems pass**: Run both sides of every proven
   theorem in `Equiv/` against PostgreSQL on 100+ random databases.
   Zero failures expected.

2. **All axioms pass**: Run both sides of every axiom against PostgreSQL.
   Any failure indicates the axiom is unsound and should be investigated
   before attempting a proof.

3. **Evaluator matches PostgreSQL**: Every query in the existing
   `DiffSqlite.lean` test suite also passes against PostgreSQL, plus
   new tests for FULL JOIN, RIGHT JOIN, boolean columns, and typed NULLs.

4. **NULL edge cases validated**: The 10 null semantics scenarios listed
   above all agree between our evaluator and PostgreSQL.

## Limitations

- **PostgreSQL is not the specification.** It has its own bugs and
  extensions. When PG and our model disagree, either could be wrong.
  The SQL standard (ISO 9075) is the ultimate arbiter.

- **Performance.** Subprocess-per-query is slow. For property-based
  testing with thousands of cases, batch queries into single `psql`
  sessions or use a connection pool via libpq bindings.

- **Coverage.** Testing cannot replace proof. Even 100,000 passing tests
  don't guarantee `∀ db row, ...`. The value is catching bugs in the
  semantics model, not replacing the Lean formalization.

- **Type system gap.** Our 3-type model (int, string, bool) doesn't
  cover float, date, interval, array, JSON, etc. PG tests are limited
  to the modeled types.
