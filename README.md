# SQL Equiv

A SQL parser and semantic equivalence prover written in Lean 4. This project provides formal verification of SQL query equivalences, enabling you to prove that two SQL queries produce identical results for all possible databases.

## Overview

SQL Equiv is a comprehensive toolkit for:

- **Parsing SQL** - Full DML support with a hand-rolled recursive descent parser
- **Evaluating queries** - A relational algebra-based semantic model
- **Proving equivalences** - Formal proofs that two SQL expressions/queries are semantically equivalent
- **Custom tactics** - Lean 4 tactics specifically designed for SQL equivalence proofs

The project is designed for compatibility with the Spider benchmark and supports complex SQL features including subqueries, aggregates, joins, and set operations.

**Trust base.** Every theorem and proof-carrying definition in the library is checked by Lean's kernel using only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`, no `native_decide`, no project axioms. `Test/TrustBaseTest.lean` checks this for every constant in the namespace, private ones included. It is part of `lake build sql_equiv_test`, which CI builds; plain `lake build` does not run it. What the theorems cover is narrower than what the evaluator runs: aggregate, window, INSERT and UPDATE evaluation are total functions (no `partial def` remains in the semantics, #278) but have no equivalence theorems yet. Expression equivalence `≃ₑ` treats aggregates and window functions as errors at expression level, so `≃ₑ` says nothing about them; it is lifted into WHERE only (`select_where_congr`).

### For Lean / CSLib readers

This repository could become a basis for SQL support in
[CSLib](https://github.com/leanprover/cslib). In brief:

- **Semantics.** An executable evaluator (`SqlEquiv/Semantics*.lean`) over
  three representations:
  - `Row := List (String × Value)`;
  - `Table := List Row`;
  - `Database := String → Table`.

  Values are untyped (int, decimal, string, bool and typed NULLs), and errors
  are `none`. It covers three-valued logic, correlated subqueries,
  aggregates, window functions and set operations.
- **Equivalences** (`SqlEquiv/Equiv/Defs.lean`). Each quantifies over **every
  database**. For queries there are three strengths:
  - `≃ᵩ`: equal result lists;
  - `≃ᵇ`: bag equality (`List.Perm`);
  - `≃ˢ`: set equality;
  - `≃ᵇᵛ` and `≃ˢᵛ`: bag and set equality of the rows' values in column
    order, with NULL type tags erased and numbers compared by value
    (`Row.valueKey`, #324). Set operations
    match rows by position and name their columns after the first branch, so
    laws that swap or merge branches hold at this level.

  Expressions use `≃ₑ` (every database and row) and statements use `≃`.
- **Validated against real engines.** sqlite3 and DuckDB serve as
  differential oracles. Where engines legitimately differ (NULL ordering,
  LIKE case sensitivity, MIN/MAX over mixed types), the behaviour is a named
  dialect setting recorded in [`docs/IMPLEMENTATION_DEFINED.md`](docs/IMPLEMENTATION_DEFINED.md).
- **Trust.** The trust base is the one described above. The certified rewriter
  and the decision procedure come with proofs (`docs/CERTIFIED_REWRITER.md`).
- **Known gaps before a library port:**
  - [#278](https://github.com/evelynmitchell/sql_equiv/issues/278) is done: no `partial def`, `unsafe`,
    `implemented_by` or `native_decide` on the proof path. `DecidableEq` on
    the AST is total and kernel-reducible, `sql_equiv!` is kernel-checked
    (`decide +kernel`), and statement-level certified checkers exist
    (`checkSelectEquiv`, `checkQueryEquiv` in `Equiv/StatementChecker.lean`).
    The 58 remaining `partial def`s (17 Nov 2026) are the parser (40), the SQL
    pretty-printer (8) and the debug `Repr` printer `toReprStr` (10); no
    semantics, proof or checker code calls them;
  - the representation choices above were made for a checker, not a library.
    Schemas and typed relations, `Multiset` for bag semantics, and a small
    core calculus with SQL translated into it are all open design questions.
- **The plan: a typed core (#287).** `SqlCore` (in this repo, on Mathlib) rebuilds the
  semantics in the typed style of
  [cslib-frontier](https://github.com/cslib-community/cslib-frontier)'s SQL development:
  positional rows, `Option` NULLs, strict errors, static typing with a soundness
  theorem. Phases 1–8 are done here: values, rows, typed expressions, queries and their
  laws are re-derived from cslib-frontier, and then extended with a certified simplifier,
  the parser bridge (`SqlBridge`), differential tests against SqlEquiv, DuckDB and sqlite,
  and the features beyond the frontier: GROUP BY and aggregates, ORDER BY/LIMIT,
  INTERSECT/EXCEPT, LIKE, exact AVG and division, and uncorrelated subqueries. 520 of the
  564 Spider dev queries elaborate into it. The other 44 are sqlite type-affinity cases,
  which a typed core rejects by design. For `SELECT … FROM t WHERE p` with comparisons and
  boolean connectives, the elaborator is proved correct against SqlEquiv (#309,
  `SqlBridge/Correct.lean`). Phase 9 retires the untyped semantics. These are
  offered upstream. See `docs/TYPED_CORE_PLAN.md` and `docs/TYPED_CORE_DECISIONS.md`.

## Features

### Full SQL DML Support

- **SELECT statements**: `*`, column lists, aliases, DISTINCT
- **Expressions**: arithmetic, comparisons, boolean logic, CASE/WHEN, BETWEEN, IN, LIKE / NOT LIKE
- **Types**: INTEGER, TEXT, BOOLEAN, and exact **DECIMAL/NUMERIC** (scaled-integer arithmetic with int↔decimal promotion — `0.1 + 0.2 = 0.3` exactly)
- **NULL handling**: Typed NULLs, IS NULL/IS NOT NULL, three-valued logic, NULL propagation
- **Joins**: INNER, LEFT, RIGHT, FULL, CROSS
- **Aggregates**: COUNT, SUM, AVG, MIN, MAX (with DISTINCT support)
- **Window functions**: ROW_NUMBER, RANK, DENSE_RANK, and aggregate windows (SUM/AVG/MIN/MAX/COUNT) with `OVER ([PARTITION BY ...] [ORDER BY ...])` and the SQL-default frame; explicit ROWS/RANGE frames and DISTINCT inside windows are rejected at parse time
- **Subqueries**: Scalar subqueries, IN subqueries, EXISTS, correlated subqueries (inner-first name resolution), and derived tables (`FROM (SELECT …) AS d`). A derived table's alias qualifies its columns (`d.name`, #257); unqualified `name` also works.
- **Set operations**: UNION, UNION ALL, INTERSECT, EXCEPT
- **Common Table Expressions**: WITH clause, WITH RECURSIVE for recursive queries
- **Clauses**: WHERE, GROUP BY, HAVING, ORDER BY, LIMIT, OFFSET. ORDER BY may use non-projected columns; in GROUP BY queries it may also sort on aggregates (`ORDER BY COUNT(*) DESC`), non-projected grouping columns, and expressions mixing output aliases with aggregates. `NULLS FIRST` / `NULLS LAST` are supported; without them, NULL sort keys follow the target dialect's rule (see **Dialects** below). With DISTINCT, a sort key that is not selected is a dialect choice: a parse error in `standard` and `postgres`, accepted in `sqlite` and `duckdb` (where the engines sort by each value's first source row, and so does our evaluator, #320).
- **INSERT statements**: VALUES, INSERT...SELECT
- **UPDATE statements**: SET with WHERE conditions
- **DELETE statements**: With WHERE conditions

### Semantic Equivalence Proofs

Define and prove equivalences at multiple levels:

```lean
-- Expression equivalence (every database and every row, so subqueries are covered)
def ExprEquiv (e1 e2 : Expr) : Prop :=
  forall (db : Database) (row : Row), evalExprWithDb db row e1 = evalExprWithDb db row e2

-- Weaker: equivalence against the empty database only (`≃ₑ₀`)
def ExprEquivEmptyDb (e1 e2 : Expr) : Prop :=
  forall row : Row, evalExpr row e1 = evalExpr row e2

-- SELECT statement equivalence
def SelectEquiv (s1 s2 : SelectStmt) : Prop :=
  forall db : Database, evalSelect db s1 = evalSelect db s2

-- Full statement equivalence
def StmtEquiv (s1 s2 : Stmt) : Prop :=
  forall db : Database, evalStmt db s1 = evalStmt db s2
```

### Custom Tactics for SQL Proofs

```lean
-- Automated equivalence proving (handles boolean, arithmetic, comparison)
example : Expr.binOp .and a b ≃ₑ Expr.binOp .and b a := by sql_equiv
example : Expr.binOp .add a (Expr.lit (.int 0)) ≃ₑ a := by sql_equiv
example : Expr.binOp .lt a b ≃ₑ Expr.binOp .gt b a := by sql_equiv

-- SQL-specific simplification
example : ... := by sql_simp

-- Reflexivity, symmetry, transitivity
example : a ≃ₑ a := by sql_refl
example (h : a ≃ₑ b) : b ≃ₑ a := by sql_symm; exact h
example (h1 : a ≃ₑ b) (h2 : b ≃ₑ c) : a ≃ₑ c := by sql_trans b <;> assumption

-- Specialized rewrite tactics
example : ... := by sql_rw_arith      -- Arithmetic identities (x+0=x, x*1=x)
example : ... := by sql_rw_compare    -- Comparison flips (x<y = y>x)
example : ... := by sql_rw_demorgan   -- De Morgan's laws
example : ... := by sql_rw_distrib    -- Distributivity
example : ... := by sql_rw_null       -- NULL handling rules
```

### Differential Testing

Every release is validated against two real engines as oracles: **sqlite3**
(broad SQL behavior) and **DuckDB** (true DECIMAL type, strict typing). One SQL
string drives both our evaluator and the engine; result multisets must agree.
See `LSpecTests/DiffSqlite.lean` and `LSpecTests/DiffDuckdb.lean` (the latter
documents known, deliberate divergences).

### Property-Based Testing

QuickCheck-style testing with random expression generation to validate equivalence properties:

- Random expression generation with depth limits
- Random row/database generation
- Property verification for commutativity, associativity, etc.

## Installation

### Prerequisites

Install Lean 4 using elan:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### Build

```bash
# Clone the repository
git clone <repository-url>
cd sql_equiv

# Build the project
lake build
```

### Run Tests

```bash
# Run the complete test suite
lake exe sql_equiv_test

# Run LSpec property-based tests (SlimCheck-powered)
lake exe sql_equiv_lspec

# Run the unused private checker
python tools/unused_private_checker.py 2>/dev/null

# Run the demo REPL
lake exe sql_equiv
```

## Dialects

Where engines legitimately differ (behaviour the SQL standard leaves to the
implementation), queries are checked against a target dialect: `standard`
(default), `sqlite`, `duckdb` or `postgres`.

```lean
parse "SELECT name FROM t ORDER BY price" (dialect := .postgres)
```

```bash
sql_equiv --dialect sqlite --file queries.sql
```

In the REPL, `dialect sqlite` switches dialect. The dialect is resolved at parse
time: the parser records each choice in the AST (e.g. the NULL position of every
ORDER BY item), so evaluation and every equivalence theorem are
dialect-independent. Configurable today: NULL ordering, LIKE letter case
(sqlite's LIKE ignores ASCII case), MIN/MAX over mixed numbers and strings
or over booleans, whether `SELECT DISTINCT` may sort on a key it does not
select, and (for the typed core's bridge) whether bare columns next to
aggregates are allowed, as sqlite allows them. `toSql` prints SQL for the default dialect (explicit
`NULLS FIRST/LAST` where an item differs from it); the MIN/MAX mode has no SQL
spelling, so re-parsing printed SQL uses the parsing dialect's mode. The full registry of implementation-defined behaviour,
with what each engine does, is `docs/IMPLEMENTATION_DEFINED.md`.

## Usage Examples

### Parsing SQL

```lean
import SqlEquiv

open SqlEquiv

-- Parse a SQL string to AST
def example1 : IO Unit := do
  match parse "SELECT * FROM users WHERE age > 18" with
  | .ok stmt => IO.println s!"Parsed: {stmt.toSql}"
  | .error e => IO.println s!"Error: {e}"

-- Parse specifically a SELECT statement
def example2 : IO Unit := do
  match parseSelectStr "SELECT name, age FROM users" with
  | .ok sel => IO.println s!"Columns: {sel.items.length}"
  | .error e => IO.println s!"Error: {e}"
```

### Evaluating Queries

```lean
import SqlEquiv

open SqlEquiv

def example3 : IO Unit := do
  -- Define a simple database
  let usersTable : Table := [
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30)],
    [("id", .int 2), ("name", .string "Bob"), ("age", .int 25)],
    [("id", .int 3), ("name", .string "Carol"), ("age", .int 35)]
  ]

  let db : Database := fun name =>
    if name == "users" then usersTable else []

  -- Parse and evaluate
  match parseSelectStr "SELECT name FROM users WHERE age > 25" with
  | .ok sel =>
    let result := evalSelect db sel
    IO.println s!"Found {result.length} rows"
    for row in result do
      IO.println s!"  {row}"
  | .error e =>
    IO.println s!"Error: {e}"
```

### Proving Equivalences

```lean
import SqlEquiv

open SqlEquiv

-- Prove AND is commutative
theorem my_and_comm (a b : Expr) :
    Expr.binOp .and a b ≃ₑ Expr.binOp .and b a := by
  sql_equiv

-- Prove double negation elimination (requires isBoolValued precondition)
theorem my_not_not (e : Expr) (h : e.isBoolValued) :
    Expr.unaryOp .not (Expr.unaryOp .not e) ≃ₑ e := by
  sql_equiv

-- Prove WHERE TRUE is equivalent to no WHERE clause
theorem my_where_true (db : Database) (items : List SelectItem) (from_ : Option FromClause) :
    evalSelect db (.mk false items from_ (some (.lit (.bool true))) [] none [] none none) =
    evalSelect db (.mk false items from_ none [] none [] none none) := by
  exact where_true_elim db items from_ [] none [] none none
```

### Recursive CTEs

```lean
import SqlEquiv

open SqlEquiv

-- Parse and evaluate a recursive CTE
def recursiveCTEExample : IO Unit := do
  -- Generate numbers 1 to 5 using recursive CTE
  let sql := "WITH RECURSIVE nums AS (
    SELECT 1 AS n
    UNION ALL
    SELECT n + 1 FROM nums WHERE n < 5
  ) SELECT * FROM nums"

  match parse sql with
  | .ok stmt =>
    let db : Database := fun _ => []  -- Empty database (CTE is self-contained)
    match stmt with
    | .query q =>
      let result := evalQuery db q
      IO.println s!"Generated {result.length} rows"
      -- Output: Generated 5 rows (n = 1, 2, 3, 4, 5)
    | _ => IO.println "Not a query"
  | .error e => IO.println s!"Error: {e}"
```

The recursive CTE evaluator uses fixed-point iteration with a maximum of 1000 iterations to prevent infinite loops.

### Using the sql_equiv Tactic

```lean
import SqlEquiv
import SqlEquiv.Tactics

open SqlEquiv

variable (a b c : Expr)

-- Basic commutativity
example : Expr.binOp .and a b ≃ₑ Expr.binOp .and b a := by sql_equiv
example : Expr.binOp .or a b ≃ₑ Expr.binOp .or b a := by sql_equiv
example : Expr.binOp .add a b ≃ₑ Expr.binOp .add b a := by sql_equiv
example : Expr.binOp .mul a b ≃ₑ Expr.binOp .mul b a := by sql_equiv

-- Double negation (requires isBoolValued precondition)
example (h : a.isBoolValued) : Expr.unaryOp .not (Expr.unaryOp .not a) ≃ₑ a := by sql_equiv

-- Using transitivity
example (h1 : a ≃ₑ b) (h2 : b ≃ₑ c) : a ≃ₑ c := by
  sql_trans b
  . exact h1
  . exact h2
```

## Architecture

### Module Overview

| Module | Description |
|--------|-------------|
| `SqlEquiv.Ast` | Abstract Syntax Tree definitions for all SQL constructs |
| `SqlEquiv.Parser` | Hand-rolled recursive descent parser with tokenizer |
| `SqlEquiv.Pretty` | Pretty printer for converting AST back to SQL strings |
| `SqlEquiv.SemanticsBase` | Core types and helpers for the evaluation model |
| `SqlEquiv.SemanticsCore` | Non-partial evaluation mirrors and lemmas |
| `SqlEquiv.Semantics` | Well-founded recursive evaluator with bridge theorems |
| `SqlEquiv.Equiv` | Re-export hub for all equivalence submodules |
| `SqlEquiv.Equiv.Defs` | Equivalence relation definitions (ExprEquiv, SelectEquiv, etc.) |
| `SqlEquiv.Equiv.ValueLemmas` | Value-level lemmas for evalBinOp/evalUnaryOp |
| `SqlEquiv.Equiv.ExprAxioms` | Expression equivalence theorems (commutativity, identity, etc.) |
| `SqlEquiv.Equiv.Comparison` | Comparison, NULL, aggregate, join, and filter theorems |
| `SqlEquiv.Equiv.StatementAxioms` | Statement-level theorems (joins, set ops, subqueries, LIMIT/OFFSET) |
| `SqlEquiv.Equiv.StatementChecker` | Certified statement checkers `checkSelectEquiv` / `checkQueryEquiv` (proof or unknown) |
| `SqlEquiv.Equiv.SetBagLemmas` | Set/bag algebra helper lemmas |
| `SqlEquiv.Equiv.Decidable` | Decidable equality for AST types |
| `SqlEquiv.Tactics` | Custom Lean 4 tactics for SQL proofs |
| `SqlEquiv.Basic` | Re-exports all modules for convenience |

### Key Types

```lean
-- SQL types for typed NULLs
inductive SqlType where
  | int | string | bool | unknown

-- Three-valued logic (TRUE, FALSE, UNKNOWN)
inductive Trilean where
  | true | false | unknown

-- Values with typed NULLs
inductive Value where
  | int    : Int -> Value
  | string : String -> Value
  | bool   : Bool -> Value
  | null   : Option SqlType -> Value  -- typed NULL (none = unknown type)

-- Expressions
inductive Expr where
  | lit       : Value -> Expr
  | col       : ColumnRef -> Expr
  | binOp     : BinOp -> Expr -> Expr -> Expr
  | unaryOp   : UnaryOp -> Expr -> Expr
  | func      : String -> List Expr -> Expr
  | agg       : AggFunc -> Option Expr -> Bool -> Expr
  | countStar : Expr
  | case      : List (Expr * Expr) -> Option Expr -> Expr
  | inList    : Expr -> Bool -> List Expr -> Expr
  | inSubquery: Expr -> Bool -> SelectStmt -> Expr
  | exists    : Bool -> SelectStmt -> Expr
  | subquery  : SelectStmt -> Expr
  | between   : Expr -> Expr -> Expr -> Expr

-- Statements
inductive Stmt where
  | query  : Query -> Stmt
  | insert : InsertStmt -> Stmt
  | update : UpdateStmt -> Stmt
  | delete : DeleteStmt -> Stmt
```

### Semantic Model

- **Row**: `List (String * Value)` - A mapping from column names to values
- **Table**: `List Row` - A collection of rows (bag semantics)
- **Database**: `String -> Table` - A mapping from table names to tables

## Available Theorems

### Expression Equivalence Properties

| Theorem | Description |
|---------|-------------|
| `expr_equiv_refl` | Reflexivity: `e ≃ₑ e` |
| `expr_equiv_symm` | Symmetry: `e1 ≃ₑ e2 -> e2 ≃ₑ e1` |
| `expr_equiv_trans` | Transitivity: `e1 ≃ₑ e2 -> e2 ≃ₑ e3 -> e1 ≃ₑ e3` |

### Commutativity

| Theorem | Description |
|---------|-------------|
| `and_comm` | `(a AND b) ≃ₑ (b AND a)` |
| `or_comm` | `(a OR b) ≃ₑ (b OR a)` |
| `add_comm` | `(a + b) ≃ₑ (b + a)` |
| `mul_comm` | `(a * b) ≃ₑ (b * a)` |
| `eq_comm` | `(a = b) ≃ₑ (b = a)` |

### Associativity

| Theorem | Description |
|---------|-------------|
| `and_assoc` | `((a AND b) AND c) ≃ₑ (a AND (b AND c))` (requires `a.isBoolValued`, `b.isBoolValued`, `c.isBoolValued`) |
| `or_assoc` | `((a OR b) OR c) ≃ₑ (a OR (b OR c))` (requires `a.isBoolValued`, `b.isBoolValued`, `c.isBoolValued`) |

### De Morgan's Laws

| Theorem | Description |
|---------|-------------|
| `not_and` | `NOT (a AND b) ≃ₑ (NOT a OR NOT b)` (requires `isBoolValued`) |
| `not_or` | `NOT (a OR b) ≃ₑ (NOT a AND NOT b)` (requires `isBoolValued`) |

### Distributivity

All distributivity theorems require `isBoolValued` on all operands.

| Theorem | Description |
|---------|-------------|
| `and_or_distrib_left` | `a AND (b OR c) ≃ₑ (a AND b) OR (a AND c)` |
| `and_or_distrib_right` | `(a OR b) AND c ≃ₑ (a AND c) OR (b AND c)` |
| `or_and_distrib_left` | `a OR (b AND c) ≃ₑ (a OR b) AND (a OR c)` |
| `or_and_distrib_right` | `(a AND b) OR c ≃ₑ (a OR c) AND (b OR c)` |

### Absorption Laws

| Theorem | Description |
|---------|-------------|
| `and_absorb_or` | `a AND (a OR b) ≃ₑ a` (requires `isBoolValued`) |
| `or_absorb_and` | `a OR (a AND b) ≃ₑ a` (requires `isBoolValued`) |

### Identity Laws

| Theorem | Description |
|---------|-------------|
| `and_true` | `a AND TRUE ≃ₑ a` |
| `or_false` | `a OR FALSE ≃ₑ a` |
| `and_false` | `a AND FALSE ≃ₑ FALSE` |
| `or_true` | `a OR TRUE ≃ₑ TRUE` |

### NULL Handling (IS NULL Laws)

| Theorem | Description |
|---------|-------------|
| `is_null_on_null` | `IS NULL` on NULL returns TRUE |
| `is_null_on_int/string/bool` | `IS NULL` on non-NULL returns FALSE |
| `is_not_null_on_null` | `IS NOT NULL` on NULL returns FALSE |
| `is_not_null_on_int/string/bool` | `IS NOT NULL` on non-NULL returns TRUE |
| `is_null_is_not_null_complement` | `IS NULL` and `IS NOT NULL` are complementary |

### NULL Propagation

| Theorem | Description |
|---------|-------------|
| `null_add_left/right` | `NULL + x = NULL`, `x + NULL = NULL` |
| `null_sub_left/right` | `NULL - x = NULL`, `x - NULL = NULL` |
| `null_mul_left/right` | `NULL * x = NULL`, `x * NULL = NULL` |
| `null_div_left/right` | `NULL / x = NULL`, `x / NULL = NULL` |
| `null_eq_left/right` | `NULL = x = NULL` (comparison returns unknown) |
| `null_ne_left/right` | `NULL <> x = NULL` |
| `null_lt_left/right` | `NULL < x = NULL` |

### Three-Valued Logic (NULL in Boolean Operations)

| Theorem | Description |
|---------|-------------|
| `false_and_null` | `FALSE AND NULL = FALSE` (FALSE dominates) |
| `null_and_false` | `NULL AND FALSE = FALSE` |
| `true_and_null` | `TRUE AND NULL = NULL` (propagates unknown) |
| `true_or_null` | `TRUE OR NULL = TRUE` (TRUE dominates) |
| `false_or_null` | `FALSE OR NULL = NULL` (propagates unknown) |
| `null_and_null` | `NULL AND NULL = NULL` |
| `null_or_null` | `NULL OR NULL = NULL` |

### Trilean Properties

| Theorem | Description |
|---------|-------------|
| `trilean_not_not` | Trilean NOT is self-inverse |
| `trilean_and_comm` | Trilean AND is commutative |
| `trilean_or_comm` | Trilean OR is commutative |
| `trilean_and_true/false` | Identity and annihilation laws |
| `trilean_or_true/false` | Identity and annihilation laws |
| `trilean_de_morgan_and` | `NOT (a AND b) = (NOT a) OR (NOT b)` |
| `trilean_de_morgan_or` | `NOT (a OR b) = (NOT a) AND (NOT b)` |

### COALESCE and NULLIF

| Theorem | Description |
|---------|-------------|
| `coalesce_null_left_nonnull` | `COALESCE(NULL, x) = x` (requires x non-null; replaces former unsound axiom) |
| `coalesce_int_left` | `COALESCE(n, y) = n` for non-null int |
| `coalesce_string_left` | `COALESCE(s, y) = s` for non-null string |
| `coalesce_bool_left` | `COALESCE(b, y) = b` for non-null bool |
| `coalesce_single_*` | `COALESCE(x) = x` for single argument |
| `coalesce_empty` | `COALESCE() = NULL` |
| `nullif_same_int` | `NULLIF(n, n) = NULL` |
| `nullif_diff_int` | `NULLIF(n, m) = n` when `n ≠ m` |

> **Historical note:** The former `coalesce_null_left` axiom was removed because
> it was unsound — when the second argument is `some (.null _)`, the
> implementation returns `none`, not the null value. The unsound axiom was
> deleted (rather than merely deprecated) to prevent accidental use in proofs.
> `coalesce_null_left_nonnull` is the sound replacement. See
> [Pitfalls: COALESCE(NULL, NULL)](docs/tutorials/reference/pitfalls.md#coalescenull-null-and-typed-nulls)
> for a detailed explanation.

### Aggregate Theorems

| Theorem | Description |
|---------|-------------|
| `count_star_nonneg` | `COUNT(*) >= 0` (always non-negative) |
| `count_star_empty` | `COUNT(*) = 0` on empty table |
| `count_star_singleton` | `COUNT(*) = 1` on single-row table |
| `count_after_filter_le` | `COUNT(*) WHERE p <= COUNT(*)` |
| `sum_empty` | `SUM([]) = 0` |
| `sum_singleton` | `SUM([n]) = n` |
| `sum_add_zero` | `SUM(xs ++ [0]) = SUM(xs)` |
| `min_singleton` | `MIN([n]) = n` |
| `max_singleton` | `MAX([n]) = n` |
| `min_le_elem` | `MIN(xs) <= n` for any `n ∈ xs` |
| `max_ge_elem` | `MAX(xs) >= n` for any `n ∈ xs` |
| `distinct_count_le` | `COUNT(DISTINCT x) <= COUNT(x)` |
| `distinct_idempotent` | `DISTINCT(DISTINCT(xs)) = DISTINCT(xs)` |

### CASE Expression Theorems

| Theorem | Description |
|---------|-------------|
| `case_when_true` | `CASE WHEN TRUE THEN x ELSE y END = x` |
| `case_when_false` | `CASE WHEN FALSE THEN x ELSE y END = y` |
| `case_when_false_no_else` | `CASE WHEN FALSE THEN x END = NULL` |
| `case_empty_else` | `CASE ELSE y END = y` |
| `case_empty_no_else` | `CASE END = NULL` |

### Predicate Pushdown Theorems

| Theorem | Description |
|---------|-------------|
| `filter_and_eq_filter_filter` | `filter(p AND q) = filter(q, filter(p))` |
| `filter_comm` | `filter(q, filter(p)) = filter(p, filter(q))` |
| `predicate_pushdown` | `SELECT * FROM t WHERE p` filtered by q = `WHERE (p AND q)` |

### Arithmetic Expression Theorems

| Theorem | Description |
|---------|-------------|
| `expr_add_zero` | `x + 0 = x` |
| `expr_zero_add` | `0 + x = x` |
| `expr_mul_one` | `x * 1 = x` |
| `expr_one_mul` | `1 * x = x` |
| `expr_mul_zero` | `x * 0 = 0` |
| `expr_zero_mul` | `0 * x = 0` |
| `expr_sub_zero` | `x - 0 = x` |

### IN List Theorems

| Theorem | Description |
|---------|-------------|
| `in_empty_false` | `x IN () = FALSE` |
| `not_in_empty_true` | `x NOT IN () = TRUE` |
| `in_singleton` | `x IN (a) = (x = a)` |
| `not_in_singleton` | `x NOT IN (a) = (x <> a)` |
| `in_pair` | `x IN (a, b) = (x = a OR x = b)` |
| `not_in_pair` | `x NOT IN (a, b) = (x <> a AND x <> b)` |
| `in_list_or_expansion` | General IN to OR expansion |
| `not_in_list_and_expansion` | General NOT IN to AND expansion |

### BETWEEN Theorems

| Theorem | Description |
|---------|-------------|
| `between_expansion` | `x BETWEEN a AND b = (x >= a AND x <= b)` |
| `between_reflexive` | `x BETWEEN x AND x` expansion |
| `not_between_expansion` | `NOT (x BETWEEN a AND b) = (x < a OR x > b)` |

### LIKE Pattern Theorems

| Theorem | Description |
|---------|-------------|
| `like_match_all` | `x LIKE '%' = TRUE` for non-null x |
| `like_empty_pattern` | `x LIKE '' = (x = '')` |
| `like_self` | `x LIKE x = TRUE` for non-null x (no wildcards) |

### String Function Theorems

| Theorem | Description |
|---------|-------------|
| `concat_empty_left` | `CONCAT('', x) = x` |
| `concat_empty_right` | `CONCAT(x, '') = x` |
| `upper_idempotent` | `UPPER(UPPER(x)) = UPPER(x)` |
| `lower_idempotent` | `LOWER(LOWER(x)) = LOWER(x)` |
| `upper_lower_upper` | `UPPER(LOWER(UPPER(x))) = UPPER(x)` |
| `lower_upper_lower` | `LOWER(UPPER(LOWER(x))) = LOWER(x)` |
| `length_empty` | `LENGTH('') = 0` |

### Comparison Theorems

| Theorem | Description |
|---------|-------------|
| `eq_reflexive` | `x = x` is TRUE (for non-null, NULL-aware via CASE) |
| `ne_irreflexive` | `x <> x` is FALSE (for non-null) |
| `not_eq_is_ne` | `NOT (x = y) = (x <> y)` |
| `not_ne_is_eq` | `NOT (x <> y) = (x = y)` |
| `not_lt_is_ge` | `NOT (x < y) = (x >= y)` |
| `not_le_is_gt` | `NOT (x <= y) = (x > y)` |
| `not_gt_is_le` | `NOT (x > y) = (x <= y)` |
| `not_ge_is_lt` | `NOT (x >= y) = (x < y)` |
| `lt_flip` | `x < y = y > x` |
| `le_flip` | `x <= y = y >= x` |
| `gt_flip` | `x > y = y < x` |
| `ge_flip` | `x >= y = y <= x` |

### Set Operation Theorems (UNION, INTERSECT, EXCEPT)

| Theorem | Description |
|---------|-------------|
| `union_comm` | `A UNION B ≃ᵇᵛ B UNION A` |
| `union_all_comm` | `A UNION ALL B ≃ᵇᵛ B UNION ALL A` |
| `intersect_comm` | `A INTERSECT B ≃ˢᵛ B INTERSECT A` |
| `union_assoc` | `(A UNION B) UNION C ≃ᵇᵛ A UNION (B UNION C)` |
| `intersect_assoc` | `(A INTERSECT B) INTERSECT C ≃ᵩ A INTERSECT (B INTERSECT C)` |
| `union_idempotent` | `A UNION A ≃ˢᵛ A` |
| `intersect_idempotent` | `A INTERSECT A ≃ˢᵛ A` |
| `except_self_empty` | `A EXCEPT A = ∅` |
| `union_empty_right` | `A UNION ∅ ≃ˢᵛ A` |
| `intersect_empty_right` | `A INTERSECT ∅ = ∅` |
| `union_all_length` | `|A UNION ALL B| = |A| + |B|` |
| `union_intersect_distrib` | `A UNION (B INTERSECT C) ≃ˢᵛ (A UNION B) INTERSECT (A UNION C)` |
| `intersect_union_distrib` | `A INTERSECT (B UNION C) ≃ˢᵛ (A INTERSECT B) UNION (A INTERSECT C)` |

### JOIN Theorems

| Theorem | Description |
|---------|-------------|
| `join_comm` | INNER JOIN is commutative (row membership) |
| `join_comm_full` | INNER JOIN commutativity (full equality) |
| `join_assoc` | INNER JOIN is associative |
| `cross_join_comm` | CROSS JOIN is commutative (row membership) |
| `cross_join_assoc` | CROSS JOIN is associative |
| `cross_join_cardinality_comm` | `|A × B| = |B × A|` |
| `inner_join_true_is_cross` | `A INNER JOIN B ON TRUE = A CROSS JOIN B` |
| `inner_join_false_empty` | `A INNER JOIN B ON FALSE = ∅` |
| `left_join_false_all_left` | `|A LEFT JOIN B ON FALSE| = |A|` |
| `cross_join_cardinality` | `|A × B| = |A| * |B|` |
| `inner_join_cardinality_le` | `|A ⋈ B| ≤ |A| * |B|` |
| `left_join_cardinality_ge` | `|A LEFT JOIN B| ≥ |A|` |
| `right_join_cardinality_ge` | `|A RIGHT JOIN B| ≥ |B|` |
| `inner_join_empty_left` | `∅ INNER JOIN B = ∅` |
| `inner_join_empty_right` | `A INNER JOIN ∅ = ∅` |
| `cross_join_empty_left` | `∅ × B = ∅` |
| `cross_join_empty_right` | `A × ∅ = ∅` |
| `cross_join_assoc_cardinality` | `|(A × B) × C| = |A × (B × C)|` |
| `inner_join_to_where` | `A ⋈ B ON cond = (A × B) WHERE cond` |
| `left_join_preserves_left` | LEFT JOIN preserves all left rows |
| `right_join_preserves_right` | RIGHT JOIN preserves all right rows |
| `inner_subset_cross` | `|A ⋈ B ON cond| ≤ |A × B|` |
| `left_join_filter_null_is_inner` | LEFT JOIN filtered by non-null = INNER JOIN |

### Subquery Theorems

| Theorem | Description |
|---------|-------------|
| `exists_empty_false` | `EXISTS (empty) = FALSE` |
| `not_exists_empty_true` | `NOT EXISTS (empty) = TRUE` |
| `exists_nonempty_true` | `EXISTS (non-empty) = TRUE` |
| `not_exists_nonempty_false` | `NOT EXISTS (non-empty) = FALSE` |
| `not_not_exists` | `NOT NOT EXISTS = EXISTS` |
| `in_empty_subquery_false` | `x IN (empty subquery) = FALSE` |
| `not_in_empty_subquery_true` | `x NOT IN (empty subquery) = TRUE` |
| `scalar_subquery_empty_null` | Scalar subquery on empty = NULL |
| `exists_as_count_gt_zero` | `EXISTS = (COUNT(*) > 0)` |
| `not_exists_as_count_eq_zero` | `NOT EXISTS = (COUNT(*) = 0)` |
| `in_subquery_as_exists` | `x IN (SELECT col FROM t) = EXISTS (SELECT 1 FROM t WHERE col = x)`, when `x` and `col` are never NULL |
| `not_in_subquery_as_not_exists` | `x NOT IN (...) = NOT EXISTS (...)`, when `x` and `col` are never NULL |
| `subquery_limit_one` | Subquery with LIMIT 1 returns at most 1 row |
| `scalar_subquery_is_first` | Scalar subquery = first column of first row |
| `exists_monotonic` | EXISTS is monotonic (superset preserves TRUE) |
| `subquery_where_true` | Adding WHERE TRUE doesn't change subquery |
| `subquery_where_false` | Adding WHERE FALSE makes subquery empty |
| `in_singleton_subquery` | `x IN (single value v) = (x = v)` |
| `in_subquery_unnest_to_join` | IN subquery unnested to semi-join (equal on values, as a bag) |
| `not_in_subquery_unnest_to_antijoin` | NOT IN subquery unnested to anti-join, when `t.x` and `s.y` are never NULL |

### ORDER BY Theorems

| Theorem | Description |
|---------|-------------|
| `order_by_preserves_count` | ORDER BY doesn't change row count |
| `order_by_length_invariant` | Different ORDER BY clauses produce same row count |
| `order_limit_deterministic` | ORDER BY + LIMIT gives deterministic prefix |

### LIMIT Theorems

| Theorem | Description |
|---------|-------------|
| `limit_zero_empty` | `LIMIT 0` returns empty result |
| `limit_upper_bound` | `LIMIT n` returns at most n rows |
| `limit_none_all_rows` | No LIMIT = all rows |
| `limit_monotonic` | Larger LIMIT gives more rows |
| `limit_one_singleton` | `LIMIT 1` returns at most 1 row |

### OFFSET Theorems

| Theorem | Description |
|---------|-------------|
| `offset_zero_identity` | `OFFSET 0` is identity |
| `offset_too_large_empty` | `OFFSET >= count` returns empty |
| `offset_reduces_count` | OFFSET reduces row count |
| `offset_monotonic` | Larger OFFSET gives fewer rows |

### LIMIT + OFFSET Combination Theorems

| Theorem | Description |
|---------|-------------|
| `limit_offset_compose` | `LIMIT n OFFSET m` = skip m, take n |
| `offset_limit_zero_empty` | `OFFSET x LIMIT 0` = empty |
| `pagination_upper_bound` | `LIMIT n OFFSET m` returns at most n rows |
| `pagination_identity` | `OFFSET 0 LIMIT count` = all rows |
| `consecutive_pages` | Page 1 ++ Page 2 = combined page |

### WHERE Clause Theorems

| Theorem | Description |
|---------|-------------|
| `where_true_elim` | `SELECT ... WHERE TRUE` equals `SELECT ...` |
| `where_false_empty` | `SELECT ... WHERE FALSE` returns empty |
| `filter_true_elim'` | `filter(TRUE)` is identity |
| `filter_false_empty'` | `filter(FALSE)` returns empty |

## Contributing

### Adding New Equivalences

1. **Define the theorem** in the appropriate `SqlEquiv/Equiv/` submodule:
   - Expression-level: `Equiv/ExprAxioms.lean` or `Equiv/Comparison.lean`
   - Statement-level (joins, set ops, subqueries): `Equiv/StatementAxioms.lean`
   - Value-level helpers: `Equiv/ValueLemmas.lean`

```lean
theorem my_new_theorem (a b : Expr) :
    Expr.binOp .someOp a b ≃ₑ Expr.binOp .someOp b a := by
  intro db row
  -- Your proof here (a `sorry` fails `lake build sql_equiv_test`: see Test/TrustBaseTest.lean)
  sorry
```

2. **Add tests** in `Test/EquivTest.lean`:

```lean
-- Compile-time verification
#check @my_new_theorem

-- Runtime test
def myTests : List TestResult := [
  testSyntacticEquiv "my_test"
    (.binOp .someOp (col "x") (col "y"))
    (.binOp .someOp (col "y") (col "x"))
]
```

3. **Add property tests** in `Test/PropertyTest.lean` for random testing.

### Adding New SQL Features

1. **Extend the AST** in `SqlEquiv/Ast.lean`
2. **Extend the parser** in `SqlEquiv/Parser.lean`
3. **Extend the pretty printer** in `SqlEquiv/Pretty.lean`
4. **Extend the semantics** in `SqlEquiv/Semantics.lean`
5. **Add tests** in the appropriate test file

### Running Tests

```bash
# Build and run all tests
lake build && lake exe sql_equiv_test
```

## Project Structure

```
sql_equiv/
+-- SqlEquiv/
|   +-- Ast.lean               # AST definitions
|   +-- Parser.lean            # SQL parser
|   +-- Pretty.lean            # Pretty printer
|   +-- SemanticsBase.lean     # Core types and helpers
|   +-- SemanticsCore.lean     # Non-partial evaluation mirrors and lemmas
|   +-- Semantics.lean         # Well-founded recursive evaluator
|   +-- Equiv.lean             # Re-export hub for Equiv submodules
|   +-- Equiv/
|   |   +-- Defs.lean          # Equivalence relation definitions
|   |   +-- ValueLemmas.lean   # Value-level lemmas
|   |   +-- ExprAxioms.lean    # Expression equivalence theorems
|   |   +-- Comparison.lean    # Comparison, NULL, aggregate, filter theorems
|   |   +-- StatementAxioms.lean # JOIN, set ops, subquery, LIMIT/OFFSET theorems
|   |   +-- SetBagLemmas.lean  # Set/bag algebra helpers
|   |   +-- Decidable.lean     # Decidable equality for AST types
|   +-- Tactics.lean           # Custom tactics
|   +-- Basic.lean             # Re-exports
+-- Test/
|   +-- Common.lean            # Test infrastructure
|   +-- ParserTest.lean        # Parser tests
|   +-- SemanticsTest.lean     # Semantics tests
|   +-- EquivTest.lean         # Equivalence tests
|   +-- PropertyTest.lean      # Property-based tests
|   +-- AxiomCoverageTest.lean # Runtime coverage tests for all theorems
|   +-- Main.lean              # Test runner
+-- LSpecTests/
|   +-- Generators.lean        # SlimCheck generators for SQL types
|   +-- ExprAlgebra.lean       # Expression algebra property tests
|   +-- NullSemantics.lean     # NULL propagation property tests
|   +-- QueryHelpers.lean      # Query-level property tests
|   +-- EdgeCaseDb.lean        # Edge-case database tests
|   +-- DiffSqlite.lean        # Differential testing against SQLite
|   +-- Main.lean              # LSpec test runner
+-- tools/
|   +-- axiom_coverage_validator.py # Static analysis for test coverage
|   +-- count_axioms_theorems.py   # Axiom/theorem counter
|   +-- unused_private_checker.py  # Text-based unused private finder
|   +-- ci_sparkline.py            # CI anomaly detection
+-- docs/                    # Documentation and specs
|   +-- axiom_dependencies.dot # Graphviz axiom dependency graph
|   +-- specs/               # Feature specifications
|   +-- tutorials/           # Tutorial series (10 chapters)
+-- benchmarks/              # SQL benchmark suites
+-- Main.lean                # Demo REPL
+-- lakefile.toml            # Lake build config
+-- README.md                # This file
```

## Dependencies

- [Lean 4](https://lean-lang.org/) (v4.36.0-rc2, the toolchain of cslib-frontier) - The programming language and theorem prover
- [Batteries](https://github.com/leanprover-community/batteries) - Standard library extensions
- [LSpec](https://github.com/argumentcomputer/LSpec) - Property-based testing with SlimCheck

## License

Copyright (c) 2026 evelynmitchell and contributors.

Licensed under the [Apache License, Version 2.0](LICENSE). Versions before
13 Nov 2026 were released under the MIT License.
