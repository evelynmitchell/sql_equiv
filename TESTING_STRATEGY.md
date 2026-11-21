# Testing Strategy: Defense in Depth

This project uses several independent verification layers, each catching a different class of
error, so that a gap in one is covered by another. The layers below are in the order CI runs
them (`.github/workflows/ci.yml`). There are two semantics under test: the original untyped
evaluator (`SqlEquiv`) and the typed core (`SqlCore`, reached from parsed SQL through
`SqlBridge`); several layers exist to keep the two honest against each other and against real
engines.

## Verification layers

### 1. Lean kernel and the trust base (compile time)

- **Catches:** incorrect proofs, and anything that would widen what has to be trusted.
- **How:** every `theorem` is kernel-checked by `lake build`. The trust base is asserted, not
  assumed: `Test/TrustBaseTest.lean` (`#assert_trust_base SqlEquiv`,
  `#assert_no_runtime_overrides SqlEquiv`) and `SqlCoreTest/TrustBaseTest.lean` (the same for
  `SqlCore` and `SqlBridge`) fail the test build if any theorem or definition depends on an axiom
  other than `propext`, `Classical.choice`, `Quot.sound`: no `sorry`, no project axioms, no
  `native_decide`, no `unsafe`/`implemented_by` overrides. `Test/TacticTest.lean` pins the axioms
  of `sql_equiv!`.
- **Watch for:** these checks run only when the test targets are built (`sql_equiv_test`,
  `sqlcore_test`), not on a plain `lake build`. `tools/rewrite-audit/scripts/lean/check_trust_base.sh`
  runs the same check by hand; `/audit` covers the rewriters.

### 2. Static consistency checks (no build)

- **Definition coverage matrix** (`tools/definition_coverage_matrix.py --check`): every
  operator × value-type cell of the evaluator has an arm. A new `Value` type must be taught to
  this tool and to the LSpec generators in the same PR, or it reports vacuous green.
- **Identical sides** (`tools/rewrite-audit/scripts/lean/find_identical_sides.py SqlEquiv SqlCore
  SqlBridge`, #307): no theorem whose two sides are the same text.
- **Generated code** (`tools/gen_ast_deceq.py --check`): the AST's `DecidableEq` block is
  current.
- **Axiom ratchet** (`tools/axiom_coverage_validator.py --runtime`,
  `tools/axiom_count_minimum.txt` = 0): a leftover from when the library had axioms. With none
  left it finds no declarations and passes `0 >= 0`, so it checks nothing today; pointing it at
  theorems is #181. Do not read its green as coverage. The validator has two kinds of mode:
  with `--runtime` it only matches names in text files; without it, it comments declarations
  out in the source files one at a time and rebuilds (hours with `--theorems`). Never edit the
  tree while the second kind runs. If that happens anyway, the restore step keeps the edit and
  stops the run (`--self-test` checks this in CI).

### 3. Unit tests (`lake exe sql_equiv_test`)

- **Catches:** evaluator bugs, parser regressions, rewriter regressions, pinned
  implementation-defined choices.
- **How:** hand-written suites under `Test/` (parser, semantics, equivalence, certified rewriter,
  tactics, AST equality). Results are also written per test (`TEST_RESULTS_JSON`).
- **Watch for:** every row of the registry in `docs/IMPLEMENTATION_DEFINED.md` needs a unit test
  pinning our choice.

### 4. Typed-core tests (`lake exe sqlcore_test`)

- **Compile-time examples** (`SqlCoreTest/*Examples.lean`): `#guard`s and `example`s for scalars,
  schemas, expressions, queries, laws, aggregates, ordering, set operations, subqueries and the
  simplifier.
- **Differential against `SqlEquiv`** (`ScalarDiffTest`, `ExprDiffTest`, `BridgeDiffTest`): the
  same inputs through both semantics. Each corpus entry states what is expected: `agree`,
  `rejected` (with the error category), `agreeRounded` (a repeating `AVG`, equal after
  `SqlEquiv`'s 16-place rounding) or a documented `SqlEquiv` bug.
- **Differential against engines** (`DuckdbDiffTest`, `SqliteDiffTest`): parsed SQL through the
  bridge against DuckDB, and the sqlite-only bare-column rule against sqlite.
- **Elaborator-correctness guards** (`CorrectExamples`): the hypotheses of the elaborator
  theorems (#352) are satisfiable by queries that elaborate, and the fragment's shapes
  (`stmtShape`, `aggShape`, `aggBareShape`, `groupedShape`) are spot-checked inside and outside.
- **Coverage report against the theorems** (`CoverageAgreeTest`): the Spider coverage count
  (`SqlBridge.Coverage`) agrees with the theorems' shapes on every query of
  `benchmarks/spider/dev_queries.jsonl`. It fails on any disagreement and if fewer than 500
  queries parse.
- **Watch for:** the engine tests print `SKIPPED` when a binary is missing; CI installs DuckDB.
  Run from the repo root so the Spider file is found.

### 5. Spider ratchets (north-star metrics)

- **Parse rate** (`tools/spider_parse_baseline.py --check`), **evaluate agreement with sqlite**
  (`tools/spider_eval_baseline.py --check`, Postgres as tiebreaker) and **typed-core
  elaboration** (`tools/spider_elab_baseline.py --check`). Each has a minimum in
  `tools/spider_*_minimum.txt`; CI fails on a regression, and `--update-ratchet` raises it.
- **Watch for:** the evaluate figure is a sum of exact matches, tie-valid answers and
  TEXT-affinity emulation; only the sum is ratcheted today (#266). The reports under
  `benchmarks/spider/` are generated; failure classes in them become issues.

### 6. Differential oracles for `SqlEquiv` (in `lake exe sql_equiv_lspec`)

- **Catches:** semantics that every internal layer agrees on and a real engine does not.
- **How:** `LSpecTests/DiffSqlite.lean`, `DiffDuckdb.lean`, `DiffPostgres.lean` run one SQL
  string through our parser and evaluator and through the engine on the same data. sqlite is the
  Spider-fidelity target, DuckDB the standards and DECIMAL cross-check, Postgres the tiebreaker.
- **Watch for:** where engines legitimately differ, the choice is a named dialect setting with a
  registry row (`docs/IMPLEMENTATION_DEFINED.md`): check the engines by running them, record the
  choice, and add an explicit disagreement case for the engines that differ. Where DuckDB and
  Postgres raise a query error, `SqlEquiv` returns a quiet `none` (#270).

### 7. LSpec property tests (`lake exe sql_equiv_lspec`)

- **Catches:** edge cases hand-written tests miss: NULL propagation, type mismatches, algebraic
  boundary conditions, rewriter soundness on generated expressions.
- **How:** SlimCheck generates expressions (`LSpecTests/Generators.lean`); CI runs
  `LSPEC_SAMPLES=100000`. The Context Sweep (`RewriterProperties`) runs every rewriter over
  generated contexts and includes a mutant check: an unguarded `a AND TRUE → a` rewriter must be
  caught.
- **Watch for:** databases are fixtures, not generated (#245), so a property can go vacuous if
  its fixture does not match the query (`/test-vacuity`). Findings go in `LSPEC_FINDINGS.md`.

### 8. Review

- **Critical self-review** (`/critical-self-review`) when a bug would be quiet: semantics
  changes, new value types, parser changes, new external surfaces, and changes whose tests were
  written in the same pass. Skip it where a bug would be loud. Verify findings by probing.
- **`/audit`** after edits to the evaluator dispatch, the AST's value and operator types, or the
  equivalence modules.
- **`/doc-freshness`** before closing a tracking issue.

## Per-test result artifacts (#209)

Every CI run uploads `test-results/*.jsonl` (one object per test: suite, name, pass). The unit
runner writes it directly; the LSpec log is converted by `tools/lspec_results_to_json.py`. The
history is there for flake detection in the subprocess-based oracle tests and for the
mutation-testing proposal (#210).

## Running the layers locally

```bash
lake build
```

```bash
lake build sql_equiv_test sqlcore_test sql_equiv_lspec
```

```bash
lake exe sql_equiv_test
```

```bash
lake exe sqlcore_test
```

```bash
LSPEC_SAMPLES=1000 lake exe sql_equiv_lspec
```

```bash
python3 tools/definition_coverage_matrix.py --check
```

```bash
python3 tools/rewrite-audit/scripts/lean/find_identical_sides.py SqlEquiv SqlCore SqlBridge
```

```bash
python3 tools/spider_parse_baseline.py --check
```

```bash
python3 tools/spider_eval_baseline.py --check
```

```bash
python3 tools/spider_elab_baseline.py --check
```

Never run `lake clean` (a full rebuild takes over twenty minutes).

## Known gaps

- The axiom ratchet checks nothing (#181).
- Exact Spider matches are not ratcheted on their own (#266).
- Property tests use fixture databases, not generated ones (#245).
- No mutation testing: nothing shows that every evaluator arm has a test that would notice it
  being wrong (#210).
- `SqlEquiv`'s equivalences are relative to its quiet-error model (#270); the typed core is
  strict.

## Anti-patterns

- **Don't skip a failing layer.** Fix the root cause; never disable or quarantine a check.
- **Don't write the test in the same pass as the code and call it verified.** That is the case
  the self-review rule exists for.
- **Don't trust a coverage tool on a type or shape it was never taught.** It reports vacuous
  green; give each new check a way to fail (a minimum count, a mutant).
- **Don't lower a ratchet to get green.** A drop is a regression until shown otherwise.
- **Don't ignore CI duration changes.** They can mean a layer silently stopped running (as
  happened when `Equiv.lean` was split).
