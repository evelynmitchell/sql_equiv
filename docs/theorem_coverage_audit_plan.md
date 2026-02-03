# Theorem Coverage Audit Plan

## Status
- Branch: `fix-build-and-coalesce-tests` (PR #21, commit `6bb48db`)
- Master: `8b57bda` (build broken by commit 2ff5b9e)
- 156 axioms in `SqlEquiv/Equiv.lean`
- 341 tests currently passing

## Goal
Identify which axioms in Equiv.lean have no test coverage. An axiom with no
coverage can be removed (or replaced with `sorry`) without any test failing,
meaning there's no runtime or compile-time check that it's correct.

## Approach: Automated Script

Since there are 156 axioms, manual removal is impractical. Write a script that:

1. Extracts each axiom name from `SqlEquiv/Equiv.lean`
2. For each axiom:
   a. Comment it out (replace `axiom` with `-- axiom`)
   b. Attempt `lake build sql_equiv_test` (with timeout)
   c. If build fails → axiom IS referenced → has compile-time coverage → RESTORE and record "covered (compile)"
   d. If build succeeds → run `lake exe sql_equiv_test`
   e. If tests fail → axiom has runtime coverage → RESTORE and record "covered (runtime)"
   f. If tests pass → NO COVERAGE → RESTORE and record "UNCOVERED"
3. Produce summary report

## Key Constraints
- NEVER run `lake clean` (20+ min full rebuild)
- Each axiom removal should trigger incremental rebuild (seconds to minutes)
- Some axioms are used by theorems/other axioms — removing one cascades
- Script must always restore the file to avoid corrupting the build

## Expected Categories of Results
- **Compile-time covered**: Axiom used in a theorem proof or another declaration
  that's part of the build (e.g., `evalBinOp_and_assoc` is used by `and_assoc`)
- **Runtime covered**: Axiom not directly in build path but tested via runtime
  evaluation (e.g., optimizer tests exercise optimizer axioms)
- **Uncovered**: Axiom exists but nothing tests it (like `coalesce_null_left` was)

## Axiom Groups (for reference)
- Boolean algebra: and_assoc, or_assoc, distributivity, absorption, identity (lines 290-614)
- WHERE clause: where_true_elim, where_false_empty (lines 615-630)
- JOIN: join_comm, join_assoc, cross_join_* (lines 631-1276)
- Filter: filter_and, filter_commute, filter_idempotent, etc. (lines 1317-1358)
- NULL handling: already has tests after our PR
- Aggregates: min_le_elem, max_ge_elem, distinct_* (lines 1924-1940)
- CASE: case_when_true/false, etc. (lines 1949-1965)
- Arithmetic identity: expr_add_zero, expr_mul_one, etc. (lines 2000-2024)
- IN/BETWEEN/LIKE: in_empty_false, between_expansion, etc. (lines 2032-2142)
- Comparison: eq_reflexive, not_eq_is_ne, lt_flip, etc. (lines 2150-2199)
- Set ops: union_comm, intersect_assoc, etc. (lines 2207-2269)
- Join properties: cardinality, emptiness, etc. (lines 2278-2382)
- Subquery: exists_*, in_subquery_*, unnesting (lines 2398-2636)
- ORDER BY/LIMIT/OFFSET: (lines 2652-2839)
