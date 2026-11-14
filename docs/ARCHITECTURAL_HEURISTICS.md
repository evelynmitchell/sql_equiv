# Architectural Heuristics for sql_equiv

**Date:** 2026-02-20

This document captures heuristics for detecting architectural issues early,
drawn from patterns observed during the axiom proving campaign (531/538
theorems proved). The project grew incrementally over many PRs, and several
issues only became visible late — costing days of proof effort that could
have been avoided with a few minutes of upfront checking.

---

## The Three-Check Rule

Before investing proof effort in any axiom, spend 5 minutes on these three
checks:

1. **Can Lean reduce the functions I need?** (try `simp`)
2. **Are the stated blockers still real?** (check the source)
3. **Is the statement actually true?** (try counterexamples)

Each check targets a distinct failure mode. Together they catch the most
expensive class of wasted work: successfully proving something that wasn't
needed, or failing to prove something that was provable all along.

---

## 1. Namespace Pollution from `partial def`

### The problem

A single `partial def` in a file prevents equational theorem generation for
**every** function in that namespace. In Lean 4, `partial def` compiles to
`opaque` in the kernel — and the presence of `opaque` definitions in a
namespace interferes with `simp [f]` and `.eq_def` for other, perfectly
well-founded functions sharing that namespace.

### How it manifested

`Decidable.lean` contained 7 `partial def`s (e.g., `decideExprEq`; all removed in #278). The
function `exprReferencesOnlyTable` in the same file is a proper WFR
function with a complete termination proof — but `simp` couldn't reduce it.
This silently blocked `filter_join_left` and `filter_join_right` for weeks.

### Detection heuristic

**"Can I `simp [f]` right after defining `f`?"**

After adding any non-trivial definition, write a one-line smoke test:

```lean
-- Smoke test: does this function reduce?
example : exprReferencesOnlyTable "t" (.lit (.int 1)) = false := by
  simp [exprReferencesOnlyTable]
```

If it fails and the function is not `partial`, something else in the file
is poisoning the namespace.

### When to check

Every time you add a WFR function to a file that also contains `partial
def`s. The cost of checking is seconds; the cost of not checking is
discovering the blocker months later.

### The fix

Move the function to a file that does not import `partial def`s. The
pattern is well-established in this codebase:

- `SemanticsBase.lean` — pure helpers, no `partial def`s
- `SemanticsCore.lean` — WFR core evaluators with termination proofs
- `Semantics.lean` — `partial def` mutual block + bridge axioms

Apply the same split wherever `partial def`s and provable functions coexist.

---

## 2. Stale Blocker Annotations

### The problem

Comments like `-- blocked by partial def exprReferencesOnlyTable` become
stale when the upstream issue is resolved. The comment persists, making the
axiom appear harder than it actually is and misdirecting prioritization.

### How it manifested

`filter_join_left` had a blocker comment citing `exprReferencesOnlyTable`
as `partial`. That function was converted to WFR weeks earlier. The real
blocker was different `partial def`s in the same file — but the stale
comment pointed attention in the wrong direction.

### Detection heuristic

**"Does the stated blocker still exist?"**

When you encounter a "blocked by X" comment, verify it:

- Is the function still `partial`? (`grep "partial def X"`)
- Is the upstream PR still open? (`gh pr view`)
- Does the cited line number still contain what the comment says?

### When to check

During any planning pass over remaining axioms. A 30-second grep beats
weeks of misprioritization.

### Structural fix

Instead of free-text "blocked by" comments, use a machine-checkable format:

```lean
-- BLOCKED: requires `exprReferencesOnlyTable` to be non-partial
-- CHECK: grep -c "partial def exprReferencesOnlyTable" SqlEquiv/Decidable.lean
--        Expected: 0 (if resolved, remove this BLOCKED annotation)
```

The `CHECK` line is a runnable command that verifies the blocker. Stale
blockers become self-diagnosing. A CI script could even run these
automatically.

---

## 3. Missing Preconditions (Unsound Axiom Statements)

### The problem

Axioms stated without preconditions may only hold under specific conditions
(column disjointness, NULL-freeness, type constraints). Attempting to prove
an unsound statement wastes hours before the counterexample surfaces.

### How it manifested

Multiple times across the project:

| Axiom | Issue | Resolution |
|-------|-------|------------|
| `coalesce_null_left` | False when second arg is NULL | Deleted; replaced with `coalesce_null_left_nonnull` |
| `join_comm_full` | False for non-disjoint column names | Deleted (Batch 22) |
| `join_comm` | Unprovable without column disjointness | Needs precondition (pending) |
| `not_in_subquery_unnest_to_antijoin` | False when subquery has NULL values | Needs NULL-freeness precondition (pending) |
| `eq_reflexive` | Failed for error-producing expressions | Added `Expr.evaluable` precondition (PR #92) |
| Arithmetic identities | Failed for non-integer expressions | Added `Expr.isIntValued` precondition (PR #93) |
| Boolean identities | Failed for non-boolean expressions | Added `Expr.isBoolValued` precondition (PR #104) |

### Detection heuristic

**"Can I break this with NULL, empty, or ambiguous inputs?"**

Before attempting any proof, spend 5 minutes trying to construct a
counterexample with these five pathological inputs:

| Input class | What it breaks |
|-------------|----------------|
| `NULL` values | NOT IN semantics, COALESCE, comparison chains |
| Empty tables/lists | Aggregate behavior, EXISTS, cardinality claims |
| Duplicate column names | Join commutativity, column resolution order |
| Type mismatches | Arithmetic identities, boolean simplification |
| `none` vs `some (.null _)` | Any axiom quantifying over `Option Value` |

The `/counterexample` skill automates this. The key is making it a
**mandatory pre-step** before any proof attempt, not an optional diagnostic.

### When to check

Before writing the first line of any proof. If the counterexample search
takes more than 10 minutes without finding anything, the axiom is likely
sound. If it finds one in 2 minutes, you just saved days.

### The `Option Value` trap specifically

The distinction between `none` (evaluation failure / no value) and
`some (.null _)` (SQL NULL was produced) is easy to overlook. When writing
or reviewing axioms that quantify over `Option Value`, always check five
representative values:

```
some (.int 42)       -- normal integer
some (.string "abc") -- normal string
some (.bool true)    -- normal boolean
some (.null none)    -- SQL NULL
none                 -- evaluation error (missing column, type mismatch)
```

This was the root cause of the `coalesce_null_left` unsoundness and the
original `eq_reflexive` unprovability (before the PR #92 null semantics
fix).

---

## Common Thread

All three patterns share a root cause: **information decays as the codebase
evolves**. A function that was `partial` becomes WFR. A blocker that was
real gets resolved. An axiom that seemed obvious turns out to need
preconditions.

The general principle: before investing proof effort, spend a few minutes
verifying assumptions about the current state. The cost of checking is
always small relative to the cost of working from stale assumptions.

---

## Checklist for New Axioms

Before adding a new `axiom` declaration:

- [ ] Run `/counterexample` with NULL, empty, duplicate-column, and
      type-mismatch inputs
- [ ] Verify all referenced functions are reducible (`simp [f]` smoke test)
- [ ] Check that no `partial def` in the file blocks equational reasoning
- [ ] If adding a precondition, verify it matches SQL standard behavior
      (check PostgreSQL docs for edge cases)
- [ ] Add a runtime test in `Test/AxiomCoverageTest.lean`

Before attempting to prove an existing `axiom`:

- [ ] Re-read the axiom statement — is it still what you expect?
- [ ] Check all "blocked by" comments — are the blockers still real?
- [ ] Try `/counterexample` — is the axiom actually sound?
- [ ] Verify infrastructure lemmas are available (`simp` smoke test)

---

## Checklist for File Reorganization

When splitting a file or moving definitions:

- [ ] Count `axiom` and `theorem` declarations before and after
      (`grep -c "^axiom\|^theorem"`)
- [ ] Verify no `partial def`s leak into files meant for provable functions
- [ ] Run `lake build` to catch import cycle issues
- [ ] Check that `simp` still works for functions that were previously
      reducible
- [ ] Update any "blocked by" comments that reference the moved definitions
