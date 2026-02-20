# LeanDojo Trace Report

**Date:** 2026-02-19
**Commit:** `bc5c584`
**Tooling:** LeanDojo-v2 1.0.0, Lean 4.27.0

## Overview

We ran [LeanDojo](https://github.com/lean-dojo/LeanDojo-v2) on the sql_equiv repo to extract structured proof data: per-theorem tactic states, premise dependencies, and file-level dependency graphs. This report documents the setup, results, and assessment of the data's usefulness for our proof workflow.

## Setup

### Installation

```bash
uv pip install --system lean-dojo-v2
```

LeanDojo v1 (4.20.0) is deprecated and incompatible with Lean 4.27.0 due to universe-level changes in `StateT` and the `String.trim` → `String.trimAscii` rename. LeanDojo-v2 (1.0.0) handles these correctly.

### Running the Trace

```bash
python3 tools/leandojo_trace.py              # uses project root, HEAD, auto-detects token
python3 tools/leandojo_trace.py --commit abc123 --dst /tmp/trace
```

The scripts auto-detect `GITHUB_ACCESS_TOKEN` via `gh auth token` if not already set. You can also export it explicitly:

```bash
export GITHUB_ACCESS_TOKEN=$(gh auth token)
```

Key configuration:
- **`build_deps=False`** is essential. With `build_deps=True`, LeanDojo traces all 2,094 files (Lean 4 stdlib + batteries), taking ~31 hours. With `build_deps=False`, it traces only our 18 project files in ~25 minutes.
- The repo must be passed as a local path with `HEAD` as the commit reference. LeanDojo copies to a cache and validates `HEAD == requested_commit`.

### Output Location

- Cache: `~/.cache/lean_dojo/gitpython-sql_equiv-<commit>/sql_equiv/`
- Trace files: `.leandojo_trace/` (`.ast.json` + `.trace.xml` per file)
- Summary: `.leandojo_trace/trace_summary.json`

## Results

### Extraction Summary

| Metric | Count |
|--------|-------|
| Files traced | 17 / 18 |
| Theorems extracted | 503 |
| Tactic steps captured | 3,408 |
| Unique stdlib lemmas referenced | 287 |

`Tactics.lean` failed to trace (custom tactic macros cause elaboration errors in LeanDojo's extraction script).

### Per-File Breakdown

| File | Theorems | Tactics |
|------|----------|---------|
| Equiv/Comparison.lean | 189 | 994 |
| Equiv/StatementAxioms.lean | 84 | 568 |
| SemanticsCore.lean | 62 | 615 |
| Semantics.lean | 47 | 145 |
| Equiv/ExprAxioms.lean | 42 | 220 |
| Equiv/ValueLemmas.lean | 38 | 319 |
| Equiv/Defs.lean | 20 | 40 |
| Equiv/Decidable.lean | 14 | 395 |
| Equiv/SetBagLemmas.lean | 6 | 67 |
| SemanticsBase.lean | 1 | 45 |

## Data Format

### Tactic State Traces

For every tactic step in every proof, LeanDojo captures a `(state_before, tactic, state_after)` triple. Example from `except_self_empty`:

```
Step 1: simp only [evalQuery_compound, evalQuery_simple]
  BEFORE: ⊢ evalQuery db ((Query.simple a).compound SetOp.exceptOp (Query.simple a)) = []
  AFTER:  ⊢ List.filter (fun x => !List.contains (evalSelect db a) x) (evalSelect db a) = []

Step 2: generalize evalSelect db a = l
  BEFORE: ⊢ List.filter (fun x => !List.contains (evalSelect db a) x) (evalSelect db a) = []
  AFTER:  l : Table ⊢ List.filter (fun x => !List.contains l x) l = []

Step 3: rw [List.filter_eq_nil_iff]
  BEFORE: l : Table ⊢ List.filter (fun x => !List.contains l x) l = []
  AFTER:  l : Table ⊢ ∀ (a : Row), a ∈ l → ¬(!List.contains l a) = true

...

Step 6: exact absurd hx h
  BEFORE: hx : x ∈ l, h : ¬x ∈ l ⊢ False
  AFTER:  (no goals)
```

The full `trace_summary.json` contains this data for all 3,408 tactic steps.

### Premise Data

For each theorem, LeanDojo records every definition, lemma, and constructor referenced in the proof. For `except_self_empty`:

```
Project premises: evalQuery_compound, evalQuery_simple, evalSelect
Stdlib premises:  List.filter_eq_nil_iff, absurd
```

**Caveat:** Raw premise lists include type constructors (`Option.some`, `Bool.true`, etc.) with high multiplicity. For example, `evalBinOp_and_comm` lists 88 "premises" but only `Bool.and_comm` is the key lemma — the rest are constructor noise. Useful analysis requires deduplication and filtering.

### Most-Used Premises

**Project lemmas** (by number of theorems referencing them):

| Uses | Premise |
|------|---------|
| 84 | `evalBinOp` |
| 76 | `evalExpr` |
| 76 | `Expr.binOp` |
| 59 | `evalExprWithDb_binOp` |
| 54 | `evalExprWithDb` |
| 51 | `evalSelect` |
| 43 | `Expr.lit` |
| 41 | `evalExprWithDb_lit` |
| 40 | `evalUnaryOp` |
| 34 | `evalFrom` |

**Stdlib lemmas** (constructors excluded):

| Uses | Premise |
|------|---------|
| 35 | `List.length` |
| 26 | `List.foldl` |
| 20 | `Eq.symm` |
| 17 | `List.map` |
| 16 | `absurd` |
| 13 | `List.filter` |
| 11 | `List.mem_cons_self` |
| 11 | `List.flatMap_cons` |
| 9 | `List.length_cons` |
| 8 | `List.mem_cons_of_mem` |
| 8 | `Nat.le_refl` |
| 7 | `List.filter_cons` |
| 7 | `List.nil_append` |
| 7 | `List.foldl_cons` |

### File Dependency Graph

```
Ast.lean
├── SemanticsBase.lean
│   ├── SemanticsCore.lean
│   │   └── Semantics.lean
│   │       ├── Equiv/Defs.lean
│   │       │   ├── Equiv/SetBagLemmas.lean
│   │       │   ├── Equiv/ExprAxioms.lean
│   │       │   └── Equiv/Decidable.lean
│   │       └── Equiv/ValueLemmas.lean
│   │           ├── Equiv/Comparison.lean
│   │           ├── Equiv/StatementAxioms.lean
│   │           └── Equiv/ExprAxioms.lean
├── Parser.lean
└── Pretty.lean
```

## Potential Applications

### What This Data Enables

1. **Premise retrieval for proof guidance.** When stuck on a proof, query: "What lemmas do theorems with similar goal shapes use?" For example, all proofs involving `List.filter ... = []` use `List.filter_eq_nil_iff` — seeing this pattern across multiple theorems makes it discoverable.

2. **Tactic suggestion via ML.** The 3,408 `(state_before, tactic, state_after)` triples are the training data format for models like [ReProver](https://arxiv.org/abs/2306.15626). Given a goal state, a trained model predicts the next tactic.

3. **Proof similarity analysis.** Theorems sharing the same premise set likely share proof strategies. Clustering theorems by premise overlap could surface reusable proof patterns (e.g., "all set-operation proofs use `List.filter_eq_nil_iff` + `List.mem_cons_self`").

4. **Dependency impact analysis.** The premise graph shows that changing `evalBinOp` affects 84 theorems. This is more precise than file-level dependency tracking.

### What's Not Immediately Useful

- **We don't have an ML tactic predictor.** The tactic state data needs a model like ReProver to be actionable. Training one on 503 theorems is possible but small for ML standards.
- **Premise data is noisy without post-processing.** Raw extraction includes type constructors, which dominate the counts. Filtering is needed.
- **~25-minute trace time** makes it impractical for per-PR CI. Our `axiom_coverage_validator.py` already tracks axiom counts in seconds.

### CI/CD Feasibility

| Approach | Timing | Value |
|----------|--------|-------|
| Per-PR | ~25 min — too slow | Not recommended |
| Nightly scheduled | Acceptable | Track theorem count trends, detect premise drift |
| On-demand (workflow dispatch) | Acceptable | Deep analysis when needed |

## Scripts

| Script | Purpose |
|--------|---------|
| `tools/leandojo_trace.py` | Run the full trace (builds repo, extracts data). Args: `--repo`, `--commit`, `--dst` |
| `tools/leandojo_explore.py` | Load cached trace and generate `trace_summary.json`. Args: `--cache-dir`, `--output-dir` |

Both require `lean-dojo-v2` installed. `GITHUB_ACCESS_TOKEN` is auto-detected via `gh auth token` if not set.

## Recommendations

1. **Keep as an exploration tool**, not CI. Run manually when investigating proof patterns or after significant refactors.
2. **Post-process premises** before analysis: deduplicate, filter out constructors/types, keep only named theorems and lemmas.
3. **Revisit if we adopt ReProver** or another ML tactic predictor. The trace data is exactly what these tools consume.
4. **Consider extracting just the premise graph** (without full tactic states) via lighter-weight Lean metaprogramming if we want faster CI integration.
