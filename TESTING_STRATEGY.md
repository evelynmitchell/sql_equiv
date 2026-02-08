# Testing Strategy: Defense in Depth

This project uses multiple independent verification layers so that no single
failure mode can go unnoticed. Each layer catches different classes of errors,
and the redundancy means a gap in one layer is covered by another.

## Verification Layers

### 1. Lean Kernel (compile-time)
- **What it catches:** Incorrect proofs. The kernel is the ultimate authority.
- **How it works:** `theorem` declarations are machine-checked during `lake build`.
- **Watch for:** Axioms (`axiom`) bypass the kernel entirely — they are trusted
  without proof. As axioms are converted to theorems, this layer grows stronger.

### 2. Runtime Test Suite (lake exe sql_equiv_test)
- **What it catches:** Evaluator bugs, parser regressions, optimizer incorrectness.
- **How it works:** ~800 hand-written tests with named coverage of all axioms.
- **Watch for:** Test names must follow the naming convention for the coverage
  validator (axiom name followed by a non-word character). New test files are
  auto-discovered.

### 3. Axiom Count Ratchet (CI)
- **What it catches:** Silent loss of axiom coverage after refactoring.
- **How it works:** `tools/axiom_count_minimum.txt` stores a floor. CI runs
  `--runtime` and fails if the count drops below it.
- **Watch for:** When axioms are intentionally removed (converted to theorems),
  update the ratchet: `python3 tools/axiom_coverage_validator.py --runtime --update-ratchet`

### 4. LSpec Property Tests (lake exe sql_equiv_lspec)
- **What it catches:** Edge cases in the evaluator and optimizer that
  hand-written tests miss, especially around NULL propagation, type
  mismatches, and algebraic identity boundary conditions.
- **How it works:** SlimCheck generates random expressions and checks that
  algebraic laws and optimizer transformations preserve semantics.
- **Watch for:** Findings go in `LSPEC_FINDINGS.md`. When adding new axioms
  or optimizer passes, add corresponding property tests.

### 5. Manual Validation
- **What it catches:** Systemic issues that automated checks can't see —
  CI duration changes, coverage gaps in the tooling itself, design-level
  concerns.
- **How it works:** Periodic human review. Run
  `python3 tools/axiom_coverage_validator.py --runtime` and check the output.
- **Watch for:** Unexpected changes in axiom counts, test counts, or CI timing.

### 6. AI-Assisted Review
- **What it catches:** Patterns across the codebase that are hard to spot
  in isolation — stale hardcoded lists, naming convention violations,
  missing test coverage for new features.
- **How it works:** Claude reviews changes, investigates anomalies, and
  cross-references across layers.
- **Watch for:** Ask for a coverage check when making structural changes
  (file moves, module splits, new axiom files).

## Maintaining the Layers

When making changes, verify that all layers still function:

```bash
# Layer 1: Lean kernel
lake build SqlEquiv

# Layer 2: Runtime tests
lake build sql_equiv_test && lake exe sql_equiv_test

# Layer 3: Ratchet
python3 tools/axiom_coverage_validator.py --runtime

# Layer 4: Property tests
lake build sql_equiv_lspec && lake exe sql_equiv_lspec
```

## Anti-Patterns to Avoid

- **Don't skip a failing layer** — fix the root cause instead of disabling the check.
- **Don't let the ratchet go stale** — update it promptly when axioms are
  intentionally converted to theorems.
- **Don't add axioms without tests** — the coverage validator will catch this,
  but it's better to add tests at the same time.
- **Don't add optimizer passes without property tests** — the LSpec suite is
  the primary defense for unproven optimizer correctness.
- **Don't ignore CI duration changes** — they can signal that a layer silently
  stopped running (as happened when Equiv.lean was split).
