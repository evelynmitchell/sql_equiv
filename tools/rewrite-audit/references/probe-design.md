# Empirical probe

The protocol is a hand-trace. The probe checks it by execution: evaluate
original and rewritten expressions over many operands and contexts, and
compare.

## If the project already has one

1. Find the property, fuzz or differential tests that compare
   `eval(e)` with `eval(rewrite(e))`. They're named in the config `probe`
   field once known.
2. Run them. Report the number of expressions, how many were actually
   rewritten, the contexts covered and the mismatch count.

   A probe where few expressions are rewritten is weak. Report the ratio.
3. **Vacuity check, always.** Confirm the probe can fail:
   - If the project has a built-in self-check, confirm it passes, **and check
     that it is a real mutant check**. It must run a deliberately unsound
     rewriter through the *same* mismatch function, cases and contexts as the
     real probe, and require it to be caught. An assertion that merely shows
     the evaluator distinguishes two expressions (e.g. `eval(42 AND TRUE) ≠
     eval(42)`) tests the evaluator, not the probe, and does not count.
   - Otherwise, make a temporary mutant on a scratch branch or copy, so the
     working tree is never left modified. Remove one guard from an identity
     rule (the `a AND TRUE → a` shape) and confirm the probe reports a
     mismatch.

   Revert, and confirm the working tree is clean.

## Comparing results

- **Kind-strict equality.** Compare results so that values of different kinds
  never compare equal, even if the host language says so: Python
  `1 == True`, JS `1 == "1"`, `1 == 1.0`. Compare the kind (type) as well as
  the value, and treat NaN as equal to itself only if the evaluator does.
- **Change detection.** "Was this expression rewritten?" must not use the same
  loose equality, or rewrites like `Lit(1) → Lit(True)` go unseen. Compare a
  structural, kind-preserving representation (e.g. `repr`).

## Vacuity check details

- **Baseline already failing.** If the probe already reports mismatches on the
  unmodified code, the mutant cannot "turn it red". Compare the *set* of
  distinct failing expressions instead: the mutant must add failures, and the
  mutant's own target expression must fail.
- **Choose a disjoint mutant.** Prefer a guard whose removal changes
  expressions that do not already fail for another reason. Otherwise the
  check cannot tell the mutant's effect from the known bugs.

## If it has none

Propose a probe; do not add it to the test suite without the user's
agreement. Shape:

```
for each rewrite arm A:
  for each operand kind combination K (from the value-domain table):
    for each context C (row variants; empty and non-empty data; config modes):
      e  := an expression matching A's pattern with operands of kinds K
      e' := rewrite(e)
      assert eval(C, e) == eval(C, e')   -- report e, K, C on failure
also count how many generated e were actually changed by rewrite
```

Include at least:
- one operand of every kind, including NULL kinds and an error-producing
  operand (e.g. a type mismatch inside it);
- for data-dependent constructs, an empty and a non-empty data source;
- each mode the evaluator has (dialect, collation, strictness).

The mutant vacuity check applies to a new probe too.
