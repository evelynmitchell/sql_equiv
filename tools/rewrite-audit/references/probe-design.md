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
   - If the project has a built-in self-check (a mutant oracle run inside the
     suite), confirm it passes.
   - Otherwise, make a temporary mutant on a scratch branch or copy, so the
     working tree is never left modified. Remove one guard from an identity
     rule (the `a AND TRUE → a` shape) and confirm the probe reports a
     mismatch.

   Revert, and confirm the working tree is clean.

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
