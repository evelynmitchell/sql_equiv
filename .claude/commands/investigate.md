# /investigate

Notice and investigate anomalies in the project's health signals.

## Usage

- `/investigate` - Capture current baselines and check for anomalies
- `/investigate <observation>` - Investigate a specific odd thing

## Philosophy

The hardest part of catching bugs early is **noticing**. This requires
knowing what normal looks like — having a strong baseline built through
regular attention — so that strangeness stands out. A CI run that's
30 seconds faster, a test count that's slightly off, a file that shouldn't
have changed — these are signals, not noise. Never let the odd thing go.

## Instructions

### When run without an observation: Build baselines

Capture the current state of all project health signals so anomalies
can be detected later. This is the "knowing normal" part.

1. **Axiom count and coverage:**
   ```bash
   uv run python tools/axiom_coverage_validator.py --runtime 2>&1
   ```
   Note the axiom count, test count, files scanned, and any uncovered axioms.

2. **Test suite health:**
   ```bash
   lake build sql_equiv_test && lake exe sql_equiv_test 2>&1 | tail -20
   ```
   Note pass/fail counts per suite and total.

3. **LSpec property tests:**
   ```bash
   lake build sql_equiv_lspec && lake exe sql_equiv_lspec 2>&1 | tail -30
   ```
   Note total property count and any failures.

4. **Build timing (rough):**
   ```bash
   time lake build SqlEquiv 2>&1 | tail -5
   ```

5. **Report the baseline:**
   Summarize all signals in a compact table. Flag anything that looks
   different from expected. Compare against the ratchet file:
   ```bash
   cat tools/axiom_count_minimum.txt
   ```

### When run with an observation: Investigate

The user has noticed something odd. Follow the investigation protocol:

1. **Name the anomaly concretely.**
   Restate what the user observed in measurable terms.
   Not "CI seems different" but "CI duration dropped from 3min to 45s."

2. **Form hypotheses (at least two).**
   What could cause this? Think about what changed recently.
   Check `git log --oneline -10` for recent changes.

3. **Gather evidence — one hypothesis at a time.**
   Use the project's health signals to confirm or rule out each one.
   Don't fix anything yet. Understand first.

4. **Find the root cause — keep asking "why".**
   Don't stop at the proximate cause. Ask why it was possible.
   Not "the file wasn't scanned" but "the file list was hardcoded,
   so any refactoring silently breaks it."

5. **Fix the root cause, not the symptom.**
   Structural fix over patch. Auto-discover over hardcode.
   Make the class of error impossible, not just this instance.

6. **Add a guard.**
   The anomaly should be impossible to ignore next time.
   A CI check, a ratchet, a property test — something automated
   that fails loudly if this happens again.

7. **Document in LSPEC_FINDINGS.md or TESTING_STRATEGY.md.**
   What you found, why it happened, what guard you added.
   Future sessions won't have today's context.

### Signals worth investigating

These are the kinds of things that should trigger a `/investigate`:

- CI duration changed significantly (faster or slower)
- Test count changed without an obvious reason
- Axiom count doesn't match the ratchet
- A property test started failing after an unrelated change
- Build output has new warnings
- A file was modified that shouldn't have been
- Coverage percentage changed

## Related Commands

- `/test` - Run the main test suite
- `/lspec` - Run LSpec property tests
- `/lint` - Check for warnings
- `/build` - Build the project
