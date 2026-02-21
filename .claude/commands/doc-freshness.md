# /doc-freshness

Check documentation for stale counts, outdated references, and inconsistencies with the actual codebase.

## Usage

- `/doc-freshness` — Full scan of all docs

## Instructions

### Steps

1. **Collect ground truth from the codebase:**

   ```bash
   # Axiom/theorem counts (authoritative)
   python3 tools/count_axioms_theorems.py -v

   # Sorry count (approximate — may include commented-out occurrences)
   grep -rn "sorry" SqlEquiv/ --include="*.lean"

   # Axiom ratchet
   cat tools/axiom_count_minimum.txt
   ```

   Note: the sorry grep may match occurrences inside block comments (`/- ... -/`). Manually inspect each hit to confirm it's active code, not commented out.

   Use `tools/count_axioms_theorems.py` as the authoritative source for axiom/theorem totals — raw `grep "^axiom "` misses `private axiom` and indented declarations.

2. **Scan documentation files for numeric claims:**

   Files to check (recursive scan — includes subdirectories):
   - `docs/` and all subdirectories (`docs/specs/`, `docs/proposals/`, `docs/tutorials/`, etc.)
   - `README.md`

   Look for patterns:
   ```bash
   grep -rn "[0-9]* axiom" docs/
   grep -rn "[0-9]* theorem" docs/
   grep -rn "[0-9]* sorry" docs/
   grep -rn "PR #[0-9]*" docs/
   ```

3. **Cross-check each claim against ground truth.** Flag any mismatch.

4. **Check for references to removed code:**
   - The optimizer module was removed in PR #156. Any doc mentioning `Optimizer/`, `optimizeExpr`, `simplifyArithmetic`, `applyIdentityLaws` etc. is stale.
   - Grep for these:
     ```bash
     grep -rn "optimiz\|Optimizer\|simplifyArith\|applyIdentity\|constantFold" docs/
     ```

5. **Check PR references still make sense** — a doc saying "PR #120 added X" is fine (historical), but "PR #120 will add X" (future tense for a merged PR) is stale.

6. **Check MEMORY.md "Next Session TODO"** — are items there still relevant or already done?

### Output Format

```
Doc Freshness Report
====================

docs/PROVING_AXIOMS_PLAN.md:
  line 12: "22 axioms remaining" — STALE (actual: 0)
  line 45: references Optimizer module — STALE (removed PR #156)
  line 78: "561 theorems" — ✓ current

docs/PROVING_LOG.md:
  line 5: "4→3 axioms" — ✓ historical (correct at time of writing)

tools/axiom_count_minimum.txt:
  value: 0 — ✓ matches

Summary: 3 stale references found across 2 files.
```

### Fixing Stale Docs

For each stale reference, either:
- **Update the number** if it's a current-state claim
- **Add "(as of PR #N)"** if it's a historical claim that should be preserved
- **Delete the section** if it references removed functionality

### Related Commands

- `/count` — Get current axiom/theorem counts
- `/sorry-audit` — Get current sorry count
