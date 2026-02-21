# /sorry-audit

Audit all `sorry` usage across the codebase and verify documentation is accurate.

## Usage

- `/sorry-audit` — Full audit with doc cross-check

## Instructions

### Steps

1. **Find all sorry occurrences:**
   ```bash
   grep -rn "sorry" SqlEquiv/ --include="*.lean"
   ```
   Also check test files:
   ```bash
   grep -rn "sorry" Test/ --include="*.lean"
   ```

2. **For each sorry, classify it:**

   | Category | Description | Example |
   |----------|-------------|---------|
   | **Termination** | `decreasing_by` obligation | `decreasing_by all_goals sorry` |
   | **DecidableEq** | Opaque decidability instance | `unsafe def ... lcProof` |
   | **Proof gap** | Incomplete theorem proof | `theorem foo : ... := by sorry` |
   | **Test placeholder** | Placeholder in test code | Should not exist |

3. **Check each sorry has an explanatory comment** within 5 lines (before or after). Flag any that don't.

4. **Cross-check documentation counts:**
   - Read `docs/PROVING_AXIOMS_PLAN.md` and `docs/PROVING_LOG.md` for sorry/axiom count claims
   - Read `MEMORY.md` "Next Session TODO" for sorry count claims
   - Compare against actual grep results

5. **Report discrepancies** between documented counts and reality.

### Expected State (as of PR #174)

- **3 sorry** in `SqlEquiv/Semantics.lean` — Block 1 `decreasing_by` (lambda callbacks in mutual WFR, Lean 4.27.0 limitation)
- **1 sorry** in `SqlEquiv/Equiv/Decidable.lean` — opaque `DecidableEq` via `lcProof` (by design)
- **0 sorry** elsewhere

### Output Format

```
Sorry Audit
===========
Found: 4 sorry across 2 files

SqlEquiv/Semantics.lean:
  line 288: decreasing_by all_goals sorry  [Termination] [HAS COMMENT]
  line 300: decreasing_by all_goals sorry  [Termination] [HAS COMMENT]
  line 317: decreasing_by all_goals sorry  [Termination] [HAS COMMENT]

SqlEquiv/Equiv/Decidable.lean:
  line 1103: sorry  [DecidableEq] [HAS COMMENT / MISSING COMMENT]

Documentation cross-check:
  MEMORY.md says 3+1 sorry  ✓ matches
  PROVING_LOG.md says ...    ✓/✗

No undocumented sorry found.
```
