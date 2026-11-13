# Report format

```
## Rewrite Audit: [function name or "Full Scan"] ([project], [commit])

### Trust base (proof-assistant projects)
- #print axioms <theorem>: [...]   (expected: propext, Classical.choice, Quot.sound)
- Whole-library guard: <result, theorem count> / not present (recommend)
- Runtime overrides on path: none / [list with on-path / off-path]

### [rewriter] (file:line)

#### Arm N: `pattern → result`   [guard: …]
- Free variables: a, b
- Proof: <theorem> concludes <relation> (full / weaker: …) / none
- Type analysis (unproven arms, or where the proof's scope is in doubt):
  | a kind | b kind | BEFORE | AFTER | Status |
  |--------|--------|--------|-------|--------|
  | int    | -      | error  | int n | MISMATCH |
  | bool   | -      | bool b | bool b | ok |
  | null   | -      | null   | null  | ok |
  | error  | -      | error  | error | ok |
- Verdict: SOUND / UNSOUND — <one line>
- Guard check: <guard> / bridge <theorem or test> / missing
- Suggested fix: …

### Empirical probe
- Expressions: N, rewritten: M, contexts: …, mismatches: K
- Vacuity check: <mutant> caught? yes/no

### Summary
- Rewriters audited: N
- Arms checked: M
- Issues: K
  - [rewriter:arm] — description
- Observations (not soundness issues): …
```

Status markers:
- `ok` — same result before and after
- `MISMATCH` — different results: a soundness bug, with a counterexample
- `GUARD` — would mismatch, but the arm's guard excludes this combination
