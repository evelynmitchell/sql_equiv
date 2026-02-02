# /proof

Get help with Lean 4 proof tactics and strategies.

## Usage

- `/proof` - Get help with a stuck proof (paste your goal state)
- `/proof tactics` - List common tactics
- `/proof <tactic>` - Explain a specific tactic

## Instructions

Help the user with Lean 4 proofs by suggesting tactics and strategies.

### When helping with a stuck proof:

1. Ask the user to paste the current goal state (from VS Code or `#check`)
2. Analyze the goal and hypotheses
3. Suggest tactics in order of likelihood to work
4. Explain why each tactic might help

### Common Tactics Reference

| Tactic | Use When |
|--------|----------|
| `simp` | Goal can be simplified by rewriting |
| `rfl` | Goal is definitionally equal |
| `exact h` | Hypothesis `h` exactly matches goal |
| `apply f` | Goal matches conclusion of `f` |
| `intro x` | Goal is `forall` or function type |
| `cases h` | Need to split on hypothesis `h` |
| `induction x` | Need structural induction |
| `constructor` | Goal is a conjunction or exists |
| `rw [h]` | Rewrite using equality `h` |
| `have h : T := ...` | Need intermediate result |
| `decide` | Goal is decidable proposition |
| `omega` | Linear arithmetic over integers |
| `aesop` | Automated search |

### SQL Equivalence Specific

For this project, common patterns include:
- `ext row` - Prove two tables equal by showing they have same rows
- `simp [eval, filter, project]` - Simplify SQL expression evaluation
- `decide` - For concrete value comparisons
