# Issue #124: IN-list Evaluator Semantics Fix

## Overview
Fix evaluator so `x IN (a, b, ...)` matches SQL semantics (equivalent to `(x=a) OR (x=b) OR ...`).
Blocks issue #58 (6 IN-list expansion axioms).

## Three Sub-problems (in dependency order)

### Sub-problem 1: `evalBinOp .or/.and` missing null rules
**File**: `SqlEquiv/Semantics.lean` lines ~124-182
- `FALSE OR NULL` returns `none` (error) — should return `some (.null none)` (SQL NULL)
- Missing 6 three-valued logic rules:
  - `.or`: FALSE OR NULL → NULL, NULL OR FALSE → NULL, NULL OR NULL → NULL
  - `.and`: TRUE AND NULL → NULL, NULL AND TRUE → NULL, NULL AND NULL → NULL
- Short-circuit rules (TRUE OR x → TRUE, FALSE AND x → FALSE) already exist and are correct
- **Existing proofs that will break**: `false_or_null` (Comparison.lean:421), `null_or_false` (~:425), `null_and_null` (~:431)
- These proofs currently assert the *wrong* (current) behavior — they need to be updated to assert the *correct* (new) behavior

### Sub-problem 2: `inList` evaluator rewrite
**File**: `SqlEquiv/Semantics.lean` lines ~276-282
- Current implementation uses `filterMap` + `any` — drops errors/nulls
- New implementation: `foldl` over `evalBinOp .or` / `evalBinOp .eq`
- Pseudocode for new semantics:
  ```
  evalInList val [] = some (.bool false)   -- base case
  evalInList val (x::xs) = evalBinOp .or (evalBinOp .eq val x) (evalInList val xs)
  ```
- This automatically gets null propagation from sub-problem 1's fix

### Sub-problem 3: `evalExprWithDb_inList` infrastructure axiom
**File**: `SqlEquiv/Semantics.lean` lines ~835-842
- Must be updated to match the new evaluator definition
- Statement should decompose inList into the foldl/OR chain

### Optional Sub-problem 4: `evalBinOp .eq/.ne` type-mismatch → false instead of error
**File**: `SqlEquiv/Semantics.lean` line ~147 and ~75-81
- Currently `(.int 1).eq (.string "a")` → `none` (error)
- Could change to `some (.bool false)` (not equal)
- Would make IN-list axioms fully unconditional (no type-match precondition)
- **Risk**: may break other proofs that rely on type-mismatch → none behavior

## Behavioral Changes
| Expression | Current | After fix |
|-----------|---------|-----------|
| `1 IN (NULL)` | `FALSE` | `NULL` |
| `1 IN (error)` | `FALSE` | `error` |
| `NULL IN (1,2)` | `FALSE` | `NULL` |
| `1 IN (1, NULL)` | `TRUE` | `TRUE` (unchanged) |

## Downstream Impact Checklist
- [ ] `in_empty_false` — reprove (base case of foldl is `some (.bool false)`, should be simpler)
- [ ] `not_in_empty_true` — reprove
- [ ] `false_or_null` (Comparison.lean:421) — update to new behavior
- [ ] `null_or_false` (Comparison.lean:~425) — update to new behavior
- [ ] `null_and_null` (Comparison.lean:~431) — update to new behavior
- [ ] Any proofs in ValueLemmas.lean using `.or`/`.and` with null — check
- [ ] Any proofs in ExprAxioms.lean using `.or`/`.and` with null — check
- [ ] InListTest.lean — update expected values in tests
- [ ] `evalExprWithDb_inList` — rewrite to match new definition
- [ ] Property tests (LSpec) — check if any test null+or/and combos

## Implementation Order
1. Fix `evalBinOp .or/.and` null rules (sub-problem 1)
2. Update broken proofs from step 1
3. Rewrite `inList` evaluator (sub-problem 2)
4. Update `evalExprWithDb_inList` axiom (sub-problem 3)
5. Update tests
6. Build and verify all proofs still pass
7. (Optional) Fix eq/ne type-mismatch (sub-problem 4) — evaluate risk first

## Key Code Locations to Re-read
- `SqlEquiv/Semantics.lean` — evalBinOp (or/and arms), inList evaluator, evalExprWithDb_inList
- `SqlEquiv/Equiv/Comparison.lean` — false_or_null, null_or_false, null_and_null, null_or_null
- `SqlEquiv/Equiv/ExprAxioms.lean` — in_empty_false, not_in_empty_true, any inList axioms
- `SqlEquiv/Equiv/ValueLemmas.lean` — any Value.or/Value.and lemmas
- `Test/InListTest.lean` — existing inList tests
