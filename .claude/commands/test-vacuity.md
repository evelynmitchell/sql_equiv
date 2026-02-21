# /test-vacuity

Check tests for vacuity — cases where both sides of a comparison silently return empty or error, making the test pass without exercising the intended behavior.

## Usage

- `/test-vacuity` — Audit all test files
- `/test-vacuity <file>` — Audit a specific test file

## Instructions

### Background

A vacuous test compares two expressions that both evaluate to `[]` (empty table) or `none` (error) due to a bug in the test setup — wrong column names, wrong table names, missing qualifiers, etc. The test passes but proves nothing. This has happened multiple times in this project.

### Steps

1. **Read each test file** under `Test/`:
   ```
   Test/EvalTest.lean
   Test/EquivTest.lean
   Test/AxiomCoverageTest.lean
   Test/InfraAxiomTest.lean
   Test/SubqueryTest.lean
   ```

2. **For each test assertion**, identify the pattern:

   | Pattern | What to check |
   |---------|---------------|
   | `lhs == rhs` | Could both be `[]`? Could both be `none`? |
   | `result.length == N` | Is N == 0? (comparing against empty is weak) |
   | `evalSelect db stmt == expected` | Does `expected` have actual rows? |
   | `evalExprWithDb db row expr == some val` | Is val a meaningful value? |

3. **Flag suspicious tests:**
   - Both sides could be empty (`[] == []`)
   - Both sides could be error (`none == none`)
   - Expected value is `[]` or `none` without a companion test showing non-empty case
   - Column references use unqualified names where `evalFrom` produces qualified names (e.g., `"x"` vs `"t.x"`)
   - Table names in test don't match `testDb` keys

4. **Check for anti-vacuity guards.** Good tests include:
   - `testLengthGe result 1` — asserts the result is non-empty
   - A companion test with different inputs that produces a different result
   - Explicit row count assertions

5. **For each flagged test**, suggest a quick verification: modify one expected value and confirm the test fails. If flipping the expected value doesn't cause failure, the test is vacuous.

### Output Format

```
Test Vacuity Audit
==================
Test/EvalTest.lean:
  line 45: "cross join produces rows"
    ✓ Anti-vacuity: testLengthGe result 2
  line 82: "left join null column"
    ⚠ SUSPECT: expected value is [none], no positive case companion
    Suggestion: verify by changing expected to [some (.int 1)] and confirming failure

Test/EquivTest.lean:
  line 120: "filter pushdown"
    ✓ Both sides non-empty (3 rows)

Summary: 2 suspect tests found across 5 files.
```

### Common Vacuity Patterns in This Project

- `testDb "tableName"` returns unqualified rows, but `evalFrom` qualifies as `"alias.col"`. A test comparing `evalFrom` output against raw `testDb` rows will get `[] == []` (no column match).
- `col "x"` in test expressions when the FROM clause aliases the table — need `qcol "t" "x"`.
- `evalSelect` with wrong `SelectItem` alias — projection returns `[(wrong_name, val)]`, comparison against `[(right_name, val)]` fails, both sides effectively empty from the test's perspective.
