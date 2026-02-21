# /dead-code

Find unused private declarations across the SqlEquiv codebase.

## Usage

- `/dead-code` — Scan all `.lean` files under `SqlEquiv/`
- `/dead-code <file>` — Scan a specific file

## Instructions

### Steps

1. **Collect all private declarations:**
   ```bash
   grep -rn "^private " SqlEquiv/ --include="*.lean"
   ```

2. **For each private declaration, extract the name** (second or third word, depending on `private def`, `private theorem`, `private lemma`, `private abbrev`).

3. **Count occurrences of each name** in the same file. A private declaration is "used" if its name appears at least **twice** in the file (once for the definition, once or more for usage).

   ```bash
   # For each name, count literal occurrences in its file:
   grep -F -c "name_here" <file>
   ```

   Use `-F` (fixed-string) because Lean names like `List.filterMap_none` contain `.` which is a regex metacharacter.

4. **Report unused declarations** — any private name appearing exactly once (definition only, no usage).

### Important Notes

- Private declarations are file-scoped in Lean 4 — only check the same file for usage.
- Names ending in `'` (prime) need care: `grep` word boundaries don't work. Use `grep -F` for literal matching.
- Lean's built-in linter does NOT flag unused `private theorem` or `private def`. This check catches what the linter misses.
- Proof exploration often leaves dead helpers from abandoned approaches.

### Output Format

```
Dead Code Scan
==============
SqlEquiv/Equiv/StatementAxioms.lean:
  line 42: private theorem helper_lemma_v2  (UNUSED)
  line 98: private def old_approach         (UNUSED)

SqlEquiv/SemanticsCore.lean:
  (all private declarations used)

Summary: 2 unused private declarations found in 1 file.
```

If no unused declarations are found, report that.

### Fix

For each unused declaration, the fix is simple: delete it. But verify first that it's truly unused — some declarations are used via `simp` lemma sets or tactic `exact` with elaboration, which textual grep might miss. When in doubt, delete and rebuild.
