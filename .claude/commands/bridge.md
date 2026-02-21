# /bridge

Prove a bridge theorem connecting a WFR function in Semantics.lean to its Core equivalent in SemanticsCore.lean.

## Usage

- `/bridge <core-lemma-name>` — Prove the bridge theorem for the specified Core lemma

## Instructions

### Background

The codebase uses a 3-file split: `SemanticsBase.lean` (types) → `SemanticsCore.lean` (non-partial parametric functions + proofs) → `Semantics.lean` (WFR functions + bridge theorems + final theorems). Bridge theorems connect the WFR functions to their Core equivalents, enabling proofs to use Core-level lemmas.

### Steps

1. **Read the Core lemma** in `SqlEquiv/SemanticsCore.lean`. Note:
   - Its parameter signature (which callbacks does it take?)
   - What it proves about the Core function

2. **Identify which bridge(s) you need.** The existing bridges are:

   | Bridge | Proof | Line |
   |--------|-------|------|
   | `evalExprWithDb_eq_evalExprCore` | `simp [evalExprWithDb]` | ~573 |
   | `evalFrom_eq_evalFromCore` | `simp only [evalFrom]; congr 1` | ~590 |
   | `evalSelect_eq_evalSelectCore` | `simp only [evalSelect, evalSelectWithContext]` | ~937 |
   | `evalSelectWithContext_eq_evalSelectCore` | `simp only [evalSelectWithContext]` | ~952 |
   | `evalQuery_eq_evalQueryCore_simple` | `unfold evalQuery; simp [evalQueryCore]` | ~925 |
   | `evalQuery_eq_evalQueryCore_compound` | `unfold evalQuery evalQueryCore; rfl` | ~930 |

3. **Write the bridge theorem** in `SqlEquiv/Semantics.lean`, placed after the existing bridge theorems (after line ~964). The pattern:

   ```lean
   theorem <name> (db : Database) (<params>) :
       <WFR_function> db <args> = <Core_lemma_conclusion_with_callbacks_instantiated> := by
     rw [<existing_bridge>]
     exact <core_lemma> <args>
   ```

   Or if the Core lemma's conclusion directly matches after bridge rewrite:
   ```lean
   theorem <name> (db : Database) (<params>) :
       <WFR_function> db <args> = <expected> := by
     have h := <existing_bridge> db <args>
     rw [h]
     exact <core_lemma> <args>
   ```

4. **Common proof patterns:**

   **Direct bridge + Core lemma:**
   ```lean
   theorem evalSelect_foo (db : Database) (sel : SelectStmt) :
       evalSelect db sel = <expected> := by
     rw [evalSelect_eq_evalSelectCore]
     exact evalSelectCore_foo ...
   ```

   **Bridge with `have raw` + `exact` for definitional equality gaps:**
   ```lean
   theorem evalSelect_bar (db : Database) (sel : SelectStmt) :
       evalSelect db sel = <expected> := by
     have raw := by
       rw [evalSelect_eq_evalSelectCore]
       exact evalSelectCore_bar ...
     rw [raw, list_map_nil_append_eq]
   ```

   **Bridge via `.trans` (chaining equalities):**
   ```lean
   theorem evalQuery_simple (db : Database) (sel : SelectStmt) :
       evalQuery db (.simple sel) = evalSelect db sel :=
     (evalQuery_eq_evalQueryCore_simple db sel).trans (evalQueryCore_simple ..)
   ```

5. **Key callback abbreviation:** `private abbrev ee` (line ~935) is shorthand for `fun db' (r : Row) e => @evalExprWithDb db' r e`. Use it when instantiating `evalSelectCore` callbacks.

6. **Build and verify:**
   ```bash
   lake build sql_equiv_test
   ```

### Important Notes

- Bridge theorems must be placed AFTER the mutual block `end` (line ~319) and after the bridge axiom declarations
- `simp [evalExprWithDb]` works because WFR functions have equational theorems (unlike `partial def`)
- For mutual WFR functions, use `unfold` instead of `simp` (mutual blocks don't generate equational theorems for `simp`)
- `List.map ([] ++ ·)` artifacts from `evalSelectCore` → clean up with `list_map_nil_append_eq`
- `evalSelectItemParam ee` vs `evalSelectItem`: use `have raw := by exact ...` to bridge the definitional equality gap

### Related Commands

- `/proof` — Interactive proof assistance
- `/build` — Build the project
