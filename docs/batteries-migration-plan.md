# Batteries Migration Plan

> **Historical snapshot.** Axiom/theorem counts in this document are as of when it was written. As of 2026-11 the codebase has **0 axioms** (all proved since PR #173) and **622 theorems**; run `python3 tools/count_axioms_theorems.py` for the live count.

## Motivation

The project currently avoids importing Batteries because `Tactic.Alias` (re-exported
by Batteries) makes `alias` a reserved command name, breaking pattern-match bindings
across Optimizer.lean, Semantics.lean, PredicatePushdown.lean, and others.

This avoidance has two costs:

1. **~1,100 lines of hand-rolled proofs** duplicating Batteries lemmas (list
   permutations, boolean algebra, Option combinators).

2. **Fragility under new Value constructors.** The `ValueLemmas.lean` proofs use
   exhaustive case analysis. Adding one constructor to `Value` (e.g. `float`) adds
   arms to every theorem — 36→49 for 2-arg proofs, 216→343 for 3-arg proofs.
   SQL needs float, date/datetime, and decimal at minimum.

The migration unblocks type expansion and replaces brittle exhaustive proofs with
compositional ones.

---

## Prerequisites

### P1. Rename `alias` → `as_name` across the codebase

Batteries re-exports `Tactic.Alias`, which registers `alias` as a top-level
command. This prevents using `alias` as an identifier anywhere in files that
(transitively) import Batteries.

**Scope:** 89 occurrences across 15 files. The rename is mechanical:

- `TableRef.alias` → `TableRef.as_name` (structure field, Ast.lean:185)
- `SelectItem.exprItem` second parameter (Ast.lean:259)
- `FromClause.subquery` second parameter (Ast.lean:264)
- All pattern-match sites in Semantics, Optimizer, PredicatePushdown, Pretty,
  Main, OptimizerUtils, Decidable, test files

**Risk:** Low. Pure rename, type-checker catches any missed site.
**Estimated effort:** Small — one `sed` pass + `lake build` to confirm.

### P2. Pin Batteries to a specific rev

Change `lakefile.toml` from `rev = "main"` to a specific commit hash.
Building against `main` means any Batteries update can break the build.

---

## Phase 1: Unlock Batteries imports (no proof changes)

**Goal:** Import Batteries successfully; delete `SetBagLemmas.lean` hand-rolled
lemmas and replace with Batteries equivalents.

### 1.1 Apply the `alias` → `as_name` rename (P1)

### 1.2 Add `import Batteries` to modules that need it

Start with `SetBagLemmas.lean`. Replace:
- `perm_ext_iff_of_nodup` → `List.Perm.eq_of_nodup` or equivalent
- `mem_eraseDups` → `List.mem_dedup`
- `nodup_eraseDups` → `List.nodup_dedup`
- `Perm_eraseDups` → `List.Perm.dedup`
- `mem_filter_contains` → `List.mem_filter` + `List.mem_contains`
- `mem_eraseDups_append` → composition of above

**Validation:** `lake build` passes. All existing tests pass.

### 1.3 Use Batteries in `StatementAxioms.lean`

Several proved theorems use `SetBagLemmas` primitives. After 1.2, these
should simplify. Additionally, check whether any of the 44 axioms become
provable with Batteries' `List.Perm`, `List.take`, `List.drop` lemmas:

- `orderBy_idempotent` — may need `List.Sorted` / `List.mergeSort`
- `orderBy_reverse` — may need `List.reverse_perm` or similar
- LIMIT/OFFSET axioms — `List.take_drop` composition

---

## Phase 2: Refactor evalBinOp to factor out null propagation

**Goal:** Make adding a new `Value` constructor O(1) for proofs instead of
O(n²) or O(n³).

### 2.1 Define a null-propagation wrapper

```lean
/-- Apply a binary operation with standard null propagation:
    if either input is null, return null; otherwise delegate. -/
def nullPropBinOp (f : Value → Value → Option Value)
    : Option Value → Option Value → Option Value
  | some (.null _), _ => some (.null none)
  | _, some (.null _) => some (.null none)
  | some a, some b => f a b
  | _, _ => none
```

Most of `evalBinOp` becomes:
```lean
| .add => nullPropBinOp fun
  | .int a, .int b => some (.int (a + b))
  | _, _ => none
| .sub => nullPropBinOp fun
  | .int a, .int b => some (.int (a - b))
  | _, _ => none
-- etc.
```

AND/OR retain their current short-circuit structure (not null-propagating).

### 2.2 Prove null-propagation meta-lemmas once

```lean
theorem nullPropBinOp_comm (f : Value → Value → Option Value)
    (hf : ∀ a b, f a b = f b a) :
    ∀ l r, nullPropBinOp f l r = nullPropBinOp f r l

theorem nullPropBinOp_assoc (f : Value → Value → Option Value)
    (hf : ∀ a b c, f a (f b c |>.getD ...) = f (f a b |>.getD ...) c) :
    -- (sketch — exact statement depends on how associativity composes
    --  through the Option layer)
```

These are proved **once** against the 6 (or N) null/none cases.
Individual operator commutativity then reduces to proving `Int.add_comm`,
`Bool.and_comm`, etc. — which Batteries provides.

### 2.3 Rewrite ValueLemmas.lean

Replace the 29 exhaustive-match theorems with compositional proofs:

| Current theorem | New proof strategy |
|---|---|
| `evalBinOp_and_comm` | AND/OR keep direct proof (short-circuit, ~6 arms) |
| `evalBinOp_add_comm` | `nullPropBinOp_comm` + `Int.add_comm` |
| `evalBinOp_mul_comm` | `nullPropBinOp_comm` + `Int.mul_comm` |
| `evalBinOp_eq_comm` | `nullPropBinOp_comm` + `Value.eq_comm` |
| `evalBinOp_and_assoc` | Direct proof, ~6 effective arms (bool×bool×bool + short-circuit) |
| `evalBinOp_or_assoc` | Same |
| `evalBinOp_and_or_distrib_left` | Direct proof on bool cases + short-circuit |
| `evalBinOp_or_and_distrib_left` | Same |
| De Morgan's laws | Direct proof on bool + null cases |

**Expected reduction:** ~844 lines → ~150-200 lines.

### 2.4 Verify ExprAxioms.lean still compiles

ExprAxioms calls ValueLemmas by name. As long as the theorem signatures
don't change (same type, same name), ExprAxioms is unaffected. If
`evalBinOp`'s definitional behavior changes (it will — the match structure
changes), some `rfl`-based proofs in ExprAxioms may need `simp` or `unfold`
adjustments.

**Test:** `lake build` passes. All existing tests pass.

---

## Phase 3: Add new Value constructors

With the null-propagation wrapper in place, adding a type follows a recipe:

### For each new constructor (e.g. `float : Float → Value`):

1. **Ast.lean:** Add constructor to `Value`, update `SqlType`, add deriving
   instances. Batteries' `LawfulBEq` / `DecidableEq` infrastructure helps here.

2. **Semantics.lean:** Add arms to the *inner dispatch* functions only:
   ```lean
   -- In the add inner function:
   | .float a, .float b => some (.float (a + b))
   ```
   The null-propagation wrapper handles null cases automatically.

3. **ValueLemmas.lean:** If the new type's operations are commutative/
   associative (they will be — `Float.add_comm` etc.), the existing
   `nullPropBinOp_comm` lemma covers it. No new theorem needed.

4. **Tests:** Add test cases for the new type.

**No changes needed in:** ExprAxioms, Defs, StatementAxioms, SetBagLemmas,
Optimizer, PredicatePushdown, Pretty (unless they pattern-match on Value
constructors for type-specific behavior).

### Planned new types (priority order):

| Type | SQL types covered | Blocked by |
|---|---|---|
| `float : Float → Value` | REAL, DOUBLE, FLOAT | Nothing — Float is in core |
| `datetime : Int → Value` (epoch millis) | DATE, DATETIME, TIMESTAMP | Comparison semantics |
| `decimal : Int × Nat → Value` (value × scale) | DECIMAL, NUMERIC, MONEY | Arithmetic semantics |

---

## Phase 4: Reduce axiom count with Batteries lemmas

With Batteries available, revisit the 95 axioms and check which become
provable:

### Likely provable with Batteries:

- **ORDER BY axioms** (2): `orderBy_idempotent`, `orderBy_reverse` —
  using `List.mergeSort` stability lemmas and `List.Sorted`
- **LIMIT/OFFSET axioms** (if any remain unproved): `List.take` / `List.drop`
  composition lemmas
- **`Decidable.lean` sorry** (1): Needs `LawfulBEq` instances, which
  Batteries provides for standard types

### Unlikely to change (SQL-semantic axioms):

- JOIN semantics (16 axioms) — domain-specific
- Subquery semantics (20 axioms) — domain-specific
- Evaluation axioms (21 axioms) — define the SQL execution model
- Optimization correctness (8 axioms) — require full optimizer verification

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| `alias` rename misses a site | Low | Low | Type-checker catches it |
| Batteries API changed since last checked | Medium | Medium | Pin to specific rev |
| `evalBinOp` refactor breaks ExprAxioms proofs | High | Medium | Phase 2.4 — fix `rfl`→`simp` |
| AND/OR short-circuit semantics accidentally changed | Medium | High | Preserve direct match, don't use nullPropBinOp for AND/OR |
| `nullPropBinOp` associativity lemma hard to state | Medium | Medium | May need `Option`-aware formulation; Batteries' `Option.bind_assoc` helps |
| Build time regression from Batteries import | Low | Low | Batteries is already downloaded; only adds elaboration cost |

---

## Migration Order

```
P1  rename alias → as_name
P2  pin Batteries rev
     │
     ▼
Phase 1  import Batteries, delete SetBagLemmas hand-rolled proofs
     │
     ▼
Phase 2  refactor evalBinOp + nullPropBinOp + rewrite ValueLemmas
     │
     ▼
Phase 3  add float/datetime/decimal constructors
     │
     ▼
Phase 4  prove more axioms with Batteries lemmas
```

Each phase is independently committable and testable. Phase 3 can begin
as soon as Phase 2 is merged; Phase 4 can happen in parallel with Phase 3.

---

## Success Criteria

- [ ] `lake build` passes with Batteries imported
- [ ] All existing tests pass (`lake exe sql_equiv_test`)
- [ ] `alias` no longer used as an identifier anywhere
- [ ] `ValueLemmas.lean` < 250 lines (down from 844)
- [ ] Adding `float` constructor requires < 20 lines of proof changes
- [ ] `SetBagLemmas.lean` removed or reduced to re-exports
- [ ] At least 2 axioms converted to proved theorems via Batteries
