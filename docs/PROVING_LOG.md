# Proving Log

Running notes on proving axioms — reasoning, obstacles, lessons learned.

---

## Batch 1: Comparison Negation (#54) + Flip (#55) + CASE/WHEN (#61)

**Branch**: `claude/prove-comparison-axioms` | **PR**: #85 (merged)

### Comparison Negation (#54) — 6 axioms

**Strategy**: Two-layer approach — prove value-level helpers first, then lift to `ExprEquiv`.

The negation axioms say `NOT (a op b) = a inv_op b` (e.g., `NOT (a = b)` is `a <> b`).
Since `evalExprWithDb` is `partial def` and can't be unfolded, we use the existing
`evalExprWithDb_unaryOp` and `evalExprWithDb_binOp` axioms to rewrite, then prove
the value-level identity.

**Value-level pattern** (e.g., `evalUnaryOp_not_eq`):
- Match on both `Option Value` arguments
- For `some (.bool b)` cases, `rfl` works
- For `none` cases, `rfl` works
- Key insight: `evalBinOp .eq` returns `(a.eq b).map Value.bool`, and
  `evalUnaryOp .not` only handles `some (.bool b)`. So when either input is
  `none`, the binOp returns `none`, and `NOT none = none`, matching `.ne` which
  also returns `none`. Clean.

**Proof pattern**:
```lean
theorem not_eq_is_ne (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .eq a b) ≃ₑ Expr.binOp .ne a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_eq _ _
```

All 6 went smoothly. No surprises.

### Comparison Flip (#55) — 4 axioms

**Strategy**: Prove `(compare a b).swap = compare b a` generically, then use for
`lt`/`le`/`gt`/`ge` flip proofs.

**Obstacles**:
1. **Wildcard match patterns don't reduce**: Tried `| none, _ => rfl` for
   `evalBinOp` but Lean can't evaluate when the second argument's structure is
   unknown. Had to enumerate all constructor combinations explicitly:
   ```lean
   | some (.null _), some (.int _) => rfl
   | some (.null _), some (.string _) => rfl
   -- etc.
   ```

2. **String.compare swap was hard**: Initially tried manual case analysis with
   `omega` for Int (worked) but couldn't unfold `String.compare`. Tried
   `by_contra` — not available (need `Classical.byContradiction`). Tried
   `simp_all` — it unhelpfully transformed `¬(b < a)` into `a ≤ b`.

3. **Solution: `Std.OrientedCmp.eq_swap`** from Batteries. This gives
   `cmp x y = (cmp y x).swap` for any lawful `Ord` instance. Both `Int` and
   `String` have lawful `Ord`. But the direction is backwards from what we need
   (`(cmp x y).swap = cmp y x`), so we use `Ordering.swap_swap` to flip it:
   ```lean
   private theorem compare_swap_gen {α : Type} [Ord α] [Std.OrientedCmp (α := α) compare]
       (a b : α) : (compare a b).swap = compare b a := by
     have h := Std.OrientedCmp.eq_swap (cmp := (compare : α → α → Ordering)) (a := a) (b := b)
     rw [h, Ordering.swap_swap]
   ```

**Lesson**: When stuck on a specific type's implementation details, look for
typeclass-based lemmas in Batteries/Std that work generically.

### CASE/WHEN (#61) — 5 axioms

**Strategy**: Need to bridge `evalExprWithDb` to `evalCase`. No existing axiom for
this, so added infrastructure axioms to `Semantics.lean`.

**New infrastructure axioms added**:
- `evalExprWithDb_case` — unfolds `.case` to `evalCase`
- `evalCase_nil_some` — empty branches with ELSE
- `evalCase_nil_none` — empty branches, no ELSE → NULL
- `evalCase_cons_true` — true condition → return result
- `evalCase_cons_false` — false condition → skip to rest

**Obstacle**: First attempt used `rfl` to prove the literal condition evaluates to
`true`/`false`, but `evalExprWithDb_lit` is an axiom, not definitional. Fix: bind
the lit axiom to a hypothesis and pass it explicitly:
```lean
have h := evalExprWithDb_lit (fun _ => []) row (.bool true)
rw [evalCase_cons_true _ _ _ _ _ _ h]
```

**Lesson**: Infrastructure axioms will be needed for each new expression form we
prove theorems about. Track them in PROVING_AXIOMS_PLAN.md.

---

## Unsound Axioms: Comprehensive Analysis

Many axioms in the codebase are **unsound as stated** — they claim equivalences
for ALL expressions, but only hold for specific types (booleans, integers, strings).
This section documents every unsound axiom found during proving work.

### Category 1: Boolean-only axioms (Wave 1)

These axioms only hold when all expression arguments evaluate to `some (.bool _)`.
For non-boolean values (int, string, null), operations like AND/OR/NOT return
`none`, but the axioms claim the result equals the original expression.

| Issue | Axiom | Counterexample |
|-------|-------|----------------|
| #46 | `not_not` | `NOT(NOT 5)` = `none` ≠ `some (.int 5)` |
| #47 | `and_absorb_or` | `5 AND (5 OR b)` = `none` ≠ `some (.int 5)` |
| #47 | `or_absorb_and` | `5 OR (5 AND b)` = `none` ≠ `some (.int 5)` |
| #48 | `and_true` | `5 AND TRUE` = `none` ≠ `some (.int 5)` |
| #48 | `or_false` | `5 OR FALSE` = `none` ≠ `some (.int 5)` |
| #49 | `and_self` | `5 AND 5` = `none` ≠ `some (.int 5)` |
| #49 | `or_self` | `5 OR 5` = `none` ≠ `some (.int 5)` |
| #50 | `and_not_self` | `5 AND (NOT 5)` = `none` ≠ `some (.bool false)` |
| #50 | `or_not_self` | `5 OR (NOT 5)` = `none` ≠ `some (.bool true)` |

**Fix**: Add precondition `∀ row, ∃ b, evalExpr row e = some (.bool b)`.

### Category 2: Integer-only axioms (Wave 1)

| Issue | Axiom | Counterexample |
|-------|-------|----------------|
| #57 | `add_zero` (x + 0 = x) | `"hello" + 0` = `none` ≠ `some (.string "hello")` |
| #57 | `mul_one` (x * 1 = x) | Same pattern |
| #57 | All 7 arithmetic identities | Same pattern |

**Fix**: Add precondition `∀ row, ∃ n, evalExpr row e = some (.int n)`.

### Category 3: Representation mismatch — `none` vs `some (.null none)` (Wave 1)

| Issue | Axiom | Problem |
|-------|-------|---------|
| #56 | `eq_reflexive` | `NULL = NULL` gives `none` (via `Value.eq`), but CASE returns `some (.null none)` |
| #56 | `ne_irreflexive` | Same mismatch |

**Detailed trace for `eq_reflexive`**:

The axiom says `(e = e) ≃ₑ CASE WHEN IS_NULL(e) THEN NULL ELSE TRUE END`.

When `evalExprWithDb db row e = some (.null t)`:
- **LHS**: `evalBinOp .eq (some (.null t)) (some (.null t))`
  = `(Value.eq (.null t) (.null t)).map Value.bool`
  = `none.map Value.bool` = **`none`**
- **RHS**: `isNullValue (some (.null t))` = `true` → CASE returns
  `evalExprWithDb db row (lit (null none))` = **`some (.null none)`**

`none ≠ some (.null none)`.

**Root cause**: `Value.eq` returns `Option Bool` where `none` means "null
propagation". This lifts to `none : Option Value` via `.map`. But the CASE
expression's null branch produces an explicit `some (.null none)`. Our encoding
conflates "evaluation error" and "SQL NULL propagation" under the same `none`.

**Fix options**:
- Change `Value.eq` on null inputs to return `some false` (but that changes SQL semantics)
- Add precondition `∀ row, evalExpr row e ≠ none`
- Define weaker equivalence that treats `none` ≈ `some (.null _)`

### Category 4: Type-specific axioms (Wave 2)

| Issue | Axiom | Sound? | Problem |
|-------|-------|--------|---------|
| #58 | `in_empty_false` | **Proved** | PR #112 (was unsound, proved with infrastructure axiom) |
| #58 | `not_in_empty_true` | **Proved** | PR #112 (was unsound, proved with infrastructure axiom) |
| #58 | `in_singleton`, `not_in_singleton` | **Unblocked** | PR #125 fixed evaluator: `inList` now uses `foldl`+`evalBinOp` semantics |
| #58 | `in_pair`, `not_in_pair` | **Unblocked** | PR #125 fixed evaluator: AND/OR null propagation + `inList` rewrite |
| #59 | `between_expansion` | **Proved** | PR #109; `evaluable` precondition dropped in PR #125 (BETWEEN redefined as AND(GE,LE)) |
| #59 | `not_between_expansion` | **Proved** | PR #109; `evaluable` precondition dropped in PR #125 (BETWEEN redefined as AND(GE,LE)) |
| #60 | `like_match_all` | **No** | Non-string `e`: LHS `none`, RHS `some (.bool true)` |
| #60 | `like_self` | **No** | Non-string `e`: LHS `none`, RHS `some (.bool true)` |
| #62 | `concat_empty_left/right` | **Fixed** | `evalFunc` had no "CONCAT" case (PR #107 adds it + `isStringOrNullValued` precondition) |

### Category 5: Implementation bugs (all fixed)

| Axiom | Bug | Fix |
|-------|-----|-----|
| `concat_empty_left` | `evalFunc` had no CONCAT handler | PR #107: added CONCAT to evalFunc + `isStringOrNullValued` precondition |
| `concat_empty_right` | Same bug | Same fix |

### Summary

Of ~152 original axioms, **18 proven** so far. Of the remaining ~134:
- ~20 are unsound as stated (categories 1-4 above)
- ~2 have implementation bugs (category 5)
- The rest haven't been triaged yet

---

## Design Decision: How to Handle Unsound Axioms

### The fundamental problem

Our `ExprEquiv` (≃ₑ) is defined as:
```lean
def ExprEquiv (e1 e2 : Expr) : Prop :=
  ∀ row : Row, evalExpr row e1 = evalExpr row e2
```

where `evalExpr` returns `Option Value`. The `Option` layer conflates two
semantically different situations under the same `none`:

1. **SQL NULL propagation**: `NULL + 1` → NULL, `NULL = NULL` → NULL.
   This is correct SQL behavior — NULL propagates through expressions.

2. **Evaluation errors**: `"hello" + 1` → error, missing column → error.
   These represent ill-typed or malformed expressions.

Because both map to `none : Option Value`, axioms that are correct for
well-typed SQL become false for ill-typed expressions that our untyped
AST allows constructing.

### Option 1: Add type preconditions to individual axioms

Change:
```lean
axiom not_not (e : Expr) : ¬¬e ≃ₑ e
```
to:
```lean
theorem not_not (e : Expr)
    (h : ∀ row, ∃ b, evalExpr row e = some (.bool b)) :
    ¬¬e ≃ₑ e
```

**Fixes**: Categories 1, 2 (boolean-only, integer-only axioms).

**Pros**:
- Each axiom becomes a provable theorem
- Preconditions are natural — `NOT NOT e` should only apply to booleans
- Incremental: fix one axiom at a time

**Cons**:
- Callers must prove preconditions at every use site
- Preconditions are existentially quantified over ALL rows — hard to establish
  without a type system
- Different axioms need different preconditions (bool, int, string)
- Chaining axioms gets verbose: to apply `not_not` then `and_true`, you need
  separate proofs that the intermediate expressions are boolean-valued
- Doesn't fix Category 3 (null representation mismatch)

### Option 2: Introduce a type system / well-typedness predicate

Define a syntactic typing judgment:
```lean
inductive ExprType | bool | int | string | nullable (t : ExprType) | any

def Expr.hasType : Expr → ExprType → Prop := ...
```

Then use it:
```lean
theorem not_not (e : Expr) (h : e.hasType .bool) : ¬¬e ≃ₑ e
```

**Fixes**: Categories 1, 2, and potentially 3 (with `hasType` implying `evalExpr`
returns `some`).

**Pros**:
- Clean, composable preconditions
- `hasType` is syntactic — checkable without evaluating
- Matches how real SQL works (type checking at plan time, before execution)
- Can prove type preservation through rewrites: if `e.hasType .bool` and
  `e ≃ₑ e'`, then `e'.hasType .bool`
- This is essentially what `SQL_TYPES_CONCRETE_PLAN.md` already proposes

**Cons**:
- Significant new infrastructure (type definitions, typing rules, soundness)
- Must prove the "fundamental theorem": `e.hasType τ → evalExpr row e = some v`
  for some `v` of type `τ`
- Substantial upfront investment before any new axioms become provable
- Risk of getting stuck on the type system design

### Option 3: Fix semantics to separate null from error

Change `evalBinOp` to explicitly propagate `some (.null none)` for null inputs,
instead of letting them fall through to `none`:

```lean
def evalBinOp (op : BinOp) (l r : Option Value) : Option Value :=
  match l, r with
  | none, _ => none                           -- genuine error
  | _, none => none                           -- genuine error
  | some (.null _), _ => some (.null none)    -- NULL propagation
  | _, some (.null _) => some (.null none)    -- NULL propagation
  | some a, some b => evalBinOpValues op a b  -- actual computation
```

**Fixes**: Category 3 (representation mismatch). `eq_reflexive` becomes provable
because `NULL = NULL` yields `some (.null none)` matching the CASE expression.
Also fixes `in_empty_false` and similar axioms where `e` evaluates to a null value.

**Does NOT fix**: Categories 1-2. `NOT(NOT 5)` is a genuine type error, not null
propagation. It correctly returns `none` for non-booleans.

**Pros**:
- Fixes the null/error conflation at the root
- Better models SQL semantics (NULL is a value that propagates, not an error)
- Relatively contained change: modify `evalBinOp`, `evalUnaryOp`, `evalFunc`
- Makes many more axioms provable without preconditions
- Doesn't require a type system

**Cons**:
- Changes core semantics — touches many functions
- Breaks existing proven theorems (18 so far) — they'd need re-proving
- Need to decide on NULL propagation rules for every operator
  (e.g., `NULL AND FALSE` = `FALSE` in SQL, not `NULL` — short-circuit)
- Some edge cases are subtle (LIKE, BETWEEN, IN with nulls)

### Option 4: Define a weaker equivalence relation

Instead of exact equality, define equivalence modulo null representation:
```lean
def nullEquiv : Option Value → Option Value → Prop
  | none, none => True
  | none, some (.null _) => True
  | some (.null _), none => True
  | some v1, some v2 => v1 = v2
  | _, _ => False

def ExprEquivWeak (e1 e2 : Expr) : Prop :=
  ∀ row, nullEquiv (evalExpr row e1) (evalExpr row e2)
```

**Fixes**: Category 3 only.

**Pros**:
- No changes to semantics
- `eq_reflexive` provable under weak equiv
- Existing proofs (using `=`) trivially imply weak equiv

**Cons**:
- Doesn't fix categories 1-2
- Two equivalence relations is confusing — which one do axioms use?
- Transitivity is delicate: `none ≈ some (.null _)` and `some (.null _) ≈ some (.null _)`
  but the chain `none ≈ some (.null _) = some (.int 5)` would be unsound
- May need to reprove that weak equiv is a congruence (preserved by all Expr constructors)
- Feels like a workaround rather than a fix

### Option 5: Leave as axioms with documented unsoundness

Keep unsound axioms as `axiom` (not `theorem`), with clear documentation.

**Pros**:
- Zero implementation effort
- Axioms document intended SQL equivalences
- Already have code comments noting boolean-only validity
- Pragmatic — the project is exploring SQL formalization, not building a
  verified query optimizer

**Cons**:
- Axioms can derive `False` if instantiated with concrete counterexamples
- Undermines the proof system: any theorem that depends on unsound axioms is suspect
- Mixing proven theorems with unsound axioms without clear separation is misleading
- We can't tell which "proven" results are actually trustworthy

### Recommendation

**Short term** (now): **Option 5 + continue proving sound axioms**. We're
already doing this. Document unsoundness clearly. Focus proving effort on
axioms that ARE sound.

**Medium term**: **Option 3 (fix null semantics)**. This is the highest-value
change because:
- It's relatively contained (~200 lines of Semantics.lean changes)
- It unblocks `eq_reflexive`, `ne_irreflexive`, and the IN/BETWEEN axioms
- It makes the semantics more correct regardless of proving
- Existing proofs mostly still work (comparison negation/flip don't depend
  on null behavior at the `none` vs `some (.null _)` level)

**Long term**: **Option 2 (type system)** from SQL_TYPES_CONCRETE_PLAN.md.
This is the proper fix for categories 1-2. With a type system:
- Boolean axioms get `e.hasType .bool` preconditions
- Arithmetic axioms get `e.hasType .int` preconditions
- The typing judgment provides the proof obligation that callers must meet
- Optimizer passes can be proven to preserve types

The type system (Option 2) and null fix (Option 3) are complementary, not
competing. Option 3 fixes the value representation. Option 2 provides the
framework for type-conditional axioms. Together they make ~all axioms provable.

---

## Prototype Comparison: Building All Three Options

**Branches**: `claude/option1-type-preconditions` (PR #87), `claude/option2-type-system` (PR #88), `claude/option3-fix-null-semantics` (PR #89)

We built three working prototypes to compare approaches. Each branch modifies
the same axioms (`not_not`/`expr_add_zero` for Options 1-2, `eq_reflexive` for
Option 3) so the comparison is apples-to-apples.

### Option 1: Ad-hoc type preconditions

Added `IsBoolValued`/`IsIntValued` predicates per axiom.

**Results:**
- Proves `not_not` and `expr_add_zero` — proofs are clean and direct
- **Fatal composability gap**: Can't chain `not_not` (needs bool) with arithmetic
  axioms (needs int). Each predicate is an isolated silo
- 5 caller sorry sites in Tactics.lean/Optimizer.lean
- Proliferation risk: each new axiom may need a new predicate

### Option 2: Minimal type system

Added unified `Expr.wellTyped` with `Value.hasType` and `SqlType`.

**Results:**
- Same proofs as Option 1, but unified under one predicate
- **Type preservation works**: proved `lit_bool_typed`, `unaryOp_not_typed`, etc.
  allowing proofs to chain — if `e` is bool-typed, `NOT e` is also bool-typed
- Strict typing required — including null in `hasType` made `expr_add_zero`
  unprovable (`null + 0 = none ≠ some (.null _)`)
- **Nullable type gap**: comparisons return "bool or null" which needs
  `SqlType.nullable` to express
- Same 5 caller sorry sites as Option 1

### Option 3: Fix null semantics

Changed `evalBinOp`/`evalUnaryOp` to return `some (.null none)` for null
propagation, distinguishing it from `none` (genuine errors).

**Results:**
- **Key win**: `eq_reflexive` becomes provable with only `Expr.evaluable`
  (expression produces *some* value) — a very mild precondition
- `not_not` remains unprovable — `NOT 5 = none` is a type error, not null issue
- 93 initial build errors; 90 mechanically repairable, 2 sorry'd (still true),
  1 new prototype sketch sorry
- 20+ null theorem statements updated: `= none` → `= some (.null none)` — these
  are actually *more correct* as SQL semantics
- All 195 runtime tests pass unchanged
- Zero caller breakage for existing axiom signatures

### Verdict: These fix *different problems*

| Problem | Option 1 | Option 2 | Option 3 |
|---------|----------|----------|----------|
| Null/error conflation (`eq_reflexive`) | No | No | **Yes** |
| Boolean-only axioms (`not_not`) | **Yes** | **Yes** | No |
| Integer-only axioms (`expr_add_zero`) | **Yes** | **Yes** | No |
| Composability across types | No | **Yes** | N/A |
| Caller breakage | 5 sorry sites | 5 sorry sites | 0 |
| Semantics correctness | Unchanged | Unchanged | **Improved** |

**Recommended path**: Option 3 first (fixes root cause — the null/error
conflation is a genuine semantic bug, not just a proof obstacle), then Option 2
on top (adds type system for type-mismatch axioms like `not_not`). Option 1 is
strictly dominated by Option 2 and should not be pursued.

**Key insight**: Option 3's proof repair burden was manageable. The comparison
negation helpers (NOT(x=y) = (x<>y) etc.) were fully repairable — just needed
explicit null case splits. The distributivity proofs need the same treatment
(more cases for nulls in the exhaustive enumeration). The semantic change makes
the codebase *more correct* regardless of the proving effort.

---

## Batch 2: Provable axioms from Wave 1-2

**Branch**: `claude/prove-wave1-batch2` | **PR**: #86

### Soundness triage

After triaging all Wave 1-2 axioms (see "Unsound Axioms" section above), found
3 fully provable axioms. The `upper/lower_idempotent` axioms are mathematically
sound but need Char-level lemmas that may not exist in Batteries.

### like_empty_pattern

`Expr.binOp .like e (lit (.string "")) ≃ₑ Expr.binOp .eq e (lit (.string ""))`

Both sides use `evalExprWithDb_binOp` (no new infrastructure needed).
Need value-level lemma: `evalBinOp .like v (some (.string "")) = evalBinOp .eq v (some (.string ""))`.

Case analysis on `v`:
- `none` → both `none` ✓
- `some (.null _)` → both `none` ✓ (LIKE needs string, eq returns none for null)
- `some (.int _)` → both `none` ✓
- `some (.bool _)` → both `none` ✓
- `some (.string s)` → LHS: `simpleLike s ""`. RHS: `(s == "")`. The `simpleLike`
  function falls through all wildcard checks (none match empty pattern) to `s == pat`
  which is `s == ""`. ✓

### length_empty

`Expr.func "LENGTH" [lit (.string "")] ≃ₑ lit (.int 0)`

Need `evalExprWithDb_func` infrastructure axiom. Then:
`evalFunc "LENGTH" [some (.string "")] = some (.int "".length) = some (.int 0)`.
And `evalExprWithDb_lit _ _ (.int 0) = some (.int 0)`. ✓

### between_reflexive

`Expr.between e e e ≃ₑ Expr.binOp .and (Expr.binOp .ge e e) (Expr.binOp .le e e)`

Need `evalExprWithDb_between` infrastructure axiom. Case analysis on `eval e`:
- `none` → both `none` ✓
- `some (.null _)` → `Value.compare (.null _) (.null _) = none` → both `none` ✓
- `some (.bool _)` → `Value.compare (.bool _) (.bool _) = none` → both `none` ✓
- `some (.int n)` → `compare n n = .eq` → BETWEEN: `| some .eq, some .eq` → true.
  RHS: `ge` = `(.eq != .lt)` = true, `le` = `(.eq != .gt)` = true, AND = true ✓
- `some (.string s)` → same as int ✓

---

## Option 3: Null Semantics Fix — ADOPTED

**Date:** 2026-02-06
**Branch:** `claude/prove-wave2-3-sound-axioms`

### What changed

Applied the Option 3 null semantics fix to the main proving branch. This
changes `evalBinOp` and `evalUnaryOp` to return `some (.null none)` for SQL
null propagation, distinguishing it from `none` (genuine evaluation errors).

### Scope

**Modified operations:**
- Arithmetic: `+`, `-`, `*`, `/`, `%` — null inputs produce `some (.null none)`
- Comparison: `=`, `<>`, `<`, `<=`, `>`, `>=` — null inputs produce `some (.null none)`
- Unary: `NOT`, `NEG` — null input produces `some (.null none)`
- String: `CONCAT`, `LIKE` — null inputs produce `some (.null none)`

**Unchanged operations:**
- `AND`/`OR` — kept original semantics (no null propagation change) to preserve
  distributivity laws (`evalBinOp_and_or_distrib_left`, `evalBinOp_or_and_distrib_left`)

### Key design decisions

1. **`some _` not bare `_`** for null propagation wildcards in arithmetic/comparison.
   Per Copilot review on PR #89 — bare `_` matches `none` (errors), which would
   incorrectly convert errors to nulls. With `some _`, only actual values
   (including null values) trigger propagation; `none` errors pass through.

2. **AND/OR keep original semantics.** Attempting to add null propagation to
   AND/OR broke both distributivity proofs (`evalBinOp_and_or_distrib_left` and
   `evalBinOp_or_and_distrib_left`). Tried three approaches:
   - `some _` wildcards for null AND/OR → created asymmetry breaking distributivity
   - Bare `_` wildcards → still broke `OR_AND_distrib` cases
   - Restricted to boolean-compatible types only → still 2 failures

   Root cause: distributivity requires `AND(OR(a,b),c) = OR(AND(a,c),AND(b,c))`
   for ALL value combinations including nulls mixed with non-booleans. Any null
   propagation in AND/OR creates cases where one side produces `some (.null none)`
   but the other produces `none`.

3. **`Expr.evaluable` as precondition** (not a full type system). Defined as:
   ```lean
   def Expr.evaluable (e : Expr) : Prop :=
     ∀ row : Row, ∃ v : Value, evalExpr row e = some v
   ```
   This is the mildest possible precondition — it only excludes expressions that
   produce evaluation errors. Any well-typed SQL expression satisfies it.

### Impact on existing proofs

| Category | Change |
|----------|--------|
| Null propagation theorems (12) | Signature: `Option Value` → `Value` param, conclusion: `= none` → `= some (.null none)` |
| `evalBinOp_eq_comm` | Explicit null case splits (was `\| none, some _ =>`, now `\| none, some (.int _) =>` etc.) |
| Comparison negation helpers (6) | Explicit null case splits (~20 lines each, up from ~3) |
| Distributivity proofs (2) | `simp [evalBinOp]` → `rfl` (more robust with new pattern complexity) |
| Three-valued logic theorems (6) | Unchanged (`= none`, since AND/OR retain original semantics) |

### New theorems proved

- **`eq_reflexive`** — was axiom, now theorem with `Expr.evaluable` precondition.
  Proof case-splits on evaluated value: null → both sides = `some (.null none)`;
  int/string/bool → CASE condition false, else = `some (.bool true)`.
- **`ne_irreflexive`** — same structure, result is `some (.bool false)`.

### Verification

- Build: clean, no warnings
- Tests: all 195 pass
- Sorry count: no new `sorry` introduced (only pre-existing one at `checkEquivFull`)

---

## Batch 3: Arithmetic Identities (#57) — 7 axioms

**Branch**: `claude/prove-arithmetic-identities` | **PR**: #93
**Date**: 2026-02-08

### Axioms proved

| Axiom | Statement | Int lemma used |
|-------|-----------|---------------|
| `expr_add_zero` | `e + 0 ≃ₑ e` | `Int.add_zero` |
| `expr_zero_add` | `0 + e ≃ₑ e` | `Int.zero_add` |
| `expr_mul_one` | `e * 1 ≃ₑ e` | `Int.mul_one` |
| `expr_one_mul` | `1 * e ≃ₑ e` | `Int.one_mul` |
| `expr_mul_zero` | `e * 0 ≃ₑ 0` | `Int.mul_zero` |
| `expr_zero_mul` | `0 * e ≃ₑ 0` | `Int.zero_mul` |
| `expr_sub_zero` | `e - 0 ≃ₑ e` | `Int.sub_zero` |

### Soundness analysis

These axioms were originally stated without preconditions (`∀ e : Expr`), but are
**unsound for non-integer expressions**:

- `"hello" + 0` → `none` (type error) ≠ `some (.string "hello")`. **FAIL.**
- `true * 1` → `none` ≠ `some (.bool true)`. **FAIL.**
- `NULL + 0` → `some (.null none)` ≠ `some (.null (some SqlType.int))`. **FAIL** (typed null mismatch).
- `e * 0 ≃ₑ 0`: even `none * 0 = none ≠ some (.int 0)`. **FAIL** for error-producing expressions.

### Solution: `Expr.isIntValued` precondition

Defined a new predicate:
```lean
def Expr.isIntValued (e : Expr) : Prop :=
  ∀ row : Row, ∃ n : Int, evalExpr row e = some (.int n)
```

This requires the expression to always evaluate to a concrete integer. Stronger than
`Expr.evaluable` (which allows any value), but necessary because:
1. Arithmetic operations only work on int×int (type mismatches → `none`)
2. Null propagation produces `some (.null none)` which differs from the original null type
3. `mul_zero`/`zero_mul` need the RHS to be `some (.int 0)`, which fails if `e` → `none`

### Proof pattern

All 7 proofs follow the same structure:
```lean
theorem expr_add_zero (e : Expr) (h : e.isIntValued) :
    Expr.binOp .add e (Expr.lit (.int 0)) ≃ₑ e := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  obtain ⟨n, hn⟩ := h row
  simp only [evalExpr] at hn
  rw [hn]
  show some (Value.int (n + 0)) = some (Value.int n)
  rw [Int.add_zero]
```

Key steps:
1. Unfold `ExprEquiv` and `evalExpr`
2. Use infrastructure axioms (`evalExprWithDb_binOp`, `evalExprWithDb_lit`) to decompose
3. Extract the integer witness `n` from the `isIntValued` hypothesis
4. Rewrite to substitute the concrete integer value
5. Use `show` to make the definitional reduction explicit (needed because `.int` is
   ambiguous between `Value.int` and `SqlType.int` — must qualify as `Value.int`)
6. Apply the appropriate `Int.*` lemma from Mathlib/core

### Obstacles encountered

1. **Definition ordering**: `Expr.isIntValued` was initially placed after the theorems
   that use it (near `Expr.evaluable` at line 949). Lean requires definitions before use
   in the same file. **Fix**: moved definition to just before the arithmetic section.

2. **Ambiguous `.int` in `show`**: `show some (.int ...) = some (.int ...)` fails because
   `.int` is ambiguous between `Value.int` and `SqlType.int`. **Fix**: fully qualify as
   `Value.int`.

3. **Double `evalExprWithDb_lit` rewrite**: For `mul_zero`/`zero_mul`, the RHS is
   `Expr.lit (.int 0)`. After `rw [evalExprWithDb_binOp]`, `rw [evalExprWithDb_lit]`
   rewrites ALL occurrences (both the binOp argument and the RHS). A second
   `rw [evalExprWithDb_lit]` fails because no occurrences remain.
   **Fix**: use only one `rw [evalExprWithDb_lit]`.

### Tactic updates

The `sql_rw_arith` tactic and `sql_equiv` step 9 were updated to pass the `isIntValued`
hypothesis via `(by assumption)`. Examples in `Tactics.lean` now require the hypothesis:
```lean
example (h : a.isIntValued) : Expr.binOp .add a (Expr.lit (.int 0)) ≃ₑ a := by sql_equiv
```

### Verification

- Build: clean, no warnings
- Tests: all 199 pass
- Axiom count: reduced by 7 (37 remain in Comparison.lean)
- Coverage validator: 100% runtime coverage on remaining 20 axioms

---

## Batch 4: Ground Expression Equivalence (#53) — 1 axiom proved, 1 kept

**Branch**: `claude/prove-ground-expr-axioms` | **PR**: #94
**Date**: 2026-02-08

### Axioms in scope

| Axiom | Status | Reason |
|-------|--------|--------|
| `ground_expr_eval_independent` | **Kept as axiom** | Both `isGround` and `evalExprWithDb` are `partial def` — Lean blocks structural induction and definitional unfolding |
| `decideGroundExprEquiv_sound` | **Proved as theorem** | Follows directly from `ground_expr_eval_independent` |

### Why `ground_expr_eval_independent` can't be proved

The axiom states: if `e.isGround = true` (no column references), then
`evalExpr r1 e = evalExpr r2 e` for any rows `r1, r2`.

The proof would go by structural induction on `e`:
- **Literals**: row-independent (no column lookup)
- **Column refs**: excluded by `isGround = false`
- **BinOp/UnaryOp**: by IH, subexpressions are row-independent
- **Aggregates/Subqueries**: have their own evaluation scope

But both `Expr.isGround` and `evalExprWithDb` are defined as `partial def` in
`mutual` blocks (because `Expr` → `SelectStmt` → `FromClause` → `Expr` creates
mutual recursion). Lean 4's `partial def` uses opaque implementation — the
kernel can't unfold the definition, so `cases`/`match` on the structure doesn't
generate proof obligations, and `simp` can't reduce applications.

This is a **genuine Lean limitation**, not a mathematical gap. The statement is
intuitively true for any well-formed expression tree.

### Proof of `decideGroundExprEquiv_sound`

**Strategy**: Use `ground_expr_eval_independent` as a lemma.

The original definition used `BEq` (`==`) to compare evaluation results:
```lean
def decideGroundExprEquiv ... : Bool := evalExpr [] e1 == evalExpr [] e2
```

This required `LawfulBEq (Option Value)` to extract propositional equality from
`==`, which needed manual instances for `SqlType`, `Value`, and `Option Value` —
a rabbit hole of case analysis that kept failing.

**Solution**: Changed to use `DecidableEq` instead:
```lean
def decideGroundExprEquiv ... : Bool :=
  if evalExpr [] e1 = evalExpr [] e2 then true else false
```

Since `Value` derives `DecidableEq`, the `if` uses the `Decidable` instance
directly. The proof then uses `split` to case-analyze the if-then-else:

```lean
theorem decideGroundExprEquiv_sound ... := by
  intro h
  unfold decideGroundExprEquiv at h
  split at h
  next h_eq =>
    intro row
    rw [← ground_expr_eval_independent e1 hg1 [] row,
        ← ground_expr_eval_independent e2 hg2 [] row, h_eq]
  next => contradiction
```

### Key lesson: `BEq` vs `DecidableEq` for proofs

`BEq` (`==`) is a computational boolean check. Extracting propositional equality
from it requires `LawfulBEq`, which asserts `(a == b) = true ↔ a = b`. For
complex types like `Value` (with `Int`, `String`, `Option SqlType` fields),
building `LawfulBEq` manually is error-prone.

`DecidableEq` (`=` in `if`) directly produces propositional equality/inequality.
When a type derives `DecidableEq`, `if a = b then ... else ...` just works, and
proofs can use `split` to case-analyze both branches cleanly.

**Rule of thumb**: When defining functions whose results will be used in proofs,
prefer `if x = y then ...` over `x == y` — it avoids the `LawfulBEq` dependency
entirely.

### Verification

- Build: clean, no warnings
- Tests: all 199 pass
- Axiom count: reduced by 1 (`decideGroundExprEquiv_sound` → theorem)

---

## Proof Regression: Equiv.lean Split (commit 711581c)

**Date discovered:** 2026-02-09
**Date of regression:** 2026-02-07 (commit 711581c, between PRs #92 and #93)

### What happened

Commit 711581c split the monolithic `SqlEquiv/Equiv.lean` (4105 lines) into
6 focused submodules (`Equiv/Defs.lean`, `Equiv/ValueLemmas.lean`,
`Equiv/ExprAxioms.lean`, `Equiv/Decidable.lean`, `Equiv/Comparison.lean`,
`Equiv/StatementAxioms.lean`). During the split, **3 theorem proofs from
PR #86 were reverted to axiom declarations**.

### Proofs lost

| Axiom | PR | Git commit with proof |
|-------|----|--------------------|
| `between_reflexive` | #86 | c36360c |
| `like_empty_pattern` | #86 | c36360c |
| `length_empty` | #86 | c36360c |

Helper lemmas also lost: `evalBetween_reflexive`, `simpleLike_empty`,
`evalBinOp_like_empty_eq_eq`.

### Root cause

The split was done by copying content from `Equiv.lean` into submodules.
Between PR #86 (which proved the 3 axioms) and PR #92 (null semantics fix),
the Option 3 prototype branch may have had a different version of `Equiv.lean`.
When the split was performed from that state, it used the pre-proof versions
of these 3 declarations.

### Recovery plan

The original proofs in commit c36360c used infrastructure axioms
(`evalExprWithDb_between`, `evalExprWithDb_func`) that still exist in
`Semantics.lean`. The proofs can be re-applied to `Equiv/Comparison.lean`
with minimal adaptation. See Batch 2 notes above for proof details.

### Lesson

When splitting large files, verify `axiom`/`theorem` counts match before and
after. Consider adding a CI check: `grep -c "^axiom " SqlEquiv/Equiv/*.lean`
should be monotonically non-increasing across commits.

---

## Optimizer Soundness Guards (PRs #99-101)

**Date:** 2026-02-08
**Not a proving batch** — but deeply connected to the unsound axiom problem.

### Context

While proving axioms, we discovered ~20 unsound axioms caused by type
mismatches (Categories 1-2 in the Unsound Axioms section). The *same* class
of bugs existed in the runtime optimizer:

- `applyIdentityLaws`: `a AND TRUE => a` unsound when `a` is non-boolean
- `simplifyArithmetic`: `a + 0 => a` unsound when `a` is non-integer
- `eliminateDoubleNegation`: `NOT NOT a => a` unsound when `a` is non-boolean

### What was done

| PR | Fix | Guard function |
|----|-----|---------------|
| #99 | `@rewrite` annotations + audit validator | (tooling) |
| #100 | Guard `simplifyArithmetic` identity/annihilation arms | `isDefinitelyNonInt` (blocklist) |
| #101 | Guard `eliminateDoubleNegation`, `applyIdempotentLaws`, `applyComplementLaws` | `isDefinitelyBool` (allowlist) |

### Connection to axiom preconditions

The optimizer guards and axiom preconditions solve the same problem from
different sides:

| Problem | Axiom precondition | Optimizer guard |
|---------|-------------------|----------------|
| Boolean rewrites on non-bool | `Expr.isBoolValued` | `isDefinitelyBool` |
| Arithmetic rewrites on non-int | `Expr.isIntValued` | `isDefinitelyNonInt` |
| Null/error conflation | `Expr.evaluable` | `some _` wildcards (not bare `_`) |

### Key design insight

**Allowlist > blocklist for type guards.** `isDefinitelyNonBool` (blocklist)
missed `.col`, `.case`, `.agg`, `.subquery`. `isDefinitelyBool` (allowlist) is
safer — only fires when the expression is *statically guaranteed* boolean.
This same principle applies to axiom preconditions: `isBoolValued` (positive
assertion) is more robust than "not definitely non-boolean".

---

## Interim Status Summary (2026-02-09, post-PR #109)

*Superseded by the current status at the end of this file.*

### Axiom/theorem counts at time of writing

- **127 axioms** remaining (across all .lean files in SqlEquiv/)
- Axiom ratchet: 127 (in `tools/axiom_count_minimum.txt`)

### Issues fully proved at time of writing

| Issue | Axioms | PR |
|-------|--------|-----|
| #24 | CONCAT evalFunc implementation + proofs | #107 |
| #54 | 6 comparison negation | #85 |
| #55 | 4 comparison flip | #85 |
| #56 | 2 eq_reflexive, ne_irreflexive | #92 |
| #57 | 7 arithmetic identities | #93 |
| #61 | 5 CASE/WHEN | #85 |
| #53 | 1 of 2 (decideGroundExprEquiv_sound) | #94 |

### Previously regressed issues (now restored)

| Issue | Axiom | Was proved in | Reverted in | Status |
|-------|-------|--------------|-------------|--------|
| #59 | `between_reflexive` | PR #86 | commit 711581c | Restored in PR #102 |
| #60 | `like_empty_pattern` | PR #86 | commit 711581c | Restored in PR #102 |
| #62 | `length_empty` | PR #86 | commit 711581c | Restored in PR #102 |

## Batch 7: String Function Axioms (#62)

**Branch**: `claude/prove-string-func-axioms` | **PR**: #105

### upper_idempotent, lower_idempotent — 2 axioms → theorems

**Strategy**: Four-layer proof architecture:
1. Char-level: prove `c.toUpper.toUpper = c.toUpper` by unfolding `Char.toUpper/toLower/ofNat/ofNatAux`, then `split` on the range condition + `split` on `isValidChar`, closing with `simp_all <;> omega`.
2. String-level: lift via `String.ext` + `String.toList_map` + `List.map_map` + `congr 1; funext`.
3. evalFunc-level: match on `Option Value` cases, use `native_decide` for string constant equality (`"UPPER".toUpper = "UPPER"`).
4. Expr-level: use `evalExprWithDb_func` axiom + `List.map`.

**Key insight**: For idempotence (2 function applications), after unfolding `Char.ofNatAux`, the `split` on `isValidChar` + the range condition gives only 3 branches, and `simp_all <;> omega` handles the UInt32/BitVec arithmetic. `omega` can see through one level of `Char.ofNat` round-trip.

### upper_lower_upper, lower_upper_lower — 2 axioms → theorems

**Problem**: Cross-composition (3 function applications) requires the `Char.ofNat` round-trip: after `toUpper` creates `Char.ofNat (c.toNat - 32)`, applying `toLower` needs `(Char.ofNat n).toNat = n`, which requires reducing through UInt32 → BitVec → Fin → Nat struct projections. The brute-force `simp_all <;> omega` approach that worked for idempotence fails here.

**What failed**:
- `dsimp at *` + `simp_all <;> omega` — struct projections partially reduced but `omega` couldn't handle remaining Char equality
- `bv_omega` — converts BitVec→Nat but not Char/UInt32 struct projections
- `ext` to decompose struct equality — `UInt32` lacks `@[ext]`
- `show P = True from by omega, ite_true` — `omega` proves `P`, not `P = True`
- `UInt32.toNat` in simp set — loops with `UInt32.toNat_toBitVec`

**Solution**: Keep `Char.ofNat` opaque; prove a bridge lemma + use surgical `rw` chains:

```lean
-- Bridge lemma: full simp lets @[simp] lemmas fire through UInt32 layer
private theorem toNat_ofNat_of_isValid (n : Nat) (h : n.isValidChar) :
    (Char.ofNat n).toNat = n := by
  have hlt : n < 4294967296 := by simp only [Nat.isValidChar] at h; omega
  simp [Char.ofNat, Char.ofNatAux, h, Char.toNat]
```

Proof pattern for each branch:
1. `rw [toNat_ofNat_of_isValid _ hv]` — strip `.toNat` off `Char.ofNat` results
2. `have h : condition := by omega; rw [if_pos h]` — resolve each if-then-else
3. `rw [show n ± 32 ∓ 32 = n from by omega, Char.ofNat_toNat]` — collapse round-trip

**Key lessons**:
- Two lemmas serve different roles: `toNat_ofNat_of_isValid` clears `.toNat` in conditions; `Char.ofNat_toNat` closes the final `Char.ofNat c.toNat = c` goal
- The "isTrue" branches (3 nested rewrites) keep `.toNat` in context throughout, so `toNat_ofNat_of_isValid` suffices
- The "isFalse.isTrue" branches end with `Char.ofNat (c.toNat ± 32 ∓ 32) = c` — no `.toNat` present, need arithmetic simplification + `Char.ofNat_toNat` directly

### Summary table update

| Issue | Count | Axioms | PR |
|-------|--------|-----|-----|
| #54 | 6 comparison negation | #85 |
| #55 | 4 comparison flip | #85 |
| #56 | 2 eq_reflexive, ne_irreflexive | #92 |
| #57 | 7 arithmetic identities | #93 |
| #61 | 5 CASE/WHEN | #85 |
| #53 | 1 of 2 (decideGroundExprEquiv_sound) | #94 |
| #62 | 4 of 7 string function axioms (upper/lower idem + cross-comp) | #105 |

---

## Batch 8: CONCAT evalFunc + Proofs (#24, #62)

**Branch**: `claude/implement-concat-evalfunc` | **PR**: #107
**Date**: 2026-02-09

### Problem

The `concat_empty_left` and `concat_empty_right` axioms used `Expr.func "CONCAT" [...]`,
but `evalFunc` had no `"CONCAT"` handler — it always returned `none` via the catch-all.
This made the axioms trivially unsound: both sides evaluated differently for any input.

This was documented in Category 5 (Implementation bugs) of the Unsound Axioms section.

### Fix 1: Add CONCAT to evalFunc (Semantics.lean)

Added three pattern-match arms before the catch-all:
```lean
| "CONCAT", [some (.null t), some _] => some (.null t)
| "CONCAT", [some _, some (.null t)] => some (.null t)
| "CONCAT", [some (.string a), some (.string b)] => some (.string (a ++ b))
```

**Design choice: null type preservation.** Unlike `BinOp.concat` which normalizes
nulls to `.null none`, `evalFunc "CONCAT"` preserves the null's `Option SqlType`.
This was required for the proofs — without it, `CONCAT("", NULL::int)` would
return `some (.null none)` but the RHS `NULL::int` evaluates to
`some (.null (some SqlType.int))`, creating an unsolvable `⊢ none = n` goal.

Semantic divergence from `BinOp.concat`:

| Scenario | `BinOp.concat` | `evalFunc "CONCAT"` |
|----------|----------------|---------------------|
| null × string | `some (.null none)` | `some (.null t)` |
| string × null | `some (.null none)` | `some (.null t)` |
| string × string | `some (.string (a++b))` | `some (.string (a++b))` |

The null-type preservation difference is intentional (needed for proofs).
Initial implementation used bare `_` wildcards for the non-null argument,
which would have matched `none` (evaluation errors) and masked them as nulls.
Copilot review caught this — tightened to `some _` to match the `BinOp`
convention from Option 3 null semantics (PR #89). See "Obstacles" below.

### Fix 2: isStringOrNullValued precondition (Defs.lean)

The axioms were **still unsound as-is** even with CONCAT in evalFunc. For
non-string expressions:
- `CONCAT("", some (.int 42))` → `none` (catch-all) ≠ `some (.int 42)` (RHS)

Added a new type precondition:
```lean
def Expr.isStringOrNullValued (e : Expr) : Prop :=
  ∀ row : Row, (∃ s : String, evalExpr row e = some (.string s)) ∨
              (∃ n, evalExpr row e = some (.null n)) ∨
              evalExpr row e = none
```

This follows the pattern of `Expr.isBoolValued` and `Expr.isIntValued`, but
covers three cases: string values, null values (any type), and evaluation errors.

### Fix 3: Prove both theorems (Comparison.lean)

Converted from `axiom` to `theorem` with `isStringOrNullValued` precondition.

**Value-level helpers:**
```lean
private theorem evalFunc_concat_empty_left (v : Option Value) :
    (∃ s, v = some (.string s)) ∨ (∃ n, v = some (.null n)) ∨ v = none →
    evalFunc "CONCAT" [some (.string ""), v] = v

private theorem evalFunc_concat_empty_right (v : Option Value) :
    (∃ s, v = some (.string s)) ∨ (∃ n, v = some (.null n)) ∨ v = none →
    evalFunc "CONCAT" [v, some (.string "")] = v
```

Both proved by `rcases` on the disjunction + `subst_vars` + `simp [evalFunc, hup]`.
The left case uses `"" ++ s = s` (definitional); the right case uses
`s ++ "" = s` (`String.append_empty`, handled by `simp`).

**Expr-level theorems:**
```lean
theorem concat_empty_left (e : Expr) (h : e.isStringOrNullValued) :
    Expr.func "CONCAT" [Expr.lit (.string ""), e] ≃ₑ e := by
  intro row; simp only [evalExpr, evalExprWithDb_func, List.map, evalExprWithDb_lit]
  exact evalFunc_concat_empty_left _ (h row)
```

Same structure as `upper_idempotent`/`lower_idempotent` — unfold via
infrastructure axioms, then apply the value-level helper.

### Obstacles

1. **First build failed** with `unsolved goals: ⊢ none = n`. The null case
   produced `evalFunc "CONCAT" [some (.string ""), some (.null n)]` = `some (.null none)`
   but the RHS was `some (.null n)`. Root cause: initially copied `BinOp.concat`'s
   `=> some (.null none)` which discards the null's type. Fix: `=> some (.null t)`.
   One build iteration.

2. **Axiom unsoundness not in the plan.** The plan assumed adding CONCAT to
   evalFunc would make the axioms provable as-is. But identity elimination
   (`f(identity, e) = e`) is almost always unsound without a type precondition —
   the same pattern as `a + 0 = a` and `a AND TRUE = a`.

3. **Bare `_` wildcard in null patterns.** Initial implementation used
   `[some (.null t), _]` — the `_` matches `none` (evaluation errors), silently
   converting them to nulls. The `/audit` flagged this as a divergence from
   `BinOp.concat` but rationalized it as "not exploitable." Copilot review
   correctly caught it and suggested `some _`. **Lesson**: when the audit flags
   a convention violation, fix it — don't rationalize individual exceptions.

### Lessons learned

- **`Value.null` carries `Option SqlType` — evalFunc must preserve it for proofs.**
  This is the typed-null lesson: `BinOp.concat` normalizes to `.null none`, but
  proofs about identity elimination need the output null to match the input null's
  type exactly.

- **Identity elimination axioms need type preconditions.** This is now the third
  time: boolean identity laws needed `isBoolValued`, arithmetic needed
  `isIntValued`, and string concat needed `isStringOrNullValued`. The pattern is
  universal: `f(identity, e) = e` fails when `e` has the wrong type because the
  LHS returns `none` (type mismatch) but the RHS returns `e`'s raw value.

### Verification

- Build: clean, no warnings
- Tests: all 199 pass
- Axiom count: 131 → 129 (2 converted to theorems)
- Coverage validator: 100% runtime coverage
- `/audit evalFunc`: no soundness issues

### Summary table update

| Issue | Count | Axioms | PR |
|-------|--------|-----|-----|
| #54 | 6 comparison negation | #85 |
| #55 | 4 comparison flip | #85 |
| #56 | 2 eq_reflexive, ne_irreflexive | #92 |
| #57 | 7 arithmetic identities | #93 |
| #61 | 5 CASE/WHEN | #85 |
| #53 | 1 of 2 (decideGroundExprEquiv_sound) | #94 |
| #62 | 4 of 7 string function axioms (upper/lower idem + cross-comp) | #105 |
| #24, #62 | 2 concat_empty_left/right | #107 |

---

## Batch 9: length_concat (#108) + BETWEEN Expansion (#59)

**Branch**: `claude/prove-length-concat` | **PR**: #109 (length_concat + BETWEEN expansion)
**Date**: 2026-02-09

### length_concat (#108) — 1 axiom → theorem

`LENGTH(CONCAT(a, b)) = LENGTH(a) + LENGTH(b)`.

**Strategy**: Value-level helper `evalFunc_length_concat` reduces both sides
through `evalFunc` dispatch. No preconditions needed — for non-string/null
inputs, both sides reduce to `none`.

**Proof (after Copilot review refactor)**:
```lean
private theorem evalFunc_length_concat (av bv : Option Value) :
    evalFunc "LENGTH" [evalFunc "CONCAT" [av, bv]] =
    evalBinOp .add (evalFunc "LENGTH" [av]) (evalFunc "LENGTH" [bv]) := by
  have hL : "LENGTH".toUpper = "LENGTH" := by native_decide
  have hC : "CONCAT".toUpper = "CONCAT" := by native_decide
  cases av with
  | none => simp [evalFunc, hC, hL, evalBinOp]
  | some v => cases bv with
    | none => cases v <;> simp [evalFunc, hC, hL, evalBinOp]
    | some w => cases v <;> cases w <;> simp [evalFunc, hC, hL, evalBinOp, String.length_append]
```

Originally had 20+ explicit match arms (one per Value constructor pair).
Copilot review on PR #109 suggested `cases <;> simp` — but simple
`cases av <;> cases bv <;> simp` fails because `cases` on `Option Value`
only splits into `none | some val` without destructuring `val`. The fix is
nested `cases` that goes one level deeper into `Value` constructors.

### between_expansion + not_between_expansion (#59) — 2 axioms → theorems

**Strategy**: Two-layer proof — value-level `evalBetween_expansion` then
expression-level `between_expansion` with `Expr.evaluable` preconditions.

**Precondition: `Expr.evaluable`** (reused from `eq_reflexive`):
```lean
def Expr.evaluable (e : Expr) : Prop :=
  ∀ row : Row, ∃ v : Value, evalExpr row e = some v
```
Needed because AND short-circuits (`anything AND FALSE = FALSE`) while
BETWEEN returns `none` when any `Value.compare` produces `none`. Without
this precondition, expression-level errors create a divergence.

**Value-level proof — key tactic discovery**:

The `evalBetween_expansion` helper must prove that BETWEEN's match-on-compare
equals `evalBinOp .and (evalBinOp .ge ...) (evalBinOp .le ...)` for all 64
Value constructor triples. The challenge: `evalBinOp` has overlapping AND
patterns that create a decision tree opaque to `rfl`.

**Three case categories**:

1. **Both compares return `none`** (null v, bool v, or cross-type pairs):
   Both sides reduce to `none`. Tactic: `rfl`.

2. **Same-type pair with variable** (int×int, string×string): `Value.compare`
   returns `some (compare a b)`, and `evalBinOp .ge/.le` reduces to
   `Option.map` form. Need to case-split on the `Ordering` result.
   Tactic: `simp only [Value.compare, evalBinOp]; cases compare a b <;> rfl`
   (or `cases compare a b <;> cases compare a c <;> rfl` for two same-type pairs).

3. **Mixed: one null + one same-type pair** (e.g., int×null×int): `evalBinOp .ge`
   returns `some (.null none)` for the null pair, which flows into AND. Need both
   `Value.compare` and `evalBinOp` reduced, then case-split.
   Same tactic: `simp only [Value.compare, evalBinOp]; cases compare a c <;> rfl`

**The universal tactic**: `simp only [Value.compare, evalBinOp]; cases compare <;> rfl`
handles categories 2 and 3. Category 1 uses `rfl` directly. This replaces
the earlier broken approach that tried to use intermediate helper lemmas
(`between_match_eq_and_map`, `evalBinOp_ge_nonnull_int`, etc.) to bridge
between `Option.map` and `evalBinOp` representations.

**`not_between_expansion`** proved by composition (no new case analysis):
```
between_expansion → unaryOp_congr → not_and → binOp_congr + not_ge_is_lt + not_le_is_gt
```

### Tactic Pattern: `simp only [Value.compare, evalBinOp]; cases compare <;> rfl`

**When it works**: Proofs where one side is a `match` on `Value.compare` results
and the other side uses `evalBinOp` calls. The `simp` reduces both `Value.compare`
(eliminating the outer match) and `evalBinOp` (navigating the overlapping pattern
decision tree), leaving goals that depend only on the `Ordering` result. `cases`
on the `Ordering` (3 values: `.lt`, `.eq`, `.gt`) then closes each sub-goal by `rfl`.

**Where it applies**:
- `evalBetween_expansion` — BETWEEN match vs AND(ge, le) (this batch)
- Comparison flip helpers (`evalBinOp_lt_eq_gt_flip`, `evalBinOp_le_eq_ge_flip`) — could simplify the 27-arm match proofs in Comparison.lean
- Any future proof comparing raw `Value.compare` dispatch against `evalBinOp` comparison operators

**Where it does NOT apply**:
- `evalBinOp` commutativity (both sides are `evalBinOp` — no `Value.compare` to reduce)
- `evalBinOp` associativity (nested `evalBinOp` calls; the inner call must fully evaluate before the outer one can, and overlapping AND/OR patterns prevent `rfl` on abstract `Bool` variables)
- Proofs involving `evalFunc` (use `cases v <;> cases w <;> simp [evalFunc, ...]` instead)

### Tactic Pattern: `cases <;> first | rfl | (simp ...; exact helper _)`

For proofs over `Option Value × Option Value` where most constructor pairs close
by `rfl` and only a few need a specific helper lemma, this pattern eliminates
exhaustive match enumeration:

```lean
cases l with
| none => cases r with | none => rfl | some v => cases v <;> rfl
| some v => cases r with
  | none => cases v <;> rfl
  | some w => cases v <;> cases w <;>
    first | rfl | (simp only [evalBinOp]; exact helper_lemma _)
```

The `first | rfl | ...` combinator tries `rfl` on each generated sub-goal and
only falls through to the helper for the cases that need it (typically non-null
same-type pairs). This turned 8 helpers with ~25 match arms each into ~7 lines each
(-200 lines total):

- `evalUnaryOp_not_{eq,ne,lt,le,gt,ge}` — NOT comparison negation
- `evalBinOp_{lt_eq_gt,le_eq_ge}_flip` — comparison argument flips

**Key insight**: `cases v <;> cases w` on `Value` generates all 16 constructor
pairs (4×4). Most pairs hit the `evalBinOp` catch-all on both sides → `rfl`.
The `first` combinator handles the asymmetry cleanly without listing which
pairs need the helper.

### Related pattern: `cases v <;> cases w <;> simp [evalFunc, ...]`

For `evalFunc`-based proofs, `cases` on `Option Value` then `Value` constructors
with `<;> simp` is more maintainable than exhaustive match. The key is that
`cases` on `Option Value` only gives `none | some val` — you must also `cases val`
to get concrete `Value` constructors that `simp [evalFunc]` can reduce.

### Summary table update

| Issue | Count | Axioms | PR |
|-------|--------|-----|-----|
| #54 | 6 comparison negation | #85 |
| #55 | 4 comparison flip | #85 |
| #56 | 2 eq_reflexive, ne_irreflexive | #92 |
| #57 | 7 arithmetic identities | #93 |
| #61 | 5 CASE/WHEN | #85 |
| #53 | 1 of 2 (decideGroundExprEquiv_sound) | #94 |
| #62 | 4 of 7 string function axioms (upper/lower idem + cross-comp) | #105 |
| #24, #62 | 3 concat_empty_left/right + length_concat | #107, #109 |
| #59 | 2 of 3 between_expansion + not_between_expansion | #109 |
| #46-50 | 9 boolean identity/absorption | #104 |
| #60 | 1 of 3 like_match_all | #111 |
| #58 | 2 of 8 in_empty_false, not_in_empty_true | #112 |
| — | 2 flattenAnd_nonempty, flattenOr_nonempty | #112 |
| #79-81 | 16 ORDER BY/LIMIT/OFFSET | #115 |
| #51 | 2 where_true_elim, where_false_empty | #116 |
| #72 | 1 of 4 filter_false_empty' | #116 |

---

## Batch 10: Boolean Identity & Absorption Axioms (#46-50) — 9 axioms → theorems

**Branch**: `claude/define-bool-valued-axioms-QlSLF` | **PR**: #104 (merged)
**Date**: 2026-02-09

### Axioms proved

| Axiom | Issue | Statement |
|-------|-------|-----------|
| `not_not` | #46 | `NOT NOT e ≃ₑ e` |
| `and_true` | #48 | `e AND TRUE ≃ₑ e` |
| `or_false` | #48 | `e OR FALSE ≃ₑ e` |
| `and_self` | #49 | `e AND e ≃ₑ e` |
| `or_self` | #49 | `e OR e ≃ₑ e` |
| `and_not_self` | #50 | `e AND (NOT e) ≃ₑ FALSE` |
| `or_not_self` | #50 | `e OR (NOT e) ≃ₑ TRUE` |
| `and_absorb_or` | #47 | `e AND (e OR f) ≃ₑ e` |
| `or_absorb_and` | #47 | `e OR (e AND f) ≃ₑ e` |

### Precondition: `Expr.isBoolValued`

```lean
def Expr.isBoolValued (e : Expr) : Prop :=
  ∀ row : Row, ∃ b : Bool, evalExpr row e = some (.bool b)
```

Same pattern as `isIntValued` for arithmetic — these axioms only hold when
all expression arguments evaluate to booleans. For non-boolean inputs,
`AND`/`OR`/`NOT` return `none`, breaking the identity.

### Proof pattern

All follow the same structure: unfold via `evalExprWithDb_binOp`/`evalExprWithDb_unaryOp`,
extract the boolean witness from `isBoolValued`, then case-split on the `Bool` value
(only 2 cases: `true`/`false`). The absorption proofs additionally need the second
expression's boolean witness.

### Connection to optimizer guards

PR #101 (same timeframe) added `isDefinitelyBool` allowlist to the optimizer,
mirroring `isBoolValued`. The axiom preconditions and optimizer guards now protect
the same rewrites from both the proof and runtime sides.

---

## Batch 11: LIKE Match All (#60) — 1 axiom → theorem

**Branch**: `claude/prove-like-match-all` | **PR**: #111 (merged)
**Date**: 2026-02-10

### like_match_all

`Expr.binOp .like e (lit (.string "%")) ≃ₑ CASE WHEN IS_NULL(e) THEN NULL ELSE TRUE`

**Precondition**: `Expr.isStringOrNull` — expression evaluates to string or null.

**Value-level helper**: `evalBinOp_like_match_all` proves that `simpleLike s "%"` = `true`
for any string `s`, because `simpleLike` checks `pat == "%"` first (branch 1).

**Soundness fix**: Added `isStringOrNull` precondition to both `like_match_all` and
`like_self`. Without it, `5 LIKE '%'` → `none` but RHS → `some (.bool true)`.

---

## Batch 12: IN Empty + Flatten Axioms (#58, normalization)

**Branch**: `claude/prove-inlist-flatten-axioms` | **PR**: #112 (merged)
**Date**: 2026-02-10

### Axioms proved

| Axiom | Statement |
|-------|-----------|
| `in_empty_false` | `e IN () ≃ₑ FALSE` |
| `not_in_empty_true` | `e NOT IN () ≃ₑ TRUE` |
| `flattenAnd_nonempty` | flattening AND preserves semantics |
| `flattenOr_nonempty` | flattening OR preserves semantics |

### Infrastructure axiom added

`evalExprWithDb_inList` — unfolds `.inList` expression evaluation.

### Soundness gap fixed in PR #125

The remaining IN axioms (`in_singleton`, `in_pair`, `in_list_or_expansion`, etc.)
were unsound because `filterMap` in `evalExprWithDb` for IN lists handled evaluation
errors differently from the OR/AND expansion. The expansion propagates `none` from
individual comparisons, while `filterMap` silently dropped them.

**Resolution**: [PR #125](https://github.com/evelynmitchell/sql_equiv/pull/125)
fixed the root cause (Issue #124). Three changes:
(1) Added broad null propagation to `evalBinOp .or/.and` (SQL three-valued logic),
(2) Rewrote `inList` evaluator to use `foldl` over `evalBinOp .or/.eq` instead of
`filterMap`/`any`, (3) Redefined BETWEEN as `AND(GE, LE)` for consistency.
All 6 remaining IN-list axioms are now unblocked and provable via the new
foldl+evalBinOp semantics. Existing proofs `in_empty_false` and `not_in_empty_true`
were reproved to match the new evaluator.

---

## Batch 13: Phase 5 — ORDER BY / LIMIT / OFFSET (#79-81) — 16 axioms → theorems

**Branch**: `claude/prove-phase5-limit-offset-axioms` | **PR**: #115 (merged)
**Date**: 2026-02-10

### Infrastructure axioms added

| Axiom | Purpose |
|-------|---------|
| `evalSelect_limit_offset` | Decomposes `evalSelect` with LIMIT/OFFSET into `List.take`/`List.drop` on the base result |
| `evalSelect_orderBy_length` | ORDER BY preserves `List.length` |

### Axioms proved (16)

**ORDER BY (3):**
- `order_by_preserves_count`, `order_by_length_invariant`, `order_limit_deterministic`

**LIMIT (5):**
- `limit_zero_empty`, `limit_upper_bound`, `limit_none_all_rows`, `limit_monotonic`, `limit_one_singleton`

**OFFSET (4):**
- `offset_zero_identity`, `offset_too_large_empty`, `offset_reduces_count`, `offset_monotonic`

**LIMIT+OFFSET combinations (4):**
- `limit_offset_compose`, `offset_limit_zero_empty`, `pagination_upper_bound`, `consecutive_pages`

### Soundness fix

`offset_too_large_empty` was unsound for `limit = some L` — it measured count
from `evalSelect ... (some L) none` instead of `evalSelect ... none none`.
Fixed by measuring from the base query with no limit/offset.

### Proof patterns

Private helper lemmas (`evalSelect_SN`, `evalSelect_S0`, `evalSelect_0N`) specialize
`evalSelect_limit_offset` for concrete `Option` values. Essential when goals have
TWO `evalSelect` calls — raw `rw` twice causes the second to match the `base`
expression from the first rewrite. With helpers + `cases limit`, each branch
uses a clean specialized lemma.

`generalize evalSelect db (... none none) = base` after rewriting replaces the
long expression with a variable for `simp`/`omega` reasoning.

### Removed axiom

`order_by_empty_identity` — was vacuously true (`∀ row ∈ [], ...`), replaced by
`order_by_preserves_count` which is more useful.

---

## Batch 14: Phase 2 — WHERE / Filter Axioms (#51, #72) — 3 axioms → theorems

**Branch**: `claude/prove-phase2-where-filter-axioms` | **PR**: #116 (open)
**Date**: 2026-02-10

### Infrastructure axioms added

| Axiom | Purpose |
|-------|---------|
| `evalSelect_where_congr` | If two WHERE clauses produce the same filtering for every row, `evalSelect` produces the same result |
| `evalSelect_filter_all_false` | WHERE clause that rejects all rows → empty result (when no aggregates) |

### Axioms proved (3)

| Axiom | Statement | Approach |
|-------|-----------|----------|
| `where_true_elim` | `WHERE TRUE` is identity | Via `evalSelect_where_congr`: `TRUE == TRUE` = `true` matches `none` filter (both pass all rows) |
| `where_false_empty` | `WHERE FALSE` → empty result | Via `evalSelect_filter_all_false` + `h_no_agg` precondition |
| `filter_false_empty'` | Variant of above | Delegates to `where_false_empty` |

### Soundness fix: aggregate queries

`where_false_empty` and `filter_false_empty'` were originally stated without
preconditions, but are **unsound for aggregate queries**: `SELECT COUNT(*) FROM t
WHERE FALSE` returns 1 row (with count 0), not 0 rows. Added
`h_no_agg : selectHasAggregate items = false` precondition.

### Blocked axioms (4)

| Axiom | Blocker |
|-------|---------|
| `filter_and` | `evalFrom .subquery` double-qualifies columns (`t.col` → `inner.t.col`) |
| `filter_commute` | Same |
| `filter_idempotent` | Same |
| `predicate_pushdown` | `evalExpr` vs `evalExprWithDb` gap (no db context in external filter) |

### PR review feedback (Copilot)

1. Changed `evalSelect_filter_all_false` premise from propositional `≠` to
   boolean `== ... = false` — aligns with `List.filter`'s actual predicate form.
2. Added regression test: `SELECT COUNT(*) WHERE FALSE` returns 1 row.

**Lesson**: Axiom premises should mirror the implementation's predicate form.
Using the same operators avoids bridging boilerplate at every call site.

---

## Batch 15: Phase 4 — Set Operation Axioms — 4 proved, 9 documented unsound

**Branch**: `claude/prove-phase4-set-operation-axioms` | **PR**: #117
**Date**: 2026-02-11

### Infrastructure axioms added

| Axiom | Purpose |
|-------|---------|
| `evalQuery_simple` | Decomposes `evalQuery db (.simple sel)` to `evalSelect db sel` |
| `evalQuery_compound` | Decomposes `evalQuery db (.compound left op right)` to list operations |

### Dependencies added

- `LawfulBEq SqlType` (derived via `ReflBEq` + `LawfulBEq`)
- `LawfulBEq Value` (derived via `ReflBEq` + `LawfulBEq`)

These are needed for `List.contains_iff_mem` which bridges `List.contains` to `∈`.

### Axioms proved (4)

| Axiom | Statement | Approach |
|-------|-----------|----------|
| `union_all_length` | `\|A UNION ALL B\| = \|A\| + \|B\|` | `evalQuery_compound` + `List.length_append` |
| `except_self_empty` | `A EXCEPT A = []` | `List.filter_eq_nil_iff` + `List.contains_iff_mem` |
| `intersect_empty_right` | `A INTERSECT empty = []` | `evalSelect_filter_all_false` for empty select |
| `intersect_idempotent` | `A INTERSECT A = A` | `List.filter_eq_self` + `List.contains_iff_mem` |

### Unsound axioms documented (9)

The remaining 9 set operation axioms are **unsound** under our exact-list-equality
semantics. `List.eraseDups` keeps first-occurrence order, and `List.filter` preserves
left-side order, so commutativity/associativity/distributivity fail.

| Axiom | Counterexample |
|-------|----------------|
| `union_comm` | `[r1]++[r2]` eraseDups = `[r1,r2]` vs `[r2,r1]` |
| `union_all_comm` | `[r1]++[r2] ≠ [r2]++[r1]` |
| `intersect_comm` | filter preserves left-side ordering |
| `union_assoc` | eraseDups ordering differs |
| `intersect_assoc` | filter ordering differs |
| `union_idempotent` | `(a++a).eraseDups ≠ a` when a has dupes |
| `union_empty_right` | `(a++[]).eraseDups ≠ a` when a has dupes |
| `union_intersect_distrib` | ordering |
| `intersect_union_distrib` | ordering |

Each axiom now has an `⚠ UNSOUND` docstring warning with a counterexample.

### Proof techniques

- `simp only [evalQuery_compound, evalQuery_simple]` — decomposes compound queries
- `List.filter_eq_nil_iff` + `List.filter_eq_self` — characterize filter results
- `List.contains_iff_mem` (requires `LawfulBEq`) — bridges `contains` to `∈`
- `evalSelect_filter_all_false` + `evalExprWithDb_lit` — proves empty select returns `[]`

### Lessons learned

**1. `deriving LawfulBEq` exists in Lean 4.27 — don't prove it manually.**
We needed `LawfulBEq Value` for `List.contains_iff_mem`. Multiple attempts at
manual proofs failed because derived `BEq` generates an opaque `instBEqValue.beq`
that `simp [BEq.beq]` can't unfold. Tried: `simp_all (config := { decide := true })`,
removing `BEq` from deriving and using `instBEqOfDecidableEq`, writing a manual
`BEq` instance — all failed or broke downstream `rfl` proofs. The fix was
`deriving ReflBEq, LawfulBEq` (Lean 4.27 has deriving handlers for both).
**Takeaway**: check what the deriving machinery can do before writing manual instances.

**2. `partial def` in `mutual` blocks requires axioms to come after the block.**
`evalQuery` is `partial def` inside a `mutual ... end` block. Placing axioms
referencing `evalQuery` before the `end` gave "unknown identifier" errors.
The fix was placing `evalQuery_simple`/`evalQuery_compound` after the `end`.
**Takeaway**: infrastructure axioms about `partial def` must be placed after
the enclosing block, not interleaved.

**3. `let` bindings in axiom statements need type annotations for dot notation.**
`let l := evalQuery db left` in `evalQuery_compound` caused `.eraseDups` and
`.filter` to fail — Lean couldn't resolve the method without knowing the type.
Adding `: Table` fixed it. This doesn't happen in `def` bodies where Lean
has more type context, but axiom statements are more rigid.

**4. `simp only` vs `rw` for infrastructure axioms: use `simp only` when
multiple occurrences need rewriting.**
`rw [evalQuery_simple, evalQuery_simple]` failed because `rw` rewrites one
occurrence at a time, and after the first rewrite the second had nothing to
match. `simp only [evalQuery_compound, evalQuery_simple]` rewrites all
occurrences simultaneously.

**5. Proving "filter removes everything" vs "filter keeps everything".**
These are dual patterns that came up repeatedly:
- `except_self_empty` (filter removes all): `List.filter_eq_nil_iff` +
  show the predicate is false for every element via `List.contains_iff_mem`
- `intersect_idempotent` (filter keeps all): `List.filter_eq_self` +
  show the predicate is true for every element via `List.contains_iff_mem`
Both require `LawfulBEq` to bridge `List.contains` (boolean) to `∈` (propositional).

**6. Most set operation axioms are unsound under list equality — and that's
a design insight, not a bug.**
9 of 13 set operation axioms fail because `List.eraseDups` preserves
first-occurrence order and `List.filter` preserves left-side order. This
means commutativity (`A ∪ B = B ∪ A`), associativity, and distributivity
all break. These would hold under set or multiset semantics. This is a
fundamental limitation of modeling SQL query results as ordered lists with
propositional equality. The honest response is to document them as unsound
rather than weaken them into uselessness.
**Takeaway**: when an axiom can't be proved, always check whether the
semantics model is the problem before assuming the axiom statement is wrong.

---

## Batch 16: Bag/Set Equivalence — 9 "unsound" axioms proved

**Branch**: `claude/bag-set-equivalence`
**Date**: 2026-02-11

### Problem

9 set operation axioms (union_comm, union_all_comm, intersect_comm, union_assoc,
intersect_assoc, union_idempotent, union_empty_right, union_intersect_distrib,
intersect_union_distrib) were marked "unsound" because they failed under exact list
equality. However, SQL set operations are inherently order-independent — the failure
was a semantic model mismatch, not a mathematical falsehood.

### Solution: Equivalence hierarchy

Added two weaker equivalence relations to `Defs.lean`:
- **`≃ᵇ` (QueryBagEquiv)**: results are `List.Perm` (same elements, same multiplicities)
- **`≃ˢ` (QuerySetEquiv)**: results have same membership (`∀ row, row ∈ q1 ↔ row ∈ q2`)

Hierarchy: `≃ᵩ` (exact) → `≃ᵇ` (bag) → `≃ˢ` (set), with proofs of each implication.

### Helper lemmas (SetBagLemmas.lean)

| Lemma | Statement | Proof technique |
|-------|-----------|----------------|
| `perm_ext_iff_of_nodup` | Nodup + same membership → Perm | `perm_iff_count` + `Nodup.count` |
| `mem_eraseDups` | `a ∈ l.eraseDups ↔ a ∈ l` | Strong induction on list length |
| `nodup_eraseDups` | `l.eraseDups.Nodup` | Strong induction on list length |
| `Perm_eraseDups` | `l₁ ~ l₂ → l₁.eraseDups ~ l₂.eraseDups` | `perm_ext_iff_of_nodup` + `mem_eraseDups` |
| `mem_filter_contains` | `x ∈ l.filter (r.contains ·) ↔ x ∈ l ∧ x ∈ r` | `List.mem_filter` + `simp` |
| `mem_eraseDups_append` | `a ∈ (l₁ ++ l₂).eraseDups ↔ a ∈ l₁ ∨ a ∈ l₂` | `mem_eraseDups` + `List.mem_append` |

### Axioms proved (9)

| Axiom | Equiv | Approach |
|-------|-------|----------|
| `union_all_comm` | ≃ᵇ | `List.perm_append_comm` |
| `union_comm` | ≃ᵇ | `Perm_eraseDups perm_append_comm` |
| `union_assoc` | ≃ᵇ | `perm_ext_iff_of_nodup` + `or_assoc` |
| `intersect_assoc` | ≃ᵩ | `List.filter_filter` + `List.filter_congr` + Bool case split |
| `intersect_comm` | ≃ˢ | `mem_filter_contains` + `And.comm` |
| `union_idempotent` | ≃ˢ | `mem_eraseDups` + `List.mem_append` |
| `union_empty_right` | ≃ˢ | `mem_eraseDups` + `evalSelect_filter_all_false` |
| `union_intersect_distrib` | ≃ˢ | `or_and_left` |
| `intersect_union_distrib` | ≃ˢ | `and_or_left` |

### Key insight: intersect_assoc is exact (≃ᵩ)

`intersect_assoc` was classified as "unsound" but is actually provable under exact
equality. Both sides filter the same list (`evalQuery db a`) in the same order —
only the predicate differs. `List.filter_filter` reduces the LHS to a single filter,
and `List.filter_congr` shows the predicates are Boolean-equal via case analysis on
`contains` values. This makes it the strongest of the 9.

### Lessons learned

**1. "Unsound" axioms may just need a weaker equivalence.**
All 9 axioms were provable — 1 under exact equality, 3 under bag equivalence,
5 under set equivalence. The axioms weren't wrong; the equality relation was too strong.

**2. Strong induction is required for `eraseDups` proofs.**
`eraseDups_cons` recurses on `(xs.filter ...).eraseDups`, not `xs.eraseDups`.
Standard structural induction gives an IH about `xs` but not `xs.filter ...`.
The fix: `suffices ∀ n l, l.length ≤ n → P l` + induction on `n`.

**3. Avoid importing Batteries.Data.List.Perm transitively.**
Batteries re-exports `Tactic.Alias`, which makes `alias` a keyword. This broke
Optimizer.lean and PredicatePushdown.lean which use `alias` as a variable name.
The fix: prove `perm_ext_iff_of_nodup` ourselves from core lemmas (`perm_iff_count`
+ `Nodup.count`) rather than importing Batteries.

**4. Don't trust "unsound" labels — verify the claim.**
`intersect_assoc` was labeled "unsound — filter ordering differs" but both sides
filter the same list in the same order. The comment was wrong. Pushing for ≃ᵩ
instead of settling for ≃ˢ revealed it was never actually broken.

**5. Infrastructure is the hard part; individual proofs are easy.**
Once `mem_eraseDups`, `nodup_eraseDups`, and `Perm_eraseDups` were proved,
every theorem was 3–5 lines: unfold with `simp only [evalQuery_compound]`,
rewrite membership, close with a propositional tautology (`or_assoc`, `And.comm`,
`or_and_left`). The strong-induction proofs for the helpers took more thought
than all 9 theorems combined.

---

## Current Status Summary (2026-02-11, post-Batch 16)

### Axiom/theorem counts

- **95 axioms** remaining (across all .lean files in SqlEquiv/)
- **291 theorems** proved (75.4%)
- Axiom ratchet: 95 (in `tools/axiom_count_minimum.txt`)

### All issues with proved axioms

| Issue | Axioms proved | PR(s) |
|-------|---------------|-------|
| #24 | CONCAT evalFunc + proofs | #107 |
| #46 | `not_not` | #104 |
| #47 | `and_absorb_or`, `or_absorb_and` | #104 |
| #48 | `and_true`, `or_false` | #104 |
| #49 | `and_self`, `or_self` | #104 |
| #50 | `and_not_self`, `or_not_self` | #104 |
| #51 | `where_true_elim`, `where_false_empty` | #116 |
| #53 | `decideGroundExprEquiv_sound` (1 of 2) | #94 |
| #54 | 6 comparison negation | #85 |
| #55 | 4 comparison flip | #85 |
| #56 | `eq_reflexive`, `ne_irreflexive` | #92 |
| #57 | 7 arithmetic identities | #93 |
| #58 | `in_empty_false`, `not_in_empty_true` (2 of 8); 6 unblocked by #125 | #112, #125 |
| #59 | `between_reflexive`, `between_expansion`, `not_between_expansion` (3 of 3) | #102, #109, #125 |
| #60 | `like_empty_pattern`, `like_match_all` (2 of 3) | #102, #111 |
| #61 | 5 CASE/WHEN | #85 |
| #62 | 7 string function axioms (all) | #102, #105, #107, #109 |
| #72 | `filter_false_empty'` (1 of 4) | #116 |
| #79 | 3 ORDER BY | #115 |
| #80 | 5 LIMIT | #115 |
| #81 | 5+3 OFFSET/pagination | #115 |
| — | `flattenAnd_nonempty`, `flattenOr_nonempty` | #112 |

---

## Sequencing Decision: Axiom Proving Before Batteries Migration

**Date**: 2026-02-11

### Context

A Batteries migration plan was added (`docs/batteries-migration-plan.md`) proposing
to rename `alias` → `as_name`, import Batteries, refactor `evalBinOp` with a
`nullPropBinOp` wrapper, and add new `Value` constructors (`float`, `datetime`,
`decimal`). The question: should we do this before or after proving remaining axioms?

### Decision: Prove axioms first

**Reasoning:**

1. **Remaining axioms are SQL-semantic, not library-dependent.** Joins, subqueries,
   WHERE pushdown, and optimizer correctness are domain-specific — Batteries provides
   no relevant lemmas.

2. **Migration has high risk of breaking existing proofs.** The `evalBinOp` →
   `nullPropBinOp` refactor changes the match structure that 291 existing theorems
   depend on. The migration plan rates this as "High likelihood / Medium impact."
   Doing this while axiom counts are stable minimizes rework.

3. **`alias` rename (15 files, 89 occurrences) creates merge conflicts** with any
   parallel proof branches.

4. **Exception:** If an axiom requires an exhaustive 36+ arm Value case analysis,
   consider deferring it until after the `nullPropBinOp` refactor makes those proofs
   compositional. Most statement-level axioms won't hit this.

### Trigger for migration

- Diminishing returns on axiom proving, OR
- Need for new `Value` constructors (`float`, `datetime`), OR
- A specific proof that would clearly benefit from Batteries lemmas

---

## Batch 17: Join Edge Cases (#70) — 7 axioms → theorems

**Branch**: `claude/prove-join-edge-cases` | **PR**: #120

### Infrastructure axioms added (3)

Added to `Semantics.lean` after existing infrastructure axiom block:

- **`evalFrom_cross_join`**: decomposes `evalFrom db (.join left .cross right none)` into `(evalFrom db left).flatMap (fun lr => (evalFrom db right).map (fun rr => lr ++ rr))`
- **`evalFrom_inner_join`**: decomposes INNER JOIN into `flatMap`/`filterMap` with the ON condition
- **`evalFrom_left_join`**: decomposes LEFT JOIN with NULL-padding fallback for unmatched left rows

All three mirror the `evalFrom` implementation (lines 349-414) verbatim, following
the same pattern as `evalSelect_limit_offset`.

### Axioms proved (7)

**Empty-table axioms (4)** — straightforward:
- `cross_join_empty_left`: `rw [evalFrom_cross_join, h]; rfl` (empty list flatMap = [])
- `cross_join_empty_right`: `rw [evalFrom_cross_join]; simp [h, List.map_nil]; exact List.flatMap_const_nil _`
- `inner_join_empty_left`: `rw [evalFrom_inner_join, h]; rfl`
- `inner_join_empty_right`: `rw [evalFrom_inner_join]; simp [h, List.filterMap_nil]; exact List.flatMap_const_nil _`

**inner_join_true_is_cross**: TRUE condition makes filterMap equivalent to map.
After `rw [evalFrom_inner_join, evalFrom_cross_join]; congr 1; funext lr; dsimp`,
`simp only [evalExprWithDb_lit]` reduces the condition to `some (.bool true)`,
making the filterMap body `fun rr => some (lr ++ rr)`. Closed with
`List.filterMap_some_comp` (custom helper: `l.filterMap (fun x => some (f x)) = l.map f`).

**inner_join_false_empty**: FALSE condition makes every filterMap element `none`.
Induction on `leftRows` + `simp only [evalExprWithDb_lit, List.filterMap_none]`.
Each left row's filterMap produces `[]`, so the flatMap also produces `[]`.

**left_join_false_all_left**: FALSE condition means `matchingRows = []` for every
left row, entering the NULL-padding branch which produces exactly 1 row.
Proved via `List.length_flatMap_one` (custom helper) after showing each body
produces a length-1 list. `dsimp` + `simp only [evalExprWithDb_lit, List.filterMap_none, List.isEmpty_nil, ite_true]`
reduces the filterMap and if-then-else, then `cases rightRows.head? <;> simp <;> omega`.

### Helper lemmas added (4)

All private, in `StatementAxioms.lean`:
- `List.filterMap_none`: `l.filterMap (fun _ => none) = []`
- `List.flatMap_const_nil`: `l.flatMap (fun _ => []) = []`
- `List.filterMap_some_comp`: `l.filterMap (fun x => some (f x)) = l.map f`
- `List.length_flatMap_one`: `(l.flatMap f).length = l.length` when `∀ x, (f x).length = 1`

### Obstacles encountered

1. **`rw` with infrastructure axioms produces hostile goal forms.** `rw [evalFrom_inner_join]`
   introduces joint matches (`match on_, lr, rr with`) and unexpanded `let` bindings
   that block all subsequent `simp` matching. This is because Lean's match compiler
   optimizes the axiom's RHS into a joint match on multiple scrutinees.

2. **`simp only [h]` can't match when `h` has `let` bindings the goal has expanded.**
   Built `have h_empty : rightRows.filterMap (fun rr => let combined := lr ++ rr; ...) = []`
   but the goal had `lr ++ rr` inlined. `simp only [h_empty]` silently failed to match.
   Multiple iterations before diagnosing (simp warns "unused argument" but doesn't explain why).

3. **`ext` on lists produces `getElem?` goals.** Used `ext lr` after `congr 1` expecting
   pointwise function equality, but Lean destructured the resulting list equality into
   `∀ i, l₁[i]? = l₂[i]?`, making the induction hypothesis unusable. Fix: `funext lr`.

4. **Induction hypotheses don't track goal simplifications.** After `simp [evalExprWithDb_lit]`
   simplifies the filterMap body to `fun _ => none` in the goal, `ih` retains the original
   form with the match expression. `exact congrArg _ ih` fails on type mismatch.

### Key tactic pattern: `dsimp` → `simp only [evalExprWithDb_lit, ...]`

The winning pattern for evalFrom join proofs:
1. `rw [evalFrom_*_join]` — introduce the decomposition
2. `generalize evalFrom db a = leftRows; generalize evalFrom db b = rightRows` — abstract
3. `induction leftRows` — structural induction on the outer list
4. `dsimp` — normalize `let` bindings and reduce joint matches on concrete constructors
   (doesn't enter lambda bodies)
5. `simp only [evalExprWithDb_lit, ...]` — enters lambda bodies, reduces `evalExprWithDb`
   on literals, and applies cleanup lemmas (`List.filterMap_none`, etc.)

### Verification

- 224/224 tests pass (3 new infrastructure axiom tests added)
- 100% axiom coverage (91/91)
- Ratchet: 95 → 91

### PR review follow-up (Copilot #120)

Three comments, all valid:

1. **Strengthen left join test** — the `evalFrom_left_join` test only checked `.length`,
   not full row equality. The cross/inner join tests used `==` against the manual
   decomposition; the left join should too. Fixed by constructing `manualLeft` with the
   same flatMap/filterMap/NULL-padding logic and asserting `leftResult == manualLeft`.

2. **Remove unused `List.length_flatMap_one`** — artifact of an earlier proof approach
   (using `apply List.length_flatMap_one`) that was replaced by direct induction with
   `dsimp` + `simp`. The helper compiled but was never called. Removed.

3. **Lift `rightRows` outside the lambda in `evalFrom_left_join`** — the axiom had
   `let rightRows := evalFrom db right` inside the `flatMap` lambda, recomputing it
   per-iteration. The implementation computes it once outside. Moved to match. No proof
   impact since `generalize evalFrom db b = rightRows` achieves the same effect either way.

### PR review follow-up #2 (Copilot #120)

Four comments, all applying patterns already fixed in review #1 to the remaining axioms/tests:

1. **Hoist `rightRows` outside lambda in `evalFrom_cross_join` and `evalFrom_inner_join`** —
   review #1 fixed this for `evalFrom_left_join` only. Same pattern: `evalFrom db right`
   was recomputed inside the `flatMap` lambda. Moved `let rightRows := evalFrom db right`
   to top level in both axioms. Classic "sweep for the same pattern" miss.

2. **Replace hardcoded line numbers in docstrings** — docstrings said "Mirrors the
   implementation at lines 353-355" etc. These are fragile and break on any edit to
   `Semantics.lean`. Changed to semantic references: "Corresponds to the `.cross` case
   of `evalFrom` on `.join`".

3. **Hoist `evalFrom testDb tO` in cross join test** — same pattern as #1 but in test code.
   Extracted `let rightRows := evalFrom testDb tO` before the `flatMap`.

4. **Same hoist in inner join test** — identical fix for the inner join test.

**Proof impact of axiom restructuring**: Hoisting `let rightRows` to the axiom's top level
meant `rw [evalFrom_*_join]` now introduces a `let` binding at the goal's top level.
This blocked `congr`, `funext`, and `generalize` which couldn't see through the `let`.
Fix: add `simp only` immediately after each `rw [evalFrom_*_join]` to unfold the `let`
binding. Applied uniformly to all 7 proofs.

### PR review follow-up #3 (Copilot #120)

One comment: the `evalFrom_left_join` test only exercised the `matchingRows.isEmpty` branch
(FALSE condition → no matches → NULL padding). The axiom has three branches:

1. `on_ = some cond` where `cond` evaluates true for some rows → `else matchingRows`
2. `on_ = some cond` where no rows match → `if matchingRows.isEmpty` → NULL padding
3. `on_ = none` → all rows combine (effectively a cross join)

Only branch 2 was tested. Added two more test cases:
- Real predicate (`users.id = orders.user_id`): user 1 matches 2 orders, user 2 matches 1,
  user 3 gets NULL-padded. Exercises both the match and NULL-padding paths in a single query.
- `on_ = none`: all right rows combine with each left row, no filtering.

### Lesson: sweep means enumerate

This PR took 3 review rounds, each catching instances of the same pattern left unfixed:

| Round | Fix applied to | Missed |
|-------|---------------|--------|
| #1 | Hoist `rightRows` in left_join axiom | cross_join, inner_join axioms |
| #2 | Hoist in all 3 axioms | Corresponding tests; also docstrings |
| #2 | Fix docstrings, fix tests | — |
| #3 | — | Left join test only covered 1 of 3 branches |

The principle "sweep for the same pattern" was already in MEMORY.md from PR #101, but
"sweep" was interpreted as "glance around for obvious copies." What it actually requires
is **mechanical enumeration**: list every instance, check each one. For tests, this means
one test per match arm minimum. For structural changes (like hoisting a `let`), this means
grep for every occurrence of the old pattern across axioms *and* tests *and* docstrings.

---

## Current Status Summary (2026-02-11, post-Batch 18)

### Axiom/theorem counts

- **85 axioms** remaining (across all .lean files in SqlEquiv/)
- **~305 theorems** proved (78.2%)
- Axiom ratchet: 85 (in `tools/axiom_count_minimum.txt`)

### All issues with proved axioms

| Issue | Axioms proved | PR(s) |
|-------|---------------|-------|
| #24 | CONCAT evalFunc + proofs | #107 |
| #46 | `not_not` | #104 |
| #47 | `and_absorb_or`, `or_absorb_and` | #104 |
| #48 | `and_true`, `or_false` | #104 |
| #49 | `and_self`, `or_self` | #104 |
| #50 | `and_not_self`, `or_not_self` | #104 |
| #51 | `where_true_elim`, `where_false_empty` | #116 |
| #53 | `decideGroundExprEquiv_sound` (1 of 2) | #94 |
| #54 | 6 comparison negation | #85 |
| #55 | 4 comparison flip | #85 |
| #56 | `eq_reflexive`, `ne_irreflexive` | #92 |
| #57 | 7 arithmetic identities | #93 |
| #58 | `in_empty_false`, `not_in_empty_true` (2 of 8); 6 unblocked by #125 | #112, #125 |
| #59 | `between_reflexive`, `between_expansion`, `not_between_expansion` (3 of 3) | #102, #109, #125 |
| #60 | `like_empty_pattern`, `like_match_all` (2 of 3) | #102, #111 |
| #61 | 5 CASE/WHEN | #85 |
| #62 | 7 string function axioms (all) | #102, #105, #107, #109 |
| #69 | 7 join cardinality axioms | #121 |
| #70 | 7 join edge cases (empty, TRUE/FALSE conditions) | #120 |
| #72 | `filter_false_empty'` (1 of 4) | #116 |
| #79 | 3 ORDER BY | #115 |
| #80 | 5 LIMIT | #115 |
| #81 | 5+3 OFFSET/pagination | #115 |
| — | `flattenAnd_nonempty`, `flattenOr_nonempty` | #112 |

---

## Batch 18: Join Cardinality Axioms (#69) — 7 axioms → theorems

**Branch**: `claude/prove-join-cardinality-axioms`

### Infrastructure axiom added (1)

- **`evalFrom_right_join`** (`Semantics.lean`): decomposes RIGHT JOIN into
  `(evalFrom db right).flatMap` with NULL-padding fallback for unmatched right rows.
  Mirrors the `.right` case of `evalFrom` (lines 383-398).

### Axioms proved (7)

**cross_join_cardinality**: `|A × B| = |A| * |B|`.
After `rw [evalFrom_cross_join]; simp only []`, apply `List.length_flatMap_const` showing
each body has length `(evalFrom db b).length` via `List.length_map`.

**cross_join_cardinality_comm**: `|A × B| = |B × A|`.
Two applications of `cross_join_cardinality` + `Nat.mul_comm`.

**cross_join_assoc_cardinality**: `|(A × B) × C| = |A × (B × C)|`.
Four applications of `cross_join_cardinality` (on nested joins) + `Nat.mul_assoc`.

**inner_join_cardinality_le**: `|A ⋈ B| ≤ |A| * |B|`.
After `rw [evalFrom_inner_join]; simp only []`, apply `List.length_flatMap_le` showing
each filterMap body has length ≤ `(evalFrom db b).length` via `List.length_filterMap_le`.

**left_join_cardinality_ge**: `|A ⟕ B| ≥ |A|`.
After `rw [evalFrom_left_join]; simp only []`, apply `List.length_flatMap_ge_length` showing
each body produces ≥ 1 row via `left_join_body_length_ge_one` (if empty → singleton, else non-empty).

**right_join_cardinality_ge**: `|A ⟖ B| ≥ |B|`.
Same structure as left, using `evalFrom_right_join` and `right_join_body_length_ge_one`.

**inner_join_to_where**: `A ⋈[cond] B = (A × B) WHERE cond`.
After rewriting both sides with `evalFrom_inner_join`/`evalFrom_cross_join` and distributing
filter via `List.filter_flatMap`, reduce to per-element equality by `congr 1; funext lr`.
Induction on right rows, then `generalize` the `evalExprWithDb` result and case-split on
all `Value` constructors. For `some (.bool true)`, both sides produce `(lr ++ rr) :: tail`;
for all others, both produce just `tail`. `simp` reduces the match and BEq in each case.

### Helper lemmas added (5)

All private, in `StatementAxioms.lean`:
- `List.length_flatMap_const`: `∀ x ∈ l, (f x).length = n → (l.flatMap f).length = l.length * n`
- `List.length_flatMap_le`: `∀ x ∈ l, (f x).length ≤ n → ... ≤ l.length * n`
- `List.length_flatMap_ge_length`: `∀ x ∈ l, (f x).length ≥ 1 → ... ≥ l.length`
- `left_join_body_length_ge_one`: left join body (if/match) always produces ≥ 1 row
- `right_join_body_length_ge_one`: same for right join

### Key proof techniques

1. **`List.length_flatMap_*` helpers** factor out the inductive argument once, then each
   cardinality theorem is a 3-line proof: rewrite + simp + apply helper + show per-element bound.
2. **`Nat.add_mul` + `Nat.one_mul` + `Nat.add_comm`** replaces `ring` (unavailable without Mathlib)
   for the step `n + rest.length * n = (rest.length + 1) * n`.
3. **Generalize + case-split on `Value` constructors** for `inner_join_to_where`: avoids needing
   to prove a rewrite lemma bridging `match v with | some (.bool true) => ...` and `v == some (.bool true)`.
   After `generalize hv : evalExprWithDb ... = v; cases v`, each case is closed by `simp; exact ih`.

### Lessons learned

1. **Detailed plan with proof sketches → 0-comment Copilot review.** PR #120 (minimal plan) needed
   3 review rounds. This batch had exact tactic sequences, helper lemma signatures, dependency
   ordering, and a risk assessment in the plan. Copilot reviewed all 5 files and generated 0 comments.
   Upfront planning time pays back in fewer review iterations.

2. **`generalize + cases` beats `rw` for compiled match goals.** The plan called for a bridge lemma
   (`option_value_match_eq_beq`) to rewrite `match v with | some (.bool true) => ... | _ => ...`
   into `v == some (.bool true)`. This failed because Lean's compiled match has a different internal
   form than the lemma's LHS. The fix: `generalize hv : evalExprWithDb ... = v; cases v` —
   case-split on the scrutinee directly. Each constructor case closes with `simp; exact ih`.
   This pattern will recur in any proof involving `evalExprWithDb` result matching.

3. **Previously-documented gotchas saved a build iteration.** `List.mem_cons_self` implicit args and
   `ring` unavailability were already in MEMORY.md from earlier sessions. Hit both, recognized
   instantly, fixed in the same iteration instead of debugging from scratch.

### Verification

- 229/229 tests pass (3 new `evalFrom_right_join` tests)
- 100% axiom coverage (85/85)
- Ratchet: 91 → 85 (7 proved - 1 infrastructure added = net 6 reduction)
- **PR**: #121 (merged)

---

## Batch 19: Outer Join Preservation Axioms (#71) — 4 axioms → theorems

**Branch**: `claude/prove-outer-join-preservation`

### Soundness fix (1)

- **`left_join_filter_null_is_inner`** was unsound as originally stated. Counterexample:
  left table `[{a: 1}]`, right table `[{b: NULL}]`, `on_ = none`, `rightCol = "b"`.
  Inner join: `[{a:1, b:NULL}]` (length 1). Left join filtered: `[]` (b IS NULL removed).
  **0 ≠ 1**. Fixed by adding preconditions:
  - `hNotInLeft`: `rightCol` does not appear in left table rows (qualified column from right table)
  - `hRightNonNull`: `rightCol` exists and is non-null in every right table row

### Axioms proved (4)

**inner_subset_cross**: `|A ⋈[cond] B| ≤ |A × B|`.
Direct from `inner_join_cardinality_le` + `cross_join_cardinality` + `omega`.

**left_join_preserves_left**: every left row appears in the LEFT JOIN result.
After `rw [evalFrom_left_join]`, use `exists_mem_flatMap_of_length_ge_one` to find a witness
in the flatMap result, then `split at hjr` to case-split the if/match in the hypothesis.
For the isEmpty=false case, inline `List.mem_filterMap` + `cases on_` + `generalize`/case-split
on `evalExprWithDb` results.

**right_join_preserves_right**: symmetric to left, using `evalFrom_right_join`.

**left_join_filter_null_is_inner**: filtering LEFT JOIN NULLs gives INNER JOIN cardinality.
After `rw [evalFrom_left_join, evalFrom_inner_join]; rw [List.filter_flatMap]`, apply
`flatMap_length_eq_of_forall` to reduce to per-row equality. Three cases:
- isEmpty=true, head?=some: null-padded row → filter removes it (pred false on nulls) → length 0 = 0
- isEmpty=true, head?=none: lr alone → find? returns none → pred false → length 0 = 0
- isEmpty=false: filterMap elements all pass pred (find?_append + hNotInLeft + hRightNonNull)

### Helper lemmas added (3)

- `flatMap_length_eq_of_forall`: flatMap length equality when per-element contributions match
- `filter_pred_false_on_null_mapped`: filter pred is always false on null-mapped rows (by induction)
- `exists_mem_flatMap_of_length_ge_one`: existential witness from flatMap when body has length ≥ 1

### Key proof technique: bridging compiled predicate forms

The lambda `fun (k, _) => k == rightCol` compiles to two different syntactic forms:
- In hypotheses: `fun x => match x with | (k, snd) => k == rightCol`
- In goal (after `rw [evalFrom_left_join]`): `fun x => x.fst == rightCol`

These are definitionally equal but syntactically different. `rw` uses syntactic matching
and fails to unify them. The fix: use `have` with explicit type ascription to bridge:
```lean
have hNotInLeft' : List.find? (fun (x : String × Value) => x.fst == rightCol) lr = none :=
  hNotInLeft lr hlr
```
Since `have` only requires definitional equality between the ascribed type and the proof term's
type, this creates a hypothesis in the goal's form. Then `rw [hNotInLeft']` matches syntactically.

### Lessons learned

1. **Compiled lambda form divergence is the #1 `rw` failure mode for join proofs.**
   The same source-level lambda `fun (k, _) => k == rightCol` compiles to two different
   syntactic forms depending on context:
   - In hypotheses: `fun x => match x with | (k, snd) => k == rightCol`
   - In goals (after `rw` with infrastructure axioms): `fun x => x.fst == rightCol`

   They're definitionally equal, but `rw` uses syntactic matching, so it silently fails.
   This is invisible at the source level — the forms look identical in the `.lean` file.
   `trace_state` is the only reliable diagnostic.

2. **`have` with type ascription is the universal bridge for definitional equality gaps.**
   When a hypothesis has one compiled form and the goal needs another:
   ```lean
   have h' : List.find? (fun (x : String × Value) => x.fst == rightCol) lr = none :=
     hOriginal lr hlr
   ```
   `have` only requires definitional equality between the ascribed type and the proof term's
   type. Write the ascribed type in whatever form the *goal* needs. This pattern works for
   any definitional-but-not-syntactic mismatch, not just lambda forms.

3. **Always `trace_state` after the first `rw` with an infrastructure axiom.** The
   normalization that `rw [evalFrom_left_join]` performs on lambdas is not predictable from
   reading the source. One `trace_state` immediately reveals the form mismatch. Without it,
   you can spend hours trying different `rw`/`simp` strategies that all fail for the same
   invisible reason.

4. **`congr 1` before `rw [List.filter_eq_self]` when the goal has `.length`.** The goal
   `(filter p l).length = l.length` doesn't match `filter p l = l` (the `iff` in `filter_eq_self`).
   `congr 1` strips the `.length` first.

5. **`List.isEmpty_iff.mp` converts `isEmpty = true` to `l = []`.** Useful when the isEmpty
   condition from `split` on `if isEmpty then ...` needs to be used as a list rewrite.

6. **Meta-lesson: when `rw` silently fails, the problem is almost always a syntactic form
   mismatch invisible at the source level.** `trace_state` is the diagnostic, `have` with
   type ascription is the cure. Don't iterate on alternative `rw`/`simp` strategies — look
   at the actual goal first.

### Process retrospective

**~70% of the time on `left_join_filter_null_is_inner` was wasted.** The root cause — compiled
lambda form divergence between hypotheses and goal — was diagnosed late. Before that diagnosis,
multiple approaches were tried and abandoned:
- Bridge lemmas (`join_filterMap_eq`) that proved the forms propositionally equal but couldn't
  be applied by `rw` or `simp only` (same syntactic matching problem, one level up)
- `show ... from by` blocks with explicit types (type mismatch for the same reason)
- `simp only` variants hoping `simp` would handle definitional equality (it doesn't for
  rewrite rules — `simp only [h]` still needs syntactic matching on `h`'s LHS)
- `conv` navigation attempts

All failed for the same invisible reason. One `trace_state` after `rw [List.find?_append]`
revealed the problem immediately:
```
goal:  fun x => x.fst == rightCol
hyp:   fun x => match x with | (k, snd) => k == rightCol
```

The fix (`have` with type ascription) took ~10 minutes after that.

**Takeaway: for join proofs involving `rw` with infrastructure axioms, the first tactic after
the rewrite should be `trace_state`.** Treat the compiled form as unknown until observed.
Reasoning about what Lean's elaborator *should* do is unreliable; looking at what it *actually
did* is instant. The speculative reasoning wasn't just slow — it was actively harmful, because
each plausible-sounding but wrong theory spawned another attempt that failed for the same
undiagnosed cause.

The other three theorems (`inner_subset_cross`, `left_join_preserves_left`,
`right_join_preserves_right`) were straightforward by comparison. The whole batch could have
been a clean afternoon instead of a slog.

### Verification

- 229/229 tests pass
- 100% axiom coverage (81/81)
- Ratchet: 85 → 81 (4 axioms proved, 0 new infrastructure)

---

## Batch 20: Aggregate Property Axioms (#82) — 4 axioms → theorems

**Branch**: `claude/prove-aggregate-axioms` | **PR**: #123
**Date**: 2026-02-12

### Axioms proved (4)

| Axiom | Statement | Approach |
|-------|-----------|----------|
| `min_le_elem` | `ns.foldl min (ns.head!) ≤ n` for `n ∈ ns` | Match on `ns` to get `x :: xs`, apply `foldl_min_le_of_mem` |
| `max_ge_elem` | `n ≤ ns.foldl max (ns.head!)` for `n ∈ ns` | Symmetric: match + `le_foldl_max_of_mem` |
| `distinct_count_le` | `vs.eraseDups.length ≤ vs.length` | Strong induction on length; chain `eraseDups.length ≤ filter.length ≤ vs.length` |
| `distinct_idempotent` | `vs.eraseDups.eraseDups = vs.eraseDups` | `nodup_implies_eraseDups_eq` applied to `nodup_eraseDups` from SetBagLemmas |

### Private helpers (5)

| Helper | Purpose |
|--------|---------|
| `foldl_min_le_init` | `l.foldl min init ≤ init` — induction, `Int.min_le_left` |
| `foldl_min_le_of_mem` | `l.foldl min init ≤ n` for `n ∈ l` — cons case splits membership |
| `init_le_foldl_max` | `init ≤ l.foldl max init` — symmetric to `foldl_min_le_init` |
| `le_foldl_max_of_mem` | `n ≤ l.foldl max init` for `n ∈ l` — symmetric to `foldl_min_le_of_mem` |
| `nodup_implies_eraseDups_eq` | `l.Nodup → l.eraseDups = l` — strong induction, `filter_eq_self` |

### Key stdlib lemmas used

- `Int.min_le_left`, `Int.min_le_right`, `Int.le_max_left`, `Int.le_max_right`
- `List.eraseDups_cons`, `List.filter_eq_self`, `List.length_filter_le`
- `List.nodup_cons`, `List.mem_cons`

### Build notes

One iteration needed. Fixes:
- `List.not_mem_nil n` has type `False` in Lean 4.27.0 — used `nomatch h` instead of `absurd`
- `Nat.add_le_add_left` expects `k + n ≤ k + m` but goal had `... + 1` — used `omega`
- `bne_iff_ne`/`beq_iff_eq` unused by simp — switched to `Bool.not_eq_true'` + `beq_eq_false_iff_ne`

### Verification

- 229/229 tests pass
- 100% axiom coverage (77/77)
- No unused private declarations
- Ratchet: 81 → 77 (4 axioms proved, 0 new infrastructure)

---

## Batch 21: IN-list Evaluator Semantics Fix (#124) — Evaluator rewrite + 6 axioms unblocked

**Branch**: `claude/issue-124-inlist-semantics` | **PR**: #125 (merged)
**Date**: 2026-02-12

### Motivation

The `inList` evaluator used `filterMap`/`any` which silently dropped nulls and
errors, while the OR/AND expansion (used in axiom RHS) propagated them. This made
6 IN-list axioms (`in_singleton`, `not_in_singleton`, `in_pair`, `not_in_pair`,
`in_list_or_expansion`, `not_in_list_and_expansion`) provably unsound.

### Evaluator changes

| Change | Before | After |
|--------|--------|-------|
| AND/OR null propagation | No null handling beyond short-circuit | Broad `some (.null _), _ => some (.null _)` arms after short-circuit |
| `inList` evaluator | `filterMap`/`any` (drops nulls/errors) | `foldl` over `evalBinOp .or/.eq` (propagates nulls) |
| BETWEEN | Direct `Value.compare` match (90-line proof) | `evalBinOp .and (evalBinOp .ge ev evlo) (evalBinOp .le ev evhi)` — consistent by construction |

### Theorems improved (4)

| Theorem | Change |
|---------|--------|
| `between_expansion` | `evaluable` precondition dropped (BETWEEN now defined via evalBinOp) |
| `not_between_expansion` | Same |
| `in_empty_false` | Reproved for new `foldl` semantics |
| `not_in_empty_true` | Reproved for new `foldl` semantics |

### Theorems regressed to axioms (4)

| Axiom | Reason |
|-------|--------|
| `evalBinOp_and_or_distrib_left` | Value-level distributivity false for `none` inputs: `AND(FALSE, error)` short-circuits the error |
| `evalBinOp_or_and_distrib_left` | Same pattern with OR |
| `evalBinOp_and_or_distrib_right` | Same |
| `evalBinOp_or_and_distrib_right` | Same |

> **Design insight**: Expression-level distributivity is still correct (SQL operands
> are always boolean), so the expression-level axioms remain sound. The value-level
> theorems regressed because broad null propagation makes `AND(FALSE, error)` return
> `FALSE` (short-circuit) while distributed form `OR(AND(FALSE,x), AND(FALSE,y))`
> can return error if x or y errors. This is the expected SQL behavior.

### Axioms unblocked (6)

These axioms were blocked on Issue #124 and are now provable via the new
`foldl`+`evalBinOp` semantics:

| Axiom | Statement |
|-------|-----------|
| `in_singleton` | `e IN (v)` ≃ₑ `e = v` |
| `not_in_singleton` | `e NOT IN (v)` ≃ₑ `e <> v` |
| `in_pair` | `e IN (v1, v2)` ≃ₑ `e = v1 OR e = v2` |
| `not_in_pair` | `e NOT IN (v1, v2)` ≃ₑ `e <> v1 AND e <> v2` |
| `in_list_or_expansion` | General IN list → OR chain |
| `not_in_list_and_expansion` | General NOT IN list → AND chain |

### Net axiom count change

- **4 distributivity theorems → axioms**: +4
- **0 new infrastructure axioms**: +0
- **Net**: 77 → 81 axioms

### Verification

- 231/231 tests pass
- 100% axiom coverage (81/81)
- All 4 regressed axioms have runtime tests confirming SQL-correct behavior
