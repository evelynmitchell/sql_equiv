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
| #58 | `in_empty_false` | **No** | `none ≠ some (.bool false)` when `e` evals to `none` |
| #58 | `not_in_empty_true` | **No** | `none ≠ some (.bool true)` when `e` evals to `none` |
| #58 | `in_singleton`, `not_in_singleton` | **No** | Requires `e` to produce `some` |
| #58 | `in_pair`, `not_in_pair` | **No** | OR/AND short-circuit creates mismatch |
| #59 | `between_expansion` | **No** | AND short-circuit: `5 BETWEEN "x" AND 3` → `none` but RHS → `some (.bool false)` |
| #59 | `not_between_expansion` | **No** | OR short-circuit, same class |
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

### Soundness gap documented

The remaining IN axioms (`in_singleton`, `in_pair`, `in_list_or_expansion`, etc.)
are unsound because `filterMap` in `evalExprWithDb` for IN lists handles evaluation
errors differently from the OR/AND expansion. The expansion propagates `none` from
individual comparisons, while `filterMap` silently drops them.

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

## Current Status Summary (2026-02-11, post-PR #116)

### Axiom/theorem counts

- **106 axioms** remaining (across all .lean files in SqlEquiv/)
- **278 theorems** proved (72.4%)
- Axiom ratchet: 106 (in `tools/axiom_count_minimum.txt`)

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
| #58 | `in_empty_false`, `not_in_empty_true` (2 of 8) | #112 |
| #59 | `between_reflexive`, `between_expansion`, `not_between_expansion` (3 of 3) | #102, #109 |
| #60 | `like_empty_pattern`, `like_match_all` (2 of 3) | #102, #111 |
| #61 | 5 CASE/WHEN | #85 |
| #62 | 7 string function axioms (all) | #102, #105, #107, #109 |
| #72 | `filter_false_empty'` (1 of 4) | #116 |
| #79 | 3 ORDER BY | #115 |
| #80 | 5 LIMIT | #115 |
| #81 | 5+3 OFFSET/pagination | #115 |
| — | `flattenAnd_nonempty`, `flattenOr_nonempty` | #112 |
