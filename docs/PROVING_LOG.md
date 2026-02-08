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
| #62 | `concat_empty_left/right` | **No** | **BUG**: `evalFunc` has no "CONCAT" case — always returns `none` |

### Category 5: Implementation bugs

| Axiom | Bug |
|-------|-----|
| `concat_empty_left` | Uses `Expr.func "CONCAT"` but `evalFunc` has no CONCAT handler. Should use `Expr.binOp .concat` |
| `concat_empty_right` | Same bug |

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

**Branch**: `claude/prove-arithmetic-identities` | **Issue**: #57
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
