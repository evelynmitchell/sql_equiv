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

## Batch 2: Wave 1 remaining

**Branch**: `claude/prove-wave1-batch2` | **PR**: TBD

### Assessment of remaining Wave 1 axioms

| Issue | Axioms | Provable? | Why |
|-------|--------|-----------|-----|
| #46 | `not_not` | **No** (unsound) | Only holds for boolean-valued exprs. `NOT(NOT 5)` = `none` ≠ `5` |
| #47 | `and_absorb_or`, `or_absorb_and` | **No** (unsound) | Boolean-only. `5 AND (5 OR b)` = `none` ≠ `5` |
| #48 | `and_true`, `or_false` | **No** (unsound) | Boolean-only. `5 AND TRUE` = `none` ≠ `5` |
| #49 | `and_self`, `or_self` | **No** (unsound) | Boolean-only. `5 AND 5` = `none` ≠ `5` |
| #50 | `and_not_self`, `or_not_self` | **No** (unsound) | Boolean-only. |
| #57 | Arithmetic identities (7) | **No** (unsound) | Integer-only. `"hello" + 0` = `none` ≠ `"hello"` |
| #56 | `eq_reflexive`, `ne_irreflexive` | **Yes** | Handle null explicitly via CASE expression |

### #56 eq_reflexive, ne_irreflexive — ALSO UNSOUND

Traced through the semantics manually:

**`eq_reflexive`** says `(e = e) ≃ₑ CASE WHEN IS_NULL(e) THEN NULL ELSE TRUE END`.

When `evalExprWithDb db row e = some (.null t)`:
- **LHS**: `evalBinOp .eq (some (.null t)) (some (.null t))`
  = `(Value.eq (.null t) (.null t)).map Value.bool`
  = `none.map Value.bool` = **`none`**
- **RHS**: `isNullValue (some (.null t))` = `true` → CASE returns
  `evalExprWithDb db row (lit (null none))` = **`some (.null none)`**

`none ≠ some (.null none)` — the axiom is **unsound**.

**Root cause**: In our representation, `Value.eq` on two NULLs returns `none`
(Option Bool), which lifts to `none` (Option Value). But the RHS CASE
expression produces `some (.null none)`. In real SQL, `NULL = NULL` yields
`NULL`, and both sides should agree — but our encoding uses `none : Option Value`
for "evaluation produced no result" AND for "SQL NULL propagation through
operators". The CASE branch produces an explicit `some (.null none)` that
doesn't match the implicit `none` from `Value.eq`.

Same issue affects `ne_irreflexive` and also the `none` case (when
`evalExprWithDb` returns `none` for an invalid expression).

**Conclusion**: All remaining Wave 1 axioms are unsound as stated. Moving to
Wave 2 to find provable axioms.

### Wave 1 unsound axioms — future fix options

The unsound axioms (#46-#50, #56, #57) fall into two categories:

1. **Boolean-only** (#46-#50): Need precondition like
   `∀ row, ∃ b, evalExpr row e = some (.bool b)`.

2. **Representation mismatch** (#56): The `none` vs `some (.null none)`
   distinction. Could fix by either:
   - Changing `Value.eq` to return `some false` or `some (.null none)` for null
     inputs instead of `none`
   - Adding a precondition that `e` always evaluates to `some`
   - Defining a weaker equivalence that treats `none` and `some (.null _)` as
     equal

These are design decisions to discuss with the project owner.

---

## Batch 2: Wave 2 provable axioms

**Branch**: `claude/prove-wave1-batch2` | **PR**: TBD

### Soundness triage of Wave 2

Traced through semantics for every Wave 2 axiom. Core issue: many axioms fail
when subexpressions evaluate to `none` (malformed/ill-typed expressions).

| Issue | Axiom | Sound? | Why |
|-------|-------|--------|-----|
| #58 | `in_empty_false` | **No** | `none ≠ some (.bool false)` when `e` evals to `none` |
| #58 | `not_in_empty_true` | **No** | Same: `none ≠ some (.bool true)` |
| #58 | `in_singleton` | **No** | `none` from inList vs `none` from eq only match when both `e` and `a` give some |
| #58 | `not_in_singleton` | **No** | Same |
| #58 | `in_pair`, `not_in_pair` | **No** | OR/AND short-circuit creates mismatch |
| #59 | `between_expansion` | **No** | AND short-circuit: `5 BETWEEN "x" AND 3` → `none` but RHS → `some (.bool false)` |
| #59 | `between_reflexive` | **Yes** | All 3 subexprs are same `e`, so eval is consistent |
| #59 | `not_between_expansion` | **No** | OR short-circuit, same class as between_expansion |
| #60 | `like_match_all` | **No** | Non-string: LHS `none`, RHS `some (.bool true)` |
| #60 | `like_empty_pattern` | **Yes** | All value types give consistent results |
| #60 | `like_self` | **No** | Non-string: LHS `none`, RHS `some (.bool true)` |
| #62 | `length_empty` | **Yes** | Pure computation, no expression variables |
| #62 | `concat_empty_left/right` | **No** | BUG: `evalFunc` has no CONCAT case, always `none` |
| #62 | `upper/lower_idempotent` | **Likely** | Need `String.toUpper` idempotent lemma (hard) |
| #62 | `upper_lower_upper` | **Likely** | Same difficulty |
| #62 | `lower_upper_lower` | **Likely** | Same difficulty |

**Plan**: Prove the 3 sound ones (`like_empty_pattern`, `length_empty`,
`between_reflexive`). The string function idempotent axioms are mathematically
true but need Char-level lemmas that may not exist in Batteries.

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
