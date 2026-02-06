#!/usr/bin/env bash
#
# Creates GitHub issues for all 152 axioms in Equiv.lean, grouped by category.
# Run from your laptop where `gh` is installed and authenticated.
#
# Usage:
#   cd sql_equiv
#   bash scripts/create_axiom_issues.sh
#
# To do a dry run first (just prints, doesn't create):
#   DRY_RUN=1 bash scripts/create_axiom_issues.sh
#
set -euo pipefail

REPO="${REPO:-$(gh repo view --json nameWithOwner -q .nameWithOwner 2>/dev/null || echo "evelynmitchell/sql_equiv")}"
LABELS="axiom,proof-needed"

create_issue() {
  local title="$1"
  local body="$2"

  if [[ "${DRY_RUN:-0}" == "1" ]]; then
    echo "=== WOULD CREATE ==="
    echo "Title: $title"
    echo "Body (first 200 chars): ${body:0:200}..."
    echo ""
    return
  fi

  gh issue create \
    --repo "$REPO" \
    --title "$title" \
    --label "$LABELS" \
    --body "$body"

  # Rate limit: GitHub API allows 30 requests/minute for authenticated users
  sleep 2
}

echo "Creating axiom issues for $REPO..."
echo "Ensure labels 'axiom' and 'proof-needed' exist, or remove --label flag."
echo ""

# ============================================================================
# 1. Boolean Logic Axioms (9 axioms)
# ============================================================================

create_issue "Prove axiom: not_not (double negation elimination)" "$(cat <<'EOF'
## Axiom to prove

**File:** `SqlEquiv/Equiv.lean:910`
**Dependency level:** 1 (Boolean/Expression)

```lean
axiom not_not (e : Expr) : Expr.unaryOp .not (Expr.unaryOp .not e) ≃ₑ e
```

## Proof strategy

Unfold `ExprEquiv`, introduce db and row, case-split on `evalExprWithDb db row e`.
For `some (.bool b)`, `Trilean.not (Trilean.not b) = b` by cases on `b`.
For `some (.null _)` and `none`, `Trilean.not .unknown = .unknown`.

## Category
Boolean logic — Level 1 in axiom dependency hierarchy.

## Acceptance criteria
- [ ] Axiom replaced with `theorem`
- [ ] `lake build` succeeds
- [ ] No new `sorry` introduced
EOF
)"

create_issue "Prove axioms: and_absorb_or, or_absorb_and (absorption laws)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:1436-1441`
**Dependency level:** 1 (Boolean/Expression)

```lean
axiom and_absorb_or (a b : Expr) :
    Expr.binOp .and a (Expr.binOp .or a b) ≃ₑ a

axiom or_absorb_and (a b : Expr) :
    Expr.binOp .or a (Expr.binOp .and a b) ≃ₑ a
```

## Proof strategy

Unfold equivalence, introduce db/row. Let `va = evalExprWithDb db row a`,
`vb = evalExprWithDb db row b`. Case-split on the Trilean values of `va` and `vb`.
For each of 3×3 = 9 Trilean combinations, verify absorption holds.

Key insight: only the Trilean value of `a` and `b` matters, not the full `Value`.

## Category
Boolean logic — absorption laws. Used by `sql_equiv` tactic.

## Acceptance criteria
- [ ] Both axioms replaced with `theorem`
- [ ] `lake build` succeeds
- [ ] `sql_equiv` tactic examples still pass
EOF
)"

create_issue "Prove axioms: and_true, or_false (identity laws)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:1449-1454`
**Dependency level:** 1 (Boolean/Expression)

```lean
axiom and_true (a : Expr) :
    Expr.binOp .and a (Expr.lit (.bool true)) ≃ₑ a

axiom or_false (a : Expr) :
    Expr.binOp .or a (Expr.lit (.bool false)) ≃ₑ a
```

## Proof strategy

Unfold equivalence. `evalExprWithDb db row (Expr.lit (.bool true))` always returns
`some (.bool true)`. Then `evalBinOp .and va (some (.bool true))` simplifies by
case analysis on `va`.

## Category
Boolean logic — identity laws. Used by `sql_equiv` tactic.

## Acceptance criteria
- [ ] Both axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: and_self, or_self (idempotent laws)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:1557-1560`
**Dependency level:** 1 (Boolean/Expression)

```lean
axiom and_self (a : Expr) : Expr.binOp .and a a ≃ₑ a
axiom or_self (a : Expr) : Expr.binOp .or a a ≃ₑ a
```

## Proof strategy

Unfold equivalence. Let `va = evalExprWithDb db row a`. Show
`evalBinOp .and va va = va` by case analysis on `va`.

**Caveat:** These axioms claim `a AND a ≃ₑ a` for ALL expressions, but this
only holds when `a` is boolean-valued. For `a = Expr.lit (.int 5)`,
`evalBinOp .and (some (.int 5)) (some (.int 5))` returns null, while
`evalExpr` of the int literal returns `some (.int 5)`. Verify the axiom is
actually sound, or add a boolean-valued precondition.

## Category
Boolean logic — idempotent laws.

## Acceptance criteria
- [ ] Soundness verified or precondition added
- [ ] Axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: and_not_self, or_not_self (complement laws)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:1570-1575`
**Dependency level:** 1 (Boolean/Expression)

```lean
axiom and_not_self (a : Expr) :
    Expr.binOp .and a (Expr.unaryOp .not a) ≃ₑ Expr.lit (.bool false)

axiom or_not_self (a : Expr) :
    Expr.binOp .or a (Expr.unaryOp .not a) ≃ₑ Expr.lit (.bool true)
```

## Proof strategy

Case analysis on the Trilean value of `a`. When `a` is unknown (NULL),
`a AND (NOT a) = unknown AND unknown = unknown ≠ false`. This axiom may be
**unsound** for NULL-valued expressions. Verify carefully.

## Category
Boolean logic — complement laws. Similar soundness concern as `and_self`/`or_self`.

## Acceptance criteria
- [ ] Soundness verified (check NULL case!)
- [ ] Axioms replaced with `theorem` or removed if unsound
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 2. WHERE Clause Axioms (2 axioms)
# ============================================================================

create_issue "Prove axioms: where_true_elim, where_false_empty" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:1474-1484`
**Dependency level:** 2 (Expression Evaluation)

```lean
axiom where_true_elim (db : Database) (items : List SelectItem)
    (from_ : Option FromClause) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) : ...

axiom where_false_empty (db : Database) (items : List SelectItem)
    (from_ : Option FromClause) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) : ...
```

## Proof strategy

Unfold `evalSelect`. The WHERE clause filters rows by `evalExprWithDb`.
- `WHERE TRUE`: every row satisfies `(.bool true)`, filter is identity
- `WHERE FALSE`: no row satisfies `(.bool false)`, result is `[]`

Requires unfolding `evalSelect` and showing `List.filter (fun _ => true) = id`.

## Category
Query-level semantics — Level 2. Type-independent.

## Acceptance criteria
- [ ] Both axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 3. Normalization / Ground Expression Axioms (4 axioms)
# ============================================================================

create_issue "Prove axioms: normalizeExpr_equiv, syntacticEquiv_implies_equiv" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:1665-1671`
**Dependency level:** 2 (Expression Evaluation)

```lean
axiom normalizeExpr_equiv (e : Expr) : normalizeExpr e ≃ₑ e

axiom syntacticEquiv_implies_equiv {e1 e2 : Expr}
    (h : syntacticEquiv e1 e2 = true) : e1 ≃ₑ e2
```

## Proof strategy

`normalizeExpr_equiv`: structural induction on `Expr`, showing each
normalization step preserves semantics. Depends on commutativity theorems
already proven.

`syntacticEquiv_implies_equiv`: if syntactic forms match after normalization,
evaluation must be identical. Follows from `normalizeExpr_equiv` +
structural equality implies semantic equality.

## Category
Normalization — used by `sql_equiv!` tactic for `native_decide` path.

## Acceptance criteria
- [ ] Both axioms replaced with `theorem`
- [ ] `sql_equiv!` tactic still works
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: ground_expr_eval_independent, decideGroundExprEquiv_sound" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:1916-1929`
**Dependency level:** 2 (Expression Evaluation)

```lean
axiom ground_expr_eval_independent (e : Expr) (hg : e.isGround = true) :
    ∀ r1 r2 : Row, evalExpr r1 e = evalExpr r2 e

axiom decideGroundExprEquiv_sound {e1 e2 : Expr}
    (hg1 : e1.isGround = true) (hg2 : e2.isGround = true) :
    decideGroundExprEquiv e1 e2 hg1 hg2 = true → e1 ≃ₑ e2
```

## Proof strategy

`ground_expr_eval_independent`: A ground expression contains no column
references, so evaluation cannot depend on the row. Structural induction
on `Expr`; the `isGround` hypothesis rules out `.col` constructors.

`decideGroundExprEquiv_sound`: follows from `ground_expr_eval_independent`
— if both exprs are ground and evaluate to the same value on any row,
they're equivalent on all rows.

## Category
Ground expression decidability — enables `native_decide` for constant exprs.

## Acceptance criteria
- [ ] Both axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 4. Comparison Axioms (12 axioms)
# ============================================================================

create_issue "Prove axioms: comparison negation rules (6 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3022-3043`
**Dependency level:** 1 (Boolean/Expression)

```lean
axiom not_eq_is_ne (a b : Expr) : NOT (a = b) ≃ₑ a <> b
axiom not_ne_is_eq (a b : Expr) : NOT (a <> b) ≃ₑ a = b
axiom not_lt_is_ge (a b : Expr) : NOT (a < b) ≃ₑ a >= b
axiom not_le_is_gt (a b : Expr) : NOT (a <= b) ≃ₑ a > b
axiom not_gt_is_le (a b : Expr) : NOT (a > b) ≃ₑ a <= b
axiom not_ge_is_lt (a b : Expr) : NOT (a >= b) ≃ₑ a < b
```

## Proof strategy

Unfold equivalence. Case-split on `evalBinOp` result for each comparison.
The key insight: `evalBinOp .ne` is defined as `not (evalBinOp .eq)`,
and similarly for other pairs. So the negation just cancels.

**Type-sensitive:** needs case analysis on `Value` constructors (currently
4×4 = 25 cases each, most trivial by `rfl`).

## Category
Comparison rules — used by `sql_equiv` and `sql_rw_compare` tactics.

## Acceptance criteria
- [ ] All 6 axioms replaced with `theorem`
- [ ] `sql_rw_compare` tactic examples still pass
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: comparison flip rules (4 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3046-3059`
**Dependency level:** 1 (Boolean/Expression)

```lean
axiom lt_flip (a b : Expr) : a < b ≃ₑ b > a
axiom le_flip (a b : Expr) : a <= b ≃ₑ b >= a
axiom gt_flip (a b : Expr) : a > b ≃ₑ b < a
axiom ge_flip (a b : Expr) : a >= b ≃ₑ b <= a
```

## Proof strategy

Unfold equivalence. Show `evalBinOp .lt va vb = evalBinOp .gt vb va`
by case analysis on `Value.compare`. The semantics definition should
make this nearly definitional.

**Type-sensitive:** requires Value case analysis.

## Category
Comparison rules — used by `sql_rw_compare` tactic.

## Acceptance criteria
- [ ] All 4 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: eq_reflexive, ne_irreflexive" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3009-3017`
**Dependency level:** 1 (Boolean/Expression)

```lean
axiom eq_reflexive (e : Expr) :
    Expr.binOp .eq e e ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool true)))

axiom ne_irreflexive (e : Expr) :
    Expr.binOp .ne e e ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool false)))
```

## Proof strategy

`e = e` is TRUE for non-null, NULL for null. The CASE expression on the
right-hand side captures exactly this. Unfold both sides and show they
produce the same value for each possible evaluation of `e`.

## Category
Comparison rules — reflexivity with NULL awareness.

## Acceptance criteria
- [ ] Both axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 5. Arithmetic Identity Axioms (7 axioms)
# ============================================================================

create_issue "Prove axioms: arithmetic identities (7 axioms: x+0, 0+x, x*1, 1*x, x*0, 0*x, x-0)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:2859-2884`
**Dependency level:** 1 (Boolean/Expression)

```lean
axiom expr_add_zero (e : Expr) : e + 0 ≃ₑ e
axiom expr_zero_add (e : Expr) : 0 + e ≃ₑ e
axiom expr_mul_one (e : Expr) : e * 1 ≃ₑ e
axiom expr_one_mul (e : Expr) : 1 * e ≃ₑ e
axiom expr_mul_zero (e : Expr) : e * 0 ≃ₑ 0
axiom expr_zero_mul (e : Expr) : 0 * e ≃ₑ 0
axiom expr_sub_zero (e : Expr) : e - 0 ≃ₑ e
```

## Proof strategy

Unfold equivalence. `Expr.lit (.int 0)` evaluates to `some (.int 0)`.
Then `evalBinOp .add va (some (.int 0))`:
- If `va = some (.int n)`: returns `some (.int (n + 0))` = `some (.int n)` by `Int.add_zero`
- If `va = some (.string _)`: cross-type, returns null. But the axiom claims `e + 0 ≃ₑ e`,
  which would mean `null ≃ₑ string`. **Check soundness for non-int expressions.**

**Soundness concern:** These axioms may only be valid when `e` evaluates to an int.
If `e` evaluates to a string, `e + 0` is null but `e` is a string — not equivalent.

## Category
Arithmetic identities — used by `sql_rw_arith` tactic. **May need preconditions.**

## Acceptance criteria
- [ ] Soundness verified for all Value types
- [ ] Axioms replaced with `theorem` (with preconditions if needed)
- [ ] `sql_rw_arith` tactic updated if signatures change
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 6. IN / BETWEEN / LIKE Axioms (13 axioms)
# ============================================================================

create_issue "Prove axioms: IN list expansion rules (6 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:2891-2925`
**Dependency level:** 2 (Expression Evaluation)

```lean
axiom in_empty_false (e : Expr) : e IN () ≃ₑ FALSE
axiom not_in_empty_true (e : Expr) : e NOT IN () ≃ₑ TRUE
axiom in_singleton (e a : Expr) : e IN (a) ≃ₑ e = a
axiom not_in_singleton (e a : Expr) : e NOT IN (a) ≃ₑ e <> a
axiom in_list_or_expansion (e : Expr) (vals : List Expr) :
    e IN (vals) ≃ₑ OR-chain of (e = v) for each v in vals
axiom not_in_list_and_expansion (e : Expr) (vals : List Expr) :
    e NOT IN (vals) ≃ₑ AND-chain of (e <> v) for each v in vals
```

Also `in_pair` and `not_in_pair` (lines 2907-2914).

## Proof strategy

Unfold `evalExprWithDb` for `Expr.inList`. The implementation iterates
over the value list, comparing each. Show this is equivalent to the
OR/AND chain by induction on the list.

Type-independent (operates on Expr structure).

## Category
Expression rewrite rules — IN expansion.

## Acceptance criteria
- [ ] All axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: BETWEEN expansion rules (3 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:2933-2945`
**Dependency level:** 2 (Expression Evaluation)

```lean
axiom between_expansion (e lo hi : Expr) :
    e BETWEEN lo AND hi ≃ₑ e >= lo AND e <= hi

axiom between_reflexive (e : Expr) :
    e BETWEEN e AND e ≃ₑ e >= e AND e <= e

axiom not_between_expansion (e lo hi : Expr) :
    NOT (e BETWEEN lo AND hi) ≃ₑ e < lo OR e > hi
```

## Proof strategy

Unfold `evalExprWithDb` for `Expr.between`. The semantics should directly
implement the expansion. `between_reflexive` follows from `between_expansion`.
`not_between_expansion` requires De Morgan on the expanded form.

Type-independent.

## Category
Expression rewrite rules — BETWEEN.

## Acceptance criteria
- [ ] All 3 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: LIKE pattern rules (3 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:2952-2966`
**Dependency level:** 2 (Expression Evaluation)

```lean
axiom like_match_all (e : Expr) : e LIKE '%' ≃ₑ IS NOT NULL(e)
axiom like_empty_pattern (e : Expr) : e LIKE '' ≃ₑ e = ''
axiom like_self (e : Expr) : e LIKE e ≃ₑ ... (pattern with no wildcards)
```

## Proof strategy

Unfold `evalBinOp .like`. The LIKE implementation does pattern matching.
- `'%'` matches any string → equivalent to IS NOT NULL
- `''` matches only empty string → equivalent to equality
- `like_self` is trickier — only valid when `e` contains no LIKE wildcards

**Soundness check needed for `like_self`.**

## Category
Expression rewrite rules — LIKE patterns.

## Acceptance criteria
- [ ] All 3 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 7. CASE/WHEN Axioms (5 axioms)
# ============================================================================

create_issue "Prove axioms: CASE/WHEN simplification rules (5 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:2808-2825`
**Dependency level:** 2 (Expression Evaluation)

```lean
axiom case_when_true (x y : Expr) : CASE WHEN TRUE THEN x ELSE y ≃ₑ x
axiom case_when_false (x y : Expr) : CASE WHEN FALSE THEN x ELSE y ≃ₑ y
axiom case_when_false_no_else (x : Expr) : CASE WHEN FALSE THEN x ≃ₑ NULL
axiom case_empty_else (y : Expr) : CASE (empty) ELSE y ≃ₑ y
axiom case_empty_no_else : CASE (empty) ≃ₑ NULL
```

## Proof strategy

Unfold `evalExprWithDb` for `Expr.case`. The implementation iterates
through branches, evaluating conditions. With TRUE/FALSE literals, the
first matching branch (or ELSE/NULL) is selected deterministically.

Type-independent.

## Category
Expression rewrite rules — CASE simplification.

## Acceptance criteria
- [ ] All 5 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 8. String Function Axioms (7 axioms)
# ============================================================================

create_issue "Prove axioms: string function properties (7 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:2975-3003`
**Dependency level:** 2 (Expression Evaluation)

```lean
axiom concat_empty_left (e : Expr) : CONCAT('', e) ≃ₑ e
axiom concat_empty_right (e : Expr) : CONCAT(e, '') ≃ₑ e
axiom upper_idempotent (e : Expr) : UPPER(UPPER(e)) ≃ₑ UPPER(e)
axiom lower_idempotent (e : Expr) : LOWER(LOWER(e)) ≃ₑ LOWER(e)
axiom upper_lower_upper (e : Expr) : UPPER(LOWER(UPPER(e))) ≃ₑ UPPER(e)
axiom lower_upper_lower (e : Expr) : LOWER(UPPER(LOWER(e))) ≃ₑ LOWER(e)
axiom length_empty : LENGTH('') ≃ₑ 0
```

## Proof strategy

Unfold `evalFunc` for each function. These depend on Lean's `String`
library functions:
- `String.append "" s = s` for concat
- `String.toUpper ∘ String.toUpper = String.toUpper` for idempotence
- `"".length = 0` for length_empty

**Soundness concern for concat:** `CONCAT('', e) ≃ₑ e` fails when `e` is
non-string (CONCAT returns null for non-strings, but `e` evaluates to the
non-string value). May need a string-typed precondition.

## Category
String functions. Partially type-sensitive.

## Acceptance criteria
- [ ] Soundness verified
- [ ] All 7 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 9. Set Operation Axioms (12 axioms)
# ============================================================================

create_issue "Prove axioms: set operation commutativity (3 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3066-3078`
**Dependency level:** 3 (Query-level)

```lean
axiom union_comm (a b : SelectStmt) : (a UNION b) ≃ᵩ (b UNION a)
axiom union_all_comm (a b : SelectStmt) : (a UNION ALL b) ≃ᵩ (b UNION ALL a)
axiom intersect_comm (a b : SelectStmt) : (a INTERSECT b) ≃ᵩ (b INTERSECT a)
```

## Proof strategy

Unfold `QueryEquiv` and `evalQuery`. Set operations on lists:
- UNION: `List.union` is commutative (as sets)
- UNION ALL: `List.append` — **NOT commutative as lists!** Order differs.
  This axiom may be unsound unless QueryEquiv ignores row order.
- INTERSECT: `List.inter` is commutative (as sets)

**Check QueryEquiv definition** — if it compares ordered lists, `union_all_comm` is wrong.

## Category
Set operations — commutativity. Type-independent.

## Acceptance criteria
- [ ] Verify `union_all_comm` soundness
- [ ] All 3 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: set operation associativity and distributivity (4 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3081-3130`
**Dependency level:** 3 (Query-level)

```lean
axiom union_assoc (a b c : Query) : (a UNION b) UNION c ≃ᵩ a UNION (b UNION c)
axiom intersect_assoc (a b c : Query) : (a ∩ b) ∩ c ≃ᵩ a ∩ (b ∩ c)
axiom union_intersect_distrib (a b c : Query) : a ∪ (b ∩ c) ≃ᵩ (a ∪ b) ∩ (a ∪ c)
axiom intersect_union_distrib (a b c : Query) : a ∩ (b ∪ c) ≃ᵩ (a ∩ b) ∪ (a ∩ c)
```

## Proof strategy

These are set-theoretic identities. Proof depends on how `evalQuery`
implements UNION (dedup) and INTERSECT. If using `List.eraseDups` and
`List.inter`, standard set lemmas apply.

## Category
Set operations — algebraic properties. Type-independent.

## Acceptance criteria
- [ ] All 4 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: set operation edge cases (5 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3091-3118`
**Dependency level:** 3 (Query-level)

```lean
axiom union_idempotent (a : SelectStmt) : a UNION a ≃ᵩ a
axiom intersect_idempotent (a : SelectStmt) : a INTERSECT a ≃ᵩ a
axiom except_self_empty (db : Database) (a : SelectStmt) : eval(a EXCEPT a) = []
axiom union_empty_right (db : Database) (a : SelectStmt) : a UNION empty = eval(a)
axiom intersect_empty_right (db : Database) (a : SelectStmt) : a INTERSECT empty = []
```

Also: `union_all_length` (line 3116).

## Proof strategy

Standard set/list properties. `except_self_empty` = `A \ A = ∅`.
`union_idempotent` = `A ∪ A = A` (after dedup). These follow directly
from the list operation definitions.

## Category
Set operations — edge cases. Type-independent.

## Acceptance criteria
- [ ] All axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 10. Join Axioms (20 axioms)
# ============================================================================

create_issue "Prove axioms: join_comm, join_comm_full (INNER JOIN commutativity)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:1490, 2123`
**Dependency level:** 4 (Join Algebra) — **HIGH PRIORITY**

```lean
axiom join_comm (db : Database) (a b : FromClause) (cond : Expr) :
    ∀ row ∈ evalFrom db (.join a .inner b (some cond)),
    ∃ row2 ∈ evalFrom db (.join b .inner a (some cond)), ...

axiom join_comm_full (db : Database) (a b : FromClause) (cond : Expr) :
    evalFrom db (.join a .inner b (some cond)) =
    evalFrom db (.join b .inner a (some cond))
```

## Proof strategy

This is one of the hardest axioms. Need to show that for INNER JOIN:
1. Row merging is commutative (as sets of key-value pairs)
2. Condition evaluation is symmetric
3. The cross-product iteration order doesn't matter

Key challenge: `mergeRows rowA rowB` vs `mergeRows rowB rowA` produce
different list orderings. `join_comm_full` claims **list equality**, which
may be too strong — the rows may appear in different order.

**May need to weaken to set/bag equality** or prove the implementation
produces the same order (depends on nested loop structure).

See `PROVING_AXIOMS_PLAN.md` Phase 4 for detailed strategy.

## Category
Join algebra — Level 4. Type-independent. **Blocks Phases 5-8.**

## Acceptance criteria
- [ ] Both axioms replaced with `theorem` (or one subsumed by the other)
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: cross_join_comm, cross_join_assoc" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:2129-2135`
**Dependency level:** 4 (Join Algebra)

```lean
axiom cross_join_assoc (db : Database) (a b c : FromClause) :
    evalFrom db (A × B) × C = evalFrom db A × (B × C)

axiom cross_join_comm (db : Database) (a b : FromClause) :
    ∀ row ∈ evalFrom db (A × B),
    ∃ row' ∈ evalFrom db (B × A), ...
```

## Proof strategy

Cross join = cartesian product. Commutativity and associativity of
cartesian products are standard. The challenge is the list representation.

For `cross_join_assoc`: show `List.bind (List.bind as f) g = List.bind as (fun a => List.bind (f a) g)` which is the monad associativity law for lists.

## Category
Join algebra — Level 4. Type-independent.

## Acceptance criteria
- [ ] Both axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axiom: join_assoc (INNER JOIN associativity)" "$(cat <<'EOF'
## Axiom to prove

**File:** `SqlEquiv/Equiv.lean:2116`
**Dependency level:** 5 (Join Algebra) — **HARDEST AXIOM**

```lean
axiom join_assoc (db : Database) (a b c : FromClause) (cond1 cond2 : Expr) :
    ∀ row ∈ evalFrom db ((A ⋈[cond1] B) ⋈[cond2] C),
    ∃ row' ∈ evalFrom db (A ⋈[cond1] (B ⋈[cond2] C)), ...
```

## Proof strategy

Hardest proof in the project. Need to show three-way join is associative:
1. Any row produced by `(A ⋈ B) ⋈ C` can be produced by `A ⋈ (B ⋈ C)`
2. The merged row contains the same key-value pairs

Key challenge: predicates `cond1` and `cond2` may reference columns from
any of the three tables. Need to show evaluation is preserved under
reassociation.

Depends on: `cross_join_assoc`, row merge associativity, condition
evaluation independence from join structure.

See `PROVING_AXIOMS_PLAN.md` Phase 5.

## Category
Join algebra — Level 5. Type-independent. **Blocks optimizer proofs.**

## Acceptance criteria
- [ ] Axiom replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: join cardinality bounds (7 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3137-3206`
**Dependency level:** 4 (Join Algebra)

```lean
axiom cross_join_cardinality_comm (db) (a b) : |A × B| = |B × A|
axiom cross_join_cardinality (db) (a b) : |A × B| = |A| * |B|
axiom inner_join_cardinality_le (db) (a b) (on_) : |A ⋈ B| ≤ |A| * |B|
axiom left_join_cardinality_ge (db) (a b) (on_) : |A ⟕ B| ≥ |A|
axiom right_join_cardinality_ge (db) (a b) (on_) : |A ⟖ B| ≥ |B|
axiom cross_join_assoc_cardinality (db) (a b c) : |(A×B)×C| = |A×(B×C)|
axiom inner_join_to_where : A ⋈[cond] B = (A × B) WHERE cond
```

## Proof strategy

These are cardinality/containment properties of join implementations:
- Cross join cardinality = product of input sizes (List.bind length)
- Inner join ≤ cross join (filter can only remove rows)
- Left/right join ≥ left/right input (preserved rows + NULLs)
- `inner_join_to_where`: unfold inner join as cross join + filter

Most follow from List.filter/List.bind properties.

## Category
Join algebra — cardinality bounds. Type-independent.

## Acceptance criteria
- [ ] All 7 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: join edge cases (7 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3143-3241`
**Dependency level:** 4 (Join Algebra)

```lean
axiom inner_join_true_is_cross (db) (a b) : A ⋈[TRUE] B = A × B
axiom inner_join_false_empty (db) (a b) : A ⋈[FALSE] B = []
axiom left_join_false_all_left (db) (a b) : A ⟕[FALSE] B preserves A
axiom inner_join_empty_left (db) (a b) (on_) (h: A=[]) : A ⋈ B = []
axiom inner_join_empty_right (db) (a b) (on_) (h: B=[]) : A ⋈ B = []
axiom cross_join_empty_left (db) (a b) (h: A=[]) : A × B = []
axiom cross_join_empty_right (db) (a b) (h: B=[]) : A × B = []
```

## Proof strategy

- `true_is_cross`: filter with `fun _ => true` is identity
- `false_empty`: filter with `fun _ => false` is `[]`
- `empty_left/right`: bind over empty list is empty
- `left_join_false`: all rows from A with NULL-padded B columns

Straightforward from the implementation definitions.

## Category
Join algebra — edge cases. Type-independent.

## Acceptance criteria
- [ ] All 7 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: outer join preservation (4 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3219-3241`
**Dependency level:** 4 (Join Algebra)

```lean
axiom left_join_preserves_left (db) (a b) (on_) :
    ∀ row ∈ evalFrom db a, ∃ joinRow ∈ evalFrom db (A ⟕ B), ...

axiom right_join_preserves_right (db) (a b) (on_) :
    ∀ row ∈ evalFrom db b, ∃ joinRow ∈ evalFrom db (A ⟖ B), ...

axiom inner_subset_cross (db) (a b) (cond) :
    ∀ row ∈ evalFrom db (A ⋈ B), row ∈ evalFrom db (A × B)

axiom left_join_filter_null_is_inner (db) (a b) (on_) (rightCol) :
    LEFT JOIN + WHERE right.col IS NOT NULL ≃ INNER JOIN
```

## Proof strategy

- `left_join_preserves_left`: Every left row appears in the result,
  either matched with a right row or NULL-padded
- `inner_subset_cross`: Inner join = cross join filtered
- `left_join_filter_null_is_inner`: Classic optimization rule

## Category
Join algebra — outer join properties. Type-independent.

## Acceptance criteria
- [ ] All 4 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 11. Filter/Pushdown Axioms (6 axioms)
# ============================================================================

create_issue "Prove axioms: filter composition rules (4 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:2176-2219`
**Dependency level:** 3 (Filter/Projection)

```lean
axiom filter_and (db) (...) (p q) :
    WHERE (p AND q) = WHERE p WHERE q (filter composition)

axiom filter_commute (db) (...) (p q) :
    WHERE p WHERE q = WHERE q WHERE p

axiom filter_idempotent (db) (...) (p) :
    WHERE p WHERE p = WHERE p

axiom filter_false_empty' (db) (...) :
    WHERE FALSE = [] (empty result)
```

## Proof strategy

- `filter_and`: `List.filter (p && q) = (List.filter p).filter q`
  This is a standard list library lemma.
- `filter_commute`: `(filter p . filter q) = (filter q . filter p)`
  Follows from `filter_and` + boolean AND commutativity.
- `filter_idempotent`: `filter p . filter p = filter p`
  Follows from `filter_and` + boolean AND idempotence.
- `filter_false_empty'`: `filter (fun _ => false) = []`

## Category
Filter algebra — Level 3. Type-independent. **Required for pushdown proofs.**

## Acceptance criteria
- [ ] All 4 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: filter_join_left, filter_join_right, filter_pushdown_table" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:2086-2110`
**Dependency level:** 6 (Filter Pushdown) — **HIGH PRIORITY**

```lean
axiom filter_join_left (db) (a b) (cond filter) (items) ... :
    SELECT ... FROM (A ⋈ B) WHERE filter =
    SELECT ... FROM (A WHERE filter) ⋈ B
    -- when filter references only A's columns

axiom filter_join_right (db) (a b) (cond filter) (items) ... :
    (symmetric version for right side)

axiom filter_pushdown_table (db) (t) (filter) (items) ... :
    SELECT ... FROM t WHERE filter =
    SELECT ... FROM (SELECT * FROM t WHERE filter)
```

## Proof strategy

These are the core predicate pushdown axioms. See `PROVING_AXIOMS_PLAN.md`
Phases 3 and 6 for detailed strategy.

**Known blocker:** Double-qualification of column names in subquery wrapping
(see "Known Evaluator Limitations" in PROVING_AXIOMS_PLAN.md). May require
fixing `evalFrom`'s `.subquery` case first.

## Category
Filter pushdown — Level 6. Type-independent. **Required for optimizer correctness.**

## Acceptance criteria
- [ ] Evaluator column qualification issue resolved
- [ ] All 3 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axiom: predicate_pushdown (optimizer-level)" "$(cat <<'EOF'
## Axiom to prove

**File:** `SqlEquiv/Equiv.lean:2849`
**Dependency level:** 7 (Optimizer Preservation)

```lean
axiom predicate_pushdown (db : Database) (t : String) (p q : Expr) :
    SELECT * FROM t WHERE (p AND q) ≃ₛ
    SELECT * FROM (SELECT * FROM t WHERE p) WHERE q
```

## Proof strategy

Combines:
- `filter_and` (filter composition)
- `filter_pushdown_table` (subquery wrapping)

This is the single-table version. The full `pushdown_preserves_semantics`
axiom (in PredicatePushdown.lean) requires additionally `filter_join_left`
and `filter_join_right`.

## Category
Optimizer preservation — Level 7. **End goal for predicate pushdown.**

## Acceptance criteria
- [ ] Axiom replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 12. Subquery Axioms (18 axioms)
# ============================================================================

create_issue "Prove axioms: EXISTS/NOT EXISTS basic rules (5 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3257-3278`
**Dependency level:** 2 (Expression Evaluation)

```lean
axiom exists_empty_false (db) (row) (sel) (h: eval=[]): EXISTS → false
axiom not_exists_empty_true (db) (row) (sel) (h: eval=[]): NOT EXISTS → true
axiom exists_nonempty_true (db) (row) (sel) (h: len>0): EXISTS → true
axiom not_exists_nonempty_false (db) (row) (sel) (h: len>0): NOT EXISTS → false
axiom not_not_exists (sel) : NOT EXISTS ≃ₑ NOT (EXISTS)
```

## Proof strategy

Unfold `evalExprWithDb` for `Expr.exists`. The implementation checks
`(evalSelectWithContext db row sel).length > 0`. Direct from definition.

Type-independent.

## Category
Subquery rules — EXISTS semantics.

## Acceptance criteria
- [ ] All 5 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: IN subquery rules (5 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3281-3327`
**Dependency level:** 2 (Expression Evaluation)

```lean
axiom in_empty_subquery_false (e) (sel) : e IN (empty subquery) ≃ₑ FALSE
axiom not_in_empty_subquery_true (e) (sel) : e NOT IN (empty subquery) ≃ₑ TRUE
axiom in_subquery_as_exists (db) (row) (e) (...) : IN ≃ EXISTS (correlation)
axiom not_in_subquery_as_not_exists (db) (row) (e) (...) : NOT IN ≃ NOT EXISTS
axiom in_singleton_subquery (db) (row) (e) (sel) (...) : IN (single row) ≃ equality
```

## Proof strategy

- Empty subquery: no rows to match, IN is false
- IN → EXISTS: standard equivalence, unfold both sides
- Singleton: single-row subquery reduces to direct comparison

Type-independent.

## Category
Subquery rules — IN/EXISTS equivalence.

## Acceptance criteria
- [ ] All 5 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: subquery unnesting (IN → JOIN, NOT IN → ANTI-JOIN)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3418-3497`
**Dependency level:** 4 (depends on join semantics)

```lean
axiom in_subquery_unnest_to_join (db) (...) :
    SELECT * FROM t WHERE x IN (SELECT y FROM s) ≃ₛ
    SELECT DISTINCT t.* FROM t JOIN s ON t.x = s.y

axiom not_in_subquery_unnest_to_antijoin (db) (...) :
    SELECT * FROM t WHERE x NOT IN (SELECT y FROM s) ≃ₛ
    SELECT t.* FROM t LEFT JOIN s ON t.x = s.y WHERE s.y IS NULL

axiom in_subquery_implies_join_match (db) (row) (...) :
    IN result true → exists matching join row

axiom join_match_implies_in_subquery (db) (row) (...) :
    matching join row → IN result true
```

## Proof strategy

These are the classic subquery-to-join transformations. Complex because
they involve showing the SELECT-level and JOIN-level semantics produce
equivalent results. Depends on join semantics being well-established.

## Category
Subquery unnesting — advanced optimization rules. Type-independent.

## Acceptance criteria
- [ ] All 4 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: scalar subquery and correlated subquery rules (8 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3295-3397`
**Dependency level:** 2-3 (Expression/Query)

```lean
axiom scalar_subquery_empty_null (db) (row) (sel) (h): empty scalar → NULL
axiom exists_as_count_gt_zero (db) (row) (sel): EXISTS ↔ COUNT > 0
axiom not_exists_as_count_eq_zero (db) (row) (sel): NOT EXISTS ↔ COUNT = 0
axiom uncorrelated_subquery_independent (db) (row1 row2) (sel): uncorrelated → row-independent
axiom subquery_limit_one (db) (row) (...): scalar subquery result
axiom scalar_subquery_is_first (db) (row) (sel): scalar = first row
axiom exists_monotonic (db) (row) (sel1 sel2) (h): superset → EXISTS preserved
axiom correlated_subquery_uses_context (db) (outerRow) (sel) (...): context sensitivity
```

Also: `subquery_where_true`, `subquery_where_false` (lines 3370-3383).

## Proof strategy

Mix of straightforward (empty scalar → NULL) and subtle (correlated
subquery context sensitivity). Most follow from `evalSelectWithContext`
definition.

## Category
Subquery semantics. Type-independent.

## Acceptance criteria
- [ ] All axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 13. ORDER BY / LIMIT / OFFSET Axioms (15 axioms)
# ============================================================================

create_issue "Prove axioms: ORDER BY properties (5 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3511-3560`
**Dependency level:** 2 (Query-level)

```lean
axiom order_by_preserves_count: ORDER BY doesn't change row count
axiom order_by_empty_identity: ORDER BY on empty result is identity
axiom order_by_idempotent: ORDER BY twice with same key = ORDER BY once
axiom order_by_last_wins: two ORDER BYs, second overrides first
axiom order_by_reverse: ORDER BY ASC vs DESC reverses
```

## Proof strategy

ORDER BY is a permutation — it preserves the multiset of rows but
changes order. Count preservation follows directly. Idempotence and
last-wins follow from the sort being stable/deterministic.

## Category
ORDER BY semantics. Type-independent.

## Acceptance criteria
- [ ] All 5 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: LIMIT properties (5 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3565-3610`
**Dependency level:** 2 (Query-level)

```lean
axiom limit_zero_empty: LIMIT 0 = []
axiom limit_upper_bound: |LIMIT n result| ≤ n
axiom limit_none_all_rows: no LIMIT = all rows
axiom limit_monotonic: n ≤ m → |LIMIT n| ≤ |LIMIT m|
axiom limit_one_singleton: |LIMIT 1 (nonempty)| = 1
```

## Proof strategy

LIMIT = `List.take`. These are all standard `List.take` properties:
- `List.take 0 = []`
- `(List.take n xs).length ≤ n`
- `List.take xs.length xs = xs`
- `n ≤ m → (List.take n xs).length ≤ (List.take m xs).length`

Should be provable using Batteries/Std list lemmas.

## Category
LIMIT semantics. Type-independent.

## Acceptance criteria
- [ ] All 5 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

create_issue "Prove axioms: OFFSET and pagination properties (5 axioms)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:3612-3700`
**Dependency level:** 2 (Query-level)

```lean
axiom offset_zero_identity: OFFSET 0 = identity
axiom offset_too_large_empty: OFFSET ≥ |rows| = []
axiom offset_reduces_count: |OFFSET n result| = max(0, |result| - n)
axiom offset_monotonic: n ≤ m → |OFFSET n| ≥ |OFFSET m|
axiom limit_offset_compose: LIMIT + OFFSET composition
```

Also: `offset_limit_zero_empty`, `pagination_upper_bound`,
`pagination_identity`, `consecutive_pages`, `order_limit_deterministic`.

## Proof strategy

OFFSET = `List.drop`. These are standard `List.drop` properties:
- `List.drop 0 = id`
- `n ≥ length → List.drop n = []`
- Composition: `List.take m (List.drop n xs)`

## Category
OFFSET/pagination semantics. Type-independent.

## Acceptance criteria
- [ ] All axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

# ============================================================================
# 14. Aggregate Axioms (4 axioms)
# ============================================================================

create_issue "Prove axioms: aggregate properties (min_le_elem, max_ge_elem, distinct_count_le, distinct_idempotent)" "$(cat <<'EOF'
## Axioms to prove

**File:** `SqlEquiv/Equiv.lean:2783-2796`
**Dependency level:** 1 (Value-level)

```lean
axiom min_le_elem (n : Int) (ns : List Int) (h : n ∈ ns) :
    ns.foldl min (ns.head!) ≤ n

axiom max_ge_elem (n : Int) (ns : List Int) (h : n ∈ ns) :
    n ≤ ns.foldl max (ns.head!)

axiom distinct_count_le (vs : List Value) :
    vs.eraseDups.length ≤ vs.length

axiom distinct_idempotent (vs : List Value) :
    vs.eraseDups.eraseDups = vs.eraseDups
```

## Proof strategy

- `min_le_elem` / `max_ge_elem`: Induction on list. `foldl min` produces
  the minimum element. Standard library may have this.
- `distinct_count_le`: `eraseDups` can only remove elements, so length
  decreases. Should be in Batteries/Std.
- `distinct_idempotent`: `eraseDups` is idempotent (no dups → eraseDups
  is identity). Should be in Batteries/Std.

Partially type-sensitive (Value's BEq instance used for eraseDups).

## Category
Aggregate properties. Note: Phase 1 of PROVING_AXIOMS_PLAN already proved
some of these — verify which are still axioms.

## Acceptance criteria
- [ ] All 4 axioms replaced with `theorem`
- [ ] `lake build` succeeds
EOF
)"

echo ""
echo "============================================"
echo "Done! Created issues for all 152 axioms."
echo "Issues are grouped into 14 categories."
echo "============================================"
