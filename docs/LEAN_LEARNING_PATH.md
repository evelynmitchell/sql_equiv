# Lean 4 Learning Path for sql_equiv Contributors

A practical guide to Lean 4 gotchas, oriented toward someone who knows SQL and
wants to contribute proofs to this codebase. Not a Lean textbook -- just the
things that will trip you up here.

---

## How to Use This Document

**If you're brand new to Lean:** Read Levels 0-2 first, then try the exercises.
Come back to Levels 3-5 when you're ready to write real proofs.

**If you know some Lean:** Skip to Level 3 (the project-specific patterns) and
the Gotchas Reference at the end.

**If you just need to read proofs, not write them:** Level 1 + the Gotchas
Reference is enough.

---

## Level 0: Lean Basics You Must Know

### The Type System in 30 Seconds

```lean
-- Everything has a type
42 : Int          -- 42 is an Int
"hello" : String  -- "hello" is a String
true : Bool       -- true is a Bool

-- Functions have arrow types
def add (a b : Int) : Int := a + b
-- add : Int -> Int -> Int

-- Propositions are types too
-- "a = b" is a *type*. A proof of "a = b" is a *value* of that type.
-- If you can construct a value, the proposition is true.
```

### Inductive Types (Our Core Tool)

This is how `SqlType`, `Value`, `Expr`, etc. are defined:

```lean
inductive SqlType where
  | int
  | string
  | bool
  | unknown
```

**Gotcha #1:** Every `match` on an inductive must cover ALL constructors.
When we add `float`, `decimal`, etc., every existing `match` on `SqlType`
and `Value` will break. Lean's exhaustiveness checker is your friend here --
it flags every incomplete match.

### Pattern Matching

```lean
def Value.isNull : Value -> Bool
  | .null _ => true
  | _ => false  -- wildcard catches everything else
```

**Gotcha #2:** The wildcard `_` catches everything, including constructors
you add later. This means some matches WON'T break when you add types --
but they might silently do the wrong thing. Always audit wildcard matches
when adding new constructors.

### `#check` and `#eval` -- Your Best Friends

```lean
#check Value.isNull        -- shows the type
#eval Value.isNull (.int 5)  -- runs the function
```

Use these constantly in VS Code (or the Lean web editor) to explore.

---

## Level 1: Reading Proofs

### Theorem Statements

Every theorem in `Equiv.lean` follows this shape:

```lean
theorem evalBinOp_add_comm (l r : Option Value) :
    evalBinOp .add l r = evalBinOp .add r l := by
  ...
```

Read this as: "For ALL possible values `l` and `r`, evaluating `l + r`
gives the same result as evaluating `r + l`."

The `by` keyword starts a proof in *tactic mode*.

### The Proof State

When you're inside a `by` block, Lean tracks:
- **Goal:** what you still need to prove
- **Context:** hypotheses you can use

VS Code shows this in the Lean Infoview panel. Place your cursor at
different points in the proof to see how the state changes.

### Reading Case Analysis Proofs

Most proofs in this codebase look like this:

```lean
theorem evalBinOp_add_comm (l r : Option Value) :
    evalBinOp .add l r = evalBinOp .add r l := by
  match l, r with
  | some (.int a), some (.int b) =>
    simp only [evalBinOp, Int.add_comm]
  | some (.int _), some (.bool _) => rfl
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.null _) => rfl
  ...
```

**What's happening:**
1. `match l, r with` -- split into every possible combination of `l` and `r`
2. `simp only [evalBinOp, Int.add_comm]` -- unfold the definition and use
   `Int.add_comm` to close the goal (this is the interesting case)
3. `rfl` -- "both sides are literally identical after evaluation" (the trivial
   cross-type cases where both sides return NULL)

**Gotcha #3:** `rfl` only works when Lean can compute both sides to the
same normal form. If it fails, you need to provide more reasoning. Try
`simp` or `decide` before escalating.

### Our Custom Tactics

These are defined in `Tactics.lean` and save you from writing boilerplate:

| Tactic | What it does | When to use |
|--------|-------------|-------------|
| `sql_equiv` | Tries reflexivity, commutativity, associativity, De Morgan, distributivity, absorption, identity, complement, arithmetic, comparison rules | First thing to try |
| `sql_equiv!` | All of the above plus normalization and `native_decide` | When `sql_equiv` fails |
| `sql_simp` | Unfolds `ExprEquiv`, `SelectEquiv`, etc. | When you need to see inside equivalence definitions |
| `sql_refl` | Proves `a ≃ₑ a` | Obvious |
| `sql_symm` | Flips `a ≃ₑ b` to `b ≃ₑ a` | When your goal is backwards |
| `sql_trans b` | Chains `a ≃ₑ b` and `b ≃ₑ c` to get `a ≃ₑ c` | Multi-step proofs |
| `sql_congr` | Descends into subexpressions of binary/unary ops | When only one operand differs |
| `sql_rw_demorgan` | Applies De Morgan's laws | Specific rewrite |
| `sql_rw_distrib` | Applies distributivity | Specific rewrite |
| `sql_rw_null` | Applies NULL propagation rules | NULL-related proofs |

**Gotcha #4:** `sql_equiv` is a decision procedure, not magic. It only knows
about the rules listed in `Tactics.lean`. If your theorem involves new patterns
(like float arithmetic), you'll need to add support to the tactic or prove
it manually.

---

## Level 2: Writing Your First Proof

### The `sorry` Workflow

`sorry` is a placeholder that accepts any proof obligation. Use it to
sketch proofs incrementally:

```lean
theorem my_theorem : P := by
  sorry  -- compiles but with a warning
```

**Gotcha #5:** `sorry` marks the entire file as having unproven claims.
NEVER commit `sorry` -- use `axiom` instead if you genuinely need to
defer a proof (with a comment explaining why).

### The Case-Analysis Pattern (You'll Use This Constantly)

For any theorem about `Value` operations:

```lean
theorem my_value_theorem (v1 v2 : Value) : P v1 v2 := by
  cases v1 with
  | int a => cases v2 with
    | int b => ...      -- int, int: interesting case
    | string b => ...   -- int, string: usually rfl (returns null)
    | bool b => ...     -- int, bool: usually rfl
    | null b => ...     -- int, null: usually rfl
  | string a => cases v2 with
    | int b => ...
    ...
```

Currently 4x4 = 16 cases. After full type expansion (11 constructors +
`none`), 12x12 = 144 cases. The cross-type cases are almost all `rfl`.

**Gotcha #6:** When you add a new type, you must add cases for it in
EVERY existing proof that does `cases v`. Lean will tell you which cases
are missing -- look for "missing cases" errors.

### Trying a Real Exercise

Open `SqlEquiv/Equiv.lean` in your editor and try this:

```lean
-- Scroll to the end and add:
theorem my_first_theorem :
    Expr.binOp .and (Expr.lit (.bool true)) a ≃ₑ a := by
  sql_equiv
```

If `sql_equiv` doesn't close it, try:
```lean
  exact true_and a
```

This works because `true_and` is already proven in the file.

---

## Level 3: Project-Specific Patterns

### Pattern 1: The 25-Case Binary Operation Proof

This is the bread and butter of `Equiv.lean`. Here's the template:

```lean
theorem evalBinOp_FOO_comm (l r : Option Value) :
    evalBinOp .FOO l r = evalBinOp .FOO r l := by
  match l, r with
  -- Same-type cases (the interesting ones)
  | some (.int a), some (.int b) => simp only [evalBinOp, COMMUTATIVITY_LEMMA]
  | some (.string a), some (.string b) => simp only [evalBinOp, COMMUTATIVITY_LEMMA]
  | some (.bool a), some (.bool b) => simp only [evalBinOp, COMMUTATIVITY_LEMMA]
  -- Cross-type cases (trivial: both sides evaluate to the same null/error)
  | some (.int _), some (.string _) => rfl
  | some (.string _), some (.int _) => rfl
  ... (12 more cross-type pairs)
  -- NULL cases
  | some (.null _), _ => rfl  -- or: cases r <;> rfl
  | _, some (.null _) => rfl
  | none, _ => rfl
  | _, none => rfl
```

**Gotcha #7:** The order of match arms matters for readability but not
correctness. Lean tries them top-down. Put interesting cases first, then
bulk the trivial ones.

### Pattern 2: Axioms vs Theorems

```lean
-- AXIOM: assumed true without proof (152 of these right now)
axiom join_comm_full (t1 t2 : Table) (cond : Expr) :
  innerJoin t1 t2 cond ~ innerJoin t2 t1 cond

-- THEOREM: actually proven (153 of these right now)
theorem evalBinOp_and_comm (l r : Option Value) :
    evalBinOp .and l r = evalBinOp .and r l := by
  ...actual proof...
```

**Gotcha #8:** Axioms are promises. They're sound only if they're true.
One wrong axiom makes the entire proof system unsound (you can prove
anything from `False`). When you can, convert axioms to theorems.

### Pattern 3: Mutual Inductives

`Expr`, `SelectStmt`, `FromClause`, etc. are mutually recursive:

```lean
mutual
  inductive Expr where ...
  inductive SelectStmt where ...
  inductive FromClause where ...
end
```

**Gotcha #9:** Lean has limitations with mutual inductives:
- No automatic `DecidableEq` -- that's why we hand-wrote `.beq` for all of them
- Structural recursion must be explicit -- `partial def` is used for many functions
- Induction principles are limited -- some proofs need `match` instead of `induction`

### Pattern 4: `partial def` Everywhere

```lean
partial def Expr.toReprStr : Expr -> String
```

**Gotcha #10:** `partial def` means Lean doesn't verify termination.
This is fine for evaluation functions (we trust they terminate), but
you CANNOT use `partial def` results directly in proofs. If you need
to prove something about a `partial def`, you typically need to
reformulate it as a total function or use `axiom`.

### Pattern 5: The Equivalence Notation

```lean
-- These are defined in Equiv.lean:
notation:50 e1 " ≃ₑ " e2 => ExprEquiv e1 e2
notation:50 s1 " ≃ₛ " s2 => SelectEquiv s1 s2
notation:50 q1 " ≃_q " q2 => QueryEquiv q1 q2
```

`ExprEquiv e1 e2` means "for every database and row, evaluating `e1`
and `e2` gives the same result."

---

## Level 4: Surviving the Type Expansion

When we add float, decimal, date, time, timestamp, interval, binary:

### What Breaks

1. **Every `match` on `Value`** in Semantics.lean, Optimizer.lean, etc.
   Lean flags these immediately.

2. **Every case-analysis proof** in Equiv.lean. Each theorem that matches
   on `Value` needs new arms for the new constructors.

3. **`BEq` instances** need new cases in the hand-written `.beq` functions.

### What Doesn't Break (But Should Be Audited)

1. **Wildcard matches** (`| _ => ...`) -- these compile but might give wrong
   results for new types. SEARCH for `| _ =>` after adding types.

2. **Axioms** -- they compile regardless of types. But their meaning might
   need updating if the expanded type system changes what they claim.

### The Cross-Type Elimination Strategy

Instead of writing 64 cross-type `rfl` cases per theorem, we'll prove
one helper lemma:

```lean
lemma mismatched_types_null (op : BinOp) (v1 v2 : Value)
  (h : v1.sqlType != v2.sqlType) :
  evalBinOp op (some v1) (some v2) = some (Value.null none) := by
  cases v1 <;> cases v2 <;> simp_all [evalBinOp, Value.sqlType]
```

Then each commutativity proof becomes:
1. ~8 same-type cases (one per type) -- needs actual reasoning
2. Cross-type: invoke `mismatched_types_null` once
3. NULL/none cases: a few `rfl`s

**Gotcha #11:** This strategy only works if `evalBinOp` actually returns
null for mismatched types. It does today, and we must maintain this
invariant when adding new types. If a new type introduces coercion
(e.g., `int + float` promotes to float), those coercion cases need
their own proof arms.

### The Coercion Complication

SQL standard says `int + float` coerces the int to float. This means:
- `evalBinOp .add (some (.int 1)) (some (.float 2.0))` returns `some (.float 3.0)`
- `evalBinOp .add (some (.float 2.0)) (some (.int 1))` returns `some (.float 3.0)`

These are NOT trivially `rfl` -- you need to prove the coercion is
symmetric. Each coercion pair (int/float, int/decimal, decimal/float)
needs its own commutativity lemma.

---

## Level 5: Common Lean Gotchas Reference

Quick-reference for things that will confuse you.

### Build & Tooling

| Gotcha | Symptom | Fix |
|--------|---------|-----|
| `lake clean` wipes everything | 20+ minute rebuild | NEVER run `lake clean` unless absolutely necessary. Use `lake build` for incremental builds. |
| Unused variable warning | `unused variable 'h1'` | Prefix with underscore: `_h1` |
| VS Code infoview not updating | Stale proof state | Save the file, wait for Lean server to catch up |
| Import order matters | `unknown identifier` | Check imports at top of file. We use `import SqlEquiv.Ast` etc. |
| `lake build` seems stuck | Long output on first build | Normal for first build. Subsequent builds are fast. |

### Proof Writing

| Gotcha | Symptom | Fix |
|--------|---------|-----|
| `rfl` fails | "type mismatch" | Both sides aren't definitionally equal. Try `simp` or `decide`. |
| `simp` loops | Lean hangs | Use `simp only [specific_lemma]` to limit what simp tries. |
| `cases` gives weird names | Auto-generated names like `a_1` | Use `cases x with \| constructor => ...` for named cases. |
| `match` inside `by` confuses goals | Goal doesn't simplify | Use `cases` tactic instead of term-mode `match` inside tactic mode. |
| Can't find a lemma | Proof stuck | Use `#check`, `exact?`, or `apply?` to search. |
| `omega` fails on `Int` | "omega failed" | `omega` works on `Nat` and `Int` but needs linear arithmetic. For nonlinear, try `decide` or manual case analysis. |
| `native_decide` fails | Timeout or error | The proposition may involve infinite types. Only works for finite decidable props. |
| Theorem compiles with `sorry` but fails without | Your proof doesn't actually prove the goal | Remove `sorry` and read the error. Check the goal in infoview. |

### Type System

| Gotcha | Symptom | Fix |
|--------|---------|-----|
| `Float` equality is weird | `NaN != NaN` | IEEE 754 semantics. `Float.beq` follows this. Our proofs must account for it. |
| `String` comparison is lex | Dates as strings compare correctly only in ISO format | We rely on ISO-8601 format. Enforce at parse time. |
| `Option Value` vs `Value` | Type mismatch in `evalBinOp` | `evalBinOp` takes `Option Value` (none = missing). Don't confuse with `Value.null` (SQL NULL). |
| `Nat` vs `Int` | Subtraction doesn't work as expected on `Nat` | `5 - 7 = 0` for `Nat` (no negatives). Use `Int` for SQL integers. |
| `partial def` in proofs | Can't unfold | Lean won't unfold `partial def` in proofs. Need to restructure as total or use axiom. |

### SQL-Specific

| Gotcha | Symptom | Fix |
|--------|---------|-----|
| Three-valued logic | `not unknown != unknown` confusion | `Trilean.not .unknown = .unknown` by definition. This is correct per SQL standard. |
| `NULL = NULL` is `NULL`, not `TRUE` | Proof about equality fails | SQL NULL propagates. `Value.eq (.null _) _ = none`. |
| `FALSE AND NULL = FALSE` | Unexpected short-circuit | SQL AND short-circuits on FALSE. `Trilean.and .false .unknown = .false`. |
| Bag vs set semantics | Duplicate rows matter | Our `Table = List Row` uses bag semantics (duplicates exist). UNION removes them, UNION ALL doesn't. |

---

## Suggested Learning Sequence

### Week 1: Read Only

1. Read this document (Levels 0-2)
2. Open `SqlEquiv/Equiv.lean` in VS Code with the Lean extension
3. Place cursor inside proofs and watch the Infoview panel
4. Read 5 theorems: `evalBinOp_and_comm`, `evalBinOp_add_comm`,
   `and_comm`, `or_comm`, `not_not`
5. Read Tutorial 01 (`docs/tutorials/01-first-proof.md`)
6. Read Tutorial 07 (`docs/tutorials/07-formal-methods-intro.md`)

### Week 2: Copy and Modify

1. Try the exercise from Level 2 (prove `true AND a = a`)
2. Pick a theorem in Equiv.lean, copy it, change the operator, re-prove it
3. Deliberately break a proof (remove a case) and see what Lean says
4. Try `sql_equiv` on various goals to see what it can and can't handle
5. Read the Tactics.lean examples section (lines 435-546)

### Week 3: Independent Proofs

1. Find a `sorry` or `axiom` in the codebase
2. Try to prove it (start with the easiest-looking one)
3. Use `exact?` and `apply?` when stuck
4. Ask Claude for help when the Lean error messages are cryptic
5. Read Tutorial 09 (`docs/tutorials/09-manual-proofs.md`)

### Week 4: Ready for Type Expansion

1. Try adding a dummy type to `SqlType` (e.g., `| dummy`) on a branch
2. Follow the exhaustiveness errors through every file
3. See how many cases each proof needs
4. Revert the change
5. You're now ready to work on Batch 1 of `SQL_TYPES_CONCRETE_PLAN.md`

---

## External Resources

### Essential

- **Lean 4 Playground**: https://live.lean-lang.org/ -- test snippets without local setup
- **Theorem Proving in Lean 4**: https://lean-lang.org/theorem_proving_in_lean4/ -- official tutorial, chapters 1-5 are most relevant
- **Lean 4 Tactic Reference**: https://lean-lang.org/lean4/doc/tactics.html -- the full list

### Helpful

- **Mathematics in Lean**: https://leanprover-community.github.io/mathematics_in_lean/ -- overkill for us but great if you enjoy it
- **Lean Zulip Chat**: https://leanprover.zulipchat.com/ -- the community; search before asking
- **Mathlib docs**: https://leanprover-community.github.io/mathlib4_docs/ -- we don't use Mathlib, but its patterns are standard

### Not Needed

- Lean 3 resources (syntax is different)
- Category theory (not relevant here)
- Dependent type theory papers (unless you're curious)

---

## Quick Troubleshooting

**"I changed a file and now nothing builds"**
- Run `lake build` and read the FIRST error. Fix it, rebuild. Don't try to fix everything at once.

**"The proof used to work and now it doesn't"**
- Did you change a definition that the proof depends on? Lean proofs are sensitive to definitional changes.

**"I don't understand the error message"**
- Post the error in Lean Zulip or ask Claude. Include the goal state from Infoview.

**"Which tactic should I try?"**
- Try in this order: `rfl` -> `simp` -> `decide` -> `cases` -> manual reasoning
- For SQL equivalences: `sql_equiv` -> `sql_equiv!` -> manual

**"The proof is 200 lines of cases and I'm going insane"**
- You're doing it right. This is what formal verification of SQL looks like.
- The `mismatched_types_null` lemma (Level 4) will help enormously once implemented.

---

*Created: 2026-02-06*
*Complements: Tutorial 08 (lean-proofs.md), Tactics.lean, PLAN_expand_types.md*
