# Tutorial 8: Reading and Writing Proofs in Lean

**Time:** 60 minutes
**Prerequisites:** Tutorial 7

---

## Learning Objectives

By the end of this tutorial, you will:
- Read Lean theorem statements and understand what they claim
- Follow proof scripts step by step
- Write simple proofs for SQL properties
- Know when to use tactics vs term-mode proofs

---

## Outline

### 1. Lean Basics (10 min)
- Types and terms
- Function definitions
- Pattern matching
- The `Prop` type (propositions)

### 2. Reading Theorem Statements (10 min)
- Universal quantification: `∀ (x : T), P x`
- Implication: `P → Q`
- Equality: `a = b`
- Custom predicates: `QueryEquiv q1 q2`
- Parsing complex statements

### 3. Proof Tactics (15 min)
- `intro`: Introduce hypotheses
- `apply`: Use a lemma
- `exact`: Provide the exact proof term
- `simp`: Simplification
- `cases`: Case analysis
- `induction`: Structural induction
- `rfl`: Reflexivity (a = a)
- `rw`: Rewriting with equalities

### 4. Worked Examples (15 min)

#### Example 1: AND Commutativity
```lean
theorem and_comm (p q : Bool) : p && q = q && p := by
  cases p <;> cases q <;> rfl
```

#### Example 2: Filter Composition
```lean
theorem filter_filter (p q : Row → Bool) (rows : List Row) :
  (rows.filter p).filter q = rows.filter (fun r => p r && q r) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp [List.filter]
    cases hp : p r <;> cases hq : q r <;> simp [hp, hq, ih]
```

#### Example 3: SQL-specific Property
```lean
theorem where_and_split (t : Table) (p q : Expr) :
  evalWhere (p AND q) t = evalWhere q (evalWhere p t) := by
  -- Proof structure walkthrough
```

### 5. Writing Your Own Proofs (10 min)
- Start with the goal
- Work backwards
- Use `sorry` as placeholder
- Check partial proofs frequently
- Common patterns for SQL theorems

---

## Exercises

1. **Read the theorem**: What does this claim?
   ```lean
   theorem join_comm (a b : Table) (cond : Expr) :
     innerJoin a b cond = innerJoin b a cond
   ```

2. **Fill in the proof**:
   ```lean
   theorem or_self (p : Bool) : p || p = p := by
     sorry
   ```

3. **Induction exercise**: Prove for lists:
   ```lean
   theorem filter_length_le (p : α → Bool) (xs : List α) :
     (xs.filter p).length ≤ xs.length := by
     sorry
   ```

4. **SQL exercise**: Complete the proof:
   ```lean
   theorem select_star_from_t_equiv (t : TableRef) :
     parseAndEval "SELECT * FROM t" = parseAndEval "SELECT t.* FROM t" := by
     sorry
   ```

---

## Tactic Reference Card

| Tactic | Purpose | Example |
|--------|---------|---------|
| `intro x` | Introduce ∀ or → | `∀ x, P x` → `P x` with `x` in context |
| `apply h` | Apply hypothesis/lemma | If `h : P → Q` and goal is `Q`, new goal is `P` |
| `exact e` | Provide exact proof | When `e` has exactly the goal type |
| `rfl` | Prove `a = a` | Reflexivity |
| `simp` | Simplify | Applies simp lemmas |
| `simp [h]` | Simplify with hint | Uses `h` for rewriting |
| `cases x` | Case split | For inductive types |
| `induction x` | Induction | With `with` for naming |
| `rw [h]` | Rewrite | Replace using equation |
| `constructor` | Build structure | For ∧, ∃, etc. |
| `left`/`right` | Choose disjunct | For ∨ goals |
| `sorry` | Admit (cheat) | Placeholder, marks proof incomplete |

---

## Common Patterns in sql_equiv

### Pattern 1: Case Analysis on Expression Type
```lean
theorem expr_property (e : Expr) : P e := by
  cases e with
  | lit v => -- handle literals
  | col c => -- handle columns
  | binOp op l r => -- handle binary ops
  -- ...
```

### Pattern 2: Induction on List (Rows)
```lean
theorem row_list_property (rows : List Row) : P rows := by
  induction rows with
  | nil => -- base case: empty list
  | cons r rs ih => -- inductive case: use ih
```

### Pattern 3: Rewriting with Equivalence
```lean
theorem transform_preserves (q : Query) : eval (transform q) = eval q := by
  simp [transform]
  rw [some_equivalence_lemma]
  -- ...
```

---

## Pitfalls

| Mistake | Symptom | Fix |
|---------|---------|-----|
| Wrong goal | Tactic fails | Check goal with `#check` |
| Missing case | Incomplete proof | Add all constructors |
| Infinite loop | Lean hangs | Check termination |
| Type mismatch | Red squiggles | Verify types match |
| `sorry` left in | Warning | Complete the proof |
