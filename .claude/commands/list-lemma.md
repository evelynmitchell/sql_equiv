# /list-lemma

Prove a list algebra lemma (filter, map, flatMap, filterMap, length, etc.) for use in SQL equivalence proofs.

## Usage

- `/list-lemma <statement>` — Prove the specified list lemma

## Instructions

### Background

SQL equivalence proofs reduce to list algebra: `evalSelect` produces lists via `map`/`filter`/`flatMap`/`filterMap`. List algebra lemmas are the building blocks that close these proofs. They live in `SqlEquiv/SemanticsCore.lean` (private, same-file use) or are made public when needed across files.

### Steps

1. **Determine where the lemma belongs:**

   | Scope | Visibility | File |
   |-------|-----------|------|
   | Used only in SemanticsCore proofs | `private theorem` | `SqlEquiv/SemanticsCore.lean` |
   | Used in Semantics.lean proofs | `theorem` (public) | `SqlEquiv/SemanticsCore.lean` |
   | Used only in StatementAxioms proofs | `private theorem` | `SqlEquiv/Equiv/StatementAxioms.lean` |

   **Rule:** If it might be needed across files, don't mark it `private`.

2. **Write the lemma using the standard template.** Almost all list lemmas follow one of these patterns:

### Template 1: Simple structural property (identity, commutativity)

```lean
private theorem list_<name> {α : Type} (l : List α) : <LHS> = <RHS> := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [List.<op>_cons, ih]
```

### Template 2: Property with membership precondition

```lean
private theorem list_<name> {α : Type} (l : List α) (p : α → Bool)
    (h : ∀ a ∈ l, <predicate> a) : <LHS> = <RHS> := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp [List.<op>_cons, h a List.mem_cons_self,
          ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
```

### Template 3: Filter/predicate lemma (case-split on Bool)

```lean
private theorem list_<name> {α : Type} (l : List α) (p q : α → Bool) :
    <LHS> = <RHS> := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.<op>_cons]
    cases hp : p a <;> simp [ih]
```

### Template 4: Length/arithmetic bound

```lean
private theorem list_<name> {α β : Type} (l : List α) (f : α → List β) (n : Nat)
    (h : ∀ x ∈ l, (f x).length = n) :
    (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
    omega
```

### Template 5: Congruence with membership

```lean
private theorem list_<name> {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self]
    exact congrArg _ (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))
```

3. **Common tactics and their uses:**

   | Tactic | When to use |
   |--------|-------------|
   | `induction l with \| nil => rfl \| cons a rest ih =>` | Every list lemma (structural induction) |
   | `simp [List.op_cons, ih]` | After induction, unfold the list operation and apply IH |
   | `cases hp : p a <;> simp [ih]` | When proof branches on a Bool predicate result |
   | `cases hfx : f x with \| none => ... \| some b => ...` | When proof branches on an Option result |
   | `h a List.mem_cons_self` | Apply membership precondition to the head element |
   | `ih (fun x hx => h x (List.mem_cons_of_mem a hx))` | Pass membership precondition to the IH for the tail |
   | `omega` | Close arithmetic goals (length bounds, Nat inequalities) |
   | `congr 1` / `congrArg` | Structural congruence when outer function matches |
   | `rw [Bool.and_comm]` / `ext r` | For filter algebra (AND commutativity, extensionality) |

4. **Build and verify:**
   ```bash
   lake build sql_equiv_test
   ```

### Important Notes

- `ring` tactic is NOT available (no Mathlib). For `n + m * n = (m + 1) * n`, use `rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]` or `omega`.
- `set` tactic is NOT available. Use `generalize` or `let` instead.
- `by_cases` on Bool produces `decide` wrappers. Use `cases hp : p a` instead.
- `List.filter_congr` is better than `funext` when you need membership info in the hypothesis.
- If the lemma will be used from another file, do NOT mark it `private`.
- Existing public list lemmas in SemanticsCore: `list_filter_and_eq`, `list_flatMap_filter_comm`, `list_filter_filterMap_comm`.

### Related Commands

- `/proof` — Interactive proof assistance
- `/bridge` — Bridge theorems connecting WFR to Core
- `/build` — Build the project
