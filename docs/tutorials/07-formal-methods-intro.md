# Tutorial 7: Introduction to Formal Methods for Programmers

**Time:** 45 minutes
**Prerequisites:** Tutorials 1-6, programming experience

---

## What You'll Learn

- What formal methods are (and aren't)
- Why they matter for SQL equivalence
- Basic concepts: specifications, properties, proofs
- How sql_equiv uses formal verification internally

---

## What Are Formal Methods?

**Formal methods** are mathematical techniques for specifying, developing, and verifying software.

### The Informal Way (How Most Code is Verified)

```python
def add(a, b):
    return a + b

# Test it
assert add(2, 3) == 5
assert add(-1, 1) == 0
assert add(0, 0) == 0
# Looks good! Ship it.
```

**Problem**: We only tested 3 inputs. What about the other ~18 quintillion 64-bit integer pairs?

### The Formal Way

```lean
def add (a b : Int) : Int := a + b

-- Prove a property about ALL inputs
theorem add_comm (a b : Int) : add a b = add b a := by
  simp [add, Int.add_comm]
```

**Advantage**: This proves commutativity for *every* possible pair of integers, not just the ones we tested.

---

## Why Formal Methods for SQL?

### Testing SQL Equivalence is Hard

Consider proving these are equivalent:

```sql
SELECT * FROM t WHERE a = 1 AND b = 2
SELECT * FROM t WHERE b = 2 AND a = 1
```

To test this, you'd need to:
1. Generate all possible tables `t`
2. Run both queries on each table
3. Compare results

But "all possible tables" is infinite! Even restricting to small tables with limited values, the space is astronomical.

### Formal Verification Covers Everything

Instead of testing, we *prove*:

```
∀ database D, ∀ table t:
  eval("SELECT * FROM t WHERE a=1 AND b=2", D)
  =
  eval("SELECT * FROM t WHERE b=2 AND a=1", D)
```

This single proof covers every possible database state.

---

## Core Concepts

### 1. Specification

A **specification** describes *what* a system should do, precisely and unambiguously.

**Informal specification:**
> "The query should return all orders from VIP customers"

**Formal specification:**
```
result = { o ∈ orders | ∃ c ∈ vip_customers : o.customer_id = c.id }
```

The formal version uses set notation and is mathematically precise.

### 2. Implementation

The **implementation** is the actual code (or SQL query):

```sql
SELECT o.*
FROM orders o
WHERE o.customer_id IN (SELECT id FROM vip_customers)
```

### 3. Verification

**Verification** proves the implementation satisfies the specification:

```
Prove: eval(query) = { o ∈ orders | ∃ c ∈ vip_customers : o.customer_id = c.id }
```

If we can prove this, we *know* the query is correct—not just for our test cases, but for all possible data.

---

## How sql_equiv Represents SQL Formally

### Abstract Syntax Trees (ASTs)

SQL queries become data structures:

```sql
SELECT name FROM users WHERE age > 21
```

Becomes:

```lean
SelectStmt.mk
  (distinct := false)
  (items := [SelectItem.exprItem (Expr.col "name") none])
  (fromClause := some (FromClause.table ⟨"users", none⟩))
  (whereClause := some (Expr.binOp .gt (Expr.col "age") (Expr.lit (Value.int 21))))
  (groupBy := [])
  (having := none)
  (orderBy := [])
  (limit := none)
  (offset := none)
```

### Semantics (What Queries Mean)

We define what it means to *evaluate* a query:

```lean
/-- Evaluate a SELECT statement against a database -/
def evalSelect (db : Database) (stmt : SelectStmt) : Result :=
  let rows := evalFrom db stmt.fromClause
  let filtered := rows.filter (evalWhere db stmt.whereClause)
  let grouped := groupBy stmt.groupBy filtered
  let projected := project stmt.items grouped
  applyOrderLimit stmt.orderBy stmt.limit stmt.offset projected
```

This is the formal **semantics**—a precise definition of what every SQL construct means.

### Equivalence

Two queries are equivalent when they produce the same result for all databases:

```lean
def QueryEquiv (q1 q2 : SelectStmt) : Prop :=
  ∀ db : Database, evalSelect db q1 = evalSelect db q2
```

---

## Types of Proofs in sql_equiv

### 1. Algebraic Properties

These are fundamental laws about SQL operations:

```lean
-- AND is commutative
theorem and_comm (p q : Expr) :
  filterBy (p AND q) = filterBy (q AND p)

-- JOIN is associative (for INNER joins)
theorem join_assoc (a b c : FromClause) :
  (a JOIN b) JOIN c ≡ a JOIN (b JOIN c)

-- Filter can be pushed through projection
theorem filter_project (pred : Expr) (cols : List Column) :
  filter pred (project cols rows) = project cols (filter pred rows)
```

### 2. Transformation Correctness

These prove that specific rewrites are valid:

```lean
-- IN subquery can be converted to EXISTS
theorem in_to_exists (outer : SelectStmt) (col : ColumnRef) (subq : SelectStmt) :
  SELECT * FROM outer WHERE col IN (subq)
  ≡
  SELECT * FROM outer WHERE EXISTS (SELECT 1 FROM subq WHERE subq.col = outer.col)
```

### 3. Optimizer Soundness

These prove the optimizer doesn't change query meaning:

```lean
-- Predicate pushdown preserves semantics
theorem pushdown_preserves_semantics (pred : Expr) (from_ : FromClause) :
  let result := pushPredicateDown pred from_
  ∀ db, evalWithFilter db result.pushedFrom result.remaining
        = evalWithFilter db from_ (some pred)
```

---

## Reading Formal Statements

Let's decode some formal notation:

### Universal Quantification (∀)

```
∀ x : T, P(x)
```

"For all x of type T, property P holds"

Example:
```lean
∀ db : Database, evalSelect db q1 = evalSelect db q2
```
"For all databases db, evaluating q1 equals evaluating q2"

### Existential Quantification (∃)

```
∃ x : T, P(x)
```

"There exists an x of type T such that P holds"

Example:
```lean
∃ row ∈ orders, row.customer_id = 5
```
"There exists a row in orders with customer_id = 5"

### Implication (→)

```
P → Q
```

"If P then Q"

Example:
```lean
hasOnlyInnerJoins from_ → canReorderJoins from_
```
"If from_ has only inner joins, then joins can be reordered"

### Conjunction (∧) and Disjunction (∨)

```
P ∧ Q    -- P and Q
P ∨ Q    -- P or Q
```

### Set Membership (∈)

```
x ∈ S
```

"x is a member of set S"

---

## Proof Techniques

### 1. Direct Proof

Show the conclusion follows from definitions:

```lean
theorem and_comm (a b : Expr) :
  eval (a AND b) = eval (b AND a) := by
  simp [eval]  -- Expand definition
  exact Bool.and_comm (eval a) (eval b)  -- Use known fact about booleans
```

### 2. Case Analysis

Consider each possible case:

```lean
theorem not_not (a : Expr) :
  eval (NOT (NOT a)) = eval a := by
  cases eval a  -- Two cases: true or false
  · simp        -- If a is true: NOT (NOT true) = true ✓
  · simp        -- If a is false: NOT (NOT false) = false ✓
```

### 3. Induction

For recursive structures, prove base case and inductive step:

```lean
theorem flatten_and_equiv (e : Expr) :
  eval e = eval (unflattenAnd (flattenAnd e)) := by
  induction e with
  | lit v => simp [flattenAnd, unflattenAnd]  -- Base case
  | binOp And l r ih_l ih_r =>  -- Inductive case
    simp [flattenAnd, unflattenAnd]
    rw [ih_l, ih_r]  -- Use induction hypotheses
  | _ => simp [flattenAnd, unflattenAnd]  -- Other cases
```

### 4. Axioms

Some facts are assumed (for now) rather than proven:

```lean
-- We assume this is true (proof deferred)
axiom join_assoc (a b c : FromClause) :
  (a JOIN b) JOIN c ≡ a JOIN (b JOIN c)
```

Axioms are placeholders for proofs we haven't written yet. They're sound to use, but could theoretically be wrong if we made a mistake.

---

## The Trust Stack

What do you trust when using sql_equiv?

```
┌─────────────────────────────────────────────────────────┐
│ 1. You trust the theorem statement                      │
│    "Are we asking the right question?"                  │
├─────────────────────────────────────────────────────────┤
│ 2. You trust the semantics definition                   │
│    "Does our eval function match real SQL behavior?"    │
├─────────────────────────────────────────────────────────┤
│ 3. You trust the Lean proof checker                     │
│    "Did the proof actually check out?"                  │
├─────────────────────────────────────────────────────────┤
│ 4. You trust the parser/pretty-printer roundtrip        │
│    "Did we parse your SQL correctly?"                   │
└─────────────────────────────────────────────────────────┘
```

### Where Bugs Can Hide

1. **Specification bugs**: We prove the wrong property
2. **Semantics bugs**: Our `eval` doesn't match real SQL
3. **Axiom bugs**: An axiom we assumed is actually false
4. **Parser bugs**: We misparse the SQL

Formal methods reduce bugs dramatically but don't eliminate all categories.

---

## Comparison: Testing vs Formal Verification

| Aspect | Testing | Formal Verification |
|--------|---------|---------------------|
| Coverage | Sample of inputs | All inputs |
| Confidence | "No bugs found" | "No bugs exist" |
| False positives | None | None (if proved) |
| False negatives | Possible (missed bugs) | None (complete) |
| Effort | Write tests | Write proofs |
| Maintenance | Update tests | Update proofs |
| Finds bugs in | Implementation | Spec + Implementation |

### When to Use Each

**Use testing when:**
- Quick feedback needed
- Exploring behavior
- Property is hard to formalize

**Use formal verification when:**
- Correctness is critical
- Testing space is infinite
- You need guarantees, not confidence

**Best approach:** Use both! Test for quick feedback, prove for assurance.

---

## Practical Example: Verifying a Transformation

Let's trace through how sql_equiv proves AND is commutative.

### Step 1: Parse Both Queries

```sql
Q1: SELECT * FROM t WHERE a = 1 AND b = 2
Q2: SELECT * FROM t WHERE b = 2 AND a = 1
```

Becomes ASTs with WHERE clauses:
```
Q1.where = BinOp(AND, BinOp(EQ, Col("a"), Lit(1)),
                      BinOp(EQ, Col("b"), Lit(2)))

Q2.where = BinOp(AND, BinOp(EQ, Col("b"), Lit(2)),
                      BinOp(EQ, Col("a"), Lit(1)))
```

### Step 2: Recognize Pattern

The tool sees:
- Q1.where has form `(P AND Q)`
- Q2.where has form `(Q AND P)`
- Where P = `(a = 1)` and Q = `(b = 2)`

### Step 3: Apply Theorem

```lean
theorem and_comm (p q : Expr) :
  ∀ db row, evalExpr db row (p AND q) = evalExpr db row (q AND p)
```

This theorem says: for any expressions P and Q, and any database and row, evaluating `P AND Q` equals evaluating `Q AND P`.

### Step 4: Conclude Equivalence

Since the WHERE clauses are equivalent (by and_comm), and the rest of the query is identical, the full queries are equivalent.

```
✓ EQUIVALENT (by and_comm)
```

---

## Exercises

### Exercise 1
What does this formal statement mean in English?

```lean
∀ (p : Expr), p OR TRUE ≡ TRUE
```

<details>
<summary>Answer</summary>

"For any expression p, the expression `p OR TRUE` is equivalent to just `TRUE`."

In other words: OR-ing anything with TRUE gives TRUE (absorption law).

</details>

### Exercise 2
Is this statement true? Why or why not?

```lean
∀ (p : Expr), p AND p ≡ p
```

<details>
<summary>Answer</summary>

**Yes, it's true** (idempotence of AND).

If p is TRUE, then TRUE AND TRUE = TRUE.
If p is FALSE, then FALSE AND FALSE = FALSE.
If p is UNKNOWN (NULL), then UNKNOWN AND UNKNOWN = UNKNOWN.

In all cases, `p AND p = p`.

</details>

### Exercise 3
What's the bug in this proposed theorem?

```lean
-- PROPOSED (but wrong!)
theorem null_eq_null :
  NULL = NULL ≡ TRUE
```

<details>
<summary>Answer</summary>

**This is FALSE!** In SQL, `NULL = NULL` evaluates to `UNKNOWN`, not `TRUE`.

The correct statement would be:
```lean
theorem null_eq_null :
  eval(NULL = NULL) = UNKNOWN
```

This is exactly why formal methods are valuable—they catch these subtle semantic issues.

</details>

---

## Key Takeaways

1. **Formal methods prove properties for all inputs**, not just tested ones
2. **Specifications** define what should happen; **proofs** show the implementation matches
3. **SQL semantics** are formalized so we can reason about queries mathematically
4. **Trust comes from**: clear specs, accurate semantics, machine-checked proofs
5. **Combine testing and verification** for best results

---

## Next Steps

- [Tutorial 8: Reading and Writing Proofs in Lean](08-lean-proofs.md) - Get hands-on with proofs
- [Tutorial 9: Manual Proof Techniques](09-manual-proofs.md) - What to do when automation fails
- [Glossary](reference/glossary.md) - Formal methods terminology

---

## Further Reading

- *Software Foundations* - Free online textbook on formal verification
- *The Lean 4 Theorem Prover Documentation* - Lean's official docs
- *SQL and Relational Theory* by C.J. Date - Rigorous SQL semantics
