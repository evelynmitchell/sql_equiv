# Glossary

Terminology used in sql_equiv and formal methods.

---

## A

**Abstract Syntax Tree (AST)**
A tree representation of the syntactic structure of source code (or SQL). Each node represents a construct in the language.

**Anti-join**
A join that returns rows from the left table that have NO matching rows in the right table. Equivalent to `LEFT JOIN ... WHERE right.key IS NULL`.

**Associativity**
A property where grouping doesn't matter: `(A ⊕ B) ⊕ C = A ⊕ (B ⊕ C)`. AND, OR, and INNER JOIN are associative.

**Axiom**
A statement assumed to be true without proof. In sql_equiv, axioms are placeholders for proofs not yet written.

---

## B

**Bag Semantics**
Treating query results as multisets (bags) where duplicates are allowed but order doesn't matter. Contrast with set semantics.

**Boolean Algebra**
The mathematical system dealing with TRUE, FALSE, AND, OR, NOT. SQL extends this to three-valued logic.

---

## C

**Cardinality**
The number of rows in a table or result set.

**Commutativity**
A property where order doesn't matter: `A ⊕ B = B ⊕ A`. AND, OR, and INNER JOIN are commutative.

**Correlated Subquery**
A subquery that references columns from the outer query, evaluated once per outer row.

**Counterexample**
A specific input that disproves a claimed equivalence.

---

## D

**Decorrelation**
Transforming a correlated subquery into an uncorrelated one, typically by converting to a join.

**Distributivity**
A property relating two operators: `A ∧ (B ∨ C) = (A ∧ B) ∨ (A ∧ C)`.

---

## E

**Equivalence (Query)**
Two queries are equivalent if they produce identical results for all possible database states.

**Evaluation / eval**
The function that computes the result of a SQL query given a database state.

---

## F

**Formal Methods**
Mathematical techniques for specifying, developing, and verifying software systems.

**Formal Semantics**
A precise mathematical definition of what programs (or queries) mean.

---

## G

**Ground Expression**
An expression containing no variables (column references)—only literals.

---

## H

**HAVING Clause**
A filter applied after GROUP BY, can reference aggregate results.

---

## I

**Idempotence**
A property where applying an operation twice has the same effect as once: `A AND A = A`.

**Induction (Structural)**
A proof technique for recursive structures: prove for base case, then prove that if it holds for substructures, it holds for the whole.

**Invariant**
A property that remains true throughout a computation or transformation.

---

## J

**Join Predicate**
The condition in an ON clause specifying which rows match.

---

## L

**Lean**
The theorem prover and programming language used by sql_equiv for formal proofs.

**Lemma**
A helper theorem used to prove other theorems.

---

## M

**Monotonicity**
A property where adding more input doesn't decrease output. Used in proving termination.

---

## N

**Normal Form**
A standardized representation of expressions. Normalization converts expressions to canonical form for comparison.

**NULL**
SQL's representation of missing or unknown data. Not a value—the absence of a value.

---

## O

**Optimizer**
A component that transforms queries to improve performance while preserving semantics.

---

## P

**Predicate**
A Boolean expression used in WHERE, HAVING, or ON clauses.

**Predicate Pushdown**
Moving predicates closer to data sources (e.g., into subqueries or joins) to filter early.

**Proof**
A logical argument demonstrating that a theorem is true.

**Proposition (Prop)**
In Lean, the type of logical statements that can be true or false.

---

## Q

**Quantifier**
∀ (for all) or ∃ (there exists).

---

## R

**Rewrite Rule**
A transformation pattern: if query matches pattern A, replace with pattern B.

**Roundtrip**
Parse → Pretty-print → Parse cycle. If roundtrip preserves meaning, parser/printer are consistent.

---

## S

**Scalar Subquery**
A subquery that returns exactly one value (one row, one column).

**Selectivity**
The fraction of rows that satisfy a predicate. Used for cost estimation.

**Semantics**
The meaning of a language construct, as opposed to its syntax.

**Semi-join**
A join that returns rows from the left table that have at least one matching row in the right table, without duplicating.

**Soundness**
A property of a transformation: if it claims equivalence, the queries are truly equivalent. (No false positives.)

**Specification**
A formal description of what a system should do.

---

## T

**Tactic**
In Lean, a command that transforms the proof state (e.g., `intro`, `apply`, `simp`).

**Termination**
The property that a computation eventually finishes.

**Theorem**
A proven statement about the system.

**Three-Valued Logic (3VL)**
Logic with TRUE, FALSE, and UNKNOWN. SQL uses this because of NULL.

**Transformation**
A rewrite of a query to an equivalent (or supposedly equivalent) form.

---

## U

**Uncorrelated Subquery**
A subquery independent of the outer query, evaluated once.

**UNKNOWN**
The third truth value in SQL, arising from comparisons involving NULL.

---

## V

**Verification**
Proving that an implementation satisfies its specification.

---

## W

**Well-Founded**
A relation with no infinite descending chains. Required for termination proofs.

---

## Symbols

| Symbol | Meaning |
|--------|---------|
| ∀ | For all (universal quantification) |
| ∃ | There exists (existential quantification) |
| → | Implies / function arrow |
| ∧ | Logical AND |
| ∨ | Logical OR |
| ¬ | Logical NOT |
| ≡ | Equivalent to |
| ≢ | Not equivalent to |
| ⋈ | Join |
| σ | Selection (filter) |
| π | Projection |
| γ | Grouping / aggregation |
| := | Definition |
| ⊆ | Subset |
| ∈ | Element of |
| ∅ | Empty set |

---

## SQL-Specific Terms

| Term | Definition |
|------|------------|
| DML | Data Manipulation Language (SELECT, INSERT, UPDATE, DELETE) |
| DDL | Data Definition Language (CREATE, ALTER, DROP) |
| CTE | Common Table Expression (WITH clause) |
| UDF | User-Defined Function |
| FK | Foreign Key |
| PK | Primary Key |
