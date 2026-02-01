# SQL Equivalence Tutorials

Welcome to the sql_equiv tutorial series. These tutorials progress from basic concepts to advanced techniques for verifying SQL query equivalence.

---

## Learning Path

### Beginner Track

| # | Tutorial | Time | Prerequisites |
|---|----------|------|---------------|
| 1 | [Your First Equivalence Proof](01-first-proof.md) | 15 min | Basic SQL |
| 2 | [Easy vs Hard: When Can We Prove Equivalence?](02-easy-vs-hard.md) | 20 min | Tutorial 1 |
| 3 | [Understanding NULL and Three-Valued Logic](03-null-logic.md) | 25 min | Tutorial 2 |

### Intermediate Track

| # | Tutorial | Time | Prerequisites |
|---|----------|------|---------------|
| 4 | [Join Transformations](04-join-transforms.md) | 30 min | Tutorial 3 |
| 5 | [Subquery Equivalences](05-subquery-equiv.md) | 30 min | Tutorial 4 |
| 6 | [Aggregate and GROUP BY Rules](06-aggregates.md) | 25 min | Tutorial 5 |

### Advanced Track

| # | Tutorial | Time | Prerequisites |
|---|----------|------|---------------|
| 7 | [Introduction to Formal Methods](07-formal-methods-intro.md) | 45 min | Tutorial 6 |
| 8 | [Reading and Writing Proofs in Lean](08-lean-proofs.md) | 60 min | Tutorial 7 |
| 9 | [Manual Proof Techniques](09-manual-proofs.md) | 45 min | Tutorial 8 |
| 10 | [When the Tool Can't Help](10-beyond-automation.md) | 30 min | Tutorial 9 |

### Reference

| Document | Description |
|----------|-------------|
| [Equivalence Catalog](reference/equivalence-catalog.md) | Common transformations with proofs |
| [Pitfalls and Gotchas](reference/pitfalls.md) | Queries that look equivalent but aren't |
| [Glossary](reference/glossary.md) | Formal methods terminology |

---

## Quick Start

If you just want to check if two queries are equivalent:

```bash
# Parse and compare two queries
lake exe sql_equiv check "SELECT * FROM t WHERE a=1 AND b=2" \
                         "SELECT * FROM t WHERE b=2 AND a=1"
# Output: EQUIVALENT (by AND commutativity)
```

If you want to understand *why* they're equivalent, start with [Tutorial 1](01-first-proof.md).

---

## Who Is This For?

### Database Developers
You write SQL daily and want to know if your query rewrites are safe. Start with the **Beginner Track** to build intuition, then use the [Equivalence Catalog](reference/equivalence-catalog.md) as a reference.

### Query Optimizer Engineers
You're building or improving a query optimizer and need to verify transformations. The **Intermediate Track** covers the transformations you'll implement, and the **Advanced Track** shows how to prove them correct.

### Formal Methods Curious
You've heard about formal verification and want to see it applied to something practical. Start with [Tutorial 7: Introduction to Formal Methods](07-formal-methods-intro.md) for the conceptual foundation.

### AI/LLM Developers
You're building AI systems that generate or transform SQL. These tutorials help you understand which transformations are safe to apply and how to validate AI-generated rewrites.

---

## Key Concepts Preview

### What "Equivalent" Means

Two SQL queries are **equivalent** if they produce the same result for *every possible database state*:

```
Q1 ≡ Q2  ⟺  ∀ database D: eval(Q1, D) = eval(Q2, D)
```

This is a strong guarantee—not just "works on my test data."

### The Spectrum of Provability

```
        EASY                    HARD                 IMPOSSIBLE
          │                       │                       │
          ▼                       ▼                       ▼
    ┌─────────────┐       ┌─────────────┐       ┌─────────────┐
    │ Syntactic   │       │ Semantic    │       │ Context     │
    │ rewrites    │       │ transforms  │       │ dependent   │
    └─────────────┘       └─────────────┘       └─────────────┘

    • AND/OR order         • IN → EXISTS         • Business rules
    • Column reorder       • Subquery flatten    • Data constraints
    • Alias renaming       • Join reorder        • External knowledge
```

### Why Formal Methods?

Testing can show bugs exist. Formal methods can show bugs *don't* exist.

```
Testing:    "I tried 1000 inputs and it worked"
Formal:     "It works for ALL possible inputs, here's the proof"
```

---

## How to Use These Tutorials

1. **Read actively**: Try the examples yourself
2. **Predict first**: Before running a query, guess the result
3. **Break things**: Modify examples to see what fails
4. **Ask why**: Every equivalence has a reason—find it

---

## Getting Help

- **Questions about tutorials**: Open an issue with `[tutorial]` tag
- **Found an error**: PRs welcome!
- **Suggestions**: We'd love to hear what's confusing or missing

---

## Prerequisites

- Basic SQL knowledge (SELECT, JOIN, WHERE, GROUP BY)
- Command line familiarity
- No formal methods background required (we'll teach you!)

For Lean/proof tutorials:
- Willingness to learn new syntax
- Patience with mathematical notation
