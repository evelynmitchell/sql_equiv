# Proposal: SQL Equiv Interactive Learning Game

**Date:** 2026-02-04
**Status:** Proposal
**Inspired by:** [ReintroductionToProofs](https://github.com/emilyriehl/ReintroductionToProofs) by Emily Riehl

## Overview

This proposal outlines the creation of an interactive Lean 4 game to teach SQL equivalence proofs using the [Lean Game Server](https://adam.math.hhu.de/) platform. The game would leverage sql_equiv's existing theorem library (169+ axioms/theorems) to create a gamified learning experience.

## Motivation

### Problem

- SQL query optimization relies on equivalence transformations, but most developers don't understand *why* these transformations are valid
- Formal verification of SQL is a niche topic with a steep learning curve
- The sql_equiv library has extensive theorems but lacks an interactive way to learn them

### Solution

Create an interactive game where players prove SQL equivalences step-by-step, learning both:
1. SQL semantics (NULL handling, three-valued logic, join behavior)
2. Lean 4 theorem proving techniques

### Prior Art

The [ReintroductionToProofs](https://github.com/emilyriehl/ReintroductionToProofs) game by Emily Riehl demonstrates this approach successfully:
- Created for a Johns Hopkins University seminar (Fall 2025)
- Uses gamification to teach dependent type theory proofs
- 17 interconnected "worlds" with progressive difficulty
- Hosted on the Lean Game Server at adam.math.hhu.de

## Technical Approach

### Platform

The [Lean Game Server](https://github.com/leanprover-community/lean4game) provides:
- React-based frontend for interactive proof editing
- Sandboxed Lean 4 execution for proof validation
- Hint system with context-sensitive guidance
- Progress tracking across levels and worlds

### Starting Point

Use the [GameSkeleton](https://github.com/hhu-adam/GameSkeleton) template which provides:
- Pre-configured project structure
- GitHub Codespaces support for development
- Integration with lean4game infrastructure

### Integration with sql_equiv

Add sql_equiv as a Lake dependency:

```lean
-- lakefile.lean
require sql_equiv from git "https://github.com/evelynmitchell/sql_equiv"
```

## Proposed Game Structure

### World Organization

```
SQLEquivGame/
├── Game.lean                      # World connections & metadata
├── Game/
│   ├── Levels/
│   │   ├── TutorialWorld/         # Intro to Lean proof tactics
│   │   │   ├── L01_Intro.lean
│   │   │   ├── L02_Refl.lean
│   │   │   └── ...
│   │   ├── BooleanWorld/          # Boolean algebra (AND, OR, NOT)
│   │   │   ├── L01_AndComm.lean
│   │   │   ├── L02_OrComm.lean
│   │   │   ├── L03_NotNot.lean
│   │   │   ├── L04_DeMorgan.lean
│   │   │   └── L07_BossLevel.lean
│   │   ├── NullWorld/             # Three-valued logic (Trilean)
│   │   │   ├── L01_IsNull.lean
│   │   │   ├── L02_NullPropagation.lean
│   │   │   ├── L03_TrileanAnd.lean
│   │   │   └── ...
│   │   ├── ArithmeticWorld/       # Numeric identities
│   │   │   ├── L01_AddZero.lean
│   │   │   ├── L02_MulOne.lean
│   │   │   └── ...
│   │   ├── ComparisonWorld/       # Comparison operators
│   │   │   ├── L01_EqRefl.lean
│   │   │   ├── L02_LtFlip.lean
│   │   │   └── ...
│   │   ├── FilterWorld/           # WHERE clause equivalences
│   │   │   ├── L01_WhereTrue.lean
│   │   │   ├── L02_WhereFalse.lean
│   │   │   ├── L03_FilterAnd.lean
│   │   │   └── ...
│   │   ├── JoinWorld/             # JOIN equivalences
│   │   │   ├── L01_JoinComm.lean
│   │   │   ├── L02_JoinAssoc.lean
│   │   │   ├── L03_CrossJoin.lean
│   │   │   └── ...
│   │   ├── SetOpWorld/            # UNION, INTERSECT, EXCEPT
│   │   │   ├── L01_UnionComm.lean
│   │   │   ├── L02_IntersectComm.lean
│   │   │   └── ...
│   │   ├── SubqueryWorld/         # Subquery transformations
│   │   │   ├── L01_ExistsEmpty.lean
│   │   │   ├── L02_InAsExists.lean
│   │   │   └── ...
│   │   └── OptimizationWorld/     # Query optimization proofs
│   │       ├── L01_PredicatePushdown.lean
│   │       ├── L02_JoinReorder.lean
│   │       └── L07_BossLevel.lean
```

### World Dependency Graph

```
TutorialWorld
     │
     ▼
BooleanWorld ──────┬──────► FilterWorld ──► JoinWorld
     │             │              │              │
     ▼             ▼              ▼              ▼
NullWorld    ArithmeticWorld  SetOpWorld   SubqueryWorld
     │             │              │              │
     └─────────────┴──────────────┴──────────────┘
                          │
                          ▼
                  OptimizationWorld
```

### Example Level

```lean
import SqlEquiv

World "BooleanWorld"
Level 1

Title "AND is Commutative"

Introduction "
In SQL, the order of conditions in a WHERE clause often doesn't matter.
For example:

```sql
SELECT * FROM users WHERE age > 18 AND active = true
```

gives the same result as:

```sql
SELECT * FROM users WHERE active = true AND age > 18
```

Let's prove this formally: `a AND b ≃ b AND a`
"

Statement and_comm (a b : Expr) :
    Expr.binOp .and a b ≃ₑ Expr.binOp .and b a := by
  Hint "Try using the `sql_equiv` tactic"
  Hint (hidden := true) "The `sql_equiv` tactic handles boolean commutativity automatically"
  sql_equiv

Conclusion "
Excellent! You've proven that AND is commutative in SQL expressions.

This equivalence is fundamental to query optimization. It allows the database
to freely reorder AND conditions to:
- Use available indexes more effectively
- Short-circuit evaluation when possible
- Group related conditions together

**Real-world application:** When you write `WHERE indexed_col = 5 AND other_col > 10`,
the optimizer can rearrange this to check the indexed column first.
"

NewTactic sql_equiv
```

## Mapping sql_equiv Theorems to Worlds

### BooleanWorld (15 levels)

| Level | Theorem | SQL Example |
|-------|---------|-------------|
| 1 | `and_comm` | `a AND b ≃ b AND a` |
| 2 | `or_comm` | `a OR b ≃ b OR a` |
| 3 | `not_not` | `NOT NOT a ≃ a` |
| 4 | `and_assoc` | `(a AND b) AND c ≃ a AND (b AND c)` |
| 5 | `or_assoc` | `(a OR b) OR c ≃ a OR (b OR c)` |
| 6 | `not_and` | `NOT (a AND b) ≃ NOT a OR NOT b` |
| 7 | `not_or` | `NOT (a OR b) ≃ NOT a AND NOT b` |
| 8 | `and_true` | `a AND TRUE ≃ a` |
| 9 | `or_false` | `a OR FALSE ≃ a` |
| 10 | `and_false` | `a AND FALSE ≃ FALSE` |
| 11 | `or_true` | `a OR TRUE ≃ TRUE` |
| 12 | `and_self` | `a AND a ≃ a` |
| 13 | `or_self` | `a OR a ≃ a` |
| 14 | `and_absorb_or` | `a AND (a OR b) ≃ a` |
| 15 | **Boss Level** | Complex boolean simplification |

### NullWorld (12 levels)

| Level | Theorem | Concept |
|-------|---------|---------|
| 1 | `is_null_on_null` | IS NULL on NULL returns TRUE |
| 2 | `is_not_null_on_int` | IS NOT NULL on non-NULL |
| 3 | `null_add_left` | NULL + x = NULL |
| 4 | `null_eq_left` | NULL = x = NULL |
| 5 | `false_and_null` | FALSE AND NULL = FALSE |
| 6 | `true_or_null` | TRUE OR NULL = TRUE |
| 7 | `trilean_not_not` | Trilean double negation |
| 8 | `trilean_de_morgan_and` | De Morgan for three-valued logic |
| 9 | `coalesce_null_left_nonnull` | COALESCE(NULL, x) = x |
| 10 | `nullif_same_int` | NULLIF(n, n) = NULL |
| 11 | `value_null_or_not_null` | Every value is NULL or not NULL |
| 12 | **Boss Level** | Complex NULL handling proof |

### FilterWorld (8 levels)

| Level | Theorem | SQL Transformation |
|-------|---------|-------------------|
| 1 | `where_true_elim` | `WHERE TRUE` → remove clause |
| 2 | `where_false_empty` | `WHERE FALSE` → empty result |
| 3 | `filter_and` | `WHERE p AND q` equivalences |
| 4 | `filter_commute` | Filter order independence |
| 5 | `filter_idempotent` | `WHERE p WHERE p` → `WHERE p` |
| 6 | `predicate_pushdown` | Push filters through operations |
| 7 | `filter_join_left` | Push filter into left side of join |
| 8 | **Boss Level** | Complex predicate pushdown chain |

### JoinWorld (10 levels)

| Level | Theorem | SQL Transformation |
|-------|---------|-------------------|
| 1 | `join_comm` | `A JOIN B` ≃ `B JOIN A` |
| 2 | `join_assoc` | JOIN associativity |
| 3 | `cross_join_comm` | CROSS JOIN commutativity |
| 4 | `inner_join_true_is_cross` | `JOIN ON TRUE` = CROSS JOIN |
| 5 | `inner_join_false_empty` | `JOIN ON FALSE` = empty |
| 6 | `inner_join_to_where` | `JOIN ON cond` = `CROSS JOIN WHERE cond` |
| 7 | `left_join_filter_null_is_inner` | LEFT JOIN + NOT NULL filter = INNER |
| 8 | `inner_join_empty_left` | Empty table JOIN = empty |
| 9 | `cross_join_cardinality` | `|A × B| = |A| * |B|` |
| 10 | **Boss Level** | Join reordering optimization |

## Current sql_equiv Assets

The game can leverage existing sql_equiv infrastructure:

| Asset | Location | Usage |
|-------|----------|-------|
| **169 axioms/theorems** | `SqlEquiv/Equiv.lean` | Core proof targets |
| **Custom tactics** | `SqlEquiv/Tactics.lean` | `sql_equiv`, `sql_simp`, etc. |
| **Axiom dependency graph** | `docs/axiom_dependencies.dot` | World structure guide |
| **Comprehensive tests** | `Test/*.lean` | Validation of theorems |
| **Tutorial documentation** | `docs/tutorials/` | Level content source |

## Implementation Plan

### Phase 1: Proof of Concept (1-2 weeks)

1. Fork GameSkeleton template
2. Configure sql_equiv dependency
3. Create TutorialWorld (3-4 levels)
4. Create BooleanWorld (5-6 levels)
5. Test locally with lean4game

### Phase 2: Core Content (2-4 weeks)

1. Complete BooleanWorld (15 levels)
2. Create NullWorld (12 levels)
3. Create ArithmeticWorld (8 levels)
4. Create ComparisonWorld (10 levels)
5. Write introduction and conclusion text for all levels

### Phase 3: Advanced Content (2-4 weeks)

1. Create FilterWorld (8 levels)
2. Create JoinWorld (10 levels)
3. Create SetOpWorld (8 levels)
4. Create SubqueryWorld (10 levels)
5. Create OptimizationWorld (8 levels)

### Phase 4: Polish & Deploy (1-2 weeks)

1. Add hint system refinements
2. Create cover image and metadata
3. Test complete game flow
4. Deploy to adam.math.hhu.de
5. Create announcement/documentation

## Benefits

| Benefit | Description |
|---------|-------------|
| **Interactive learning** | Users learn SQL semantics by proving equivalences hands-on |
| **Gamification** | Progressive difficulty with boss levels maintains engagement |
| **Formal verification education** | Users understand *why* query optimizations are valid |
| **Educational outreach** | Attracts students to both SQL and theorem proving |
| **Living documentation** | The game itself documents the theorem library |
| **Community building** | Connects sql_equiv to the broader Lean community |

## Challenges & Mitigations

| Challenge | Mitigation |
|-----------|-----------|
| Lean 4 version compatibility | Pin to specific toolchain version matching lean4game |
| Game server quirks | Follow lean4game documentation carefully; test incrementally |
| sql_equiv complexity | Start with simple theorems; build up gradually |
| Custom tactic integration | Expose tactics through `NewTactic` DSL; document usage |
| Content creation time | Prioritize most educational theorems; reuse existing docs |

## Success Metrics

- Number of completed game sessions
- User feedback on difficulty progression
- Contributions back to sql_equiv (bug reports, new theorems)
- Citations/references in educational contexts

## Resources

### Documentation

- [lean4game: Creating a Game](https://github.com/leanprover-community/lean4game/blob/main/doc/create_game.md)
- [lean4game: Running Locally](https://github.com/leanprover-community/lean4game/blob/main/doc/running_locally.md)
- [GameSkeleton Template](https://github.com/hhu-adam/GameSkeleton)

### Examples

- [ReintroductionToProofs](https://github.com/emilyriehl/ReintroductionToProofs) - Emily Riehl's proof game
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/NNG4) - Classic Lean game
- [Lean Game Server](https://adam.math.hhu.de/) - Hosting platform

## Next Steps

1. **Review this proposal** - Gather feedback on scope and priorities
2. **Create repository** - Fork GameSkeleton, configure dependencies
3. **Build prototype** - TutorialWorld + partial BooleanWorld
4. **Iterate** - Refine based on testing and feedback
5. **Expand** - Complete remaining worlds
6. **Deploy** - Publish to Lean Game Server

---

*This proposal was inspired by exploring the ReintroductionToProofs repository and assessing how similar gamification techniques could be applied to sql_equiv.*
