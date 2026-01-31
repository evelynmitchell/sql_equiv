# Documentation Coverage Matrix

Tracks the relationship between code implementation, tutorial coverage, and documentation status.

---

## Legend

| Status | Meaning |
|--------|---------|
| ✅ | Implemented and documented |
| 📋 | Implemented, tutorial outline only |
| ⚠️ | Implemented, no tutorial |
| 🚧 | Partially implemented |
| ❌ | Not implemented |
| 📝 | Documented but not implemented (spec only) |

---

## 1. Core SQL Features

### 1.1 Expressions

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| Literals (int, string, bool) | ✅ `Ast.lean` | ✅ T01 | ✅ Catalog | |
| Column references | ✅ `Ast.lean` | ✅ T01 | ✅ Catalog | |
| Binary operators (+, -, *, /) | ✅ `Ast.lean` | ⚠️ | ✅ Catalog | Need tutorial examples |
| Comparison operators | ✅ `Ast.lean` | ✅ T01 | ✅ Catalog | |
| Boolean operators (AND, OR, NOT) | ✅ `Ast.lean` | ✅ T01, T02 | ✅ Catalog | Well covered |
| NULL literal | ✅ `Ast.lean` | 📋 T03 | ✅ Pitfalls | Outline ready |
| IS NULL / IS NOT NULL | ✅ `Ast.lean` | 📋 T03 | ✅ Pitfalls | |
| BETWEEN | ✅ `Ast.lean` | ✅ T01 | ✅ Catalog | |
| IN (value list) | ✅ `Ast.lean` | ✅ T01 | ✅ Catalog | |
| IN (subquery) | ✅ `Ast.lean` | 📋 T05 | ✅ Pitfalls | NOT IN trap covered |
| LIKE | ✅ `Ast.lean` | ⚠️ | ⚠️ | Needs examples |
| CASE/WHEN/THEN/ELSE | ✅ `Ast.lean` | ⚠️ | ⚠️ | Needs tutorial |
| EXISTS / NOT EXISTS | ✅ `Ast.lean` | 📋 T05 | ✅ Pitfalls | |
| Scalar subquery | ✅ `Ast.lean` | 📋 T05 | ✅ Catalog | |
| Function calls | ✅ `Ast.lean` | ⚠️ | ⚠️ | Generic, few built-ins |
| CAST | ❌ | ❌ | 📝 Gap doc | High priority gap |
| COALESCE | ❌ | ❌ | 📝 Gap doc | High priority gap |

### 1.2 SELECT Statement

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| SELECT columns | ✅ `Ast.lean` | ✅ T01 | ✅ Catalog | |
| SELECT * | ✅ `Ast.lean` | ✅ T01 | ⚠️ | |
| SELECT DISTINCT | ✅ `Ast.lean` | 📋 T06 | ✅ Catalog | DISTINCT↔GROUP BY |
| Column aliases (AS) | ✅ `Ast.lean` | ✅ T01 | ⚠️ | |
| FROM clause | ✅ `Ast.lean` | ✅ T01 | ✅ Catalog | |
| Table aliases | ✅ `Ast.lean` | ✅ T01 | ⚠️ | |
| WHERE clause | ✅ `Ast.lean` | ✅ T01, T02 | ✅ Catalog | Well covered |
| GROUP BY | ✅ `Ast.lean` | 📋 T06 | ✅ Catalog | |
| HAVING | ✅ `Ast.lean` | 📋 T06 | ✅ Catalog | |
| ORDER BY | ✅ `Ast.lean` | ⚠️ | ✅ Pitfalls | Subquery ORDER BY pitfall |
| LIMIT | ✅ `Ast.lean` | ⚠️ | ⚠️ | |
| OFFSET | ✅ `Ast.lean` | ⚠️ | ⚠️ | |

### 1.3 Joins

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| INNER JOIN | ✅ `Ast.lean` | 📋 T04 | ✅ Catalog | Comm/assoc covered |
| LEFT JOIN | ✅ `Ast.lean` | 📋 T04 | ✅ Pitfalls | LEFT≠INNER pitfall |
| RIGHT JOIN | ✅ `Ast.lean` | 📋 T04 | ✅ Catalog | |
| FULL JOIN | ✅ `Ast.lean` | 📋 T04 | ⚠️ | Needs examples |
| CROSS JOIN | ✅ `Ast.lean` | 📋 T04 | ✅ Catalog | |
| ON clause | ✅ `Ast.lean` | 📋 T04 | ✅ Pitfalls | ON vs WHERE |
| USING clause | ❌ | ❌ | 📝 Gap doc | Not implemented |
| NATURAL JOIN | ❌ | ❌ | 📝 Gap doc | Not implemented |

### 1.4 Aggregates

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| COUNT(*) | ✅ `Ast.lean` | 📋 T06 | ✅ Pitfalls | COUNT(*) vs COUNT(x) |
| COUNT(column) | ✅ `Ast.lean` | 📋 T06 | ✅ Pitfalls | |
| COUNT(DISTINCT) | ✅ `Ast.lean` | 📋 T06 | ⚠️ | |
| SUM | ✅ `Ast.lean` | 📋 T06 | ✅ Catalog | Decomposition |
| AVG | ✅ `Ast.lean` | 📋 T06 | ✅ Pitfalls | NULL handling |
| MIN | ✅ `Ast.lean` | 📋 T06 | ✅ Catalog | |
| MAX | ✅ `Ast.lean` | 📋 T06 | ✅ Catalog | |
| STDDEV, VARIANCE | ❌ | ❌ | 📝 Gap doc | |

### 1.5 Window Functions

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| OVER clause | ✅ `Ast.lean` | ⚠️ | ⚠️ | Needs tutorial |
| PARTITION BY | ✅ `Ast.lean` | ⚠️ | ⚠️ | |
| ORDER BY in OVER | ✅ `Ast.lean` | ⚠️ | ⚠️ | |
| ROW_NUMBER | ✅ `Ast.lean` | ⚠️ | ⚠️ | |
| RANK | ✅ `Ast.lean` | ⚠️ | ⚠️ | |
| DENSE_RANK | ✅ `Ast.lean` | ⚠️ | ⚠️ | |
| LAG/LEAD | ❌ | ❌ | 📝 Gap doc | |
| FIRST_VALUE/LAST_VALUE | ❌ | ❌ | 📝 Gap doc | |
| Window frames (ROWS/RANGE) | ❌ | ❌ | 📝 Gap doc | High priority gap |

### 1.6 Set Operations

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| UNION | ✅ `Ast.lean` | ⚠️ | ✅ Catalog | |
| UNION ALL | ✅ `Ast.lean` | ⚠️ | ✅ Pitfalls | UNION vs UNION ALL |
| INTERSECT | ✅ `Ast.lean` | ⚠️ | ✅ Catalog | |
| EXCEPT | ✅ `Ast.lean` | ⚠️ | ✅ Pitfalls | NULL behavior |

### 1.7 CTEs

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| WITH clause | ✅ `Ast.lean` | ⚠️ | ⚠️ | Needs tutorial |
| Multiple CTEs | ✅ `Ast.lean` | ⚠️ | ⚠️ | |
| WITH RECURSIVE | ✅ `Ast.lean` | 📋 T10 | ⚠️ | Termination issues |

### 1.8 DML

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| INSERT VALUES | ✅ `Ast.lean` | ⚠️ | ⚠️ | Not focus of equiv |
| INSERT SELECT | ✅ `Ast.lean` | ⚠️ | ⚠️ | |
| UPDATE | ✅ `Ast.lean` | ⚠️ | ⚠️ | |
| DELETE | ✅ `Ast.lean` | ⚠️ | ⚠️ | |

---

## 2. Optimizer Features

### 2.1 Implemented (PRs Merged)

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| OptimizerUtils | ✅ `OptimizerUtils.lean` | ⚠️ | 📝 Redesign doc | flattenAnd, etc. |
| Expression normalization | ✅ `ExprNormalization.lean` | ⚠️ | 📝 Redesign doc | Canonical ordering |
| Basic optimization | ✅ `Optimizer.lean` | ⚠️ | ⚠️ | Constant folding |

### 2.2 In Progress (PRs #7, #8)

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| Predicate pushdown | 🚧 PR #7 | 📋 T04 | 📝 Redesign doc | Under review |
| Join reordering | 🚧 PR #8 | 📋 T04 | 📝 Redesign doc | Under review |

### 2.3 Planned (Specs Written)

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| Advanced cost estimation | 📝 Spec | ⚠️ | ✅ Spec doc | Phase 3 |
| Aggregate pushdown | 📝 Spec | 📋 T06 | ✅ Spec doc | Phase 4 |
| Subquery flattening | 📝 Spec | 📋 T05 | ✅ Spec doc | Phase 4 |
| Window optimization | 📝 Spec | ⚠️ | ✅ Spec doc | Phase 4 |
| DP join optimizer | 📝 Spec | ⚠️ | ✅ Spec doc | Phase 5 |
| Partition pruning | 📝 Spec | ⚠️ | ✅ Spec doc | Phase 6 |
| Materialized views | 📝 Spec | ⚠️ | ✅ Spec doc | Phase 6 |

---

## 3. Formal Verification

| Feature | Code | Tutorial | Reference | Notes |
|---------|------|----------|-----------|-------|
| Semantics (evalExpr, evalFrom) | ✅ `Semantics.lean` | ✅ T07 | ⚠️ | Core definitions |
| Equivalence theorems | ✅ `Equiv.lean` | ✅ T07 | ✅ Catalog | 305+ theorems |
| Three-valued logic | ✅ `Semantics.lean` | 📋 T03 | ✅ Glossary | |
| Proof tactics | ✅ `Tactics.lean` | 📋 T08 | ⚠️ | Lean-specific |
| Axioms (to be proven) | ✅ `Equiv.lean` | ✅ T07 | 📝 Verify doc | Axiom inventory |

---

## 4. Tools

| Tool | Code | Tutorial | Reference | Notes |
|------|------|----------|-----------|-------|
| Parser | ✅ `Parser.lean` | ⚠️ | ⚠️ | Hand-rolled |
| Pretty printer | ✅ `Pretty.lean` | ⚠️ | ⚠️ | |
| SQL anonymizer | ✅ `tools/sql_anonymizer/` | ⚠️ | ✅ README | Python, standalone |
| Mapping manager | ✅ `tools/sql_anonymizer/` | ⚠️ | ✅ README | |

---

## 5. Documentation

| Document | Status | Coverage |
|----------|--------|----------|
| README.md | ⚠️ Needs update | Project overview |
| CLAUDE.md | ✅ | Build instructions |
| OPTIMIZER_REDESIGN_PLAN.md | ✅ | PRs 0, A, B, C |
| OPTIMIZER_VERIFICATION_PLAN.md | ✅ | Proof roadmap |
| OPTIMIZER_ROADMAP.md | ✅ | All phases |
| SQL_GAP_ANALYSIS.md | ✅ | Feature gaps |
| Cleanroom specs (7 docs) | ✅ | Future features |
| Tutorials (10 docs) | 🚧 4 full, 6 outline | User training |
| Reference (3 docs) | ✅ | Catalog, pitfalls, glossary |

---

## 6. Coverage Summary

### By Category

| Category | Implemented | Tutorialized | Documented |
|----------|-------------|--------------|------------|
| Core SQL | 85% | 40% | 70% |
| Joins | 90% | 50% | 80% |
| Aggregates | 70% | 30% | 60% |
| Window functions | 40% | 10% | 40% |
| Subqueries | 90% | 40% | 70% |
| Optimizer | 30% | 20% | 90% |
| Formal methods | 80% | 60% | 50% |
| Tools | 100% | 20% | 80% |

### Priority Gaps

**High priority - needs tutorial:**
1. Window functions (implemented but no tutorial)
2. CTEs (implemented but no tutorial)
3. CASE expressions (implemented but no tutorial)

**High priority - needs implementation:**
1. CAST/type conversion
2. COALESCE/NULLIF
3. Window frames
4. DATE/TIME types

**High priority - needs docs:**
1. Parser usage guide
2. Semantic evaluation walkthrough
3. How to add new SQL features

---

## 7. Action Items

### Tutorials to Expand (from outline to full)

| Priority | Tutorial | Effort | Dependency |
|----------|----------|--------|------------|
| P1 | T03: NULL Logic | 2 hrs | None |
| P1 | T04: Joins | 3 hrs | T03 |
| P1 | T05: Subqueries | 3 hrs | T04 |
| P2 | T06: Aggregates | 2 hrs | T03 |
| P2 | T08: Lean Proofs | 4 hrs | T07 |
| P3 | T10: Beyond Automation | 2 hrs | T09 |

### New Tutorials Needed

| Priority | Topic | Covers |
|----------|-------|--------|
| P1 | Window Functions | OVER, PARTITION BY, ranking |
| P2 | CTEs | WITH, WITH RECURSIVE |
| P2 | CASE Expressions | Simple and searched CASE |
| P3 | Set Operations | UNION, INTERSECT, EXCEPT |

### Documentation Gaps

| Priority | Document | Purpose |
|----------|----------|---------|
| P1 | Parser Guide | How to use/extend parser |
| P2 | Semantics Walkthrough | How eval* functions work |
| P2 | Contributing Guide | How to add features |
| P3 | API Reference | Auto-generated from code |

---

## 8. Cross-Reference: Tutorials ↔ Code

| Tutorial | Primary Code Files |
|----------|-------------------|
| T01: First Proof | `Equiv.lean` (and_comm, etc.) |
| T02: Easy vs Hard | `Equiv.lean`, `Optimizer.lean` |
| T03: NULL Logic | `Semantics.lean` (Trilean), `Equiv.lean` |
| T04: Joins | `Ast.lean` (JoinType), `Equiv.lean` (join_*) |
| T05: Subqueries | `Ast.lean` (Expr.subquery), `Equiv.lean` |
| T06: Aggregates | `Ast.lean` (AggFunc), `Semantics.lean` |
| T07: Formal Methods | `Semantics.lean`, `Equiv.lean` |
| T08: Lean Proofs | `Tactics.lean`, `Equiv.lean` |
| T09: Manual Proofs | N/A (methodology) |
| T10: Beyond Automation | N/A (methodology) |

---

*Last updated: 2026-01-31*
