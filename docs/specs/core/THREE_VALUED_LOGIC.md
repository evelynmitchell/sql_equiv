# Three-Valued Logic (Trilean)

## Cleanroom Specification

**Module:** `SqlEquiv/Ast.lean` (Trilean namespace)
**Status:** Implemented ✅
**Lines:** 36-93

---

## 1. Intended Function

SQL uses three-valued logic to handle NULL values in boolean expressions. The Trilean type models this with three values: TRUE, FALSE, and UNKNOWN.

### 1.1 Black-Box Specification

```
Trilean : Type

A type with exactly three inhabitants representing SQL's three-valued logic:
- TRUE: definite truth
- FALSE: definite falsity
- UNKNOWN: indeterminate (NULL in boolean context)
```

### 1.2 Why Three-Valued Logic?

In SQL, any comparison involving NULL yields UNKNOWN:
```sql
NULL = NULL   → UNKNOWN (not TRUE!)
NULL = 1      → UNKNOWN
5 > NULL      → UNKNOWN
```

WHERE clauses only include rows where the condition is TRUE (not UNKNOWN).

---

## 2. Data Type

```lean
inductive Trilean where
  | true
  | false
  | unknown
  deriving Repr, BEq, Inhabited, DecidableEq
```

---

## 3. Operations

### 3.1 NOT (Negation)

```
Function: Trilean.not
Signature: Trilean → Trilean

Truth Table:
  NOT TRUE    = FALSE
  NOT FALSE   = TRUE
  NOT UNKNOWN = UNKNOWN
```

**Implementation:**
```lean
def not : Trilean → Trilean
  | .true => .false
  | .false => .true
  | .unknown => .unknown
```

### 3.2 AND (Conjunction)

```
Function: Trilean.and
Signature: Trilean → Trilean → Trilean

Key Property: FALSE dominates UNKNOWN
  FALSE AND anything = FALSE

Truth Table:
       │ TRUE  │ FALSE │ UNKNOWN
  ─────┼───────┼───────┼─────────
  TRUE │ TRUE  │ FALSE │ UNKNOWN
  FALSE│ FALSE │ FALSE │ FALSE
  UNK  │ UNK   │ FALSE │ UNKNOWN
```

**Implementation:**
```lean
def and : Trilean → Trilean → Trilean
  | .false, _ => .false
  | _, .false => .false
  | .true, .true => .true
  | .true, .unknown => .unknown
  | .unknown, .true => .unknown
  | .unknown, .unknown => .unknown
```

### 3.3 OR (Disjunction)

```
Function: Trilean.or
Signature: Trilean → Trilean → Trilean

Key Property: TRUE dominates UNKNOWN
  TRUE OR anything = TRUE

Truth Table:
       │ TRUE  │ FALSE │ UNKNOWN
  ─────┼───────┼───────┼─────────
  TRUE │ TRUE  │ TRUE  │ TRUE
  FALSE│ TRUE  │ FALSE │ UNKNOWN
  UNK  │ TRUE  │ UNK   │ UNKNOWN
```

**Implementation:**
```lean
def or : Trilean → Trilean → Trilean
  | .true, _ => .true
  | _, .true => .true
  | .false, .false => .false
  | .false, .unknown => .unknown
  | .unknown, .false => .unknown
  | .unknown, .unknown => .unknown
```

### 3.4 Conversion Functions

```
Function: Trilean.ofBool
Signature: Bool → Trilean
  ofBool true  = Trilean.true
  ofBool false = Trilean.false

Function: Trilean.toBool
Signature: Trilean → Bool
  toBool true    = true
  toBool false   = false
  toBool unknown = false   -- Critical: UNKNOWN → false for WHERE clauses

Function: Trilean.isTrue / isFalse / isUnknown
Signature: Trilean → Bool
  Predicates for checking specific values
```

---

## 4. Correctness Conditions

### 4.1 Algebraic Properties

```lean
-- Commutativity
theorem and_comm (a b : Trilean) : a.and b = b.and a
theorem or_comm (a b : Trilean) : a.or b = b.or a

-- Associativity
theorem and_assoc (a b c : Trilean) : (a.and b).and c = a.and (b.and c)
theorem or_assoc (a b c : Trilean) : (a.or b).or c = a.or (b.or c)

-- Identity
theorem and_true (a : Trilean) : a.and .true = a
theorem or_false (a : Trilean) : a.or .false = a

-- Annihilation
theorem and_false (a : Trilean) : a.and .false = .false
theorem or_true (a : Trilean) : a.or .true = .true

-- Idempotence
theorem and_self (a : Trilean) : a.and a = a
theorem or_self (a : Trilean) : a.or a = a

-- De Morgan's Laws
theorem not_and (a b : Trilean) : (a.and b).not = a.not.or b.not
theorem not_or (a b : Trilean) : (a.or b).not = a.not.and b.not

-- Double Negation
theorem not_not (a : Trilean) : a.not.not = a
```

### 4.2 UNKNOWN Propagation

```lean
-- UNKNOWN propagates through most operations
theorem unknown_and_unknown : Trilean.unknown.and .unknown = .unknown
theorem unknown_or_unknown : Trilean.unknown.or .unknown = .unknown
theorem not_unknown : Trilean.unknown.not = .unknown

-- But dominators override UNKNOWN
theorem false_dominates_and (a : Trilean) : Trilean.false.and a = .false
theorem true_dominates_or (a : Trilean) : Trilean.true.or a = .true
```

### 4.3 Conversion Roundtrips

```lean
-- Bool → Trilean → Bool roundtrip (for non-unknown)
theorem bool_roundtrip (b : Bool) : (Trilean.ofBool b).toBool = b

-- toBool loses information
theorem toBool_unknown_is_false : Trilean.unknown.toBool = false
```

---

## 5. SQL Semantics Implications

### 5.1 WHERE Clause Behavior

```sql
-- Only rows where condition is TRUE are included
SELECT * FROM t WHERE condition

-- Equivalent to:
SELECT * FROM t WHERE condition = TRUE
-- NOT equivalent to:
SELECT * FROM t WHERE condition <> FALSE  -- This includes UNKNOWN!
```

**Implementation note:** `toBool` correctly maps UNKNOWN to false, matching SQL WHERE semantics.

### 5.2 Common Pitfalls

| Expression | Result | Why |
|------------|--------|-----|
| `NULL = NULL` | UNKNOWN | Equality with NULL is always UNKNOWN |
| `NOT (NULL = NULL)` | UNKNOWN | NOT UNKNOWN = UNKNOWN |
| `x = 1 OR x = NULL` | TRUE or UNKNOWN | Never definitively FALSE |
| `x = 1 AND x = NULL` | FALSE or UNKNOWN | Never definitively TRUE |

---

## 6. Testing Strategy

### 6.1 Exhaustive Testing

With only 3 values, we can exhaustively test:
- 3 values for unary operations (NOT): 3 tests
- 9 combinations for binary operations (AND, OR): 9 tests each

```lean
-- Verify full truth tables
#guard Trilean.true.and .true = .true
#guard Trilean.true.and .false = .false
#guard Trilean.true.and .unknown = .unknown
-- ... all 9 combinations
```

### 6.2 Property Tests

```lean
-- Verify algebraic properties by enumeration
#guard ∀ a b : Trilean, a.and b = b.and a  -- comm
#guard ∀ a : Trilean, a.and .true = a      -- identity
```

---

## 7. References

- ISO/IEC 9075 SQL Standard, Section 8.12 (Comparison predicates)
- C.J. Date, "SQL and Relational Theory", Chapter 4 (Missing Information)
- E.F. Codd, "Extending the Database Relational Model to Capture More Meaning" (1979)
