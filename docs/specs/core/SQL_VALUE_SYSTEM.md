# SQL Value System

## Cleanroom Specification

**Module:** `SqlEquiv/Ast.lean` (SqlType, Value namespaces)
**Status:** Implemented ✅
**Lines:** 15-140

---

## 1. Intended Function

The SQL value system represents all possible scalar values in SQL, including typed NULLs. This enables type-aware NULL handling which is critical for correct SQL semantics.

### 1.1 Black-Box Specification

```
SqlType : Type
  Represents SQL data types for type checking and typed NULL values.

Value : Type
  Represents SQL scalar values including integers, strings, booleans,
  and NULL (with optional type information).
```

### 1.2 Why Typed NULLs?

SQL NULL represents "unknown" or "missing" data, but NULLs can be typed:
```sql
CAST(NULL AS INTEGER)   -- typed NULL
NULL                    -- untyped NULL

-- Type matters for:
COALESCE(typed_null, 'default')  -- Type checking
UNION operations                  -- Column type matching
Function overloading             -- Argument type resolution
```

---

## 2. Data Types

### 2.1 SqlType

```lean
inductive SqlType where
  | int      -- Integer type
  | string   -- String/varchar type
  | bool     -- Boolean type
  | unknown  -- For untyped NULL or indeterminate expressions
  deriving Repr, BEq, Inhabited, DecidableEq
```

### 2.2 Value

```lean
inductive Value where
  | int    : Int → Value           -- Integer literal
  | string : String → Value        -- String literal
  | bool   : Bool → Value          -- Boolean literal
  | null   : Option SqlType → Value -- NULL with optional type
  deriving Repr, BEq, Inhabited, DecidableEq
```

**NULL representation:**
- `null (some .int)` — NULL known to be integer type
- `null (some .string)` — NULL known to be string type
- `null (some .bool)` — NULL known to be boolean type
- `null none` — Untyped NULL (type unknown)

---

## 3. Operations

### 3.1 Type Inference

```
Function: Value.sqlType
Signature: Value → SqlType

Purpose: Extract the SQL type from a value

Specification:
  sqlType (int _)          = SqlType.int
  sqlType (string _)       = SqlType.string
  sqlType (bool _)         = SqlType.bool
  sqlType (null (some t))  = t
  sqlType (null none)      = SqlType.unknown
```

**Implementation:**
```lean
def sqlType : Value → SqlType
  | .int _ => .int
  | .string _ => .string
  | .bool _ => .bool
  | .null (some t) => t
  | .null none => .unknown
```

### 3.2 NULL Predicates

```
Function: Value.isNull
Signature: Value → Bool

Purpose: Check if value is NULL (regardless of type)

Specification:
  isNull (null _) = true
  isNull _        = false


Function: Value.isNotNull
Signature: Value → Bool

Purpose: Check if value is definitely not NULL

Specification:
  isNotNull v = ¬(isNull v)
```

**Implementation:**
```lean
def isNull : Value → Bool
  | .null _ => true
  | _ => false

def isNotNull : Value → Bool
  | .null _ => false
  | _ => true
```

### 3.3 Typed NULL Constructors

```
Constants for common typed NULLs:

  nullInt     : Value := null (some .int)
  nullString  : Value := null (some .string)
  nullBool    : Value := null (some .bool)
  nullUntyped : Value := null none
```

### 3.4 Boolean Conversion

```
Function: Value.toTrilean
Signature: Value → Trilean

Purpose: Convert a Value to three-valued logic for boolean contexts

Specification:
  toTrilean (bool true)  = Trilean.true
  toTrilean (bool false) = Trilean.false
  toTrilean (null _)     = Trilean.unknown
  toTrilean _            = Trilean.unknown  -- non-boolean → unknown
```

**Implementation:**
```lean
def toTrilean : Value → Trilean
  | .bool true => .true
  | .bool false => .false
  | .null _ => .unknown
  | _ => .unknown  -- non-boolean treated as unknown in boolean context
```

**Note:** Non-boolean values (int, string) convert to UNKNOWN in boolean context. This matches SQL's strict type system where non-boolean values cannot be directly used as conditions.

---

## 4. Correctness Conditions

### 4.1 Type Consistency

```lean
-- Type of a value matches its constructor
theorem int_has_int_type (n : Int) : (Value.int n).sqlType = .int
theorem string_has_string_type (s : String) : (Value.string s).sqlType = .string
theorem bool_has_bool_type (b : Bool) : (Value.bool b).sqlType = .bool

-- Typed NULL preserves its type
theorem typed_null_preserves_type (t : SqlType) :
  (Value.null (some t)).sqlType = t

-- Untyped NULL has unknown type
theorem untyped_null_unknown : (Value.null none).sqlType = .unknown
```

### 4.2 NULL Predicate Properties

```lean
-- isNull and isNotNull are complements
theorem null_complement (v : Value) : v.isNull ≠ v.isNotNull

-- Only null constructor is NULL
theorem null_iff_constructor (v : Value) :
  v.isNull ↔ ∃ t, v = Value.null t

-- Non-null values are not NULL
theorem int_not_null (n : Int) : ¬(Value.int n).isNull
theorem string_not_null (s : String) : ¬(Value.string s).isNull
theorem bool_not_null (b : Bool) : ¬(Value.bool b).isNull
```

### 4.3 Trilean Conversion Properties

```lean
-- Boolean values convert correctly
theorem true_to_trilean : (Value.bool true).toTrilean = .true
theorem false_to_trilean : (Value.bool false).toTrilean = .false

-- NULL converts to unknown
theorem null_to_trilean (t : Option SqlType) : (Value.null t).toTrilean = .unknown

-- Non-boolean to unknown
theorem int_to_trilean (n : Int) : (Value.int n).toTrilean = .unknown
theorem string_to_trilean (s : String) : (Value.string s).toTrilean = .unknown
```

---

## 5. SQL Semantics Implications

### 5.1 Value Comparisons

When comparing values in SQL:

| Expression | Result | Why |
|------------|--------|-----|
| `1 = 1` | TRUE | Same integer value |
| `1 = 2` | FALSE | Different integer values |
| `1 = NULL` | UNKNOWN | Comparison with NULL |
| `NULL = NULL` | UNKNOWN | NULL is not equal to itself |
| `'a' = 'a'` | TRUE | Same string value |
| `1 = 'a'` | Error/FALSE | Type mismatch (implementation-dependent) |

### 5.2 Type Coercion

The current implementation does **not** include type coercion. Future work may add:
- Integer ↔ Float coercion
- String → Date parsing
- Numeric → String conversion

### 5.3 Interaction with Trilean

```
Value      → toTrilean    →  Trilean  → toBool → Bool
───────────────────────────────────────────────────────
bool true       →           true       →     true
bool false      →           false      →     false
null _          →           unknown    →     false
int/string      →           unknown    →     false
```

This chain is used in WHERE clause evaluation:
1. Expression evaluates to a Value
2. Value converts to Trilean
3. Trilean converts to Bool for filtering

---

## 6. Integration Points

### 6.1 Expression Evaluation

```lean
-- Expr uses Value for literals
| .lit : Value → Expr
```

The semantic evaluator (`Eval.lean`) uses Value throughout.

### 6.2 Row Representation

```lean
-- Row is a mapping from column names to values
Row := String → Option Value
```

### 6.3 Comparison Operators

Comparison operators in `BinOp` (eq, ne, lt, le, gt, ge) operate on Values and produce Trilean results.

---

## 7. Testing Strategy

### 7.1 Type Tests

```lean
-- Verify type inference
#guard (Value.int 42).sqlType == .int
#guard (Value.string "hello").sqlType == .string
#guard (Value.bool true).sqlType == .bool
#guard (Value.null (some .int)).sqlType == .int
#guard (Value.null none).sqlType == .unknown
```

### 7.2 NULL Predicate Tests

```lean
-- isNull tests
#guard (Value.null none).isNull == true
#guard (Value.null (some .int)).isNull == true
#guard (Value.int 1).isNull == false
#guard (Value.string "x").isNull == false
#guard (Value.bool false).isNull == false

-- isNotNull tests
#guard (Value.int 1).isNotNull == true
#guard (Value.null none).isNotNull == false
```

### 7.3 Trilean Conversion Tests

```lean
#guard (Value.bool true).toTrilean == .true
#guard (Value.bool false).toTrilean == .false
#guard (Value.null none).toTrilean == .unknown
#guard (Value.int 42).toTrilean == .unknown
```

---

## 8. Design Decisions

### 8.1 Why Optional Type for NULL?

**Option 1:** Single NULL value (no type info)
```lean
| null : Value  -- Simple but loses type information
```

**Option 2 (Chosen):** Optional type annotation
```lean
| null : Option SqlType → Value  -- Preserves type when known
```

The optional type approach:
- Matches SQL's CAST(NULL AS type) semantics
- Enables better type checking in UNION/COALESCE
- Preserves type information from schema context
- Allows untyped NULL when type is genuinely unknown

### 8.2 Why Unknown Type?

The `SqlType.unknown` variant handles:
- Untyped NULL literals
- Expressions with indeterminate types
- Error cases where type cannot be inferred

This avoids using `Option SqlType` throughout the codebase.

### 8.3 Non-Boolean to Unknown

The choice to convert non-boolean values to UNKNOWN (rather than error) in toTrilean:
- Simplifies evaluation logic
- Matches some SQL implementations' permissive behavior
- Errors should be caught at type-checking phase, not evaluation

---

## 9. References

- ISO/IEC 9075 SQL Standard, Section 4.5 (Data types)
- ISO/IEC 9075 SQL Standard, Section 8.1 (Predicate evaluation)
- C.J. Date, "SQL and Relational Theory", Chapter 4 (Nulls)
