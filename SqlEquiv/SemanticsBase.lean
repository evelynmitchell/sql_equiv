/-
  SQL Semantics: Base Types and Operator Evaluators

  Core types (Row, Table, Database), value operations, and operator evaluators
  that are used by both the main evaluator (Semantics.lean) and the non-partial
  core evaluators (SemanticsCore.lean).
-/
import SqlEquiv.Ast

namespace SqlEquiv

-- ============================================================================
-- Core Types
-- ============================================================================

/-- A row is a mapping from column names to values -/
abbrev Row := List (String × Value)

/-- A table is a list of rows (bag semantics for now) -/
abbrev Table := List Row

/-- A database maps table names to tables -/
abbrev Database := String → Table

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Check if string contains substring (simple implementation) -/
def stringContains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else go h n
where
  go : List Char → List Char → Bool
  | [], _ => false
  | h :: hs, needle =>
    if needle.isPrefixOf (h :: hs) then true
    else go hs needle

/-- Enumerate a list with indices -/
def listEnumerate {α : Type} (xs : List α) : List (Nat × α) :=
  go 0 xs
where
  go (i : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (i, x) :: go (i + 1) xs

-- ============================================================================
-- Row Operations
-- ============================================================================

/-- Case-insensitive key lookup. SQL identifiers are case-insensitive
    (`country` resolves a column stored as `Country`), so all row lookups
    compare case-folded keys. First match wins: two columns whose names
    differ only by case collide deliberately, the same shadowing
    `List.lookup` already gave exact-duplicate keys.
    Structured like `List.lookup` so lookup lemmas port directly. -/
def Row.lookupCI : Row → String → Option Value
  | [], _ => none
  | (k, v) :: rest, key =>
    if k.toLower == key.toLower then some v else Row.lookupCI rest key

/-- Get value from row by column name -/
def Row.get (row : Row) (col : String) : Option Value :=
  row.lookupCI col

/-- Get value from row by qualified column name -/
def Row.getQualified (row : Row) (table : Option String) (col : String) : Option Value :=
  match table with
  | some t => row.lookupCI s!"{t}.{col}"
  | none =>
    -- First entry, in row order, whose key is `col` or ends in `.col`. A
    -- single pass, so that row order decides: correlated subquery rows are
    -- `inner ++ outer`, and an unqualified outer key (from a derived table)
    -- must not beat a qualified inner key (innermost scope wins, #253).
    match row.find? (fun (k, _) =>
        k.toLower == col.toLower || k.toLower.endsWith s!".{col.toLower}") with
    | some (_, v) => some v
    | none => none

-- ============================================================================
-- Value Operations
-- ============================================================================

/-- Compare two values for equality -/
def Value.eq : Value → Value → Option Bool
  | .null _, _ => none  -- NULL = anything is NULL
  | _, .null _ => none
  | .int a, .int b => some (a == b)
  | .string a, .string b => some (a == b)
  | .bool a, .bool b => some (a == b)
  -- Decimal: compare scale-aligned unscaled values (1.0 = 1.00)
  | .decimal u1 s1, .decimal u2 s2 =>
    some (u1 * 10 ^ (max s1 s2 - s1) == u2 * 10 ^ (max s1 s2 - s2))
  -- int↔decimal promotion (#201): 1 = 1.0 is TRUE, not a type error
  | .int a, .decimal u s => some (a * 10 ^ s == u)
  | .decimal u s, .int b => some (u == b * 10 ^ s)
  | _, _ => none  -- type mismatch

/-- Compare two values for ordering -/
def Value.compare : Value → Value → Option Ordering
  | .null _, _ => none
  | _, .null _ => none
  | .int a, .int b => some (Ord.compare a b)
  | .string a, .string b => some (Ord.compare a b)
  -- Decimal: compare scale-aligned unscaled values
  | .decimal u1 s1, .decimal u2 s2 =>
    some (Ord.compare (u1 * 10 ^ (max s1 s2 - s1)) (u2 * 10 ^ (max s1 s2 - s2)))
  -- int↔decimal promotion (#201)
  | .int a, .decimal u s => some (Ord.compare (a * 10 ^ s) u)
  | .decimal u s, .int b => some (Ord.compare u (b * 10 ^ s))
  | _, _ => none

/-- Convert value to boolean for WHERE clauses -/
def Value.toBool : Value → Option Bool
  | .bool b => some b
  | .null _ => none
  | .int n => some (n != 0)
  | .decimal u _ => some (u != 0)
  | _ => none

-- ============================================================================
-- Numeric Aggregation Helpers (#201)
-- ============================================================================

/-- Numeric view for aggregation: ints promote to scale-0 scaled integers. -/
def Value.toScaled? : Value → Option (Int × Nat)
  | .int n => some (n, 0)
  | .decimal u s => some (u, s)
  | _ => none

/-- True if any value is a decimal — drives the aggregate result type
    (SUM over a decimal column is decimal; over ints stays int). -/
def anyDecimal (vs : List Value) : Bool :=
  vs.any fun | .decimal _ _ => true | _ => false

/-- Scale-aligned sum of the numeric values in the list (non-numerics are
    ignored, matching the previous int-only behavior). Empty sums to (0, 0). -/
def sumScaled (vs : List Value) : Int × Nat :=
  (vs.filterMap Value.toScaled?).foldl
    (fun a b => (a.1 * 10 ^ (max a.2 b.2 - a.2) + b.1 * 10 ^ (max a.2 b.2 - b.2),
                 max a.2 b.2))
    (0, 0)

/-- Number of numeric values (the AVG denominator). -/
def countNumeric (vs : List Value) : Nat :=
  (vs.filterMap Value.toScaled?).length

/-- SUM over numerics: decimal iff any input was decimal. Empty gives int 0;
    callers that want SQL's NULL-on-empty guard with `countNumeric`. -/
def sumNumeric (vs : List Value) : Value :=
  if anyDecimal vs then Value.mkDecimal (sumScaled vs).1 (sumScaled vs).2
  else .int (sumScaled vs).1

/-- AVG over numerics (truncating division, consistent with the existing
    integer AVG); none when there are no numeric inputs. -/
def avgNumeric (vs : List Value) : Option Value :=
  let n := countNumeric vs
  if n == 0 then none
  else if anyDecimal vs then
    some (Value.mkDecimal ((sumScaled vs).1 / Int.ofNat n) (sumScaled vs).2)
  else some (.int ((sumScaled vs).1 / Int.ofNat n))

/-- Least (`wantMax = false`) or greatest value of a list under `Value.compare`;
    returns the original value (canonical form preserved). -/
def extremeValue (wantMax : Bool) (vs : List Value) : Option Value :=
  vs.foldl (fun acc v =>
    match acc with
    | none => some v
    | some m =>
      if Value.compare m v == some (if wantMax then .lt else .gt) then some v else acc) none

/-- MIN/MAX aggregate result (#256). NULLs and non-numeric, non-string values
    are skipped. Numerics compare scale-aware, strings by code point. Input
    mixing numbers and strings is resolved by `mode` (registry row 13):
    `.error` gives `none` (an error), `.typeClass` orders numbers before
    strings (sqlite), so MAX is the greatest string and MIN the least number.
    No eligible input gives NULL. -/
def minMaxAgg (mode : MixedMinMax) (wantMax : Bool) (vs : List Value) : Option Value :=
  let nums := vs.filter fun v => (Value.toScaled? v).isSome
  let strs := vs.filter fun v => match v with | .string _ => true | _ => false
  let pool : Option (List Value) :=
    if nums.isEmpty then some strs
    else if strs.isEmpty then some nums
    else match mode with
      | .error => none
      | .typeClass => some (if wantMax then strs else nums)
  pool.map fun p => (extremeValue wantMax p).getD (.null none)

-- ============================================================================
-- Expression Evaluation Helper Functions (standalone)
-- ============================================================================

/-- Simplified LIKE pattern matching.
    Uses List Char operations for guards and body so that properties
    (e.g., `simpleLike s s = true`) are provable without unfolding
    opaque String.startsWith / String.endsWith (which go through memcmpSlice). -/
def simpleLike (s pat : String) : Bool :=
  let sc := s.toList
  let pc := pat.toList
  if pat == "%" then true
  else if pc.head? == some '%' && pc.getLast? == some '%' then
    stringContains s (String.ofList (pc.drop 1 |>.dropLast))
  else if pc.head? == some '%' then
    (pc.drop 1).isSuffixOf sc
  else if pc.getLast? == some '%' then
    pc.dropLast.isPrefixOf sc
  else
    s == pat

/-- Evaluate binary operator.
    NULL SEMANTICS (Option 3): When either operand is a SQL NULL (`some (.null _)`),
    arithmetic/comparison/string ops return `some (.null none)` instead of `none`.
    This separates "SQL NULL propagation" from "evaluation error" (which remains `none`).
    AND/OR keep SQL three-valued logic short-circuit rules.
    Note: We use `some _` (not bare `_`) so that `none` (errors) still propagate as `none`. -/
def evalBinOp (op : BinOp) (l r : Option Value) : Option Value :=
  match op, l, r with
  -- Arithmetic: null propagation
  | .add, some (.null _), some _ => some (.null none)
  | .add, some _, some (.null _) => some (.null none)
  | .add, some (.int a), some (.int b) => some (.int (a + b))
  -- Decimal arithmetic: scale-align, compute, renormalize (#201).
  -- int↔decimal promotes the int to scale-0 decimal per the SQL standard.
  | .add, some (.decimal u1 s1), some (.decimal u2 s2) =>
    some (Value.mkDecimal
      (u1 * 10 ^ (max s1 s2 - s1) + u2 * 10 ^ (max s1 s2 - s2)) (max s1 s2))
  | .add, some (.int a), some (.decimal u s) => some (Value.mkDecimal (a * 10 ^ s + u) s)
  | .add, some (.decimal u s), some (.int b) => some (Value.mkDecimal (u + b * 10 ^ s) s)
  | .sub, some (.null _), some _ => some (.null none)
  | .sub, some _, some (.null _) => some (.null none)
  | .sub, some (.int a), some (.int b) => some (.int (a - b))
  | .sub, some (.decimal u1 s1), some (.decimal u2 s2) =>
    some (Value.mkDecimal
      (u1 * 10 ^ (max s1 s2 - s1) - u2 * 10 ^ (max s1 s2 - s2)) (max s1 s2))
  | .sub, some (.int a), some (.decimal u s) => some (Value.mkDecimal (a * 10 ^ s - u) s)
  | .sub, some (.decimal u s), some (.int b) => some (Value.mkDecimal (u - b * 10 ^ s) s)
  | .mul, some (.null _), some _ => some (.null none)
  | .mul, some _, some (.null _) => some (.null none)
  | .mul, some (.int a), some (.int b) => some (.int (a * b))
  | .mul, some (.decimal u1 s1), some (.decimal u2 s2) =>
    some (Value.mkDecimal (u1 * u2) (s1 + s2))
  | .mul, some (.int a), some (.decimal u s) => some (Value.mkDecimal (a * u) s)
  | .mul, some (.decimal u s), some (.int b) => some (Value.mkDecimal (u * b) s)
  -- NOTE: decimal div/mod intentionally fall to the error catch-all for now —
  -- result-scale policy is engine-specific and deferred (tracked in #201).
  | .div, some (.null _), some _ => some (.null none)
  | .div, some _, some (.null _) => some (.null none)
  | .div, some (.int a), some (.int b) =>
    if b == 0 then none else some (.int (a / b))
  | .mod, some (.null _), some _ => some (.null none)
  | .mod, some _, some (.null _) => some (.null none)
  | .mod, some (.int a), some (.int b) =>
    if b == 0 then none else some (.int (a % b))
  -- Comparison: null propagation (NULL = anything → NULL)
  | .eq, some (.null _), some _ => some (.null none)
  | .eq, some _, some (.null _) => some (.null none)
  | .eq, some a, some b => (a.eq b).map Value.bool
  | .ne, some (.null _), some _ => some (.null none)
  | .ne, some _, some (.null _) => some (.null none)
  | .ne, some a, some b => (a.eq b).map (fun b => Value.bool (!b))
  | .lt, some (.null _), some _ => some (.null none)
  | .lt, some _, some (.null _) => some (.null none)
  | .lt, some a, some b => (a.compare b).map (fun o => Value.bool (o == .lt))
  | .le, some (.null _), some _ => some (.null none)
  | .le, some _, some (.null _) => some (.null none)
  | .le, some a, some b => (a.compare b).map (fun o => Value.bool (o != .gt))
  | .gt, some (.null _), some _ => some (.null none)
  | .gt, some _, some (.null _) => some (.null none)
  | .gt, some a, some b => (a.compare b).map (fun o => Value.bool (o == .gt))
  | .ge, some (.null _), some _ => some (.null none)
  | .ge, some _, some (.null _) => some (.null none)
  | .ge, some a, some b => (a.compare b).map (fun o => Value.bool (o != .lt))
  -- Boolean: SQL three-valued logic
  -- Short-circuit rules (FALSE dominates AND, TRUE dominates OR)
  | .and, some (.bool a), some (.bool b) => some (.bool (a && b))
  | .and, some (.bool false), _ => some (.bool false)  -- FALSE AND anything = FALSE
  | .and, _, some (.bool false) => some (.bool false)
  -- AND: null propagation (after short-circuit, null + value = null; none still propagates)
  | .and, some (.null _), some _ => some (.null none)
  | .and, some _, some (.null _) => some (.null none)
  | .or, some (.bool a), some (.bool b) => some (.bool (a || b))
  | .or, some (.bool true), _ => some (.bool true)      -- TRUE OR anything = TRUE
  | .or, _, some (.bool true) => some (.bool true)
  -- OR: null propagation (after short-circuit, null + value = null; none still propagates)
  | .or, some (.null _), some _ => some (.null none)
  | .or, some _, some (.null _) => some (.null none)
  -- String: null propagation
  | .concat, some (.null _), some _ => some (.null none)
  | .concat, some _, some (.null _) => some (.null none)
  | .concat, some (.string a), some (.string b) => some (.string (a ++ b))
  | .like, some (.null _), some _ => some (.null none)
  | .like, some _, some (.null _) => some (.null none)
  | .like, some (.string s), some (.string pat) =>
    some (.bool (simpleLike s pat))
  -- Everything else is a genuine error (type mismatch, missing value)
  | _, _, _ => none

/-- Apply a set operation to two result tables. Shared by top-level Query
    evaluation and SubQuery evaluation (#218); SQL set-op semantics:
    UNION dedups, UNION ALL concatenates, INTERSECT/EXCEPT filter by
    membership. -/
def applySetOp (op : SetOp) (l r : Table) : Table :=
  match op with
  | .union => (l ++ r).eraseDups
  | .unionAll => l ++ r
  -- INTERSECT/EXCEPT are set operations per the SQL standard: duplicates are
  -- eliminated (#223). The ALL variants (kept duplicates) are not parsed yet.
  | .intersect => (l.filter fun row => r.contains row).eraseDups
  | .exceptOp => (l.filter fun row => !r.contains row).eraseDups

/-- Check if Option Value is NULL (none or some null) -/
def isNullValue : Option Value → Bool
  | none => true
  | some (.null _) => true
  | _ => false

/-- Evaluate unary operator.
    NULL SEMANTICS (Option 3): NOT/NEG on null returns `some (.null none)` instead of `none`. -/
def evalUnaryOp (op : UnaryOp) (e : Option Value) : Option Value :=
  match op, e with
  | .not, some (.bool b) => some (.bool (!b))
  | .not, some (.null _) => some (.null none)  -- NOT NULL = NULL
  | .neg, some (.int n) => some (.int (-n))
  | .neg, some (.decimal u s) => some (.decimal (-u) s)  -- canonical form preserved
  | .neg, some (.null _) => some (.null none)  -- -NULL = NULL
  | .isNull, v => some (.bool (isNullValue v))
  | .isNotNull, v => some (.bool (!isNullValue v))
  | _, _ => none

/-- Evaluate scalar function -/
def evalFunc (name : String) (args : List (Option Value)) : Option Value :=
  match name.toUpper, args with
  | "COALESCE", vals =>
    vals.find? (fun v => !isNullValue v) |>.join
  | "NULLIF", [some a, some b] =>
    if a.eq b == some true then some (.null none) else some a
  | "ABS", [some (.null _)] => some (.null none)
  | "ABS", [some (.int n)] => some (.int n.natAbs)
  | "LENGTH", [some (.null _)] => some (.null none)
  | "LENGTH", [some (.string s)] => some (.int s.length)
  | "UPPER", [some (.null _)] => some (.null none)
  | "UPPER", [some (.string s)] => some (.string s.toUpper)
  | "LOWER", [some (.null _)] => some (.null none)
  | "LOWER", [some (.string s)] => some (.string s.toLower)
  | "CONCAT", [some (.null _), some _] => some (.null none)
  | "CONCAT", [some _, some (.null _)] => some (.null none)
  | "CONCAT", [some (.string a), some (.string b)] => some (.string (a ++ b))
  | _, _ => none

/-- Get column name from expression for output -/
def exprToName : Expr → String
  | .col c => c.column
  | .func name _ => name
  | .agg .count _ _ => "count"
  | .agg .sum _ _ => "sum"
  | .agg .avg _ _ => "avg"
  | .agg (.min _) _ _ => "min"
  | .agg (.max _) _ _ => "max"
  | .countStar => "count"
  | _ => "expr"

-- ============================================================================
-- evalBinOp Lemmas
-- ============================================================================

/-- AND returns `some (.bool true)` iff both operands are `some (.bool true)`. -/
theorem evalBinOp_and_true_iff (l r : Option Value) :
    (evalBinOp .and l r == some (.bool true)) =
    ((l == some (.bool true)) && (r == some (.bool true))) := by
  cases l with
  | none =>
    cases r with
    | none => rfl
    | some w => cases w with
      | bool b => cases b <;> rfl
      | null _ => rfl
      | int _ => rfl
      | string _ => rfl
      | decimal _ _ => rfl
  | some v =>
    cases v with
    | bool b =>
      cases b with
      | true =>
        cases r with
        | none => rfl
        | some w => cases w with
          | bool b' => cases b' <;> rfl
          | null _ => rfl
          | int _ => rfl
          | string _ => rfl
          | decimal _ _ => rfl
      | false =>
        cases r with
        | none => rfl
        | some w => cases w with
          | bool b' => cases b' <;> rfl
          | null _ => rfl
          | int _ => rfl
          | string _ => rfl
          | decimal _ _ => rfl
    | null _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl
        | decimal _ _ => rfl
    | int _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl
        | decimal _ _ => rfl
    | string _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl
        | decimal _ _ => rfl
    | decimal _ _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl
        | decimal _ _ => rfl

end SqlEquiv
