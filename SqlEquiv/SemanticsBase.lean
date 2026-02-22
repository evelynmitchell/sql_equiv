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

/-- Get value from row by column name -/
def Row.get (row : Row) (col : String) : Option Value :=
  row.lookup col

/-- Get value from row by qualified column name -/
def Row.getQualified (row : Row) (table : Option String) (col : String) : Option Value :=
  match table with
  | some t => row.lookup s!"{t}.{col}"
  | none =>
    -- Try unqualified first, then any qualified match
    match row.lookup col with
    | some v => some v
    | none =>
      match row.find? (fun (k, _) => k.endsWith s!".{col}") with
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
  | _, _ => none  -- type mismatch

/-- Compare two values for ordering -/
def Value.compare : Value → Value → Option Ordering
  | .null _, _ => none
  | _, .null _ => none
  | .int a, .int b => some (Ord.compare a b)
  | .string a, .string b => some (Ord.compare a b)
  | _, _ => none

/-- Convert value to boolean for WHERE clauses -/
def Value.toBool : Value → Option Bool
  | .bool b => some b
  | .null _ => none
  | .int n => some (n != 0)
  | _ => none

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
  | .sub, some (.null _), some _ => some (.null none)
  | .sub, some _, some (.null _) => some (.null none)
  | .sub, some (.int a), some (.int b) => some (.int (a - b))
  | .mul, some (.null _), some _ => some (.null none)
  | .mul, some _, some (.null _) => some (.null none)
  | .mul, some (.int a), some (.int b) => some (.int (a * b))
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
  | "CONCAT", [some (.null t), some _] => some (.null t)
  | "CONCAT", [some _, some (.null t)] => some (.null t)
  | "CONCAT", [some (.string a), some (.string b)] => some (.string (a ++ b))
  | _, _ => none

/-- Get column name from expression for output -/
def exprToName : Expr → String
  | .col c => c.column
  | .func name _ => name
  | .agg .count _ _ => "count"
  | .agg .sum _ _ => "sum"
  | .agg .avg _ _ => "avg"
  | .agg .min _ _ => "min"
  | .agg .max _ _ => "max"
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
      | false =>
        cases r with
        | none => rfl
        | some w => cases w with
          | bool b' => cases b' <;> rfl
          | null _ => rfl
          | int _ => rfl
          | string _ => rfl
    | null _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl
    | int _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl
    | string _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl

end SqlEquiv
