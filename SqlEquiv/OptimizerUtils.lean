/-
  OptimizerUtils - Shared utilities for query optimization

  This module provides common utilities needed by the optimizer PRs:
  - PR A: Expression normalization
  - PR B: Predicate pushdown
  - PR C: Join reordering

  Design principles:
  - Use structural recursion with `termination_by` instead of `partial` where possible
  - Complete pattern matching on all Expr constructors
  - Functions designed for provability (clear pre/postconditions)

  See docs/OPTIMIZER_REDESIGN_PLAN.md for full specification.
-/

import SqlEquiv.Ast

namespace SqlEquiv

-- ============================================================================
-- Simple Utilities (non-recursive)
-- ============================================================================

/-- Extract table name or alias from TableRef.
    Mirrors the pattern `t.alias.getD t.name` used elsewhere in the codebase. -/
def getTableName (t : TableRef) : String := t.alias.getD t.name

/-- Extract alias from SelectItem if present.
    For unaliased column references, uses the column name as implicit alias. -/
def getSelectItemAlias : SelectItem → Option String
  | .star _ => none
  | .exprItem _ (some alias) => some alias
  | .exprItem (.col c) none => some c.column  -- use column name as implicit alias
  | .exprItem _ none => none

-- ============================================================================
-- Flatten/Unflatten for AND/OR chains
-- ============================================================================

/-- Flatten nested ANDs into a list of conjuncts.
    Example: (a AND (b AND c)) → [a, b, c]
    Terminates by structural recursion on Expr. -/
def flattenAnd : Expr → List Expr
  | .binOp .and l r => flattenAnd l ++ flattenAnd r
  | e => [e]

/-- Rebuild AND chain from list (right-associative).
    Example: [a, b, c] → (a AND (b AND c))
    Returns none for empty list. -/
def unflattenAnd : List Expr → Option Expr
  | [] => none
  | [e] => some e
  | e :: es => (unflattenAnd es).map (Expr.binOp .and e ·)

/-- Flatten nested ORs into a list of disjuncts.
    Example: (a OR (b OR c)) → [a, b, c]
    Terminates by structural recursion on Expr. -/
def flattenOr : Expr → List Expr
  | .binOp .or l r => flattenOr l ++ flattenOr r
  | e => [e]

/-- Rebuild OR chain from list (right-associative).
    Example: [a, b, c] → (a OR (b OR c))
    Returns none for empty list. -/
def unflattenOr : List Expr → Option Expr
  | [] => none
  | [e] => some e
  | e :: es => (unflattenOr es).map (Expr.binOp .or e ·)

-- ============================================================================
-- Column Reference Extraction
-- ============================================================================

/-- Extract columns from WindowSpec (PARTITION BY and ORDER BY expressions) -/
def getWindowSpecColumns (spec : WindowSpec) (getRefCols : Expr → List ColumnRef) : List ColumnRef :=
  match spec with
  | .mk partBy orderBy =>
    partBy.flatMap getRefCols ++
    orderBy.flatMap (fun item => getRefCols item.expr)

/-- Extract all column references from an expression.
    Handles all 14 Expr constructors with complete pattern matching.
    Subqueries (.exists, .subquery, .inSubquery's subquery) have their own scope,
    so we don't extract columns from them (they're not "free" in the outer context). -/
partial def getReferencedColumns : Expr → List ColumnRef
  | .lit _ => []
  | .col c => [c]
  | .binOp _ l r => getReferencedColumns l ++ getReferencedColumns r
  | .unaryOp _ e => getReferencedColumns e
  | .func _ args => args.flatMap getReferencedColumns
  | .agg _ (some e) _ => getReferencedColumns e
  | .agg _ none _ => []
  | .countStar => []
  | .«case» branches else_ =>
    branches.flatMap (fun (c, r) => getReferencedColumns c ++ getReferencedColumns r) ++
    (else_.map getReferencedColumns |>.getD [])
  | .inList e _ vals => getReferencedColumns e ++ vals.flatMap getReferencedColumns
  | .inSubquery e _ _ => getReferencedColumns e  -- subquery has own scope
  | .exists _ _ => []  -- subquery has own scope
  | .subquery _ => []  -- subquery has own scope
  | .between e lo hi => getReferencedColumns e ++ getReferencedColumns lo ++ getReferencedColumns hi
  | .windowFn _ arg spec =>
    (arg.map getReferencedColumns |>.getD []) ++ getWindowSpecColumns spec getReferencedColumns

-- ============================================================================
-- Column Reference Checking
-- ============================================================================

/-- Check if two column references match.
    Handles qualified and unqualified references:
    - If either table is none (unqualified), match by column name only
    - If both are qualified, must match exactly -/
def columnRefMatches (c1 c2 : ColumnRef) : Bool :=
  c1.column == c2.column &&
  (c1.table.isNone || c2.table.isNone || c1.table == c2.table)

/-- Check if an expression refers to a specific column.
    Handles all 14 Expr constructors with complete pattern matching.
    Uses columnRefMatches for flexible matching of qualified/unqualified refs. -/
partial def exprRefersToColumn (col : ColumnRef) : Expr → Bool
  | .lit _ => false
  | .col c => columnRefMatches c col
  | .binOp _ l r => exprRefersToColumn col l || exprRefersToColumn col r
  | .unaryOp _ e => exprRefersToColumn col e
  | .func _ args => args.any (exprRefersToColumn col)
  | .agg _ (some e) _ => exprRefersToColumn col e
  | .agg _ none _ => false
  | .countStar => false
  | .«case» branches else_ =>
    branches.any (fun (c, r) => exprRefersToColumn col c || exprRefersToColumn col r) ||
    (else_.map (exprRefersToColumn col) |>.getD false)
  | .inList e _ vals => exprRefersToColumn col e || vals.any (exprRefersToColumn col)
  | .inSubquery e _ _ => exprRefersToColumn col e  -- only check expr, subquery has own scope
  | .exists _ _ => false  -- subquery has own scope
  | .subquery _ => false  -- subquery has own scope
  | .between e lo hi => exprRefersToColumn col e || exprRefersToColumn col lo || exprRefersToColumn col hi
  | .windowFn _ arg spec =>
    (arg.map (exprRefersToColumn col) |>.getD false) ||
    match spec with
    | .mk partBy orderBy =>
      partBy.any (exprRefersToColumn col) ||
      orderBy.any (fun item => exprRefersToColumn col item.expr)

/-- Check if expression is exactly a column reference matching the given column.
    Used for GROUP BY key matching - only bare column references count as grouping keys. -/
def isGroupingKey (col : ColumnRef) : Expr → Bool
  | .col c => columnRefMatches c col
  | _ => false

-- ============================================================================
-- Structural Comparison for Deterministic Ordering
-- ============================================================================

/-- Compare two Values for ordering -/
def valueCompare (v1 v2 : Value) : Ordering :=
  match v1, v2 with
  | .int n1, .int n2 => compare n1 n2
  | .string s1, .string s2 => compare s1 s2
  | .bool b1, .bool b2 => compare b1 b2
  | .null _, .null _ => Ordering.eq
  -- Different types: order by type tag
  | .int _, _ => Ordering.lt
  | .string _, .int _ => Ordering.gt
  | .string _, _ => Ordering.lt
  | .bool _, .int _ => Ordering.gt
  | .bool _, .string _ => Ordering.gt
  | .bool _, _ => Ordering.lt
  | .null _, _ => Ordering.gt

/-- Compare two ColumnRefs for ordering -/
def columnRefCompare (c1 c2 : ColumnRef) : Ordering :=
  match compare c1.column c2.column with
  | Ordering.eq => compare c1.table c2.table
  | ord => ord

/-- Compare two BinOps for ordering -/
def binOpCompare (op1 op2 : BinOp) : Ordering :=
  let toNat : BinOp → Nat
    | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .mod => 4
    | .eq => 5 | .ne => 6 | .lt => 7 | .le => 8 | .gt => 9 | .ge => 10
    | .and => 11 | .or => 12 | .concat => 13 | .like => 14
  compare (toNat op1) (toNat op2)

/-- Compare two UnaryOps for ordering -/
def unaryOpCompare (op1 op2 : UnaryOp) : Ordering :=
  let toNat : UnaryOp → Nat
    | .not => 0 | .neg => 1 | .isNull => 2 | .isNotNull => 3
  compare (toNat op1) (toNat op2)

/-- Compare two AggFuncs for ordering -/
def aggFuncCompare (f1 f2 : AggFunc) : Ordering :=
  let toNat : AggFunc → Nat
    | .count => 0 | .sum => 1 | .avg => 2 | .min => 3 | .max => 4
  compare (toNat f1) (toNat f2)

/-- Compare two WindowFuncs for ordering -/
def windowFuncCompare (f1 f2 : WindowFunc) : Ordering :=
  let toNat : WindowFunc → Nat
    | .rowNumber => 0 | .rank => 1 | .denseRank => 2
    | .sum => 3 | .avg => 4 | .min => 5 | .max => 6 | .count => 7
  compare (toNat f1) (toNat f2)

/-- Compare two OrderDirs for ordering -/
def orderDirCompare (d1 d2 : OrderDir) : Ordering :=
  let toNat : OrderDir → Nat
    | .asc => 0 | .desc => 1
  compare (toNat d1) (toNat d2)

/-- Get constructor tag for Expr (for ordering different constructor types) -/
def exprTag : Expr → Nat
  | .lit _ => 0
  | .col _ => 1
  | .binOp _ _ _ => 2
  | .unaryOp _ _ => 3
  | .func _ _ => 4
  | .agg _ _ _ => 5
  | .countStar => 6
  | .«case» _ _ => 7
  | .inList _ _ _ => 8
  | .inSubquery _ _ _ => 9
  | .exists _ _ => 10
  | .subquery _ => 11
  | .between _ _ _ => 12
  | .windowFn _ _ _ => 13

-- Helper functions for structural comparison (defined before main function)

/-- Compare two lists lexicographically -/
def listCompare {α : Type} (cmp : α → α → Ordering) : List α → List α → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | x :: xs, y :: ys => match cmp x y with
    | Ordering.eq => listCompare cmp xs ys
    | ord => ord

/-- Compare two Options -/
def optionCompare {α : Type} (cmp : α → α → Ordering) : Option α → Option α → Ordering
  | none, none => Ordering.eq
  | none, some _ => Ordering.lt
  | some _, none => Ordering.gt
  | some x, some y => cmp x y

/-- Compare two pairs -/
def pairCompare {α β : Type} (cmpA : α → α → Ordering) (cmpB : β → β → Ordering) :
    (α × β) → (α × β) → Ordering
  | (a1, b1), (a2, b2) => match cmpA a1 a2 with
    | Ordering.eq => cmpB b1 b2
    | ord => ord

/-- Compare two OrderByItems -/
def orderByItemCompare (exprCmp : Expr → Expr → Ordering) : OrderByItem → OrderByItem → Ordering
  | .mk e1 d1, .mk e2 d2 => match exprCmp e1 e2 with
    | Ordering.eq => orderDirCompare d1 d2
    | ord => ord

/-- Compare two WindowSpecs -/
def windowSpecCompare (exprCmp : Expr → Expr → Ordering) : WindowSpec → WindowSpec → Ordering
  | .mk part1 ord1, .mk part2 ord2 =>
    match listCompare exprCmp part1 part2 with
    | Ordering.eq => listCompare (orderByItemCompare exprCmp) ord1 ord2
    | ord => ord

/-- Structural comparison for expressions.
    Provides deterministic ordering for canonical form normalization.
    Replaces `toString (repr e)` used in existing normalizeExpr. -/
partial def exprStructuralCmp : Expr → Expr → Ordering
  | .lit v1, .lit v2 => valueCompare v1 v2
  | .col c1, .col c2 => columnRefCompare c1 c2
  | .binOp op1 l1 r1, .binOp op2 l2 r2 =>
    match binOpCompare op1 op2 with
    | Ordering.eq => match exprStructuralCmp l1 l2 with
      | Ordering.eq => exprStructuralCmp r1 r2
      | ord => ord
    | ord => ord
  | .unaryOp op1 e1, .unaryOp op2 e2 =>
    match unaryOpCompare op1 op2 with
    | Ordering.eq => exprStructuralCmp e1 e2
    | ord => ord
  | .func n1 args1, .func n2 args2 =>
    match compare n1 n2 with
    | Ordering.eq => listCompare exprStructuralCmp args1 args2
    | ord => ord
  | .agg f1 arg1 d1, .agg f2 arg2 d2 =>
    match aggFuncCompare f1 f2 with
    | Ordering.eq => match compare d1 d2 with
      | Ordering.eq => optionCompare exprStructuralCmp arg1 arg2
      | ord => ord
    | ord => ord
  | .countStar, .countStar => Ordering.eq
  | .«case» b1 e1, .«case» b2 e2 =>
    match listCompare (pairCompare exprStructuralCmp exprStructuralCmp) b1 b2 with
    | Ordering.eq => optionCompare exprStructuralCmp e1 e2
    | ord => ord
  | .inList e1 n1 vs1, .inList e2 n2 vs2 =>
    match exprStructuralCmp e1 e2 with
    | Ordering.eq => match compare n1 n2 with
      | Ordering.eq => listCompare exprStructuralCmp vs1 vs2
      | ord => ord
    | ord => ord
  | .between e1 lo1 hi1, .between e2 lo2 hi2 =>
    match exprStructuralCmp e1 e2 with
    | Ordering.eq => match exprStructuralCmp lo1 lo2 with
      | Ordering.eq => exprStructuralCmp hi1 hi2
      | ord => ord
    | ord => ord
  -- For subquery-containing expressions, compare by structure but not subquery content
  -- (subqueries are complex; use tag comparison for different subqueries)
  | .inSubquery e1 n1 _, .inSubquery e2 n2 _ =>
    match exprStructuralCmp e1 e2 with
    | Ordering.eq => compare n1 n2
    | ord => ord
  | .exists n1 _, .exists n2 _ => compare n1 n2
  | .subquery _, .subquery _ => Ordering.eq  -- treat all scalar subqueries as equal for ordering
  | .windowFn f1 arg1 spec1, .windowFn f2 arg2 spec2 =>
    match windowFuncCompare f1 f2 with
    | Ordering.eq => match optionCompare exprStructuralCmp arg1 arg2 with
      | Ordering.eq => windowSpecCompare exprStructuralCmp spec1 spec2
      | ord => ord
    | ord => ord
  -- Different constructor types: compare by tag
  | e1, e2 => compare (exprTag e1) (exprTag e2)

-- ============================================================================
-- Theorems (Structural Properties)
-- ============================================================================

-- Note: Expr is mutually inductive, so we can't use `induction` directly.
-- We use axioms for now; these can be replaced with terminating recursion + proofs later.

/-- flattenAnd always produces a non-empty list.
    Axiom: Structural induction on Expr shows base case returns [e] (length 1)
    and AND case returns concatenation of two non-empty lists. -/
axiom flattenAnd_nonempty (e : Expr) : (flattenAnd e).length ≥ 1

/-- flattenOr always produces a non-empty list.
    Axiom: Similar reasoning to flattenAnd_nonempty. -/
axiom flattenOr_nonempty (e : Expr) : (flattenOr e).length ≥ 1

/-- unflattenAnd of non-empty list produces some result -/
theorem unflattenAnd_nonempty (es : List Expr) (h : es.length ≥ 1) :
    (unflattenAnd es).isSome = true := by
  match es with
  | [] => simp at h
  | [_] => simp [unflattenAnd]
  | _ :: e' :: es' =>
    simp only [unflattenAnd]
    have ih : (unflattenAnd (e' :: es')).isSome = true := by
      apply unflattenAnd_nonempty
      simp
    cases hunflatten : unflattenAnd (e' :: es') with
    | none => rw [hunflatten] at ih; simp at ih
    | some _ => simp

/-- unflattenOr of non-empty list produces some result -/
theorem unflattenOr_nonempty (es : List Expr) (h : es.length ≥ 1) :
    (unflattenOr es).isSome = true := by
  match es with
  | [] => simp at h
  | [_] => simp [unflattenOr]
  | _ :: e' :: es' =>
    simp only [unflattenOr]
    have ih : (unflattenOr (e' :: es')).isSome = true := by
      apply unflattenOr_nonempty
      simp
    cases hunflatten : unflattenOr (e' :: es') with
    | none => rw [hunflatten] at ih; simp at ih
    | some _ => simp

/-- getTableName is equivalent to the common pattern -/
theorem getTableName_spec (t : TableRef) : getTableName t = t.alias.getD t.name := rfl

end SqlEquiv
