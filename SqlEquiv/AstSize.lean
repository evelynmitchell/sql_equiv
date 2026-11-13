/-
  Computable size measure on the SQL AST (#212).

  The evaluator's mutually recursive functions (Semantics.lean) guard each
  recursive callback with a size check so that well-founded recursion is
  checked by the kernel. The auto-generated `sizeOf` instances have no
  executable code, so the guards, and the termination measure, use this
  hand-written structural `size` instead. Leaves (values, column refs, names)
  count 1: only the tree shape matters for termination.
-/
import SqlEquiv.Ast

namespace SqlEquiv

mutual

def WindowSpec.size : WindowSpec → Nat
  | .mk ps os => 1 + Expr.sizeList ps + OrderByItem.sizeList os

def Expr.size : Expr → Nat
  | .lit _ => 1
  | .col _ => 1
  | .binOp _ a b => 1 + a.size + b.size
  | .unaryOp _ a => 1 + a.size
  | .func _ as => 1 + Expr.sizeList as
  | .agg _ a _ => 1 + Expr.sizeOpt a
  | .countStar => 1
  | .«case» ws el => 1 + Expr.sizePairs ws + Expr.sizeOpt el
  | .inList a _ vs => 1 + a.size + Expr.sizeList vs
  | .inSubquery a _ sq => 1 + a.size + sq.size
  | .exists _ sq => 1 + sq.size
  | .subquery sq => 1 + sq.size
  | .between a b c => 1 + a.size + b.size + c.size
  | .windowFn _ a s => 1 + Expr.sizeOpt a + s.size

def Expr.sizeList : List Expr → Nat
  | [] => 0
  | e :: es => e.size + Expr.sizeList es

def Expr.sizeOpt : Option Expr → Nat
  | none => 0
  | some e => e.size

def Expr.sizePairs : List (Expr × Expr) → Nat
  | [] => 0
  | (a, b) :: r => a.size + b.size + Expr.sizePairs r

def OrderByItem.size : OrderByItem → Nat
  | .mk e _ _ => 1 + e.size

def OrderByItem.sizeList : List OrderByItem → Nat
  | [] => 0
  | o :: os => o.size + OrderByItem.sizeList os

def SelectItem.size : SelectItem → Nat
  | .star _ => 1
  | .exprItem e _ => 1 + e.size

def SelectItem.sizeList : List SelectItem → Nat
  | [] => 0
  | i :: is => i.size + SelectItem.sizeList is

def FromClause.size : FromClause → Nat
  | .table _ => 1
  | .subquery sq _ => 1 + sq.size
  | .join l _ r on_ => 1 + l.size + r.size + Expr.sizeOpt on_

def FromClause.sizeOpt : Option FromClause → Nat
  | none => 0
  | some f => f.size

def SubQuery.size : SubQuery → Nat
  | .simple s => 1 + s.size
  | .compound l _ r => 1 + l.size + r.size

def SelectStmt.size : SelectStmt → Nat
  | .mk _ items from_ w gb hv ob _ _ =>
    1 + SelectItem.sizeList items + FromClause.sizeOpt from_ + Expr.sizeOpt w +
      Expr.sizeList gb + Expr.sizeOpt hv + OrderByItem.sizeList ob

end

end SqlEquiv

namespace SqlEquiv

/-! ### Size lemmas (#212) -/

theorem Expr.size_pos (e : Expr) : 0 < e.size := by
  cases e <;> simp [Expr.size] <;> omega

theorem Expr.size_le_sizeList_of_mem {x : Expr} :
    ∀ {l : List Expr}, x ∈ l → x.size ≤ Expr.sizeList l
  | _ :: _, .head _ => by simp [Expr.sizeList]
  | _ :: _, .tail _ h => by
    have := Expr.size_le_sizeList_of_mem h
    simp [Expr.sizeList]; omega

theorem Expr.size_le_sizePairs_of_mem {a b : Expr} :
    ∀ {l : List (Expr × Expr)}, (a, b) ∈ l → a.size + b.size ≤ Expr.sizePairs l
  | _ :: _, .head _ => by simp [Expr.sizePairs]
  | (_, _) :: _, .tail _ h => by
    have := Expr.size_le_sizePairs_of_mem h
    simp [Expr.sizePairs]; omega

theorem FromClause.size_pos (fc : FromClause) : 0 < fc.size := by
  cases fc <;> simp [FromClause.size] <;> omega


theorem SelectItem.size_le_sizeList_of_mem {x : SelectItem} :
    ∀ {l : List SelectItem}, x ∈ l → x.size ≤ SelectItem.sizeList l
  | _ :: _, .head _ => by simp [SelectItem.sizeList]
  | _ :: _, .tail _ h => by
    have := SelectItem.size_le_sizeList_of_mem h
    simp [SelectItem.sizeList]; omega

theorem OrderByItem.size_le_sizeList_of_mem {x : OrderByItem} :
    ∀ {l : List OrderByItem}, x ∈ l → x.size ≤ OrderByItem.sizeList l
  | _ :: _, .head _ => by simp [OrderByItem.sizeList]
  | _ :: _, .tail _ h => by
    have := OrderByItem.size_le_sizeList_of_mem h
    simp [OrderByItem.sizeList]; omega

theorem OrderByItem.expr_size_lt (o : OrderByItem) : o.expr.size < o.size := by
  cases o; simp [OrderByItem.size, OrderByItem.expr]

theorem OrderByItem.size_pos (o : OrderByItem) : 0 < o.size := by
  cases o; simp [OrderByItem.size]; omega

end SqlEquiv
