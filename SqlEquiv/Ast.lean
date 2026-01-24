/-
  SQL Abstract Syntax Tree

  This module defines the core types for representing SQL statements.
  Built bottom-up: literals → expressions → clauses → statements
-/

namespace SqlEquiv

-- ============================================================================
-- Value Types
-- ============================================================================

/-- SQL value literals -/
inductive Value where
  | int    : Int → Value
  | string : String → Value
  | bool   : Bool → Value
  | null   : Value
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Column reference: optionally qualified with table name -/
structure ColumnRef where
  table  : Option String
  column : String
  deriving Repr, BEq, Inhabited, DecidableEq

-- ============================================================================
-- Operators
-- ============================================================================

/-- Binary operators -/
inductive BinOp where
  -- Arithmetic
  | add | sub | mul | div | mod
  -- Comparison
  | eq | ne | lt | le | gt | ge
  -- Logical
  | and | or
  -- String
  | concat
  | like
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Unary operators -/
inductive UnaryOp where
  | not
  | neg
  | isNull
  | isNotNull
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Table reference with optional alias -/
structure TableRef where
  name  : String
  alias : Option String
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Join types -/
inductive JoinType where
  | inner
  | left
  | right
  | full
  | cross
  deriving Repr, BEq, Inhabited, DecidableEq

/-- ORDER BY direction -/
inductive OrderDir where
  | asc
  | desc
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Set operations -/
inductive SetOp where
  | union
  | unionAll
  | intersect
  | except
  deriving Repr, BEq, Inhabited, DecidableEq

-- ============================================================================
-- Core Types (with manual instances due to mutual recursion)
-- ============================================================================

/-- SQL expression AST -/
inductive Expr where
  | lit     : Value → Expr
  | col     : ColumnRef → Expr
  | binOp   : BinOp → Expr → Expr → Expr
  | unaryOp : UnaryOp → Expr → Expr
  | func    : String → List Expr → Expr  -- function call
  | «case»  : List (Expr × Expr) → Option Expr → Expr  -- CASE WHEN ... ELSE
  | inList  : Expr → List Expr → Expr
  | between : Expr → Expr → Expr → Expr

/-- ORDER BY item -/
structure OrderByItem where
  expr : Expr
  dir  : OrderDir

/-- SELECT item: an expression with optional alias, or * -/
inductive SelectItem where
  | star      : Option String → SelectItem           -- * or table.*
  | exprItem  : Expr → Option String → SelectItem    -- expr AS alias

/-- FROM clause source: can be a table or join -/
inductive FromClause where
  | table    : TableRef → FromClause
  | join     : FromClause → JoinType → FromClause → Option Expr → FromClause

/-- Full SELECT statement -/
structure SelectStmt where
  distinct : Bool
  items    : List SelectItem
  fromClause : Option FromClause
  whereClause : Option Expr
  groupBy  : List Expr
  having   : Option Expr
  orderBy  : List OrderByItem
  limitVal : Option Nat
  offsetVal : Option Nat

/-- Values source for INSERT -/
inductive InsertSource where
  | values : List (List Expr) → InsertSource  -- multiple rows
  | select : SelectStmt → InsertSource

/-- Column assignment: column = expr -/
structure Assignment where
  column : String
  value  : Expr

/-- INSERT statement -/
structure InsertStmt where
  table   : String
  columns : Option (List String)  -- None means all columns
  source  : InsertSource

/-- UPDATE statement -/
structure UpdateStmt where
  table       : String
  assignments : List Assignment
  whereClause : Option Expr

/-- DELETE statement -/
structure DeleteStmt where
  table  : String
  whereClause : Option Expr

/-- Any SQL DML statement -/
inductive Stmt where
  | select : SelectStmt → Stmt
  | insert : InsertStmt → Stmt
  | update : UpdateStmt → Stmt
  | delete : DeleteStmt → Stmt

-- ============================================================================
-- ToString instances (simpler than Repr for debugging)
-- ============================================================================

mutual
  partial def Expr.toReprStr : Expr → String
    | .lit v => s!"Expr.lit {repr v}"
    | .col c => s!"Expr.col {repr c}"
    | .binOp op l r => s!"Expr.binOp {repr op} ({l.toReprStr}) ({r.toReprStr})"
    | .unaryOp op e => s!"Expr.unaryOp {repr op} ({e.toReprStr})"
    | .func name args => s!"Expr.func {repr name} [{", ".intercalate (args.map Expr.toReprStr)}]"
    | .case branches else_ =>
      let brStr := branches.map fun (c, r) => s!"({c.toReprStr}, {r.toReprStr})"
      s!"Expr.case [{", ".intercalate brStr}] {else_.map Expr.toReprStr}"
    | .inList e vals => s!"Expr.inList ({e.toReprStr}) [{", ".intercalate (vals.map Expr.toReprStr)}]"
    | .between e lo hi => s!"Expr.between ({e.toReprStr}) ({lo.toReprStr}) ({hi.toReprStr})"

  partial def SelectItem.toReprStr : SelectItem → String
    | .star t => s!"SelectItem.star {repr t}"
    | .exprItem e a => s!"SelectItem.exprItem ({Expr.toReprStr e}) {repr a}"

  partial def FromClause.toReprStr : FromClause → String
    | .table t => s!"FromClause.table {repr t}"
    | .join l jt r on_ =>
      s!"FromClause.join ({FromClause.toReprStr l}) {repr jt} ({FromClause.toReprStr r}) {on_.map Expr.toReprStr}"

  partial def OrderByItem.toReprStr : OrderByItem → String
    | ⟨e, d⟩ => s!"OrderByItem.mk ({Expr.toReprStr e}) {repr d}"

  partial def SelectStmt.toReprStr : SelectStmt → String
    | ⟨d, items, f, w, g, h, o, l, off⟩ =>
      s!"SelectStmt.mk {d} [{", ".intercalate (items.map SelectItem.toReprStr)}] {f.map FromClause.toReprStr} {w.map Expr.toReprStr} [{", ".intercalate (g.map Expr.toReprStr)}] {h.map Expr.toReprStr} [{", ".intercalate (o.map OrderByItem.toReprStr)}] {l} {off}"

  partial def InsertSource.toReprStr : InsertSource → String
    | .values rows =>
      let rowStrs := rows.map fun row => s!"[{", ".intercalate (row.map Expr.toReprStr)}]"
      s!"InsertSource.values [{", ".intercalate rowStrs}]"
    | .select sel => s!"InsertSource.select ({SelectStmt.toReprStr sel})"

  partial def Assignment.toReprStr : Assignment → String
    | ⟨c, v⟩ => s!"Assignment.mk {repr c} ({Expr.toReprStr v})"
end

instance : Repr Expr where reprPrec e _ := e.toReprStr
instance : Repr SelectItem where reprPrec i _ := i.toReprStr
instance : Repr FromClause where reprPrec f _ := f.toReprStr
instance : Repr OrderByItem where reprPrec o _ := o.toReprStr
instance : Repr SelectStmt where reprPrec s _ := s.toReprStr
instance : Repr InsertSource where reprPrec s _ := s.toReprStr
instance : Repr Assignment where reprPrec a _ := a.toReprStr

instance : Repr InsertStmt where
  reprPrec i _ := s!"InsertStmt.mk {repr i.table} {repr i.columns} ({InsertSource.toReprStr i.source})"

instance : Repr UpdateStmt where
  reprPrec u _ := s!"UpdateStmt.mk {repr u.table} [{", ".intercalate (u.assignments.map Assignment.toReprStr)}] {u.whereClause.map Expr.toReprStr}"

instance : Repr DeleteStmt where
  reprPrec d _ := s!"DeleteStmt.mk {repr d.table} {d.whereClause.map Expr.toReprStr}"

instance : Repr Stmt where
  reprPrec s _ := match s with
    | .select sel => s!"Stmt.select ({SelectStmt.toReprStr sel})"
    | .insert ins => s!"Stmt.insert ({repr ins})"
    | .update upd => s!"Stmt.update ({repr upd})"
    | .delete del => s!"Stmt.delete ({repr del})"

-- ============================================================================
-- BEq instances
-- ============================================================================

mutual
  partial def Expr.beq : Expr → Expr → Bool
    | .lit v1, .lit v2 => v1 == v2
    | .col c1, .col c2 => c1 == c2
    | .binOp op1 l1 r1, .binOp op2 l2 r2 => op1 == op2 && Expr.beq l1 l2 && Expr.beq r1 r2
    | .unaryOp op1 e1, .unaryOp op2 e2 => op1 == op2 && Expr.beq e1 e2
    | .func n1 a1, .func n2 a2 => n1 == n2 && a1.length == a2.length && (a1.zip a2).all (fun (x, y) => Expr.beq x y)
    | .case b1 e1, .case b2 e2 =>
      b1.length == b2.length &&
      (b1.zip b2).all (fun ((c1, r1), (c2, r2)) => Expr.beq c1 c2 && Expr.beq r1 r2) &&
      match e1, e2 with
      | none, none => true
      | some x, some y => Expr.beq x y
      | _, _ => false
    | .inList e1 v1, .inList e2 v2 =>
      Expr.beq e1 e2 && v1.length == v2.length && (v1.zip v2).all (fun (x, y) => Expr.beq x y)
    | .between e1 l1 h1, .between e2 l2 h2 => Expr.beq e1 e2 && Expr.beq l1 l2 && Expr.beq h1 h2
    | _, _ => false

  partial def SelectItem.beq : SelectItem → SelectItem → Bool
    | .star t1, .star t2 => t1 == t2
    | .exprItem e1 a1, .exprItem e2 a2 => Expr.beq e1 e2 && a1 == a2
    | _, _ => false

  partial def FromClause.beq : FromClause → FromClause → Bool
    | .table t1, .table t2 => t1 == t2
    | .join l1 jt1 r1 on1, .join l2 jt2 r2 on2 =>
      FromClause.beq l1 l2 && jt1 == jt2 && FromClause.beq r1 r2 &&
      match on1, on2 with
      | none, none => true
      | some x, some y => Expr.beq x y
      | _, _ => false
    | _, _ => false

  partial def OrderByItem.beq : OrderByItem → OrderByItem → Bool
    | ⟨e1, d1⟩, ⟨e2, d2⟩ => Expr.beq e1 e2 && d1 == d2

  partial def SelectStmt.beq : SelectStmt → SelectStmt → Bool
    | ⟨d1, i1, f1, w1, g1, h1, o1, l1, off1⟩, ⟨d2, i2, f2, w2, g2, h2, o2, l2, off2⟩ =>
      d1 == d2 &&
      i1.length == i2.length && (i1.zip i2).all (fun (x, y) => SelectItem.beq x y) &&
      (match f1, f2 with | none, none => true | some x, some y => FromClause.beq x y | _, _ => false) &&
      (match w1, w2 with | none, none => true | some x, some y => Expr.beq x y | _, _ => false) &&
      g1.length == g2.length && (g1.zip g2).all (fun (x, y) => Expr.beq x y) &&
      (match h1, h2 with | none, none => true | some x, some y => Expr.beq x y | _, _ => false) &&
      o1.length == o2.length && (o1.zip o2).all (fun (x, y) => OrderByItem.beq x y) &&
      l1 == l2 && off1 == off2

  partial def InsertSource.beq : InsertSource → InsertSource → Bool
    | .values r1, .values r2 =>
      r1.length == r2.length &&
      (r1.zip r2).all (fun (row1, row2) =>
        row1.length == row2.length && (row1.zip row2).all (fun (x, y) => Expr.beq x y))
    | .select s1, .select s2 => SelectStmt.beq s1 s2
    | _, _ => false

  partial def Assignment.beq : Assignment → Assignment → Bool
    | ⟨c1, v1⟩, ⟨c2, v2⟩ => c1 == c2 && Expr.beq v1 v2
end

instance : BEq Expr where beq := Expr.beq
instance : BEq SelectItem where beq := SelectItem.beq
instance : BEq FromClause where beq := FromClause.beq
instance : BEq OrderByItem where beq := OrderByItem.beq
instance : BEq SelectStmt where beq := SelectStmt.beq
instance : BEq InsertSource where beq := InsertSource.beq
instance : BEq Assignment where beq := Assignment.beq

instance : BEq InsertStmt where
  beq i1 i2 := i1.table == i2.table && i1.columns == i2.columns && InsertSource.beq i1.source i2.source

instance : BEq UpdateStmt where
  beq u1 u2 :=
    u1.table == u2.table &&
    u1.assignments.length == u2.assignments.length &&
    (u1.assignments.zip u2.assignments).all (fun (x, y) => Assignment.beq x y) &&
    match u1.whereClause, u2.whereClause with
    | none, none => true
    | some x, some y => Expr.beq x y
    | _, _ => false

instance : BEq DeleteStmt where
  beq d1 d2 :=
    d1.table == d2.table &&
    match d1.whereClause, d2.whereClause with
    | none, none => true
    | some x, some y => Expr.beq x y
    | _, _ => false

instance : BEq Stmt where
  beq s1 s2 := match s1, s2 with
    | .select x, .select y => SelectStmt.beq x y
    | .insert x, .insert y => x == y
    | .update x, .update y => x == y
    | .delete x, .delete y => x == y
    | _, _ => false

-- ============================================================================
-- Inhabited instances
-- ============================================================================

instance : Inhabited Expr where default := .lit .null
instance : Inhabited SelectItem where default := .star none
instance : Inhabited FromClause where default := .table ⟨"", none⟩
instance : Inhabited OrderByItem where default := ⟨default, .asc⟩
instance : Inhabited SelectStmt where
  default := ⟨false, [], none, none, [], none, [], none, none⟩
instance : Inhabited InsertSource where default := .values []
instance : Inhabited Assignment where default := ⟨"", default⟩
instance : Inhabited InsertStmt where default := ⟨"", none, default⟩
instance : Inhabited UpdateStmt where default := ⟨"", [], none⟩
instance : Inhabited DeleteStmt where default := ⟨"", none⟩
instance : Inhabited Stmt where default := .select default

end SqlEquiv
