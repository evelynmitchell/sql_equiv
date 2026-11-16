/-
  Typed core phase 6 (#295): elaborating parsed SQL into the typed core.

  `elabQuery` translates a parsed `SqlEquiv.Query` in the core fragment into a
  `SqlCore.Query S n` over a schema `S`, resolving column names to positions
  with `SqlCore.resolveColumn` (exact names, ambiguity is an error; decision 7).
  Failures are distinct: an unknown table, an unknown or ambiguous column, a
  construct outside the fragment, or a type error found by `Query.typeOf`.

  The fragment: SELECT [DISTINCT] items FROM tables, inner and cross joins
  (with or without ON), WHERE, UNION ALL and UNION (as DISTINCT of UNION ALL);
  expressions: literals, columns, arithmetic, comparisons, AND/OR/NOT,
  IS [NOT] NULL, ||, [NOT] IN over literals, CASE, and BETWEEN (desugared to
  two comparisons). Untyped `NULL` takes its type from the operand it meets.
-/
import SqlEquiv
import SqlCore

namespace SqlBridge

open SqlCore

/-- Why a parsed query does not elaborate. -/
inductive ElabError where
  | unknownTable (name : String)
  | unknownColumn (qualifier : Option String) (name : String)
  | ambiguousColumn (qualifier : Option String) (name : String)
  /-- A construct outside the typed core's fragment. -/
  | unsupported (what : String)
  /-- The elaborated query is ill-typed (`Query.typeOf = none`). -/
  | typeError (what : String)
  deriving Repr, BEq, Inhabited

/-- A short category name, for reports. -/
def ElabError.category : ElabError → String
  | .unknownTable _ => "unknownTable"
  | .unknownColumn _ _ => "unknownColumn"
  | .ambiguousColumn _ _ => "ambiguousColumn"
  | .unsupported what => s!"unsupported: {what}"
  | .typeError _ => "typeError"

/-- A schema with names for its tables. -/
structure NamedSchema where
  S : DbSchema
  tables : List (String × S.Table)

abbrev ElabM := Except ElabError

/-- The value of a literal; `none` for `NULL`. -/
def elabValue : SqlEquiv.Value → Option Value
  | .int z => some (.int z)
  | .string s => some (.text s)
  | .bool b => some (.bool b)
  | .decimal u s => some (.decimal ((u : ℚ) / (10 ^ s : ℕ)))
  | .null _ => none

def elabType : SqlEquiv.SqlType → Option SqlType
  | .int => some .int
  | .string => some .text
  | .bool => some .bool
  | .decimal => some .decimal
  | .unknown => none

def elabUnOp : SqlEquiv.UnaryOp → UnOp
  | .not => .not | .neg => .neg | .isNull => .isNull | .isNotNull => .isNotNull

def elabBinOp : SqlEquiv.BinOp → ElabM BinOp
  | .add => pure (.arith .add) | .sub => pure (.arith .sub) | .mul => pure (.arith .mul)
  | .div => pure (.arith .div) | .mod => pure (.arith .mod)
  | .eq => pure (.cmp .eq) | .ne => pure (.cmp .ne) | .lt => pure (.cmp .lt)
  | .le => pure (.cmp .le) | .gt => pure (.cmp .gt) | .ge => pure (.cmp .ge)
  | .and => pure .and | .or => pure .or | .concat => pure .concat
  | .like => throw (.unsupported "LIKE") | .likeCI => throw (.unsupported "LIKE")

section Exprs

variable {n : ℕ} (cols : Fin n → Column)

/-- The typing context of a scope. -/
def ctx : Fin n → SqlType := fun i => (cols i).type

/-- Give an untyped `NULL` operand the type of the other operand. -/
def retypeNull (e other : Expr n) : Expr n :=
  match e, other.typeOf (ctx cols) with
  | .null _, some τ => .null τ
  | e, _ => e

def resolve (q : Option String) (name : String) : ElabM (Fin n) :=
  match resolveColumn cols q name with
  | .ok i => pure i
  | .error .unknownColumn => throw (.unknownColumn q name)
  | .error .ambiguousColumn => throw (.ambiguousColumn q name)

mutual

/-- Elaborate an expression in a scope. -/
def elabExpr : SqlEquiv.Expr → ElabM (Expr n)
  | .lit v =>
    match elabValue v, v with
    | some w, _ => pure (.lit w)
    | none, .null τ => pure (.null ((τ.bind elabType).getD .int))
    | none, _ => pure (.null .int)
  | .col c => return .col (← resolve cols c.table c.column)
  | .binOp op a b => do
    let op ← elabBinOp op
    let a ← elabExpr a
    let b ← elabExpr b
    pure (.binary op (retypeNull cols a b) (retypeNull cols b a))
  | .unaryOp op a => return .unary (elabUnOp op) (← elabExpr a)
  | .inList e neg vs => do
    let e ← elabExpr e
    let ds ← elabLits vs
    let t := Expr.inList e ds
    pure (if neg then .unary .not t else t)
  | .«case» branches els => do
    let els ← match els with
      | some b => elabExpr b
      | none => pure (.null .int)
    elabBranches els branches
  | .between e lo hi => do
    let e ← elabExpr e
    let lo ← elabExpr lo
    let hi ← elabExpr hi
    pure (.binary .and (.binary (.cmp .ge) e (retypeNull cols lo e))
      (.binary (.cmp .le) e (retypeNull cols hi e)))
  | .func name _ => throw (.unsupported s!"function {name}")
  | .agg _ _ _ => throw (.unsupported "aggregate")
  | .countStar => throw (.unsupported "aggregate")
  | .inSubquery _ _ _ => throw (.unsupported "subquery")
  | .exists _ _ => throw (.unsupported "subquery")
  | .subquery _ => throw (.unsupported "subquery")
  | .windowFn _ _ _ => throw (.unsupported "window function")

/-- The literal list of `IN`. -/
def elabLits : List SqlEquiv.Expr → ElabM (List Datum)
  | [] => pure []
  | .lit v :: vs => return elabValue v :: (← elabLits vs)
  | _ :: _ => throw (.unsupported "IN over non-literals")

/-- `CASE WHEN c₁ THEN a₁ … ELSE b END` as nested `caseWhen`. -/
def elabBranches (els : Expr n) : List (SqlEquiv.Expr × SqlEquiv.Expr) → ElabM (Expr n)
  | [] => pure els
  | (c, a) :: rest => do
    let c ← elabExpr c
    let a ← elabExpr a
    let rest ← elabBranches els rest
    pure (.caseWhen c (retypeNull cols a rest) (retypeNull cols rest a))

end

end Exprs

/-- An elaborated query: its arity, the query, and the names and types of its columns. -/
structure Elaborated (S : DbSchema) where
  n : ℕ
  q : Query S n
  cols : Fin n → Column

def requalify {n : ℕ} (q : String) (cols : Fin n → Column) : Fin n → Column :=
  fun i => { cols i with qualifier := some q }

variable (N : NamedSchema)

def lookupTable (name : String) : ElabM N.S.Table :=
  match N.tables.find? (·.1 == name) with
  | some (_, t) => pure t
  | none => throw (.unknownTable name)

def elabFrom : SqlEquiv.FromClause → ElabM (Elaborated N.S)
  | .table ⟨name, al⟩ => do
    let t ← lookupTable N name
    pure ⟨N.S.arity t, .table t, requalify (al.getD name) (N.S.columns t)⟩
  | .join l kind r on => do
    let ⟨n, ql, cl⟩ ← elabFrom l
    let ⟨m, qr, cr⟩ ← elabFrom r
    let cols : Fin (n + m) → Column := Fin.append cl cr
    let θ ← match kind, on with
      | .inner, some e => elabExpr cols e
      | .inner, none => pure (.lit (.bool true))
      | .cross, none => pure (.lit (.bool true))
      | .cross, some e => elabExpr cols e
      | .left, _ => throw (.unsupported "LEFT JOIN")
      | .right, _ => throw (.unsupported "RIGHT JOIN")
      | .full, _ => throw (.unsupported "FULL JOIN")
    pure ⟨n + m, .join θ ql qr, cols⟩
  | .subquery _ _ => throw (.unsupported "derived table")

/-- The expressions and output columns of a `SELECT` list. -/
def elabItems {n : ℕ} (cols : Fin n → Column) :
    List SqlEquiv.SelectItem → ElabM (List (Expr n × Column))
  | [] => pure []
  | .star none :: rest => do
    return ((List.finRange n).map fun i => (.col i, cols i)) ++ (← elabItems cols rest)
  | .star (some t) :: rest => do
    let mine := (List.finRange n).filter fun i => (cols i).qualifier == some t
    if mine.isEmpty then throw (.unknownTable t)
    return (mine.map fun i => (.col i, cols i)) ++ (← elabItems cols rest)
  | .exprItem e al :: rest => do
    let e' ← elabExpr cols e
    let some τ := e'.typeOf (ctx cols) | throw (.typeError "SELECT item")
    let name := al.getD (match e with | .col c => c.column | _ => "?column?")
    return (e', { qualifier := none, name, type := τ }) :: (← elabItems cols rest)

def elabSelect : SqlEquiv.SelectStmt → ElabM (Elaborated N.S)
  | .mk distinct items (some from_) where_ [] none [] none none => do
    let ⟨n, q, cols⟩ ← elabFrom N from_
    let q : Query N.S n ← match where_ with
      | none => pure q
      | some w => do pure (Query.select (← elabExpr cols w) q)
    let its ← elabItems cols items
    let k := its.length
    let es : Fin k → Expr n := fun i => (its[i]).1
    let outCols : Fin k → Column := fun i => (its[i]).2
    let q : Query N.S k := .project es q
    pure ⟨k, if distinct then .distinct q else q, outCols⟩
  | .mk _ _ none _ _ _ _ _ _ => throw (.unsupported "SELECT without FROM")
  | .mk _ _ _ _ (_ :: _) _ _ _ _ => throw (.unsupported "GROUP BY")
  | .mk _ _ _ _ _ (some _) _ _ _ => throw (.unsupported "HAVING")
  | .mk _ _ _ _ _ _ (_ :: _) _ _ => throw (.unsupported "ORDER BY")
  | .mk _ _ _ _ _ _ _ _ _ => throw (.unsupported "LIMIT/OFFSET")

def elabQueryRaw : SqlEquiv.Query → ElabM (Elaborated N.S)
  | .simple s => elabSelect N s
  | .compound l op r => do
    let ⟨n, ql, cl⟩ ← elabQueryRaw l
    let ⟨m, qr, _⟩ ← elabQueryRaw r
    if h : m = n then
      let u : Query N.S n := .unionAll ql (h ▸ qr)
      match op with
      | .unionAll => pure ⟨n, u, cl⟩
      | .union => pure ⟨n, .distinct u, cl⟩
      | .intersect => throw (.unsupported "INTERSECT")
      | .exceptOp => throw (.unsupported "EXCEPT")
    else throw (.typeError "set operation arity")
  | .withCTE _ _ => throw (.unsupported "WITH")

/-- Elaborate a parsed query, and check that the result is well-typed. -/
def elabQuery (q : SqlEquiv.Query) : ElabM (Elaborated N.S) := do
  let e ← elabQueryRaw N q
  if e.q.typeOf.isSome then pure e else throw (.typeError "query")

/-- Elaborate a parsed statement; only queries are in the fragment. -/
def elabStmt : SqlEquiv.Stmt → ElabM (Elaborated N.S)
  | .query q => elabQuery N q
  | _ => throw (.unsupported "DML")

end SqlBridge
