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
  Phase 8 adds GROUP BY, aggregates and HAVING (#313), ORDER BY, LIMIT and
  OFFSET (#318), and INTERSECT, EXCEPT and LIKE (#322).
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

/-- A schema with names for its tables. `fold` normalises every referenced name (tables,
aliases, columns) before the exact lookup of decision 7; it is the identity unless the schema's
names were normalised the same way (for Spider: lowercase). -/
structure NamedSchema where
  S : DbSchema
  tables : List (String × S.Table)
  fold : String → String := id
  /-- The dialect's choices that elaboration follows; today only `bareColumns` (registry T9). -/
  config : SqlEquiv.DialectConfig := SqlEquiv.Dialect.standard.config

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
  | .like => pure (.like false) | .likeCI => pure (.like true)

section Exprs

variable {n : ℕ} (cols : Fin n → Column) (fold : String → String)
  (hook : SqlEquiv.Expr → Option (Expr n))

/-- The typing context of a scope. -/
def ctx : Fin n → SqlType := fun i => (cols i).type

/-- Give an untyped `NULL` operand the type of the other operand. -/
def retypeNull (e other : Expr n) : Expr n :=
  match e, other.typeOf (ctx cols) with
  | .null _, some τ => .null τ
  | e, _ => e

def resolve (q : Option String) (name : String) : ElabM (Fin n) :=
  match resolveColumn cols (q.map fold) (fold name) with
  | .ok i => pure i
  | .error .unknownColumn => throw (.unknownColumn q name)
  | .error .ambiguousColumn => throw (.ambiguousColumn q name)

mutual

/-- Elaborate an expression in a scope. `hook` is consulted first at every node; with `GROUP BY`
it maps aggregate calls and grouping keys to columns of the aggregate's output. -/
def elabExpr (e : SqlEquiv.Expr) : ElabM (Expr n) :=
  match hook e with
  | some e' => pure e'
  | none =>
  match e with
  | .lit v =>
    match elabValue v, v with
    | some w, _ => pure (.lit w)
    | none, .null τ => pure (.null ((τ.bind elabType).getD .int))
    | none, _ => pure (.null .int)
  | .col c => return .col (← resolve cols fold c.table c.column)
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

/-- No hook: plain elaboration. -/
def noHook {n : ℕ} : SqlEquiv.Expr → Option (Expr n) := fun _ => none

end Exprs

/-! ### Aggregates (phase 8a, #313) -/

mutual

/-- The aggregate calls in an expression, outermost first. -/
def aggsOf : SqlEquiv.Expr → List SqlEquiv.Expr
  | .agg fn arg d => [.agg fn arg d]
  | .countStar => [.countStar]
  | .binOp _ a b => aggsOf a ++ aggsOf b
  | .unaryOp _ a => aggsOf a
  | .inList e _ vs => aggsOf e ++ aggsOfList vs
  | .«case» bs els => aggsOfBranches bs ++ aggsOfOpt els
  | .between a b c => aggsOf a ++ aggsOf b ++ aggsOf c
  | .func _ args => aggsOfList args
  | _ => []

def aggsOfList : List SqlEquiv.Expr → List SqlEquiv.Expr
  | [] => []
  | e :: es => aggsOf e ++ aggsOfList es

def aggsOfOpt : Option SqlEquiv.Expr → List SqlEquiv.Expr
  | none => []
  | some e => aggsOf e

def aggsOfBranches : List (SqlEquiv.Expr × SqlEquiv.Expr) → List SqlEquiv.Expr
  | [] => []
  | (c, a) :: bs => aggsOf c ++ aggsOf a ++ aggsOfBranches bs

end

mutual

/-- The column references of an expression outside its aggregate calls: the candidates for bare
columns (registry T9). -/
def colsOutsideAggs : SqlEquiv.Expr → List SqlEquiv.ColumnRef
  | .col c => [c]
  | .agg _ _ _ => []
  | .countStar => []
  | .binOp _ a b => colsOutsideAggs a ++ colsOutsideAggs b
  | .unaryOp _ a => colsOutsideAggs a
  | .inList e _ vs => colsOutsideAggs e ++ colsOutsideAggsList vs
  | .«case» bs els => colsOutsideAggsBranches bs ++ colsOutsideAggsOpt els
  | .between a b c => colsOutsideAggs a ++ colsOutsideAggs b ++ colsOutsideAggs c
  | .func _ args => colsOutsideAggsList args
  | _ => []

def colsOutsideAggsList : List SqlEquiv.Expr → List SqlEquiv.ColumnRef
  | [] => []
  | e :: es => colsOutsideAggs e ++ colsOutsideAggsList es

def colsOutsideAggsOpt : Option SqlEquiv.Expr → List SqlEquiv.ColumnRef
  | none => []
  | some e => colsOutsideAggs e

def colsOutsideAggsBranches : List (SqlEquiv.Expr × SqlEquiv.Expr) → List SqlEquiv.ColumnRef
  | [] => []
  | (c, a) :: bs => colsOutsideAggs c ++ colsOutsideAggs a ++ colsOutsideAggsBranches bs

end

mutual

/-- The subqueries of an expression (phase 8f): scalar `(SELECT …)` and `e [NOT] IN (SELECT …)`
nodes, outermost first, with their bodies; nodes inside a subquery are not visited. -/
def subsOf : SqlEquiv.Expr → List (SqlEquiv.Expr × SqlEquiv.SubQuery)
  | .subquery sq => [(.subquery sq, sq)]
  | .inSubquery e neg sq => [(.inSubquery e neg sq, sq)]
  | .binOp _ a b => subsOf a ++ subsOf b
  | .unaryOp _ a => subsOf a
  | .inList e _ vs => subsOf e ++ subsOfList vs
  | .«case» bs els => subsOfBranches bs ++ subsOfOpt els
  | .between a b c => subsOf a ++ subsOf b ++ subsOf c
  | .func _ args => subsOfList args
  | _ => []

def subsOfList : List SqlEquiv.Expr → List (SqlEquiv.Expr × SqlEquiv.SubQuery)
  | [] => []
  | e :: es => subsOf e ++ subsOfList es

def subsOfOpt : Option SqlEquiv.Expr → List (SqlEquiv.Expr × SqlEquiv.SubQuery)
  | none => []
  | some e => subsOf e

def subsOfBranches : List (SqlEquiv.Expr × SqlEquiv.Expr) → List (SqlEquiv.Expr × SqlEquiv.SubQuery)
  | [] => []
  | (c, a) :: bs => subsOf c ++ subsOf a ++ subsOfBranches bs

end

/-- Whether a branch of a compound subquery has `ORDER BY`, `LIMIT` or `OFFSET`. -/
def subHasOrderOrLimit : SqlEquiv.SubQuery → Bool
  | .simple (.mk _ _ _ _ _ _ o l off) => !o.isEmpty || l.isSome || off.isSome
  | _ => false

/-- Elaborate one aggregate call over the input scope. -/
def elabAgg {n : ℕ} (cols : Fin n → Column) (fold : String → String) :
    SqlEquiv.Expr → ElabM (AggCall n)
  | .countStar => pure .countStar
  | .agg .count none _ => pure .countStar
  | .agg .count (some e) d => return .call .count d (← elabExpr cols fold noHook e)
  | .agg .sum (some e) d => return .call .sum d (← elabExpr cols fold noHook e)
  | .agg (.min _) (some e) d => return .call .min d (← elabExpr cols fold noHook e)
  | .agg (.max _) (some e) d => return .call .max d (← elabExpr cols fold noHook e)
  | .agg .avg (some e) d => return .call .avg d (← elabExpr cols fold noHook e)
  | _ => throw (.unsupported "aggregate")

/-- An elaborated query: its arity, the query, and the names and types of its columns. -/
structure Elaborated (S : DbSchema) where
  n : ℕ
  q : Query S n
  cols : Fin n → Column

def requalify {n : ℕ} (q : String) (cols : Fin n → Column) : Fin n → Column :=
  fun i => { cols i with qualifier := some q }

variable (N : NamedSchema)

def lookupTable (name : String) : ElabM N.S.Table :=
  match N.tables.find? (·.1 == N.fold name) with
  | some (_, t) => pure t
  | none => throw (.unknownTable name)

/-- Elaborate a `FROM` clause. `sub` elaborates the body of a derived table `(SELECT …) AS alias`
(phase 8f): its columns are requalified by the alias, as in `SqlEquiv` (#257). -/
def elabFrom (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S)) :
    SqlEquiv.FromClause → ElabM (Elaborated N.S)
  | .table ⟨name, al⟩ => do
    let t ← lookupTable N name
    pure ⟨N.S.arity t, .table t, requalify (N.fold (al.getD name)) (N.S.columns t)⟩
  | .join l kind r on => do
    let ⟨n, ql, cl⟩ ← elabFrom sub l
    let ⟨m, qr, cr⟩ ← elabFrom sub r
    let cols : Fin (n + m) → Column := Fin.append cl cr
    let θ ← match kind, on with
      | .inner, some e => elabExpr cols N.fold noHook e
      | .inner, none => pure (.lit (.bool true))
      | .cross, none => pure (.lit (.bool true))
      | .cross, some e => elabExpr cols N.fold noHook e
      | .left, _ => throw (.unsupported "LEFT JOIN")
      | .right, _ => throw (.unsupported "RIGHT JOIN")
      | .full, _ => throw (.unsupported "FULL JOIN")
    pure ⟨n + m, .join θ ql qr, cols⟩
  | .subquery sq al => do
    let ⟨n, q, cols⟩ ← sub sq
    pure ⟨n, q, requalify (N.fold al) cols⟩

/-- The expressions and output columns of a `SELECT` list. -/
def elabItems {n : ℕ} (cols : Fin n → Column) :
    List SqlEquiv.SelectItem → ElabM (List (Expr n × Column))
  | [] => pure []
  | .star none :: rest => do
    return ((List.finRange n).map fun i => (.col i, cols i)) ++ (← elabItems cols rest)
  | .star (some t) :: rest => do
    let mine := (List.finRange n).filter fun i => (cols i).qualifier == some (N.fold t)
    if mine.isEmpty then throw (.unknownTable t)
    return (mine.map fun i => (.col i, cols i)) ++ (← elabItems cols rest)
  | .exprItem e al :: rest => do
    let e' ← elabExpr cols N.fold noHook e
    let some τ := e'.typeOf (ctx cols) | throw (.typeError "SELECT item")
    let name := al.getD (match e with | .col c => c.column | _ => "?column?")
    return (e', { qualifier := none, name, type := τ }) :: (← elabItems cols rest)

/-- The aggregate's output scope: the key columns (a key that is a column keeps its name), then one
column per aggregate call. -/
def aggScope {n g a : ℕ} (cols : Fin n → Column) (keys : Fin g → Expr n) (aggs : Fin a → AggCall n) :
    ElabM (Fin (g + a) → Column) := do
  let keyCols ← (List.finRange g).mapM fun i => do
    let some τ := (keys i).typeOf (ctx cols) | throw (.typeError "GROUP BY key")
    pure (match keys i with
      | .col k => cols k
      | _ => ({ qualifier := none, name := "?column?", type := τ } : Column))
  let aggCols ← (List.finRange a).mapM fun j => do
    let some τ := (aggs j).typeOf (ctx cols) | throw (.typeError "aggregate")
    pure ({ qualifier := none, name := "?aggregate?", type := τ } : Column)
  if h : keyCols.length = g ∧ aggCols.length = a then
    pure (Fin.append (fun i => keyCols[i]'(by omega)) (fun j => aggCols[j]'(by omega)))
  else throw (.typeError "aggregate scope")

/-- The hook for the aggregate's output: an aggregate call becomes its column, and an expression
equal to a grouping key becomes the key's column. -/
def aggHook {n g a : ℕ} (cols : Fin n → Column) (fold : String → String) (keys : Fin g → Expr n)
    (aggExprs : List SqlEquiv.Expr) (e : SqlEquiv.Expr) : Option (Expr (g + a)) :=
  match aggExprs.findIdx? (· == e) with
  | some j => if h : j < a then some (.col (Fin.natAdd g ⟨j, h⟩)) else none
  | none =>
    match elabExpr cols fold noHook e with
    | .ok e' => ((List.finRange g).find? fun i => keys i == e').map fun i => .col (Fin.castAdd a i)
    | .error _ => none

/-- A `SELECT` before its projection (phase 8b): the query, a function elaborating an expression
in its scope, and the elaborated `SELECT` list. -/
structure Scoped (S : DbSchema) where
  m : ℕ
  q : Query S m
  scope : SqlEquiv.Expr → ElabM (Expr m)
  items : List (Expr m × Column)

/-- An `ORDER BY` item over the scope of a `SELECT`. As in Postgres and sqlite, an integer literal
is the position of a `SELECT` item, and a bare name is first looked up among the output column
names (an alias or a selected column); anything else is an expression of the input. -/
def elabOrderKey {m : ℕ} (fold : String → String) (sc : SqlEquiv.Expr → ElabM (Expr m))
    (its : List (Expr m × Column)) : SqlEquiv.OrderByItem → ElabM (SortKey m)
  | .mk e dir nulls => do
    let e' ← match e with
      | .lit (.int k) =>
        if h : 0 < k.toNat ∧ k.toNat ≤ its.length then pure (its[k.toNat - 1]'(by omega)).1
        else throw (.unsupported "ORDER BY position out of range")
      | .col ⟨none, c⟩ =>
        match (its.filter fun it => fold it.2.name == fold c).map (·.1) |>.eraseDups with
        | [] => sc e
        | [e'] => pure e'
        | _ => throw (.ambiguousColumn none c)
      | _ => sc e
    pure ⟨e', dir == .desc, nulls == .first⟩

/-- Projection, `DISTINCT`, `ORDER BY` and `LIMIT`/`OFFSET` over a scoped `SELECT`. Without
`DISTINCT` the sort is below the projection, so a key may be any expression of the input. With
`DISTINCT` and every key selected, the sort is above the `DISTINCT`, over the output columns.
With a key that is not selected (registry row 5: the parser has already rejected it in the
`standard` and `postgres` dialects), each distinct row sorts by the key of its first source row,
as in sqlite and DuckDB: `aggregate` groups by the selected expressions, in order of first
appearance like `DISTINCT`, with `AggCall.first` of each key; the sort is over those columns, and
a projection keeps the selected ones. -/
def finishSelect {S : DbSchema} (fold : String → String) (sc : Scoped S) (distinct : Bool)
    (orderBy : List SqlEquiv.OrderByItem) (limitVal offsetVal : Option ℕ) :
    ElabM (Elaborated S) := do
  let its := sc.items
  let k := its.length
  let keyList ← orderBy.mapM (elabOrderKey fold sc.scope its)
  if let some Γ := sc.q.typeOf then
    for key in keyList do
      if (key.e.typeOf Γ).isNone then throw (.typeError "ORDER BY key")
  let o := keyList.length
  let proj (q : Query S sc.m) : Query S k := .project (fun i => (its[i]).1) q
  let q : Query S k ←
    if distinct then
      let outKeys := keyList.filterMap fun key =>
        match its.findIdx? (·.1 == key.e) with
        | some i => if h : i < k then some ({ key with e := .col ⟨i, h⟩ } : SortKey k) else none
        | none => none
      let dq : Query S k := .distinct (proj sc.q)
      if h : outKeys.length = o then
        pure (if o = 0 then dq else .orderBy (fun i : Fin o => outKeys[i]'(by omega)) dq)
      else
        -- a key that is not selected: sort by its value on each distinct row's first source row
        let grouped : Query S (k + o) :=
          .aggregate (fun i : Fin k => (its[i]).1) (fun j : Fin o => .first (keyList[j]).e) sc.q
        let sortKeys : Fin o → SortKey (k + o) := fun j => { keyList[j] with e := .col (Fin.natAdd k j) }
        pure (.project (fun i : Fin k => .col (Fin.castAdd o i)) (.orderBy sortKeys grouped))
    else
      pure (if o = 0 then proj sc.q
        else proj (.orderBy (fun i : Fin o => keyList[i]) sc.q))
  let q : Query S k := match limitVal, offsetVal with
    | none, none => q
    | l, off => .limit l (off.getD 0) q
  pure ⟨k, q, fun i => (its[i]).2⟩

mutual

/-- Elaborate a subquery body. `fuel` bounds the nesting of subqueries, so that elaboration is a
total function. -/
def elabSubQuery (fuel : ℕ) (sq : SqlEquiv.SubQuery) : ElabM (Elaborated N.S) :=
  match fuel, sq with
  | 0, _ => throw (.unsupported "subqueries nested too deeply")
  | f + 1, .simple s => elabSelectF f s
  | f + 1, .compound l op r => do
    if subHasOrderOrLimit l || subHasOrderOrLimit r then
      throw (.unsupported "ORDER BY/LIMIT in a compound query")
    let ⟨n, ql, cl⟩ ← elabSubQuery f l
    let ⟨m, qr, _⟩ ← elabSubQuery f r
    if h : m = n then
      match op with
      | .unionAll => pure ⟨n, .unionAll ql (h ▸ qr), cl⟩
      | .union => pure ⟨n, .distinct (.unionAll ql (h ▸ qr)), cl⟩
      | .intersect => pure ⟨n, .intersect ql (h ▸ qr), cl⟩
      | .exceptOp => pure ⟨n, .difference ql (h ▸ qr), cl⟩
    else throw (.typeError "set operation arity")
termination_by fuel

/-- Elaborate a `SELECT`; its subqueries are elaborated with less fuel. -/
def elabSelectF (fuel : ℕ) (stmt : SqlEquiv.SelectStmt) : ElabM (Elaborated N.S) :=
  match stmt with
  | .mk distinct items (some from_) where_ groupBy having orderBy limitVal offsetVal => do
    let ⟨n, q, cols⟩ ← elabFrom N (fun sq => match fuel with
      | 0 => throw (.unsupported "subqueries nested too deeply")
      | f + 1 => elabSubQuery f sq) from_
    let q : Query N.S n ← match where_ with
      | none => pure q
      | some w =>
        -- Uncorrelated subqueries (phase 8f, #329): each becomes a column of the input
        -- (`Query.attach`), which the predicate reads; the extra columns are projected away.
        let subs := (subsOf w).foldl
          (fun acc x => if acc.any (·.1 == x.1) then acc else acc ++ [x]) []
        if subs.isEmpty then do pure (Query.select (← elabExpr cols N.fold noHook w) q)
        else do
          let subsE ← match fuel with
            | 0 => throw (.unsupported "subqueries nested too deeply")
            | f + 1 => subs.mapM fun (node, sq) => do
              let r ← match elabSubQuery f sq with
                | .ok r => pure r
                | .error (.unknownColumn qq c) =>
                  match resolveColumn cols (qq.map N.fold) (N.fold c) with
                  | .ok _ => throw (.unsupported "correlated subquery")
                  | .error _ => throw (.unknownColumn qq c)
                | .error err => throw err
              if h : r.n = 1 then
                pure (node, (h ▸ r.q : Query N.S 1), (r.cols ⟨0, by omega⟩).type)
              else throw (.typeError "subquery arity")
          let acc ← subsE.foldlM (init := (⟨n, q, cols⟩ : Elaborated N.S))
            fun acc (node, sub, τ) => do
              let (kind, ty) ← match node with
                | .subquery _ =>
                  pure (SubKind.scalar (N.config.scalarSubqueryRows == .firstRow), τ)
                | .inSubquery e neg _ => do
                  pure (SubKind.inSub neg (← elabExpr acc.cols N.fold noHook e), SqlType.bool)
                | _ => throw (.unsupported "subquery")
              pure ⟨acc.n + 1, .attach kind sub acc.q,
                Fin.append acc.cols ![{ qualifier := none, name := "?subquery?", type := ty }]⟩
          let m := acc.n
          let hook : SqlEquiv.Expr → Option (Expr m) := fun e =>
            match subs.findIdx? (·.1 == e) with
            | some j => if h : n + j < m then some (.col ⟨n + j, h⟩) else none
            | none => none
          let p ← elabExpr acc.cols N.fold hook w
          if h : n ≤ m then
            pure (.project (fun i : Fin n => .col (Fin.castLE h i)) (.select p acc.q))
          else throw (.typeError "subquery scope")
    let itemExprs := items.filterMap fun | .exprItem e _ => some e | .star _ => none
    let orderExprs := orderBy.map fun | .mk e _ _ => e
    let aggExprs := (aggsOfList itemExprs ++ aggsOfOpt having ++ aggsOfList orderExprs).eraseDups
    if groupBy.isEmpty && aggExprs.isEmpty && having.isNone then
      let its ← elabItems N cols items
      finishSelect N.fold ⟨n, q, elabExpr cols N.fold noHook, its⟩ distinct orderBy limitVal
        offsetVal
    else
      -- GROUP BY and aggregates (phase 8a, #313)
      let keyList ← groupBy.mapM (elabExpr cols N.fold noHook)
      let aggList ← aggExprs.mapM (elabAgg cols N.fold)
      -- Bare columns (registry T9): in the sqlite dialect, a column that is neither grouped nor
      -- aggregated becomes an aggregate of its own: its value at the row of the one `MIN`/`MAX`
      -- (`AggCall.atExtreme`), or on the group's first row (`AggCall.first`).
      let bareRefs : List SqlEquiv.ColumnRef :=
        if N.config.bareColumns == .sqlite then
          (colsOutsideAggsList itemExprs ++ colsOutsideAggsOpt having ++
            colsOutsideAggsList orderExprs).eraseDups
        else []
      let bare : List (SqlEquiv.ColumnRef × Expr n) := bareRefs.filterMap fun c =>
        match elabExpr cols N.fold noHook (.col c) with
        | .ok e' => if keyList.contains e' then none else some (c, e')
        | .error _ => none
      let extremes := aggExprs.filter fun
        | .agg (.min _) _ _ | .agg (.max _) _ _ => true
        | _ => false
      if !bare.isEmpty then
        if extremes.any (fun | .agg _ _ true => true | _ => false) then
          throw (.unsupported "bare column with MIN/MAX DISTINCT (sqlite picks the last tie)")
        if extremes.length > 1 then
          throw (.unsupported "bare column with several MIN/MAX (sqlite: arbitrary row)")
      let bareAggs ← bare.mapM fun (_, e') => do
        match extremes with
        | [.agg (.min _) (some k) _] => return AggCall.atExtreme .lt (← elabExpr cols N.fold noHook k) e'
        | [.agg (.max _) (some k) _] => return AggCall.atExtreme .gt (← elabExpr cols N.fold noHook k) e'
        | _ => pure (AggCall.first e')
      let aggList := aggList ++ bareAggs
      let aggExprs := aggExprs ++ bare.map fun (c, _) => SqlEquiv.Expr.col c
      let g := keyList.length
      let a := aggList.length
      let keys : Fin g → Expr n := fun i => keyList[i]
      let aggs : Fin a → AggCall n := fun j => aggList[j]
      let out ← aggScope cols keys aggs
      let hook := aggHook (a := a) cols N.fold keys aggExprs
      let outExpr (e : SqlEquiv.Expr) : ElabM (Expr (g + a)) :=
        match elabExpr out N.fold hook e with
        | .ok e' => pure e'
        | .error (.unknownColumn q c) =>
          match resolveColumn cols (q.map N.fold) (N.fold c) with
          | .ok _ => throw (.unsupported "column not in GROUP BY or an aggregate")
          | .error _ => throw (.unknownColumn q c)
        | .error err => throw err
      let q' : Query N.S (g + a) := .aggregate keys aggs q
      let q' : Query N.S (g + a) ← match having with
        | none => pure q'
        | some h => do pure (Query.select (← outExpr h) q')
      let its ← items.mapM fun
        | .star _ => throw (.unsupported "* with GROUP BY or aggregates")
        | .exprItem e al => do
          let e' ← outExpr e
          let some τ := e'.typeOf (ctx out) | throw (.typeError "SELECT item")
          let name := al.getD (match e with | .col c => c.column | _ => "?column?")
          pure (e', ({ qualifier := none, name, type := τ } : Column))
      finishSelect N.fold ⟨g + a, q', outExpr, its⟩ distinct orderBy limitVal offsetVal
  | .mk _ _ none _ _ _ _ _ _ => throw (.unsupported "SELECT without FROM")
termination_by fuel

end

/-- Elaborate a `SELECT`, with subqueries nested at most 16 deep. -/
def elabSelect (stmt : SqlEquiv.SelectStmt) : ElabM (Elaborated N.S) := elabSelectF N 16 stmt

/-- Whether a branch of a compound query has `ORDER BY`, `LIMIT` or `OFFSET`. -/
def hasOrderOrLimit : SqlEquiv.Query → Bool
  | .simple (.mk _ _ _ _ _ _ o l off) => !o.isEmpty || l.isSome || off.isSome
  | _ => false

def elabQueryRaw : SqlEquiv.Query → ElabM (Elaborated N.S)
  | .simple s => elabSelect N s
  | .compound l op r => do
    -- Since #317 the parser puts a trailing ORDER BY / LIMIT of a compound query in
    -- `Query.ordered` and rejects one on an inner branch; this guards hand-built ASTs.
    if hasOrderOrLimit l || hasOrderOrLimit r then
      throw (.unsupported "ORDER BY/LIMIT in a compound query")
    let ⟨n, ql, cl⟩ ← elabQueryRaw l
    let ⟨m, qr, _⟩ ← elabQueryRaw r
    if h : m = n then
      let u : Query N.S n := .unionAll ql (h ▸ qr)
      match op with
      | .unionAll => pure ⟨n, u, cl⟩
      | .union => pure ⟨n, .distinct u, cl⟩
      | .intersect => pure ⟨n, .intersect ql (h ▸ qr), cl⟩
      | .exceptOp => pure ⟨n, .difference ql (h ▸ qr), cl⟩
    else throw (.typeError "set operation arity")
  | .withCTE _ _ => throw (.unsupported "WITH")
  | .ordered q orderBy limitVal offsetVal => do
    -- #317: ORDER BY/LIMIT over a whole compound query. Keys refer to its output columns (the
    -- parser has already turned positions into output names).
    let ⟨n, q, cols⟩ ← elabQueryRaw q
    let its : List (Expr n × Column) := (List.finRange n).map fun i => (.col i, cols i)
    let keyList ← orderBy.mapM (elabOrderKey N.fold (elabExpr cols N.fold noHook) its)
    let k := keyList.length
    let q : Query N.S n := if k = 0 then q else .orderBy (fun i : Fin k => keyList[i]) q
    pure ⟨n, (match limitVal, offsetVal with
      | none, none => q
      | l, off => .limit l (off.getD 0) q), cols⟩

/-- Elaborate a parsed query, and check that the result is well-typed. -/
def elabQuery (q : SqlEquiv.Query) : ElabM (Elaborated N.S) := do
  let e ← elabQueryRaw N q
  if e.q.typeOf.isSome then pure e else throw (.typeError "query")

/-- Elaborate a parsed statement; only queries are in the fragment. -/
def elabStmt : SqlEquiv.Stmt → ElabM (Elaborated N.S)
  | .query q => elabQuery N q
  | _ => throw (.unsupported "DML")

end SqlBridge
