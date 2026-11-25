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
import SqlBridge.Inline

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

/-- Two operands that must have one type, with an integer next to a decimal promoted (#472), as
the engines do for `CASE` branches and `COALESCE` arguments. -/
def unifyNum (a b : Expr n) : Expr n × Expr n :=
  match a.typeOf (ctx cols), b.typeOf (ctx cols) with
  | some .int, some .decimal => (.unary .toDecimal a, b)
  | some .decimal, some .int => (a, .unary .toDecimal b)
  | _, _ => (a, b)

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
    let t ← if vs.all (fun | .lit _ => true | _ => false) then do
        pure (Expr.inList e (← elabLits vs))
      else do
        -- over non-literals (phase 9.1, #459): `e = v₁ OR … OR e = vₖ`, as the standard defines
        -- `IN`; three-valued `OR` gives the same `NULL`s
        match ← elabArgs vs with
        | [] => throw (.unsupported "IN over an empty list")
        | v :: vs' => pure (vs'.foldl
            (fun acc w => .binary .or acc (.binary (.cmp .eq) e (retypeNull cols w e)))
            (.binary (.cmp .eq) e (retypeNull cols v e)))
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
  | .func name args => do
    -- scalar functions (phase 9.1, #459): ROUND, LOWER, UPPER and LENGTH are operators of the
    -- typed core; COALESCE, NULLIF, ABS and CONCAT are written with `CASE`, evaluating as the
    -- engines do (later arguments of COALESCE only when needed)
    let typeOfE (x : Expr n) : ElabM SqlType :=
      match x.typeOf (ctx cols) with
      | some τ => pure τ
      | none => throw (.typeError s!"argument of {name}")
    let es ← elabArgs args
    match name.toUpper, es, args with
    | "ROUND", [a], _ => pure (.unary (.round 0) a)
    | "ROUND", [a, _], [_, .lit (.int d)] => pure (.unary (.round d) a)
    | "ROUND", [a, _], [_, .unaryOp .neg (.lit (.int d))] => pure (.unary (.round (-d)) a)
    | "ROUND", [a, _], [_, .lit (.null _)] => do
      let τ ← typeOfE a
      pure (.caseWhen (.unary .isNull a) (.null τ) (.null τ))
    | "LOWER", [a], _ => pure (.unary .lower a)
    | "UPPER", [a], _ => pure (.unary .upper a)
    | "LENGTH", [a], _ => pure (.unary .length a)
    | "ABS", [a], _ => pure (.caseWhen (.binary (.cmp .lt) a (.lit (.int 0))) (.unary .neg a) a)
    | "NULLIF", [a, b], _ => do
      let a := retypeNull cols a b
      let τ ← typeOfE a
      pure (.caseWhen (.binary (.cmp .eq) a (retypeNull cols b a)) (.null τ) a)
    | "COALESCE", _ :: _, _ =>
      match es.reverse with
      | [] => throw (.unsupported "COALESCE()")
      | last :: rest => pure (rest.foldl
          (fun acc x =>
            let (x', acc') := unifyNum cols (retypeNull cols x acc) (retypeNull cols acc x)
            .caseWhen (.unary .isNotNull x) x' acc')
          last)
    | "CONCAT", x :: xs, _ =>
      let part (y : Expr n) : Expr n :=
        .caseWhen (.unary .isNull y) (.lit (.text "")) (retypeNull cols y (.lit (.text "")))
      pure (xs.foldl (fun acc y => .binary .concat acc (part y)) (part x))
    | _, _, _ => throw (.unsupported s!"function {name}")
  | .agg _ _ _ => throw (.unsupported "aggregate")
  | .countStar => throw (.unsupported "aggregate")
  | .inSubquery _ _ _ => throw (.unsupported "subquery")
  | .exists _ _ => throw (.unsupported "subquery")
  | .subquery _ => throw (.unsupported "subquery")
  | .windowFn _ _ _ => throw (.unsupported "window function")

/-- A list of arguments. -/
def elabArgs : List SqlEquiv.Expr → ElabM (List (Expr n))
  | [] => pure []
  | a :: as => return (← elabExpr a) :: (← elabArgs as)

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
    let (a, rest) := unifyNum cols (retypeNull cols a rest) (retypeNull cols rest a)
    pure (.caseWhen c a rest)

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
  | .inSubquery e _ _ => aggsOf e
  -- the aggregates of a window over groups (`RANK() OVER (ORDER BY SUM(x))`, phase 9.5)
  | .windowFn _ a (.mk part order) => aggsOfOpt a ++ aggsOfList part ++ aggsOfOrder order
  | _ => []

def aggsOfOrder : List SqlEquiv.OrderByItem → List SqlEquiv.Expr
  | [] => []
  | .mk e _ _ :: os => aggsOf e ++ aggsOfOrder os

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
  | .exists neg sq => [(.exists neg sq, sq)]
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

mutual

/-- Whether a subquery sits in a `THEN` or `ELSE` of a `CASE` (phase 9.4b step 3). The typed core
evaluates an attached subquery on every row, whether the branch is taken or not, and the engines
evaluate it only when it is, so the elaborator rejects it there. -/
def subInBranch : SqlEquiv.Expr → Bool
  | .binOp _ a b => subInBranch a || subInBranch b
  | .unaryOp _ a => subInBranch a
  | .inList e _ vs => subInBranch e || subInBranchList vs
  | .«case» bs els => subInBranchArms bs || (els.map fun e => !(subsOf e).isEmpty).getD false
  | .between a b c => subInBranch a || subInBranch b || subInBranch c
  | .func _ args => subInBranchList args
  | _ => false

def subInBranchList : List SqlEquiv.Expr → Bool
  | [] => false
  | e :: es => subInBranch e || subInBranchList es

def subInBranchArms : List (SqlEquiv.Expr × SqlEquiv.Expr) → Bool
  | [] => false
  | (c, a) :: bs => subInBranch c || !(subsOf a).isEmpty || subInBranchArms bs

end

/-- The expression of a `SELECT` item; none for `*`. -/
def itemExprOf : SqlEquiv.SelectItem → Option SqlEquiv.Expr
  | .exprItem e _ => some e
  | .star _ => none

/-- The expression of an `ORDER BY` item. -/
def orderExprOf : SqlEquiv.OrderByItem → SqlEquiv.Expr
  | .mk e _ _ => e

/-- The distinct subquery nodes of a list of expressions, in order. -/
def distinctSubs (es : List SqlEquiv.Expr) : List (SqlEquiv.Expr × SqlEquiv.SubQuery) :=
  (subsOfList es).foldl (fun acc x => if acc.any (·.1 == x.1) then acc else acc ++ [x]) []

mutual

/-- The window-function nodes of an expression (phase 9.5, #463), outermost first; nodes inside a
window or a subquery are not visited. -/
def winsOf : SqlEquiv.Expr → List SqlEquiv.Expr
  | .windowFn f a spec => [.windowFn f a spec]
  | .binOp _ a b => winsOf a ++ winsOf b
  | .unaryOp _ a => winsOf a
  | .inList e _ vs => winsOf e ++ winsOfList vs
  | .«case» bs els => winsOfBranches bs ++ winsOfOpt els
  | .between a b c => winsOf a ++ winsOf b ++ winsOf c
  | .func _ args => winsOfList args
  | .inSubquery e _ _ => winsOf e
  | _ => []

def winsOfList : List SqlEquiv.Expr → List SqlEquiv.Expr
  | [] => []
  | e :: es => winsOf e ++ winsOfList es

def winsOfOpt : Option SqlEquiv.Expr → List SqlEquiv.Expr
  | none => []
  | some e => winsOf e

def winsOfBranches : List (SqlEquiv.Expr × SqlEquiv.Expr) → List SqlEquiv.Expr
  | [] => []
  | (c, a) :: bs => winsOf c ++ winsOf a ++ winsOfBranches bs

end

/-- The distinct window nodes of a list of expressions, in order. -/
def distinctWins (es : List SqlEquiv.Expr) : List SqlEquiv.Expr :=
  (winsOfList es).foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The hook that reads expression node `j` of `nodes` from column `n + j`. -/
def nodeHookAt (n m : ℕ) (nodes : List SqlEquiv.Expr) (e : SqlEquiv.Expr) : Option (Expr m) :=
  match nodes.findIdx? (· == e) with
  | some j => if h : n + j < m then some (.col ⟨n + j, h⟩) else none
  | none => none

/-- Elaborate a window-function node (phase 9.5, #463); `ex` elaborates its argument and keys in
the window's input scope (over groups, an aggregate reads its column). -/
def elabWin {m : ℕ} (ex : SqlEquiv.Expr → ElabM (Expr m)) : SqlEquiv.Expr → ElabM (WinCall m)
  | .windowFn fn arg (.mk part order) => do
    let part ← part.mapM ex
    let order ← order.mapM fun | .mk e dir nulls => do
      pure ({ e := ← ex e, desc := dir == .desc, nullsFirst := nulls == .first } : SortKey m)
    let f : WinFn m ← match fn, arg with
      | .rowNumber, _ => pure .rowNumber
      | .rank, _ => pure .rank
      | .denseRank, _ => pure .denseRank
      | .count, none => pure (.agg .countStar)
      | .count, some e => do pure (WinFn.agg (.call .count false (← ex e)))
      | .sum _, some e => do pure (WinFn.agg (.call .sum false (← ex e)))
      | .avg _, some e => do pure (WinFn.agg (.call .avg false (← ex e)))
      | .min _, some e => do pure (WinFn.agg (.call .min false (← ex e)))
      | .max _, some e => do pure (WinFn.agg (.call .max false (← ex e)))
      | _, _ => throw (.unsupported "window function")
    pure ⟨part, order, f⟩
  | _ => throw (.unsupported "window function")


/-- The hook that reads subquery node `j` of `subs` from column `n + j` (phase 9.4b step 3). -/
def subHookAt (n m : ℕ) (subs : List (SqlEquiv.Expr × SqlEquiv.SubQuery)) (e : SqlEquiv.Expr) :
    Option (Expr m) :=
  match subs.findIdx? (·.1 == e) with
  | some j => if h : n + j < m then some (.col ⟨n + j, h⟩) else none
  | none => none

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
  | .agg (.sum _) (some e) d => return .call .sum d (← elabExpr cols fold noHook e)
  | .agg (.min _) (some e) d => return .call .min d (← elabExpr cols fold noHook e)
  | .agg (.max _) (some e) d => return .call .max d (← elabExpr cols fold noHook e)
  | .agg (.avg _) (some e) d => return .call .avg d (← elabExpr cols fold noHook e)
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

/-- The join node of a `FROM` join: an inner join (`INNER`, `CROSS`), or an outer join (phase 9.3,
#461) that pads unmatched rows with `NULL`. -/
def joinOf {S : DbSchema} {n m : ℕ} (kind : SqlEquiv.JoinType) (θ : Expr (n + m)) (ql : Query S n)
    (qr : Query S m) : Query S (n + m) :=
  match kind with
  | .left => .outerJoin .left θ ql qr
  | .right => .outerJoin .right θ ql qr
  | .full => .outerJoin .full θ ql qr
  | _ => .join θ ql qr

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
      | .left, some e => elabExpr cols N.fold noHook e
      | .right, some e => elabExpr cols N.fold noHook e
      | .full, some e => elabExpr cols N.fold noHook e
      | _, none => throw (.unsupported "outer join without ON")
    pure ⟨n + m, joinOf kind θ ql qr, cols⟩
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

/-- Phase 9.4b (#462, decision D6): elaborate a correlated subquery body `SELECT items FROM f [WHERE w] [LIMIT l]`
over the outer row `ocols` (`Query.outer` joined in front). A column resolves in the body's own
scope first, then in the outer row (#253). Aggregate items without `GROUP BY` are allowed. -/
def elabCorrBody {o : ℕ} (ocols : Fin o → Column) : SqlEquiv.SubQuery → ElabM (Elaborated N.S)
  | .simple (.mk false items (some f) where_ [] none [] lim none) => do
    let ⟨n, q, cols⟩ ← elabFrom N (fun _ => throw (.unsupported "nested subquery in a correlated body")) f
    let cols' : Fin (o + n) → Column := Fin.append ocols cols
    let hook : SqlEquiv.Expr → Option (Expr (o + n)) := fun
      | .col c => match resolveColumn cols (c.table.map N.fold) (N.fold c.column) with
        | .ok i => some (.col (Fin.natAdd o i))
        -- only a name the body does not have reaches the outer row; an ambiguous one is an error
        | .error .unknownColumn => match resolveColumn ocols (c.table.map N.fold) (N.fold c.column) with
          | .ok j => some (.col (Fin.castAdd n j))
          | .error _ => none
        | .error _ => none
      | _ => none
    let q₀ : Query N.S (o + n) := .join (.lit (.bool true)) (.outer (fun j => (ocols j).type)) q
    let q' : Query N.S (o + n) ← match where_ with
      | none => pure q₀
      | some w => do pure (Query.select (← elabExpr cols' N.fold hook w) q₀)
    let itemExprs := items.filterMap itemExprOf
    let aggExprs := (aggsOfList itemExprs).eraseDups
    let body : Elaborated N.S ← if aggExprs.isEmpty then do
        let its ← items.mapM fun
          | .star _ => throw (.unsupported "* in a correlated body")
          | .exprItem e al => do
            let e' ← elabExpr cols' N.fold hook e
            let some τ := e'.typeOf (ctx cols') | throw (.typeError "SELECT item")
            pure (e', ({ qualifier := none, name := al.getD "?column?", type := τ } : Column))
        pure ⟨its.length, .project (fun i => (its[i]).1) q', fun i => (its[i]).2⟩
      else do
        let aggList ← aggExprs.mapM fun
          | .countStar => pure .countStar
          | .agg .count none _ => pure .countStar
          | .agg fn (some e) d => do
            let e' ← elabExpr cols' N.fold hook e
            match fn with
            | .count => pure (.call .count d e')
            | .sum _ => pure (.call .sum d e')
            | .min _ => pure (.call .min d e')
            | .max _ => pure (.call .max d e')
            | .avg _ => pure (.call .avg d e')
          | _ => throw (.unsupported "aggregate")
        let a := aggList.length
        let aggs : Fin a → AggCall (o + n) := fun j => aggList[j]
        let noKeys : Fin 0 → Expr (o + n) := fun i => i.elim0
        let out ← aggScope cols' noKeys aggs
        let hook2 := aggHook (a := a) cols' N.fold noKeys aggExprs
        let its ← items.mapM fun
          | .star _ => throw (.unsupported "* in a correlated body")
          | .exprItem e al => do
            let e' ← elabExpr out N.fold hook2 e
            let some τ := e'.typeOf (ctx out) | throw (.typeError "SELECT item")
            pure (e', ({ qualifier := none, name := al.getD "?column?", type := τ } : Column))
        pure ⟨its.length, .project (fun i => (its[i]).1) (.aggregate noKeys aggs q'),
          fun i => (its[i]).2⟩
    pure ⟨body.n, (match lim with | none => body.q | some l => .limit (some l) 0 body.q), body.cols⟩
  | _ => throw (.unsupported "correlated subquery body shape")

/-- Phase 9.4b (#462): `EXISTS` ignores the select list, so its body counts rows. A positive
`LIMIT` does not change whether a row exists and is dropped (it would apply to the count's one
row); `LIMIT 0` is kept, and `elabCorrBody` rejects it with the other `LIMIT`s of an `EXISTS`
body it cannot express. -/
def existsBody : SqlEquiv.SubQuery → SqlEquiv.SubQuery
  | .simple (.mk d _ f w g h o (some (l + 1)) off) =>
    .simple (.mk d [.exprItem .countStar none] f w g h o none off)
  | .simple (.mk d _ f w g h o l off) => .simple (.mk d [.exprItem .countStar none] f w g h o l off)
  | sq => sq

/-- Elaborate a `WHERE` clause over the `FROM` query `q` with columns `cols`. Uncorrelated
subqueries (phase 8f, #329) each become a column of the input (`Query.attach`), which the predicate
reads; the extra columns are projected away. `sub` elaborates a subquery body. A body that reads
the outer row, and every `EXISTS`, becomes a `Query.lateral` column instead (phase 9.4b, #462,
decision D6): `elabCorrBody` elaborates it against the columns so far. -/
def elabWhere (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S)) {n : ℕ} (cols : Fin n → Column)
    (q : Query N.S n) : Option SqlEquiv.Expr → ElabM (Query N.S n)
  | none => pure q
  | some w =>
    let subs := (subsOf w).foldl
      (fun acc x => if acc.any (·.1 == x.1) then acc else acc ++ [x]) []
    if subs.isEmpty then do pure (Query.select (← elabExpr cols N.fold noHook w) q)
    else do
      -- each node: uncorrelated (`.inr`, attached with `Query.attach`) or correlated / EXISTS
      -- (`.inl`, phase 9.4b, #462: a `Query.lateral` column, elaborated against the columns so far)
      let subsE ← subs.mapM fun (node, sq) => do
        match node with
        | .exists _ _ => pure (Sum.inl (node, sq))
        | _ =>
        match sub sq with
          | .ok r =>
            if h : r.n = 1 then
              pure (Sum.inr (node, (h ▸ r.q : Query N.S 1), (r.cols ⟨0, by omega⟩).type))
            else throw (.typeError "subquery arity")
          | .error (.unknownColumn qq c) =>
            match resolveColumn cols (qq.map N.fold) (N.fold c) with
            | .ok _ => pure (Sum.inl (node, sq))
            | .error _ => throw (.unknownColumn qq c)
          | .error err => throw err
      let acc ← subsE.foldlM (init := (⟨n, q, cols⟩ : Elaborated N.S))
        fun acc x => do
          match x with
          | .inr (node, sub, τ) =>
            let (kind, ty) ← match node with
              | .subquery _ =>
                pure (SubKind.scalar (N.config.scalarSubqueryRows == .firstRow), τ)
              | .inSubquery e neg _ => do
                pure (SubKind.inSub neg (← elabExpr acc.cols N.fold noHook e), SqlType.bool)
              | _ => throw (.unsupported "subquery")
            pure ⟨acc.n + 1, .attach kind sub acc.q,
              Fin.append acc.cols ![{ qualifier := none, name := "?subquery?", type := ty }]⟩
          | .inl (node, sq) =>
            let Γ : Fin acc.n → SqlType := fun i => (acc.cols i).type
            let (col1, ty) ← match node with
              | .exists neg _ => do
                if let .simple (.mk _ _ _ _ _ _ _ (some 0) _) := sq then
                  throw (.unsupported "EXISTS over LIMIT 0")
                let op : CmpOp := if neg then .eq else .ne
                let cnt : Query N.S 1 ← match sq with
                  | .simple _ => do
                    let b ← elabCorrBody N acc.cols (existsBody sq)
                    if h : b.n = 1 then pure (h ▸ b.q) else throw (.typeError "EXISTS body")
                  | _ => do
                    -- a set operation: uncorrelated only; its rows are compared, so its items
                    -- are evaluated (9.4b step 3)
                    let r ← sub sq
                    pure (.aggregate (g := 0) (fun i => i.elim0) ![.countStar] r.q)
                pure ((.project (fun _ => .binary (.cmp op) (.col 0) (.lit (.int 0))) cnt :
                  Query N.S 1), SqlType.bool)
              | .subquery _ => do
                let b ← elabCorrBody N acc.cols sq
                if h : b.n = 1 then
                  let body : Query N.S 1 := h ▸ b.q
                  pure ((.attach (.scalar (N.config.scalarSubqueryRows == .firstRow)) body .one :
                    Query N.S (0 + 1)), (b.cols ⟨0, by omega⟩).type)
                else throw (.typeError "subquery arity")
              | .inSubquery e neg _ => do
                let b ← elabCorrBody N acc.cols sq
                let e' ← elabExpr acc.cols N.fold noHook e
                if h : b.n = 1 then
                  let body : Query N.S 1 := h ▸ b.q
                  pure ((.project (fun _ => .col (Fin.last acc.n))
                    (.attach (.inSub neg (e'.rename (Fin.castAdd 0))) body (.outer Γ)) : Query N.S 1),
                    SqlType.bool)
                else throw (.typeError "subquery arity")
              | _ => throw (.unsupported "subquery")
            pure ⟨acc.n + 1, .lateral col1 acc.q,
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

/-- Attach a column per subquery node to `base` (phase 9.4b step 3, #462): an uncorrelated body
with `Query.attach`, as `elabWhere` does, and a body that reads the row, or an `EXISTS`, with
`Query.lateral` (decision D6). `probe` elaborates the probe of an `IN` node over `base`'s
columns. Column `base.n + j` holds node `j`; read it with `subHookAt`. -/
def attachSubs (sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S)) (base : Elaborated N.S)
    (probe : SqlEquiv.Expr → ElabM (Expr base.n)) (subs : List (SqlEquiv.Expr × SqlEquiv.SubQuery)) :
    ElabM (Elaborated N.S) :=
  subs.foldlM (init := base) fun acc (node, sq) => do
    let lift (e : Expr base.n) : ElabM (Expr acc.n) :=
      if h : base.n ≤ acc.n then pure (e.rename (Fin.castLE h))
      else throw (.typeError "subquery scope")
    let Γ : Fin acc.n → SqlType := fun i => (acc.cols i).type
    let correlated : ElabM Bool := match sub sq with
      | .ok _ => pure false
      | .error (.unknownColumn qq c) =>
        match resolveColumn acc.cols (qq.map N.fold) (N.fold c) with
        | .ok _ => pure true
        | .error _ => throw (.unknownColumn qq c)
      | .error err => throw err
    let push (x : Query N.S (acc.n + 1)) (ty : SqlType) : Elaborated N.S :=
      ⟨acc.n + 1, x, Fin.append acc.cols ![{ qualifier := none, name := "?subquery?", type := ty }]⟩
    match node with
    | .exists neg _ =>
      if let .simple (.mk _ _ _ _ _ _ _ (some 0) _) := sq then
        throw (.unsupported "EXISTS over LIMIT 0")
      let op : CmpOp := if neg then .eq else .ne
      match sq with
      | .simple _ => do
        let b ← elabCorrBody N acc.cols (existsBody sq)
        if h : b.n = 1 then
          let cnt : Query N.S 1 := h ▸ b.q
          pure (push (.lateral (.project (fun _ => .binary (.cmp op) (.col 0) (.lit (.int 0))) cnt :
            Query N.S 1) acc.q) .bool)
        else throw (.typeError "EXISTS body")
      | _ => do
        -- a set operation: uncorrelated only; its rows are compared, so its items are evaluated
        let r ← sub sq
        let cnt : Query N.S (0 + 1) := .aggregate (g := 0) (fun i => i.elim0) ![.countStar] r.q
        pure (push (.attach (.scalar false)
          (.project (fun _ => .binary (.cmp op) (.col 0) (.lit (.int 0))) cnt) acc.q) .bool)
    | .subquery _ =>
      if ← correlated then do
        let b ← elabCorrBody N acc.cols sq
        if h : b.n = 1 then
          let body : Query N.S 1 := h ▸ b.q
          pure (push (.lateral (.attach (.scalar (N.config.scalarSubqueryRows == .firstRow)) body
            .one : Query N.S (0 + 1)) acc.q) (b.cols ⟨0, by omega⟩).type)
        else throw (.typeError "subquery arity")
      else do
        let r ← sub sq
        if h : r.n = 1 then
          pure (push (.attach (.scalar (N.config.scalarSubqueryRows == .firstRow)) (h ▸ r.q) acc.q)
            (r.cols ⟨0, by omega⟩).type)
        else throw (.typeError "subquery arity")
    | .inSubquery e neg _ => do
      let e' ← lift (← probe e)
      if ← correlated then do
        let b ← elabCorrBody N acc.cols sq
        if h : b.n = 1 then
          let body : Query N.S 1 := h ▸ b.q
          pure (push (.lateral (.project (fun _ => .col (Fin.last acc.n))
            (.attach (.inSub neg (e'.rename (Fin.castAdd 0))) body (.outer Γ)) : Query N.S 1) acc.q)
            .bool)
        else throw (.typeError "subquery arity")
      else do
        let r ← sub sq
        if h : r.n = 1 then pure (push (.attach (.inSub neg e') (h ▸ r.q) acc.q) .bool)
        else throw (.typeError "subquery arity")
    | _ => throw (.unsupported "subquery")

/-- Whether a branch of a compound query is a `SELECT` without `FROM` (#472). Only then does the
elaborator align the branches' types: the compound queries the bridge theorems cover have none. -/
def branchFromless : SqlEquiv.Query → Bool
  | .simple (.mk _ _ none _ _ _ _ _ _) => true
  | .compound l _ r => branchFromless l || branchFromless r
  | _ => false

/-- The same for the branches of a compound subquery. -/
def subBranchFromless : SqlEquiv.SubQuery → Bool
  | .simple (.mk _ _ none _ _ _ _ _ _) => true
  | .compound l _ r => subBranchFromless l || subBranchFromless r
  | _ => false

/-- A `NULL` literal column of a projection takes the type `τ` (#472): `SELECT NULL` next to a
decimal or text branch. Other queries are left as they are. -/
def retypeNullCol {S : DbSchema} {n : ℕ} (i : Fin n) (τ : SqlType) : Query S n → Query S n
  | .project es q =>
    .project (fun j => if j = i then (match es j with | .null _ => .null τ | e => e) else es j) q
  | q => q

/-- Give the two branches of a set operation one type (#472), as the engines do: a `NULL` literal
column takes the other branch's type, and an integer column next to a decimal one is promoted
(`UnOp.toDecimal`). The result's columns are the left branch's, with the common types. -/
def alignBranches {S : DbSchema} {n : ℕ} (ql qr : Query S n) (cl : Fin n → Column) :
    Query S n × Query S n × (Fin n → Column) :=
  -- NULL literal columns first
  let (ql, qr) := (List.finRange n).foldl (fun (ql, qr) i =>
    match ql.typeOf, qr.typeOf with
    | some Γl, some Γr =>
      if Γl i = Γr i then (ql, qr)
      else (retypeNullCol i (Γr i) ql, retypeNullCol i (Γl i) qr)
    | _, _ => (ql, qr)) (ql, qr)
  match ql.typeOf, qr.typeOf with
  | some Γl, some Γr =>
    let promote (Γ Δ : Fin n → SqlType) (i : Fin n) : Expr n :=
      if Γ i = .int ∧ Δ i = .decimal then .unary .toDecimal (.col i) else .col i
    let needL := (List.finRange n).any fun i => Γl i = .int ∧ Γr i = .decimal
    let needR := (List.finRange n).any fun i => Γr i = .int ∧ Γl i = .decimal
    let ql' := if needL then .project (promote Γl Γr) ql else ql
    let qr' := if needR then .project (promote Γr Γl) qr else qr
    let τ (i : Fin n) : SqlType :=
      if (Γl i = .int ∧ Γr i = .decimal) ∨ (Γl i = .decimal ∧ Γr i = .int) then .decimal else Γl i
    (ql', qr', fun i => { cl i with type := τ i })
  | _, _ => (ql, qr, cl)

/-- A column per window node, over `base` (phase 9.5, #463): `Query.window`, one per node, in
order. `hook` maps the scope's other nodes (aggregates over groups, subqueries) to columns of
`base`; column `base.n + j` holds window `j`. -/
def attachWins (base : Elaborated N.S)
    (hook : SqlEquiv.Expr → Option (Expr base.n)) (wins : List SqlEquiv.Expr) :
    ElabM (Elaborated N.S) :=
  wins.foldlM (init := base) fun acc w => do
    if h : base.n ≤ acc.n then
      let hk : SqlEquiv.Expr → Option (Expr acc.n) := fun e =>
        (hook e).map (·.rename (Fin.castLE h))
      let c ← elabWin (elabExpr acc.cols N.fold hk) w
      let some τ := c.typeOf (ctx acc.cols) | throw (.typeError "window function")
      pure ⟨acc.n + 1, .window c acc.q,
        Fin.append acc.cols ![{ qualifier := none, name := "?window?", type := τ }]⟩
    else throw (.typeError "window scope")

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
      if subBranchFromless l || subBranchFromless r then
        -- a branch without `FROM`: give the branches one type (#472)
        let (ql, qr, cl) := alignBranches ql (h ▸ qr) cl
        match op with
        | .unionAll => pure ⟨n, .unionAll ql qr, cl⟩
        | .union => pure ⟨n, .distinct (.unionAll ql qr), cl⟩
        | .intersect => pure ⟨n, .intersect ql qr, cl⟩
        | .exceptOp => pure ⟨n, .difference ql qr, cl⟩
      else
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
  | .mk distinct items from_ where_ groupBy having orderBy limitVal offsetVal => do
    -- Without `FROM` (phase 9.1a, #459) the source is one row with no columns.
    let ⟨n, q, cols⟩ ← match from_ with
      | some from_ => elabFrom N (fun sq => match fuel with
        | 0 => throw (.unsupported "subqueries nested too deeply")
        | f + 1 => elabSubQuery f sq) from_
      | none => pure (⟨0, .one, Fin.elim0⟩ : Elaborated N.S)
    let q : Query N.S n ← elabWhere N (fun sq => match fuel with
      | 0 => throw (.unsupported "subqueries nested too deeply")
      | f + 1 => elabSubQuery f sq) cols q where_
    let itemExprs := items.filterMap itemExprOf
    let orderExprs := orderBy.map orderExprOf
    let aggExprs := (aggsOfList itemExprs ++ aggsOfOpt having ++ aggsOfList orderExprs).eraseDups
    let sub : SqlEquiv.SubQuery → ElabM (Elaborated N.S) := fun sq => match fuel with
      | 0 => throw (.unsupported "subqueries nested too deeply")
      | f + 1 => elabSubQuery f sq
    if groupBy.isEmpty && aggExprs.isEmpty && having.isNone then
      if (distinctSubs itemExprs).isEmpty && !SqlEquiv.selectHasWindowFn items &&
          !orderExprs.any SqlEquiv.exprHasWindowFn then
        let its ← elabItems N cols items
        finishSelect N.fold ⟨n, q, elabExpr cols N.fold noHook, its⟩ distinct orderBy limitVal
          offsetVal
      else
        -- subqueries in the SELECT list (phase 9.4b step 3) and window functions in the items or
        -- ORDER BY (phase 9.5, #463): a column each, read by the items
        if itemExprs.any subInBranch then throw (.unsupported "subquery in a CASE branch")
        let subs := distinctSubs itemExprs
        let wins := distinctWins (itemExprs ++ orderExprs)
        if !subs.isEmpty && items.any (fun | .star _ => true | _ => false) then
          throw (.unsupported "* next to a subquery item")
        -- the windows first, then the subqueries, so that the probe of an `IN (subquery)` may be
        -- a window function; `subsOf` does not look inside a window, so a subquery in a window's
        -- argument or keys is rejected
        let accW ← attachWins N ⟨n, q, cols⟩ noHook wins
        let hookW := nodeHookAt n accW.n wins
        let acc2 ← attachSubs N sub accW (elabExpr accW.cols N.fold hookW) subs
        if h2 : accW.n ≤ acc2.n then
          let hook : SqlEquiv.Expr → Option (Expr acc2.n) := fun e =>
            match subHookAt accW.n acc2.n subs e with
            | some x => some x
            | none => (hookW e).map (·.rename (Fin.castLE h2))
          if h1 : n ≤ acc2.n then
            let its ← items.flatMapM fun
              | .star none => pure ((List.finRange n).map fun i =>
                  ((.col (Fin.castLE h1 i) : Expr acc2.n), cols i))
              | .star (some _) => throw (.unsupported "t.* next to a window function")
              | .exprItem e al => do
                let e' ← elabExpr acc2.cols N.fold hook e
                let some τ := e'.typeOf (ctx acc2.cols) | throw (.typeError "SELECT item")
                let name := al.getD (match e with | .col c => c.column | _ => "?column?")
                pure [(e', ({ qualifier := none, name, type := τ } : Column))]
            finishSelect N.fold ⟨acc2.n, acc2.q, elabExpr acc2.cols N.fold hook, its⟩ distinct
              orderBy limitVal offsetVal
          else throw (.typeError "window scope")
        else throw (.typeError "subquery scope")
    else if !(distinctSubs (itemExprs ++ having.toList)).isEmpty || SqlEquiv.selectHasWindowFn items ||
        orderExprs.any SqlEquiv.exprHasWindowFn then
      -- GROUP BY or aggregates with subqueries in the items or `HAVING` (phase 9.4b step 3, #462):
      -- the keys and aggregates as below, without bare columns; then a column per subquery over
      -- the aggregate's output (the probe of an `IN` may be an aggregate)
      let gsubs := distinctSubs (itemExprs ++ having.toList)
      if (itemExprs ++ having.toList).any subInBranch then
        throw (.unsupported "subquery in a CASE branch")
      if items.any (fun | .star _ => true | _ => false) then
        throw (.unsupported "* with GROUP BY or aggregates")
      let keyList ← groupBy.mapM (elabExpr cols N.fold noHook)
      -- as below (#384): every column outside an aggregate resolves in the `FROM` scope
      let _ ← (colsOutsideAggsList itemExprs ++ colsOutsideAggsOpt having).mapM fun c =>
        elabExpr cols N.fold noHook (.col c)
      let aggList ← aggExprs.mapM (elabAgg cols N.fold)
      let g := keyList.length
      let a := aggList.length
      let keys : Fin g → Expr n := fun i => keyList[i]
      let aggs : Fin a → AggCall n := fun j => aggList[j]
      let out ← aggScope cols keys aggs
      let hook := aggHook (a := a) cols N.fold keys aggExprs
      let notGrouped (e : SqlEquiv.Expr) {m : ℕ} (r : ElabM (Expr m)) : ElabM (Expr m) :=
        match r with
        | .ok e' => pure e'
        | .error (.unknownColumn q c) =>
          match resolveColumn cols (q.map N.fold) (N.fold c) with
          | .ok _ => throw (.unsupported "column not in GROUP BY or an aggregate")
          | .error _ => throw (.unknownColumn q c)
        | .error err => let _ := e; throw err
      let outExpr (e : SqlEquiv.Expr) : ElabM (Expr (g + a)) :=
        notGrouped e (elabExpr out N.fold hook e)
      let acc ← attachSubs N sub ⟨g + a, .aggregate keys aggs q, out⟩ outExpr gsubs
      if hle : g + a ≤ acc.n then
        let hk : SqlEquiv.Expr → Option (Expr acc.n) := fun e =>
          match subHookAt (g + a) acc.n gsubs e with
          | some x => some x
          | none => (hook e).map (·.rename (Fin.castLE hle))
        let outExpr' (e : SqlEquiv.Expr) : ElabM (Expr acc.n) :=
          notGrouped e (elabExpr acc.cols N.fold hk e)
        let q2 : Query N.S acc.n ← match having with
          | none => pure acc.q
          | some h => do pure (Query.select (← outExpr' h) acc.q)
        -- window functions over the groups (phase 9.5, #463), after `HAVING`
        let wins := distinctWins (itemExprs ++ orderExprs)
        let acc2 ← attachWins N ⟨acc.n, q2, acc.cols⟩ hk wins
        if h2 : acc.n ≤ acc2.n then
          let hk2 : SqlEquiv.Expr → Option (Expr acc2.n) := fun e =>
            match nodeHookAt acc.n acc2.n wins e with
            | some x => some x
            | none => (hk e).map (·.rename (Fin.castLE h2))
          let outExpr2 (e : SqlEquiv.Expr) : ElabM (Expr acc2.n) :=
            notGrouped e (elabExpr acc2.cols N.fold hk2 e)
          let its ← items.mapM fun
            | .star _ => throw (.unsupported "* with GROUP BY or aggregates")
            | .exprItem e al => do
              let e' ← outExpr2 e
              let some τ := e'.typeOf (ctx acc2.cols) | throw (.typeError "SELECT item")
              let name := al.getD (match e with | .col c => c.column | _ => "?column?")
              pure (e', ({ qualifier := none, name, type := τ } : Column))
          finishSelect N.fold ⟨acc2.n, acc2.q, outExpr2, its⟩ distinct orderBy limitVal offsetVal
        else throw (.typeError "window scope")
      else throw (.typeError "subquery scope")
    else
      -- GROUP BY and aggregates (phase 8a, #313)
      let keyList ← groupBy.mapM (elabExpr cols N.fold noHook)
      -- Every column of the items and of `HAVING` outside an aggregate resolves in the `FROM`
      -- scope (#384): without this, an ambiguous name would resolve against the aggregate's
      -- output below, where only the keys keep their names (sqlite: "ambiguous column name").
      let _ ← (colsOutsideAggsList itemExprs ++ colsOutsideAggsOpt having).mapM fun c =>
        elabExpr cols N.fold noHook (.col c)
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
      if branchFromless l || branchFromless r then
        -- a branch without `FROM`: give the branches one type (#472)
        let (ql, qr, cl) := alignBranches ql (h ▸ qr) cl
        match op with
        | .unionAll => pure ⟨n, .unionAll ql qr, cl⟩
        | .union => pure ⟨n, .distinct (.unionAll ql qr), cl⟩
        | .intersect => pure ⟨n, .intersect ql qr, cl⟩
        | .exceptOp => pure ⟨n, .difference ql qr, cl⟩
      else
      let u : Query N.S n := .unionAll ql (h ▸ qr)
      match op with
      | .unionAll => pure ⟨n, u, cl⟩
      | .union => pure ⟨n, .distinct u, cl⟩
      | .intersect => pure ⟨n, .intersect ql (h ▸ qr), cl⟩
      | .exceptOp => pure ⟨n, .difference ql (h ▸ qr), cl⟩
    else throw (.typeError "set operation arity")
  | .withCTE _ _ => throw (.unsupported "WITH inside a query")
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

/-- The substitution environment of non-recursive CTEs (phase 9.2, #460): each body, with the
earlier ones inlined (`SqlBridge.Inline`), so a CTE sees the earlier ones. Every body must
elaborate, used or not, as Postgres checks it (registry T23). -/
def inlineEnv (env₀ : List (String × SqlEquiv.SubQuery)) (ctes : List SqlEquiv.CTEDef) :
    ElabM (List (String × SqlEquiv.SubQuery)) :=
  ctes.foldlM (init := env₀) fun env c => do
    let some b := Inline.body c.query
      | throw (.unsupported "WITH: a CTE body with ORDER BY/LIMIT over a set operation")
    let b := Inline.sub N.fold env b
    let _ ← elabSubQuery N 16 b
    pure (env ++ [(N.fold c.name, b)])

/-- Inline the non-recursive CTEs of a top-level `WITH` as derived tables. -/
def inlineWith (ctes : List SqlEquiv.CTEDef) (q : SqlEquiv.Query) : ElabM SqlEquiv.Query := do
  let env ← inlineEnv N [] ctes
  let some q := Inline.query N.fold env q | throw (.unsupported "WITH inside WITH")
  pure q

end SqlBridge

/-! ### WITH RECURSIVE (phase 9.6, #464) -/

namespace SqlBridge

open SqlCore

/-- The schema `S` with one more table, `none`: a recursive CTE of `k` columns. -/
def viewSchema (S : DbSchema) (k : ℕ) (cols : Fin k → Column) : DbSchema where
  Table := Option S.Table
  arity | none => k | some t => S.arity t
  columns | none => cols | some t => S.columns t

/-- The named schema with a recursive CTE `name` as one more table; the CTE comes first, so it
hides a base table of the same name. -/
def NamedSchema.withView (N : NamedSchema) (name : String) (k : ℕ) (cols : Fin k → Column) :
    NamedSchema where
  S := viewSchema N.S k cols
  tables := (N.fold name, none) :: N.tables.map fun (s, t) => (s, some t)
  fold := N.fold
  config := N.config

/-- Replace the recursive CTE's table by the query `v`: the `recurse` query in the main query, the
working row (`outer`) in the recursive step. A syntactic map over every node. -/
def bindView {S : DbSchema} {k : ℕ} {cols : Fin k → Column} (v : Query S k) :
    {n : ℕ} → Query (viewSchema S k cols) n → Query S n
  | _, .table none => v
  | _, .table (some t) => .table t
  | _, .select p q => .select p (bindView v q)
  | _, .project es q => .project es (bindView v q)
  | _, .join θ q₁ q₂ => .join θ (bindView v q₁) (bindView v q₂)
  | _, .unionAll q₁ q₂ => .unionAll (bindView v q₁) (bindView v q₂)
  | _, .distinct q => .distinct (bindView v q)
  | _, .aggregate keys aggs q => .aggregate keys aggs (bindView v q)
  | _, .orderBy keys q => .orderBy keys (bindView v q)
  | _, .limit c o q => .limit c o (bindView v q)
  | _, .intersect q₁ q₂ => .intersect (bindView v q₁) (bindView v q₂)
  | _, .difference q₁ q₂ => .difference (bindView v q₁) (bindView v q₂)
  | _, .attach kind sub q => .attach kind (bindView v sub) (bindView v q)
  | _, .one => .one
  | _, .outer Γ => .outer Γ
  | _, .lateral body q => .lateral (bindView v body) (bindView v q)
  | _, .window c q => .window c (bindView v q)
  | _, .recurse d r b st => .recurse d r (bindView v b) (bindView v st)
  | _, .outerJoin k θ q₁ q₂ => .outerJoin k θ (bindView v q₁) (bindView v q₂)

/-- The round limit of `WITH RECURSIVE` (registry T25): after this many rounds that still add
rows, the query fails with `recursionLimit`. -/
def recursionRounds : ℕ := 1000

/-- The number of times the table `name` is a source of a `FROM` tree, outside derived tables. -/
def topRefs (fold : String → String) (name : String) : SqlEquiv.FromClause → ℕ
  | .table ⟨t, _⟩ => if fold t == name then 1 else 0
  | .subquery _ _ => 0
  | .join l _ r _ => topRefs fold name l + topRefs fold name r

/-- The `FROM` tree with its top-level references to `name` renamed out of the way. -/
def renameTop (fold : String → String) (name : String) : SqlEquiv.FromClause → SqlEquiv.FromClause
  | .table ⟨t, al⟩ => if fold t == name then .table ⟨"?recursive?", some (al.getD t)⟩ else .table ⟨t, al⟩
  | .subquery sq al => .subquery sq al
  | .join l k r on => .join (renameTop fold name l) k (renameTop fold name r) on

variable (N : NamedSchema)

/-- A recursive step that Postgres accepts (registry T24): linear recursion, the CTE `name` once,
as a source of the step's `FROM` (not in a derived table, a subquery or an expression), and no
aggregate, window function, `DISTINCT`, `GROUP BY`, `HAVING`, `ORDER BY` or `LIMIT`. -/
def stepOk (name : String) : SqlEquiv.SelectStmt → Bool
  | s@(.mk distinct items (some f) w groupBy having orderBy limitVal offsetVal) =>
    let marker : SqlEquiv.SubQuery := .simple (.mk false [] none none [] none [] none none)
    let s' : SqlEquiv.SelectStmt :=
      .mk distinct items (some (renameTop N.fold name f)) w groupBy having orderBy limitVal offsetVal
    let _ := s
    !distinct && groupBy.isEmpty && having.isNone && orderBy.isEmpty && limitVal.isNone &&
      offsetVal.isNone && (aggsOfList (items.filterMap itemExprOf)).isEmpty &&
      !SqlEquiv.selectHasWindowFn items && topRefs N.fold name f == 1 &&
      decide (Inline.select N.fold [(name, marker)] s' = s')
  | _ => false

/-- Elaborate a top-level `WITH`: non-recursive CTEs are inlined (phase 9.2); one recursive CTE
(phase 9.6, #464) becomes `Query.recurse` over its base and step, the step reading the working row
through `outer`, and the CTEs after it and the main query are elaborated with the CTE as one more
table (`NamedSchema.withView`), which `bindView` then replaces by the `recurse` query. -/
def elabWith (ctes : List SqlEquiv.CTEDef) (q : SqlEquiv.Query) : ElabM (Elaborated N.S) := do
  let names := ctes.map fun c => N.fold c.name
  if names.eraseDups.length ≠ names.length then throw (.typeError "WITH: a name defined twice")
  let marker : SqlEquiv.SubQuery := .simple (.mk false [] none none [] none [] none none)
  let mentions (name : String) (x : SqlEquiv.Query) : Bool :=
    Inline.query N.fold [(N.fold name, marker)] x != some x
  -- recursive: under `WITH RECURSIVE` and naming itself (otherwise its name is the base table's)
  let isRec (c : SqlEquiv.CTEDef) : Bool := c.isRecursive && mentions c.name c.query
  match ctes.findIdx? isRec with
  | none => elabQueryRaw N (← inlineWith N ctes q)
  | some i =>
    let before := ctes.take i
    let after := ctes.drop (i + 1)
    let some rc := ctes[i]? | throw (.typeError "WITH")
    if after.any isRec then throw (.unsupported "WITH RECURSIVE: more than one recursive CTE")
    let r := N.fold rc.name
    let env₀ ← inlineEnv N [] before
    let .compound baseQ op (.simple stepSel) := rc.query
      | throw (.unsupported "WITH RECURSIVE: the body must be <base> UNION [ALL] <step>")
    let dist ← match op with
      | .union => pure true
      | .unionAll => pure false
      | _ => throw (.unsupported "WITH RECURSIVE: the body must be <base> UNION [ALL] <step>")
    if mentions rc.name baseQ then
      throw (.unsupported "WITH RECURSIVE: the CTE in its base part")
    let some baseQ := Inline.query N.fold env₀ baseQ | throw (.unsupported "WITH inside WITH")
    let stepSel := Inline.select N.fold env₀ stepSel
    if !stepOk N r stepSel then
      throw (.unsupported "WITH RECURSIVE: a recursive step outside Postgres's rules")
    let ⟨k, qb, cb⟩ ← elabQueryRaw N baseQ
    let some Γ := qb.typeOf | throw (.typeError "WITH RECURSIVE: base")
    let N' := N.withView rc.name k (requalify r cb)
    let es ← elabSelect N' stepSel
    if h : es.n = k then
      let qs : Query N.S k := bindView (.outer Γ) (h ▸ es.q)
      let v : Query N.S k := .recurse dist recursionRounds qb qs
      if v.typeOf.isNone then
        throw (.typeError "WITH RECURSIVE: the recursive step changes a column's type")
      let env ← inlineEnv N' env₀ after
      let some q := Inline.query N'.fold env q | throw (.unsupported "WITH inside WITH")
      let e ← elabQueryRaw N' q
      pure ⟨e.n, bindView v e.q, e.cols⟩
    else throw (.typeError "WITH RECURSIVE: the step's number of columns")

/-- Elaborate a parsed query, and check that the result is well-typed. -/
def elabQuery : SqlEquiv.Query → ElabM (Elaborated N.S)
  | .withCTE ctes q => do
    let e ← elabWith N ctes q
    if e.q.typeOf.isSome then pure e else throw (.typeError "query")
  | q => do
  let e ← elabQueryRaw N q
  if e.q.typeOf.isSome then pure e else throw (.typeError "query")

/-- Elaborate a parsed statement; only queries are in the fragment. -/
def elabStmt : SqlEquiv.Stmt → ElabM (Elaborated N.S)
  | .query q => elabQuery N q
  | _ => throw (.unsupported "DML")

/-! ### INSERT, UPDATE, DELETE (phase 9.7, #465) -/

/-- A value for a column of type `τ` (registry T20): an expression of type `τ`, a `NULL` (given the
column's type), or an integer into a `DECIMAL` column (promoted, as decision 6). Every other type
is an error, where the engines cast (`1` into a `TEXT` column, `1.5` into an `INTEGER` one). -/
def assignTo {n : ℕ} (cols : Fin n → Column) (τ : SqlType) (e : Expr n) : ElabM (Expr n) :=
  match e with
  | .null _ => pure (.null τ)
  | _ =>
    match e.typeOf (ctx cols) with
    | some σ =>
      if σ = τ then pure e
      else if σ = .int ∧ τ = .decimal then pure (.unary .toDecimal e)
      else throw (.typeError "assignment")
    | none => throw (.typeError "assignment")

/-- The target columns of an `INSERT` with `k` values per row: the column list resolved against the
table, or the first `k` columns; a column listed twice is an error. With no list and fewer values
than columns, the dialect decides (registry T19): an error, or the remaining columns `NULL`. -/
def insertTargets (t : N.S.Table) (columns : Option (List String)) (k : ℕ) :
    ElabM (List (Fin (N.S.arity t))) := do
  let cols := N.S.columns t
  match columns with
  | some names =>
    let is ← names.mapM fun c => resolve cols N.fold none c
    if is.length ≠ k then throw (.typeError "INSERT: number of values and columns")
    if is.eraseDups.length ≠ is.length then throw (.typeError "INSERT: column listed twice")
    pure is
  | none =>
    if k > N.S.arity t then throw (.typeError "INSERT: more values than columns")
    if k < N.S.arity t && N.config.shortInsert == .reject then
      throw (.typeError "INSERT: fewer values than columns")
    pure ((List.finRange (N.S.arity t)).take k)

/-- The row an `INSERT` writes: value `j` into target column `j`, `NULL` elsewhere. -/
def insertRow {m : ℕ} (t : N.S.Table) (targets : List (Fin (N.S.arity t)))
    (vals : List (Expr m)) (vcols : Fin m → Column) : ElabM (Fin (N.S.arity t) → Expr m) := do
  let es ← (List.finRange (N.S.arity t)).mapM fun i => do
    let τ := (N.S.columns t i).type
    match targets.idxOf? i with
    | some j =>
      match vals[j]? with
      | some e => assignTo vcols τ e
      | none => throw (.typeError "INSERT: number of values and columns")
    | none => pure (.null τ)
  if h : es.length = N.S.arity t then pure fun i => es[i]'(by omega)
  else throw (.typeError "INSERT row")

/-- Elaborate a data-modifying statement into `SqlCore.Stmt` (phase 9.7, #465). `INSERT … VALUES`
is a `UNION ALL` of one-row projections, `INSERT … SELECT` a projection of the `SELECT`;
`UPDATE` assigns `col i` to every column it does not set, so every assignment reads the old row.
`WHERE` and the values have no subqueries yet. -/
def elabDml : SqlEquiv.Stmt → ElabM (SqlCore.Stmt N.S)
  | .query _ => throw (.unsupported "a query is not a data-modifying statement")
  | .insert ⟨name, columns, source⟩ => do
    let t ← lookupTable N name
    let q : Query N.S (N.S.arity t) ← match source with
      | .values rows => do
        -- every row has one length, as in every engine (Postgres: "VALUES lists must all be the
        -- same length"), before the dialect's rule for short rows (T19)
        if (rows.map List.length).eraseDups.length > 1 then
          throw (.typeError "INSERT: VALUES rows of different lengths")
        let qs ← rows.mapM fun vs => do
          let targets ← insertTargets N t columns vs.length
          let es ← vs.mapM (elabExpr (n := 0) Fin.elim0 N.fold noHook)
          let row ← insertRow N t targets es Fin.elim0
          pure (Query.project row (.one : Query N.S 0))
        match qs with
        | [] => throw (.typeError "INSERT without rows")
        | q :: rest => pure (rest.foldl (fun acc q' => .unionAll acc q') q)
      | .selectStmt sel => do
        let e ← elabSelect N sel
        let targets ← insertTargets N t columns e.n
        -- a `NULL` literal column of the `SELECT` takes its target column's type (as #472 does
        -- for set-operation branches)
        let q := (List.finRange e.n).foldl (fun q j =>
          match targets[j.val]? with
          | some i => retypeNullCol j (N.S.columns t i).type q
          | none => q) e.q
        let some Γ := q.typeOf | throw (.typeError "INSERT … SELECT")
        let row ← insertRow N t targets ((List.finRange e.n).map fun j => (.col j : Expr e.n))
          fun j => { e.cols j with type := Γ j }
        pure (.project row q)
    let s : SqlCore.Stmt N.S := .insert t q
    if s.WellTyped then pure s else throw (.typeError "INSERT")
  | .update ⟨name, assignments, where_⟩ => do
    let t ← lookupTable N name
    let cols := requalify (N.fold name) (N.S.columns t)
    let assigned ← assignments.mapM fun ⟨c, v⟩ => do
      let i ← resolve cols N.fold none c
      let e ← elabExpr cols N.fold noHook v
      pure (i, ← assignTo cols (cols i).type e)
    if (assigned.map (·.1)).eraseDups.length ≠ assigned.length then
      throw (.typeError "UPDATE: column assigned twice")
    let set : Fin (N.S.arity t) → Expr (N.S.arity t) := fun i =>
      ((assigned.find? (·.1 == i)).map (·.2)).getD (.col i)
    let w ← match where_ with
      | some w => elabExpr cols N.fold noHook w
      | none => pure (.lit (.bool true))
    let s : SqlCore.Stmt N.S := .update t set w
    if s.WellTyped then pure s else throw (.typeError "UPDATE")
  | .delete ⟨name, where_⟩ => do
    let t ← lookupTable N name
    let cols := requalify (N.fold name) (N.S.columns t)
    let w ← match where_ with
      | some w => elabExpr cols N.fold noHook w
      | none => pure (.lit (.bool true))
    let s : SqlCore.Stmt N.S := .delete t w
    if s.WellTyped then pure s else throw (.typeError "DELETE")

end SqlBridge
