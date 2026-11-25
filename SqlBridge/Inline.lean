/-
  Inlining non-recursive common table expressions (typed core phase 9.2, #460).

  `WITH c AS (body) … FROM c [AS x] …` means `… FROM (body) AS x …` (alias `c` when there is
  none): a non-recursive CTE is a named derived table, and SQL fixes no evaluation strategy for it,
  so the elaborator substitutes it before elaborating. Every engine gives the same rows either way
  (no SQL function in the fragment is volatile).

  `Inline.sub fold env` replaces every table reference whose folded name is bound in `env` by the
  bound body, wherever a table can occur: `FROM`, joins, derived tables and subqueries in any
  expression (window arguments included). The CTE bodies themselves are substituted in order by
  the caller, so a CTE sees the earlier ones only, and a body that names its own CTE reads the base
  table of that name, as a non-recursive CTE does.
-/
import SqlEquiv

namespace SqlBridge.Inline

open SqlEquiv

variable (fold : String → String) (env : List (String × SubQuery))

mutual

def expr : Expr → Expr
  | .binOp op a b => .binOp op (expr a) (expr b)
  | .unaryOp op a => .unaryOp op (expr a)
  | .func f args => .func f (exprs args)
  | .agg f a d => .agg f (exprOpt a) d
  | .«case» bs e => .«case» (branches bs) (exprOpt e)
  | .inList e neg vs => .inList (expr e) neg (exprs vs)
  | .inSubquery e neg sq => .inSubquery (expr e) neg (sub sq)
  | .exists neg sq => .exists neg (sub sq)
  | .subquery sq => .subquery (sub sq)
  | .between a b c => .between (expr a) (expr b) (expr c)
  | .windowFn f a (.mk p o) => .windowFn f (exprOpt a) (.mk (exprs p) (orders o))
  | e => e

def exprs : List Expr → List Expr
  | [] => []
  | e :: es => expr e :: exprs es

def exprOpt : Option Expr → Option Expr
  | none => none
  | some e => some (expr e)

def branches : List (Expr × Expr) → List (Expr × Expr)
  | [] => []
  | (c, a) :: bs => (expr c, expr a) :: branches bs

def orders : List OrderByItem → List OrderByItem
  | [] => []
  | .mk e d n :: os => .mk (expr e) d n :: orders os

def items : List SelectItem → List SelectItem
  | [] => []
  | .star q :: is => .star q :: items is
  | .exprItem e al :: is => .exprItem (expr e) al :: items is

def from_ : FromClause → FromClause
  | .table ⟨name, al⟩ =>
    match env.find? (·.1 == fold name) with
    | some (_, body) => .subquery body (al.getD name)
    | none => .table ⟨name, al⟩
  | .subquery sq al => .subquery (sub sq) al
  | .join l k r on => .join (from_ l) k (from_ r) (exprOpt on)

def fromOpt : Option FromClause → Option FromClause
  | none => none
  | some f => some (from_ f)

def sub : SubQuery → SubQuery
  | .simple s => .simple (select s)
  | .compound l op r => .compound (sub l) op (sub r)

def select : SelectStmt → SelectStmt
  | .mk d is f w g h o l off =>
    .mk d (items is) (fromOpt f) (exprOpt w) (exprs g) (exprOpt h) (orders o) l off

end

/-- A query with the CTEs of `env` substituted; `none` for a `WITH` inside it, whose names would
shadow those of `env` (the parser keeps `WITH` at the top level). -/
def query : Query → Option Query
  | .simple s => some (.simple (select fold env s))
  | .compound l op r => do pure (.compound (← query l) op (← query r))
  | .ordered q o l off => do pure (.ordered (← query q) (orders fold env o) l off)
  | .withCTE _ _ => none

/-- A CTE body as a derived-table body: a `SELECT`, or a set operation without a trailing
`ORDER BY`/`LIMIT` (which a derived table's body cannot hold). -/
def body : Query → Option SubQuery
  | .simple s => some (.simple s)
  | .compound l op r => do pure (.compound (← body l) op (← body r))
  | _ => none

end SqlBridge.Inline
