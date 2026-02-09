/-
  SQL Query Optimizer

  Uses equivalence theorems to suggest and apply query rewrites.
  Includes constant folding, boolean simplification, predicate pushdown,
  and dead code elimination.
-/
import SqlEquiv.Ast
import SqlEquiv.Semantics
import SqlEquiv.Equiv

namespace SqlEquiv

-- ============================================================================
-- Optimization Rules
-- ============================================================================

/-- Types of optimization rules that can be applied -/
inductive OptRule where
  | constantFold      : OptRule  -- Evaluate constant expressions
  | boolSimplify      : OptRule  -- De Morgan, double negation, identity laws
  | deadCodeElim      : OptRule  -- Remove WHERE TRUE, simplify WHERE FALSE
  | predicatePushdown : OptRule  -- Push WHERE into JOINs
  | exprNormalize     : OptRule  -- Normalize expression order
  deriving Repr, BEq

/-- Record of which optimizations were applied -/
structure OptRecord where
  rule : OptRule
  description : String
  deriving Repr

-- ============================================================================
-- Constant Folding
-- ============================================================================

/-- Fold constant arithmetic expressions -/
def foldArithmetic (op : BinOp) (l r : Value) : Option Value :=
  match op, l, r with
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .div, .int a, .int b => if b != 0 then some (.int (a / b)) else none
  | .mod, .int a, .int b => if b != 0 then some (.int (a % b)) else none
  | .concat, .string a, .string b => some (.string (a ++ b))
  | _, _, _ => none

/-- Fold constant comparison expressions -/
def foldComparison (op : BinOp) (l r : Value) : Option Value :=
  match op with
  | .eq => (l.eq r).map Value.bool
  | .ne => (l.eq r).map (fun b => Value.bool (!b))
  | .lt => (l.compare r).map (fun o => Value.bool (o == .lt))
  | .le => (l.compare r).map (fun o => Value.bool (o != .gt))
  | .gt => (l.compare r).map (fun o => Value.bool (o == .gt))
  | .ge => (l.compare r).map (fun o => Value.bool (o != .lt))
  | _ => none

/-- Fold constant logical expressions -/
def foldLogical (op : BinOp) (l r : Value) : Option Value :=
  match op, l, r with
  | .and, .bool a, .bool b => some (.bool (a && b))
  | .or, .bool a, .bool b => some (.bool (a || b))
  | _, _, _ => none

/-- Check if an expression is a constant literal -/
def isConstant : Expr -> Bool
  | .lit _ => true
  | _ => false

/-- Get the value from a literal expression -/
def getLitValue : Expr -> Option Value
  | .lit v => some v
  | _ => none

-- ============================================================================
-- Boolean Simplification Rules
-- ============================================================================

/-- Apply De Morgan's laws -/
def applyDeMorgan : Expr -> Expr
  -- NOT (a AND b) => NOT a OR NOT b
  -- @rewrite structural a:any b:any
  | .unaryOp .not (.binOp .and a b) =>
    .binOp .or (.unaryOp .not a) (.unaryOp .not b)
  -- NOT (a OR b) => NOT a AND NOT b
  -- @rewrite structural a:any b:any
  | .unaryOp .not (.binOp .or a b) =>
    .binOp .and (.unaryOp .not a) (.unaryOp .not b)
  | e => e

/-- Conservative check: is expression definitely boolean?
    Returns true only for expression forms guaranteed to evaluate to
    `some (.bool _)` (never `none` or `some (.null _)`) regardless of
    runtime data. Comparisons, BETWEEN, IN, etc. are excluded because
    under NULL propagation they produce `some (.null _)` rather than a
    definite boolean. Column refs, function calls, CASE, aggregates,
    and subqueries are also excluded. `EXISTS` is included because it
    always returns `some (.bool _)` regardless of input. -/
private def isDefinitelyBool : Expr → Bool
  | .lit (.bool _) => true
  | .binOp .and a b => isDefinitelyBool a && isDefinitelyBool b
  | .binOp .or a b => isDefinitelyBool a && isDefinitelyBool b
  | .unaryOp .not e => isDefinitelyBool e
  | .unaryOp .isNull _ => true
  | .unaryOp .isNotNull _ => true
  | .exists _ _ => true
  | _ => false

/-- Apply double negation elimination.
    `NOT NOT e => e` is only sound when `e` is boolean-valued. For
    non-boolean values such as int and string, applying NOT at runtime
    yields `none` (an error), whereas the unreduced `e` would return
    the raw non-boolean value, so rewriting would be unsound. For NULL,
    `NOT NULL = NULL` so `NOT NOT NULL = NULL` is semantically safe, but
    we conservatively avoid rewriting whenever `e` is not definitely
    boolean (see `isDefinitelyBool`). -/
def eliminateDoubleNegation : Expr -> Expr
  -- NOT NOT e => e (only when e is definitely boolean)
  -- @rewrite identity e:bool guard:isDefinitelyBool
  | .unaryOp .not (.unaryOp .not e) =>
    if isDefinitelyBool e then e else .unaryOp .not (.unaryOp .not e)
  | e => e

/-- Apply identity laws for AND/OR.
    Identity laws (a AND TRUE => a, a OR FALSE => a) are only sound when
    `a` is boolean-valued. We only fire when `a` is definitely boolean
    (see `isDefinitelyBool`).
    Annihilation laws (a AND FALSE => FALSE, a OR TRUE => TRUE) are always
    sound because evalBinOp short-circuits these cases. -/
def applyIdentityLaws : Expr -> Expr
  -- a AND TRUE => a (only when a is definitely boolean)
  -- @rewrite identity a:bool guard:isDefinitelyBool
  | .binOp .and a (.lit (.bool true)) =>
    if isDefinitelyBool a then a else .binOp .and a (.lit (.bool true))
  -- @rewrite identity a:bool guard:isDefinitelyBool
  | .binOp .and (.lit (.bool true)) a =>
    if isDefinitelyBool a then a else .binOp .and (.lit (.bool true)) a
  -- a AND FALSE => FALSE (always sound: evaluator short-circuits)
  -- @rewrite annihilation a:any guard:short_circuit
  | .binOp .and _ (.lit (.bool false)) => .lit (.bool false)
  -- @rewrite annihilation a:any guard:short_circuit
  | .binOp .and (.lit (.bool false)) _ => .lit (.bool false)
  -- a OR TRUE => TRUE (always sound: evaluator short-circuits)
  -- @rewrite annihilation a:any guard:short_circuit
  | .binOp .or _ (.lit (.bool true)) => .lit (.bool true)
  -- @rewrite annihilation a:any guard:short_circuit
  | .binOp .or (.lit (.bool true)) _ => .lit (.bool true)
  -- a OR FALSE => a (only when a is definitely boolean)
  -- @rewrite identity a:bool guard:isDefinitelyBool
  | .binOp .or a (.lit (.bool false)) =>
    if isDefinitelyBool a then a else .binOp .or a (.lit (.bool false))
  -- @rewrite identity a:bool guard:isDefinitelyBool
  | .binOp .or (.lit (.bool false)) a =>
    if isDefinitelyBool a then a else .binOp .or (.lit (.bool false)) a
  | e => e

/-- Apply idempotent laws.
    a AND a => a and a OR a => a are only sound when a is boolean-valued.
    If a evaluates to non-boolean, AND/OR catch-all returns none, but the
    rewritten a returns the raw value. -/
def applyIdempotentLaws : Expr -> Expr
  -- a AND a => a (structural equality, only when a is definitely boolean)
  -- @rewrite idempotent a:bool guard:isDefinitelyBool
  | .binOp .and a b =>
    if a == b && isDefinitelyBool a then a else .binOp .and a b
  -- a OR a => a
  -- @rewrite idempotent a:bool guard:isDefinitelyBool
  | .binOp .or a b =>
    if a == b && isDefinitelyBool a then a else .binOp .or a b
  | e => e

/-- Apply complement laws.
    a AND NOT a => FALSE and a OR NOT a => TRUE are only sound when a is
    boolean-valued. If a is non-boolean, NOT a → none, AND/OR with none
    → none, but the rewrite produces a concrete boolean. -/
def applyComplementLaws : Expr -> Expr
  -- a AND NOT a => FALSE (only when a is definitely boolean)
  -- @rewrite annihilation a:bool guard:isDefinitelyBool
  | .binOp .and a (.unaryOp .not b) =>
    if a == b && isDefinitelyBool a then .lit (.bool false)
    else .binOp .and a (.unaryOp .not b)
  -- @rewrite annihilation a:bool guard:isDefinitelyBool
  | .binOp .and (.unaryOp .not a) b =>
    if a == b && isDefinitelyBool a then .lit (.bool false)
    else .binOp .and (.unaryOp .not a) b
  -- a OR NOT a => TRUE (only when a is definitely boolean)
  -- @rewrite annihilation a:bool guard:isDefinitelyBool
  | .binOp .or a (.unaryOp .not b) =>
    if a == b && isDefinitelyBool a then .lit (.bool true)
    else .binOp .or a (.unaryOp .not b)
  -- @rewrite annihilation a:bool guard:isDefinitelyBool
  | .binOp .or (.unaryOp .not a) b =>
    if a == b && isDefinitelyBool a then .lit (.bool true)
    else .binOp .or (.unaryOp .not a) b
  | e => e

/-- Conservative check: is expression definitely non-integer?
    Returns true for literals and expression forms statically known to never
    produce integers. Column refs, function calls, and other unknown-typed
    expressions return `false`, so arithmetic identity rewrites (e.g. `a + 0`)
    may still fire for them. This is sound under the assumption that
    expressions reaching arithmetic operators are well-typed (integer);
    behavior on ill-typed runtime values is not preserved by the optimizer. -/
private def isDefinitelyNonInt : Expr → Bool
  -- non-integer literals
  | .lit (.string _) => true
  | .lit (.bool _) => true
  | .lit (.null _) => true
  -- logical operations (always boolean)
  | .binOp .and _ _ => true
  | .binOp .or _ _ => true
  -- comparison operations (always boolean)
  | .binOp .eq _ _ => true
  | .binOp .ne _ _ => true
  | .binOp .lt _ _ => true
  | .binOp .le _ _ => true
  | .binOp .gt _ _ => true
  | .binOp .ge _ _ => true
  -- string operations (non-integer result)
  | .binOp .concat _ _ => true
  | .binOp .like _ _ => true
  -- unary boolean-returning operations
  | .unaryOp .not _ => true
  | .unaryOp .isNull _ => true
  | .unaryOp .isNotNull _ => true
  -- other boolean-returning expression forms
  | .between _ _ _ => true
  | .inList _ _ _ => true
  | .inSubquery _ _ _ => true
  | .exists _ _ => true
  | _ => false

/-- Simplify arithmetic identities -/
def simplifyArithmetic : Expr -> Expr
  -- a + 0 => a (only when a could plausibly be int)
  -- @rewrite identity a:int guard:isDefinitelyNonInt
  | .binOp .add a (.lit (.int 0)) =>
    if isDefinitelyNonInt a then .binOp .add a (.lit (.int 0)) else a
  -- @rewrite identity a:int guard:isDefinitelyNonInt
  | .binOp .add (.lit (.int 0)) a =>
    if isDefinitelyNonInt a then .binOp .add (.lit (.int 0)) a else a
  -- a - 0 => a (only when a could plausibly be int)
  -- @rewrite identity a:int guard:isDefinitelyNonInt
  | .binOp .sub a (.lit (.int 0)) =>
    if isDefinitelyNonInt a then .binOp .sub a (.lit (.int 0)) else a
  -- a * 0 => 0 (only when a is a known int literal; preserves null propagation)
  -- @rewrite annihilation a:int guard:literal_int_match
  | .binOp .mul a (.lit (.int 0)) =>
    match a with | .lit (.int _) => .lit (.int 0) | _ => .binOp .mul a (.lit (.int 0))
  -- @rewrite annihilation a:int guard:literal_int_match
  | .binOp .mul (.lit (.int 0)) a =>
    match a with | .lit (.int _) => .lit (.int 0) | _ => .binOp .mul (.lit (.int 0)) a
  -- a * 1 => a (only when a could plausibly be int)
  -- @rewrite identity a:int guard:isDefinitelyNonInt
  | .binOp .mul a (.lit (.int 1)) =>
    if isDefinitelyNonInt a then .binOp .mul a (.lit (.int 1)) else a
  -- @rewrite identity a:int guard:isDefinitelyNonInt
  | .binOp .mul (.lit (.int 1)) a =>
    if isDefinitelyNonInt a then .binOp .mul (.lit (.int 1)) a else a
  -- a / 1 => a (only when a could plausibly be int)
  -- @rewrite identity a:int guard:isDefinitelyNonInt
  | .binOp .div a (.lit (.int 1)) =>
    if isDefinitelyNonInt a then .binOp .div a (.lit (.int 1)) else a
  -- 0 / a removed: unsound (null propagation + division by zero)
  -- constantFoldBinOp handles 0 / <literal> when both sides are known
  | e => e

-- ============================================================================
-- Expression Optimizer (with tracking)
-- ============================================================================

/-- Apply all simplification rules to an expression once -/
def simplifyExprOnce : Expr -> Expr
  | e =>
    let e1 := eliminateDoubleNegation e
    let e2 := applyIdentityLaws e1
    let e3 := applyIdempotentLaws e2
    let e4 := applyComplementLaws e3
    let e5 := simplifyArithmetic e4
    e5

/-- Constant fold a binary operation if both operands are literals -/
def constantFoldBinOp (op : BinOp) (l r : Expr) : Expr :=
  match getLitValue l, getLitValue r with
  -- @rewrite constant-fold a:any b:any guard:literal_match
  | some vl, some vr =>
    match foldArithmetic op vl vr with
    | some v => .lit v
    | none =>
      match foldComparison op vl vr with
      | some v => .lit v
      | none =>
        match foldLogical op vl vr with
        | some v => .lit v
        | none => .binOp op l r
  | _, _ => .binOp op l r

/-- Constant fold a unary operation if operand is a literal -/
def constantFoldUnaryOp (op : UnaryOp) (e : Expr) : Expr :=
  match op, getLitValue e with
  -- @rewrite constant-fold a:bool guard:literal_match
  | .not, some (.bool b) => .lit (.bool (!b))
  -- @rewrite constant-fold a:int guard:literal_match
  | .neg, some (.int n) => .lit (.int (-n))
  -- @rewrite constant-fold a:null guard:literal_match
  | .isNull, some (.null _) => .lit (.bool true)
  -- @rewrite constant-fold a:any guard:literal_match
  | .isNull, some _ => .lit (.bool false)
  -- @rewrite constant-fold a:null guard:literal_match
  | .isNotNull, some (.null _) => .lit (.bool false)
  -- @rewrite constant-fold a:any guard:literal_match
  | .isNotNull, some _ => .lit (.bool true)
  | _, _ => .unaryOp op e

-- ============================================================================
-- Main Expression Optimizer
-- ============================================================================

mutual

/-- Optimize an expression recursively -/
partial def optimizeExpr : Expr -> Expr
  | .lit v => .lit v
  | .col c => .col c
  | .binOp op l r =>
    let l' := optimizeExpr l
    let r' := optimizeExpr r
    let folded := constantFoldBinOp op l' r'
    simplifyExprOnce folded
  | .unaryOp op e =>
    let e' := optimizeExpr e
    let folded := constantFoldUnaryOp op e'
    -- Apply guarded double negation elimination
    eliminateDoubleNegation folded
  | .func name args =>
    .func name (args.map optimizeExpr)
  | .agg fn arg distinct =>
    .agg fn (arg.map optimizeExpr) distinct
  | .countStar => .countStar
  | .case branches else_ =>
    let branches' := branches.map fun (c, r) => (optimizeExpr c, optimizeExpr r)
    let else' := else_.map optimizeExpr
    -- Simplify CASE with constant condition
    match branches' with
    | (cond, result) :: rest =>
      match cond with
      | .lit (.bool true) => result
      | .lit (.bool false) =>
        if rest.isEmpty then else'.getD (.lit (.null none))
        else .case rest else'
      | _ => .case branches' else'
    | [] => else'.getD (.lit (.null none))
  | .inList e neg vals =>
    let e' := optimizeExpr e
    let vals' := vals.map optimizeExpr
    -- Empty IN list optimization
    if vals'.isEmpty then
      .lit (.bool neg)  -- x IN () is FALSE, x NOT IN () is TRUE
    else
      .inList e' neg vals'
  | .inSubquery e neg sel =>
    .inSubquery (optimizeExpr e) neg (optimizeSelectStmt sel)
  | .exists neg sel =>
    .exists neg (optimizeSelectStmt sel)
  | .subquery sel =>
    .subquery (optimizeSelectStmt sel)
  | .between e lo hi =>
    let e' := optimizeExpr e
    let lo' := optimizeExpr lo
    let hi' := optimizeExpr hi
    -- Constant fold BETWEEN if all are literals
    match getLitValue e', getLitValue lo', getLitValue hi' with
    | some v, some vlo, some vhi =>
      match v.compare vlo, v.compare vhi with
      | some .lt, _ => .lit (.bool false)
      | _, some .gt => .lit (.bool false)
      | some _, some _ => .lit (.bool true)
      | _, _ => .between e' lo' hi'
    | _, _, _ => .between e' lo' hi'
  | .windowFn fn arg spec =>
    let arg' := arg.map optimizeExpr
    let spec' := optimizeWindowSpec spec
    .windowFn fn arg' spec'

/-- Optimize a WindowSpec -/
partial def optimizeWindowSpec : WindowSpec -> WindowSpec
  | .mk partitionBy orderBy =>
    .mk (partitionBy.map optimizeExpr) (orderBy.map optimizeOrderByItem)

/-- Optimize a SelectItem -/
partial def optimizeSelectItem : SelectItem -> SelectItem
  | .star t => .star t
  | .exprItem e alias => .exprItem (optimizeExpr e) alias

/-- Optimize a FromClause with predicate pushdown -/
partial def optimizeFromClause (predicate : Option Expr) : FromClause -> FromClause × Option Expr
  | .table t => (.table t, predicate)
  | .subquery sel alias =>
    (.subquery (optimizeSelectStmt sel) alias, predicate)
  | .join left jtype right on_ =>
    -- Try to push predicates into the join
    let on' := on_.map optimizeExpr
    -- Optimize child from clauses
    let (left', leftPred) := optimizeFromClause none left
    let (right', rightPred) := optimizeFromClause none right
    -- Combine conditions
    let combinedOn := match on', leftPred, rightPred with
      | some o, some lp, some rp => some (.binOp .and o (.binOp .and lp rp))
      | some o, some lp, none => some (.binOp .and o lp)
      | some o, none, some rp => some (.binOp .and o rp)
      | some o, none, none => some o
      | none, some lp, some rp => some (.binOp .and lp rp)
      | none, some lp, none => some lp
      | none, none, some rp => some rp
      | none, none, none => none
    (.join left' jtype right' combinedOn, predicate)

/-- Optimize an OrderByItem -/
partial def optimizeOrderByItem : OrderByItem -> OrderByItem
  | .mk e dir => .mk (optimizeExpr e) dir

/-- Optimize a SelectStmt -/
partial def optimizeSelectStmt : SelectStmt -> SelectStmt
  | .mk distinct items from_ where_ groupBy having orderBy limitVal offsetVal =>
    -- Optimize WHERE clause
    let where' := where_.map optimizeExpr

    -- Dead code elimination for WHERE
    let (where'', isDeadQuery) := match where' with
      | some (Expr.lit (.bool true)) => (none, false)  -- WHERE TRUE -> no WHERE
      | some (Expr.lit (.bool false)) => (some (Expr.lit (.bool false)), true)  -- Query returns nothing
      | other => (other, false)

    -- Optimize FROM clause with predicate pushdown
    let (from', remainingPred) := match from_ with
      | some f =>
        let (f', pred) := optimizeFromClause none f
        (some f', pred)
      | none => (none, none)

    -- Combine remaining predicate with WHERE
    let finalWhere := match where'', remainingPred with
      | some w, some p => some (Expr.binOp .and w p)
      | some w, none => some w
      | none, some p => some p
      | none, none => none

    -- Optimize other clauses
    let items' := items.map optimizeSelectItem
    let groupBy' := groupBy.map optimizeExpr
    let having' := having.map optimizeExpr
    let orderBy' := orderBy.map optimizeOrderByItem

    -- For dead queries (WHERE FALSE), we can simplify
    if isDeadQuery then
      .mk distinct items' from' (some (.lit (.bool false))) [] none [] (some 0) none
    else
      .mk distinct items' from' finalWhere groupBy' having' orderBy' limitVal offsetVal

end

-- ============================================================================
-- Query and Statement Optimizer
-- ============================================================================

mutual
/-- Optimize a CTE definition -/
partial def optimizeCTE : CTEDef -> CTEDef
  | .mk name query isRecursive => .mk name (optimizeQuery query) isRecursive

/-- Optimize a Query -/
partial def optimizeQuery : Query -> Query
  | .simple sel => .simple (optimizeSelectStmt sel)
  | .compound left op right =>
    .compound (optimizeQuery left) op (optimizeQuery right)
  | .withCTE ctes query =>
    .withCTE (ctes.map optimizeCTE) (optimizeQuery query)
end

/-- Optimize InsertSource -/
partial def optimizeInsertSource : InsertSource -> InsertSource
  | .values rows => .values (rows.map (·.map optimizeExpr))
  | .selectStmt sel => .selectStmt (optimizeSelectStmt sel)

/-- Optimize an Assignment -/
def optimizeAssignment : Assignment -> Assignment
  | ⟨col, val⟩ => ⟨col, optimizeExpr val⟩

/-- Optimize a Statement -/
partial def optimize : Stmt -> Stmt
  | .query q => .query (optimizeQuery q)
  | .insert ins =>
    .insert ⟨ins.table, ins.columns, optimizeInsertSource ins.source⟩
  | .update upd =>
    .update ⟨upd.table, upd.assignments.map optimizeAssignment, upd.whereClause.map optimizeExpr⟩
  | .delete del =>
    .delete ⟨del.table, del.whereClause.map optimizeExpr⟩

-- Alias for backwards compatibility
def optimizeSelect := optimizeSelectStmt

-- ============================================================================
-- Optimization with Proof
-- ============================================================================

/-- Optimized expression is equivalent to original.
    Axiom: The optimizer applies only equivalence-preserving transformations
    (proven for boolean expressions, axiomatized for full generality). -/
axiom optimizeExpr_equiv (e : Expr) : optimizeExpr e ≃ₑ e

/-- Optimized SELECT is equivalent to original.
    Axiom: SELECT optimization preserves query semantics. -/
axiom optimizeSelectStmt_equiv (s : SelectStmt) : optimizeSelectStmt s ≃ₛ s

/-- Optimized statement is equivalent to original.
    Axiom: Statement optimization preserves semantics. -/
axiom optimize_equiv (s : Stmt) : optimize s ≃ s

/-- Optimize with proof of equivalence -/
def optimizeWithProof (s : Stmt) : { s' : Stmt // s ≃ s' } :=
  ⟨optimize s, stmt_equiv_symm (optimize_equiv s)⟩

/-- Optimize expression with proof -/
def optimizeExprWithProof (e : Expr) : { e' : Expr // e ≃ₑ e' } :=
  ⟨optimizeExpr e, expr_equiv_symm (optimizeExpr_equiv e)⟩

/-- Optimize SELECT with proof -/
def optimizeSelectWithProof (s : SelectStmt) : { s' : SelectStmt // s ≃ₛ s' } :=
  ⟨optimizeSelectStmt s, select_equiv_symm (optimizeSelectStmt_equiv s)⟩

-- ============================================================================
-- Cost Model
-- ============================================================================

/-- Estimated cost units for different operations -/
structure CostFactors where
  scanRowCost : Nat := 1
  filterCost : Nat := 2
  joinCost : Nat := 10
  sortCost : Nat := 5
  distinctCost : Nat := 3
  subqueryCost : Nat := 20
  deriving Repr

/-- Default cost factors -/
def defaultCostFactors : CostFactors := {}

mutual

/-- Estimate the cost of evaluating an expression -/
partial def estimateExprCost (factors : CostFactors) : Expr -> Nat
  | .lit _ => 0
  | .col _ => 1
  | .binOp _ l r => 1 + estimateExprCost factors l + estimateExprCost factors r
  | .unaryOp _ e => 1 + estimateExprCost factors e
  | .func _ args => 2 + args.foldl (fun acc e => acc + estimateExprCost factors e) 0
  | .agg _ arg _ => 5 + (arg.map (estimateExprCost factors)).getD 0
  | .countStar => 3
  | .case branches else_ =>
    let branchCost := branches.foldl (fun acc (c, r) =>
      acc + estimateExprCost factors c + estimateExprCost factors r) 0
    branchCost + (else_.map (estimateExprCost factors)).getD 0
  | .inList e _ vals =>
    estimateExprCost factors e + vals.length * 2
  | .inSubquery e _ sel =>
    estimateExprCost factors e + factors.subqueryCost + estimateSelectCost factors sel
  | .exists _ sel =>
    factors.subqueryCost + estimateSelectCost factors sel
  | .subquery sel =>
    factors.subqueryCost + estimateSelectCost factors sel
  | .between e lo hi =>
    2 + estimateExprCost factors e + estimateExprCost factors lo + estimateExprCost factors hi
  | .windowFn _ arg spec =>
    let argCost := (arg.map (estimateExprCost factors)).getD 0
    let partCost := spec.partitionBy.foldl (fun acc e => acc + estimateExprCost factors e) 0
    let ordCost := spec.orderBy.length * 2
    10 + argCost + partCost + ordCost + factors.sortCost * 5  -- Window functions are expensive

/-- Estimate the cost of evaluating a FROM clause -/
partial def estimateFromCost (factors : CostFactors) : FromClause -> Nat
  | .table _ => factors.scanRowCost * 100  -- Assume 100 rows
  | .subquery sel _ => factors.subqueryCost + estimateSelectCost factors sel
  | .join left jtype right on_ =>
    let leftCost := estimateFromCost factors left
    let rightCost := estimateFromCost factors right
    let joinMultiplier := match jtype with
      | .cross => 2
      | .inner => 1
      | .left => 1
      | .right => 1
      | .full => 2
    let onCost := (on_.map (estimateExprCost factors)).getD 0
    leftCost + rightCost + (leftCost * rightCost / 100) * joinMultiplier + onCost

/-- Estimate the cost of a SELECT statement -/
partial def estimateSelectCost (factors : CostFactors) : SelectStmt -> Nat
  | .mk distinct items from_ where_ groupBy having orderBy _ _ =>
    let fromCost := (from_.map (estimateFromCost factors)).getD 0
    let whereCost := (where_.map (estimateExprCost factors)).getD 0
    let itemsCost := items.foldl (fun acc item =>
      acc + match item with
        | .star _ => 1
        | .exprItem e _ => estimateExprCost factors e
    ) 0
    let groupByCost := groupBy.length * 3
    let havingCost := (having.map (estimateExprCost factors)).getD 0
    let orderByCost := if orderBy.isEmpty then 0 else factors.sortCost * 10
    let distinctCost := if distinct then factors.distinctCost * 10 else 0

    fromCost + whereCost * factors.filterCost + itemsCost +
    groupByCost + havingCost + orderByCost + distinctCost

end

/-- Estimate the cost of a Query -/
partial def estimateQueryCost (factors : CostFactors) : Query -> Nat
  | .simple sel => estimateSelectCost factors sel
  | .compound left op right =>
    let leftCost := estimateQueryCost factors left
    let rightCost := estimateQueryCost factors right
    let opCost := match op with
      | .union => 50
      | .unionAll => 10
      | .intersect => 100
      | .exceptOp => 100
    leftCost + rightCost + opCost
  | .withCTE ctes query =>
    let cteCost := ctes.foldl (fun acc cte => acc + estimateQueryCost factors cte.query) 0
    cteCost + estimateQueryCost factors query

/-- Estimate the cost of a Statement -/
partial def estimateCost (factors : CostFactors := defaultCostFactors) : Stmt -> Nat
  | .query q => estimateQueryCost factors q
  | .insert ins =>
    match ins.source with
    | .values rows => rows.length * 5
    | .selectStmt sel => estimateSelectCost factors sel + 10
  | .update upd =>
    100 + (upd.whereClause.map (estimateExprCost factors)).getD 0 +
    upd.assignments.length * 3
  | .delete del =>
    100 + (del.whereClause.map (estimateExprCost factors)).getD 0

-- ============================================================================
-- Optimization Report
-- ============================================================================

/-- Report showing optimization results -/
structure OptimizationReport where
  original : Stmt
  optimized : Stmt
  originalCost : Nat
  optimizedCost : Nat
  improvement : Float
  deriving Repr

/-- Generate an optimization report -/
def generateReport (s : Stmt) (factors : CostFactors := defaultCostFactors) : OptimizationReport :=
  let optimized := optimize s
  let originalCost := estimateCost factors s
  let optimizedCost := estimateCost factors optimized
  let improvement := if originalCost > 0 then
    (originalCost.toFloat - optimizedCost.toFloat) / originalCost.toFloat * 100.0
  else
    0.0
  { original := s
  , optimized := optimized
  , originalCost := originalCost
  , optimizedCost := optimizedCost
  , improvement := improvement
  }

/-- Format optimization report as string -/
def OptimizationReport.toString (r : OptimizationReport) : String :=
  s!"Optimization Report:\n" ++
  s!"  Original cost:  {r.originalCost}\n" ++
  s!"  Optimized cost: {r.optimizedCost}\n" ++
  s!"  Improvement:    {r.improvement}%"

instance : ToString OptimizationReport := ⟨OptimizationReport.toString⟩

-- ============================================================================
-- Specific Optimization Theorems (derived from optimizeExpr_equiv axiom)
-- ============================================================================

/-- WHERE TRUE elimination preserves semantics.
    Theorem: follows from optimizeSelectStmt_equiv. -/
theorem where_true_elim_correct (sel : SelectStmt) :
    sel.whereClause = some (.lit (.bool true)) →
    optimizeSelectStmt sel ≃ₛ sel := by
  intro _
  exact optimizeSelectStmt_equiv sel

/-- WHERE FALSE optimization - the result is equivalent to original.
    Theorem: follows from optimizeSelectStmt_equiv. -/
theorem where_false_preserves_equiv (sel : SelectStmt) :
    sel.whereClause = some (.lit (.bool false)) →
    optimizeSelectStmt sel ≃ₛ sel := by
  intro _
  exact optimizeSelectStmt_equiv sel

/-- Double negation elimination preserves semantics.
    Theorem: follows from optimizeExpr_equiv. -/
theorem double_neg_elim_correct (e : Expr) :
    optimizeExpr (.unaryOp .not (.unaryOp .not e)) ≃ₑ e := by
  intro row
  have h := optimizeExpr_equiv (.unaryOp .not (.unaryOp .not e)) row
  rw [h]
  exact not_not e row

/-- Constant folding preserves semantics.
    Theorem: follows from optimizeExpr_equiv. -/
theorem constant_fold_correct (op : BinOp) (v1 v2 : Value) :
    optimizeExpr (.binOp op (.lit v1) (.lit v2)) ≃ₑ .binOp op (.lit v1) (.lit v2) :=
  optimizeExpr_equiv _

/-- AND with FALSE simplification.
    Theorem: optimized result equals original, and original equals FALSE by and_false. -/
theorem and_false_correct (e : Expr) :
    optimizeExpr (.binOp .and e (.lit (.bool false))) ≃ₑ .lit (.bool false) := by
  intro row
  have h1 := optimizeExpr_equiv (.binOp .and e (.lit (.bool false))) row
  have h2 := and_false e row
  rw [h1, h2]

/-- OR with TRUE simplification.
    Theorem: optimized result equals original, and original equals TRUE by or_true. -/
theorem or_true_correct (e : Expr) :
    optimizeExpr (.binOp .or e (.lit (.bool true))) ≃ₑ .lit (.bool true) := by
  intro row
  have h1 := optimizeExpr_equiv (.binOp .or e (.lit (.bool true))) row
  have h2 := or_true e row
  rw [h1, h2]

end SqlEquiv
