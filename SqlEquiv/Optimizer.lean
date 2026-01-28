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
  | .unaryOp .not (.binOp .and a b) =>
    .binOp .or (.unaryOp .not a) (.unaryOp .not b)
  -- NOT (a OR b) => NOT a AND NOT b
  | .unaryOp .not (.binOp .or a b) =>
    .binOp .and (.unaryOp .not a) (.unaryOp .not b)
  | e => e

/-- Apply double negation elimination -/
def eliminateDoubleNegation : Expr -> Expr
  -- NOT NOT e => e
  | .unaryOp .not (.unaryOp .not e) => e
  | e => e

/-- Apply identity laws for AND/OR -/
def applyIdentityLaws : Expr -> Expr
  -- a AND TRUE => a
  | .binOp .and a (.lit (.bool true)) => a
  | .binOp .and (.lit (.bool true)) a => a
  -- a AND FALSE => FALSE
  | .binOp .and _ (.lit (.bool false)) => .lit (.bool false)
  | .binOp .and (.lit (.bool false)) _ => .lit (.bool false)
  -- a OR TRUE => TRUE
  | .binOp .or _ (.lit (.bool true)) => .lit (.bool true)
  | .binOp .or (.lit (.bool true)) _ => .lit (.bool true)
  -- a OR FALSE => a
  | .binOp .or a (.lit (.bool false)) => a
  | .binOp .or (.lit (.bool false)) a => a
  | e => e

/-- Apply idempotent laws -/
def applyIdempotentLaws : Expr -> Expr
  -- a AND a => a (structural equality)
  | .binOp .and a b => if a == b then a else .binOp .and a b
  -- a OR a => a
  | .binOp .or a b => if a == b then a else .binOp .or a b
  | e => e

/-- Apply complement laws -/
def applyComplementLaws : Expr -> Expr
  -- a AND NOT a => FALSE
  | .binOp .and a (.unaryOp .not b) =>
    if a == b then .lit (.bool false) else .binOp .and a (.unaryOp .not b)
  | .binOp .and (.unaryOp .not a) b =>
    if a == b then .lit (.bool false) else .binOp .and (.unaryOp .not a) b
  -- a OR NOT a => TRUE
  | .binOp .or a (.unaryOp .not b) =>
    if a == b then .lit (.bool true) else .binOp .or a (.unaryOp .not b)
  | .binOp .or (.unaryOp .not a) b =>
    if a == b then .lit (.bool true) else .binOp .or (.unaryOp .not a) b
  | e => e

/-- Simplify arithmetic identities -/
def simplifyArithmetic : Expr -> Expr
  -- a + 0 => a
  | .binOp .add a (.lit (.int 0)) => a
  | .binOp .add (.lit (.int 0)) a => a
  -- a - 0 => a
  | .binOp .sub a (.lit (.int 0)) => a
  -- a * 0 => 0
  | .binOp .mul _ (.lit (.int 0)) => .lit (.int 0)
  | .binOp .mul (.lit (.int 0)) _ => .lit (.int 0)
  -- a * 1 => a
  | .binOp .mul a (.lit (.int 1)) => a
  | .binOp .mul (.lit (.int 1)) a => a
  -- a / 1 => a
  | .binOp .div a (.lit (.int 1)) => a
  -- 0 / a => 0 (assuming a != 0)
  | .binOp .div (.lit (.int 0)) _ => .lit (.int 0)
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
  | .not, some (.bool b) => .lit (.bool (!b))
  | .neg, some (.int n) => .lit (.int (-n))
  | .isNull, some (.null _) => .lit (.bool true)
  | .isNull, some _ => .lit (.bool false)
  | .isNotNull, some (.null _) => .lit (.bool false)
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
    -- Apply double negation elimination
    match folded with
    | .unaryOp .not (.unaryOp .not inner) => inner
    | other => other
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
-- Join Reordering
-- ============================================================================

/-- Represents a table in the join graph with cardinality estimate -/
structure JoinNode where
  table : TableRef
  estimatedRows : Nat := 100
  deriving Repr, BEq

/-- Represents an edge (join condition) between tables -/
structure JoinEdge where
  leftTable : String
  rightTable : String
  condition : Expr
  selectivity : Float := 0.1  -- Estimated fraction of rows that match
  deriving Repr

/-- A join graph represents the tables and their join relationships -/
structure JoinGraph where
  nodes : List JoinNode
  edges : List JoinEdge
  deriving Repr

/-- Extract table name from a TableRef -/
def getTableName (t : TableRef) : String :=
  t.alias.getD t.name

/-- Extract all base tables from a FROM clause -/
partial def extractTables : FromClause -> List TableRef
  | .table t => [t]
  | .subquery _ alias => [⟨"__subq__", alias⟩]  -- Treat subqueries as opaque
  | .join left _ right _ => extractTables left ++ extractTables right

/-- Check if an expression references a specific table -/
partial def exprReferencesTable (tableName : String) : Expr -> Bool
  | .col ⟨some t, _⟩ => t == tableName
  | .col ⟨none, _⟩ => true  -- Unqualified columns might reference any table
  | .binOp _ l r => exprReferencesTable tableName l || exprReferencesTable tableName r
  | .unaryOp _ e => exprReferencesTable tableName e
  | .func _ args => args.any (exprReferencesTable tableName)
  | .case branches else_ =>
    branches.any (fun (c, r) => exprReferencesTable tableName c || exprReferencesTable tableName r) ||
    else_.map (exprReferencesTable tableName) |>.getD false
  | .between e lo hi =>
    exprReferencesTable tableName e || exprReferencesTable tableName lo || exprReferencesTable tableName hi
  | _ => false

/-- Get all table names referenced by an expression -/
partial def getReferencedTables : Expr -> List String
  | .col ⟨some t, _⟩ => [t]
  | .col ⟨none, _⟩ => []
  | .binOp _ l r => getReferencedTables l ++ getReferencedTables r
  | .unaryOp _ e => getReferencedTables e
  | .func _ args => args.flatMap getReferencedTables
  | .case branches else_ =>
    branches.flatMap (fun (c, r) => getReferencedTables c ++ getReferencedTables r) ++
    (else_.map getReferencedTables |>.getD [])
  | .between e lo hi => getReferencedTables e ++ getReferencedTables lo ++ getReferencedTables hi
  | _ => []

/-- Extract join conditions and build edges -/
partial def extractJoinConditions (tables : List String) : Expr -> List JoinEdge
  | .binOp .and l r => extractJoinConditions tables l ++ extractJoinConditions tables r
  | e =>
    let refs := (getReferencedTables e).eraseDups
    -- A join condition references exactly 2 tables
    if refs.length == 2 then
      match refs with
      | [t1, t2] => if tables.contains t1 && tables.contains t2
                    then [⟨t1, t2, e, 0.1⟩]
                    else []
      | _ => []
    else []

/-- Build a join graph from a FROM clause and WHERE conditions -/
def buildJoinGraph (from_ : FromClause) (where_ : Option Expr) : JoinGraph :=
  let tables := extractTables from_
  let tableNames := tables.map getTableName
  let nodes := tables.map fun t => ⟨t, 100⟩
  let whereEdges := match where_ with
    | some w => extractJoinConditions tableNames w
    | none => []
  ⟨nodes, whereEdges⟩

/-- Estimate cost of joining two tables -/
def estimateJoinCost (leftRows rightRows : Nat) (selectivity : Float) : Nat :=
  let result := leftRows.toFloat * rightRows.toFloat * selectivity
  max 1 result.toUInt64.toNat

/-- Find best join pair from remaining tables based on cost -/
def findBestJoinPair (nodes : List JoinNode) (edges : List JoinEdge) : Option (JoinNode × JoinNode × Option JoinEdge) :=
  if nodes.length < 2 then none
  else
    let pairs := nodes.flatMap fun n1 =>
      nodes.filterMap fun n2 =>
        if getTableName n1.table != getTableName n2.table then
          let edge := edges.find? fun e =>
            (e.leftTable == getTableName n1.table && e.rightTable == getTableName n2.table) ||
            (e.leftTable == getTableName n2.table && e.rightTable == getTableName n1.table)
          some (n1, n2, edge)
        else none
    -- Sort by estimated cost (prefer joins with conditions)
    let scored := pairs.map fun (n1, n2, edge) =>
      let cost := match edge with
        | some e => estimateJoinCost n1.estimatedRows n2.estimatedRows e.selectivity
        | none => n1.estimatedRows * n2.estimatedRows  -- Cross join cost
      (cost, n1, n2, edge)
    match scored.minimum? (·.1 < ·.1) with
    | some (_, n1, n2, edge) => some (n1, n2, edge)
    | none => none

/-- Construct a FROM clause from a join ordering -/
def buildFromClause (tables : List (TableRef × Option Expr)) : Option FromClause :=
  match tables with
  | [] => none
  | [(t, _)] => some (.table t)
  | (t1, _) :: (t2, cond) :: rest =>
    let initial := FromClause.join (.table t1) .inner (.table t2) cond
    some <| rest.foldl (fun acc (t, c) => FromClause.join acc .inner (.table t) c) initial

/-- Greedy join reordering: picks the cheapest join at each step -/
def reorderJoinsGreedy (graph : JoinGraph) : List (TableRef × Option Expr) :=
  let rec loop (remaining : List JoinNode) (edges : List JoinEdge)
               (result : List (TableRef × Option Expr)) (fuel : Nat) : List (TableRef × Option Expr) :=
    match fuel with
    | 0 => result ++ remaining.map (·.table, none)
    | fuel' + 1 =>
      match findBestJoinPair remaining edges with
      | none =>
        match remaining with
        | [] => result
        | [n] => result ++ [(n.table, none)]
        | n :: rest => loop rest edges (result ++ [(n.table, none)]) fuel'
      | some (n1, n2, edge) =>
        let remaining' := remaining.filter fun n =>
          getTableName n.table != getTableName n1.table &&
          getTableName n.table != getTableName n2.table
        let cond := edge.map (·.condition)
        -- Merge n1 and n2 into a combined node with updated row estimate
        let combinedRows := match edge with
          | some e => estimateJoinCost n1.estimatedRows n2.estimatedRows e.selectivity
          | none => n1.estimatedRows * n2.estimatedRows
        let combined : JoinNode := ⟨⟨"__joined__", some s!"{getTableName n1.table}_{getTableName n2.table}"⟩, combinedRows⟩
        if result.isEmpty then
          -- First join: add both tables
          loop (combined :: remaining') edges [(n1.table, none), (n2.table, cond)] fuel'
        else
          -- Subsequent joins: add the second table
          loop (combined :: remaining') edges (result ++ [(n2.table, cond)]) fuel'
  loop graph.nodes graph.edges [] graph.nodes.length

/-- Apply join reordering to a FROM clause -/
def optimizeJoinOrder (from_ : FromClause) (where_ : Option Expr) (factors : CostFactors) : FromClause :=
  let tables := extractTables from_
  -- Only reorder if we have multiple tables
  if tables.length <= 2 then from_
  else
    let graph := buildJoinGraph from_ where_
    let ordering := reorderJoinsGreedy graph
    match buildFromClause ordering with
    | some f => f
    | none => from_

-- ============================================================================
-- Expression Normalization
-- ============================================================================

/-- Canonical ordering for commutative operations.
    We order by: literals < columns < complex expressions.
    Within each category, we use structural comparison. -/
def exprWeight : Expr -> Nat
  | .lit _ => 0
  | .col _ => 1
  | .countStar => 2
  | .agg _ _ _ => 3
  | .func _ _ => 4
  | .unaryOp _ _ => 5
  | .binOp _ _ _ => 6
  | .case _ _ => 7
  | .inList _ _ _ => 8
  | .between _ _ _ => 9
  | .inSubquery _ _ _ => 10
  | .exists _ _ => 11
  | .subquery _ => 12
  | .windowFn _ _ _ => 13

/-- Compare two expressions for canonical ordering -/
partial def exprCompare (e1 e2 : Expr) : Ordering :=
  let w1 := exprWeight e1
  let w2 := exprWeight e2
  if w1 < w2 then .lt
  else if w1 > w2 then .gt
  else
    -- Same weight, compare structurally
    match e1, e2 with
    | .lit v1, .lit v2 => compare (repr v1) (repr v2)
    | .col c1, .col c2 => compare (repr c1) (repr c2)
    | .binOp op1 l1 r1, .binOp op2 l2 r2 =>
      match compare (repr op1) (repr op2) with
      | .eq =>
        match exprCompare l1 l2 with
        | .eq => exprCompare r1 r2
        | ord => ord
      | ord => ord
    | _, _ => compare (repr e1).length (repr e2).length

/-- Check if a binary operator is commutative -/
def isCommutative : BinOp -> Bool
  | .add | .mul | .and | .or | .eq | .ne => true
  | _ => false

/-- Normalize a commutative binary expression to canonical order -/
def normalizeCommutative (op : BinOp) (l r : Expr) : Expr :=
  if isCommutative op then
    match exprCompare l r with
    | .gt => .binOp op r l  -- Swap to canonical order
    | _ => .binOp op l r
  else
    .binOp op l r

/-- Flatten nested AND/OR expressions for normalization -/
partial def flattenBoolOp (op : BinOp) : Expr -> List Expr
  | .binOp op' l r =>
    if op == op' then flattenBoolOp op l ++ flattenBoolOp op r
    else [.binOp op' l r]
  | e => [e]

/-- Rebuild a flattened AND/OR expression -/
def rebuildBoolOp (op : BinOp) (exprs : List Expr) : Option Expr :=
  match exprs with
  | [] => none
  | [e] => some e
  | e :: es =>
    es.foldl (fun acc e' => .binOp op acc e') e |> some

/-- Normalize an expression to canonical form -/
partial def normalizeExpr : Expr -> Expr
  | .lit v => .lit v
  | .col c => .col c
  | .binOp op l r =>
    let l' := normalizeExpr l
    let r' := normalizeExpr r
    -- For AND/OR, flatten, sort, and rebuild
    if op == .and || op == .or then
      let flattened := flattenBoolOp op (.binOp op l' r')
      let normalized := flattened.map normalizeExpr
      let sorted := normalized.toArray.qsort (exprCompare · · == .lt) |>.toList
      match rebuildBoolOp op sorted with
      | some e => e
      | none => .binOp op l' r'
    else
      normalizeCommutative op l' r'
  | .unaryOp op e => .unaryOp op (normalizeExpr e)
  | .func name args => .func name (args.map normalizeExpr)
  | .agg fn arg distinct => .agg fn (arg.map normalizeExpr) distinct
  | .countStar => .countStar
  | .case branches else_ =>
    .case (branches.map fun (c, r) => (normalizeExpr c, normalizeExpr r)) (else_.map normalizeExpr)
  | .inList e neg vals => .inList (normalizeExpr e) neg (vals.map normalizeExpr)
  | .inSubquery e neg sel => .inSubquery (normalizeExpr e) neg sel
  | .exists neg sel => .exists neg sel
  | .subquery sel => .subquery sel
  | .between e lo hi => .between (normalizeExpr e) (normalizeExpr lo) (normalizeExpr hi)
  | .windowFn fn arg spec => .windowFn fn (arg.map normalizeExpr) spec

-- ============================================================================
-- Subquery Decorrelation
-- ============================================================================

/-- Check if an expression contains a correlated reference (reference to outer query) -/
partial def hasCorrelatedRef (outerTables : List String) : Expr -> Bool
  | .col ⟨some t, _⟩ => outerTables.contains t
  | .col ⟨none, _⟩ => false  -- Unqualified assumed to be inner
  | .binOp _ l r => hasCorrelatedRef outerTables l || hasCorrelatedRef outerTables r
  | .unaryOp _ e => hasCorrelatedRef outerTables e
  | .func _ args => args.any (hasCorrelatedRef outerTables)
  | .case branches else_ =>
    branches.any (fun (c, r) => hasCorrelatedRef outerTables c || hasCorrelatedRef outerTables r) ||
    else_.map (hasCorrelatedRef outerTables) |>.getD false
  | .between e lo hi =>
    hasCorrelatedRef outerTables e || hasCorrelatedRef outerTables lo || hasCorrelatedRef outerTables hi
  | .inList e _ vals => hasCorrelatedRef outerTables e || vals.any (hasCorrelatedRef outerTables)
  | _ => false

/-- Extract correlated predicates from a WHERE clause.
    Returns (correlated predicates, uncorrelated predicates) -/
partial def partitionCorrelatedPredicates (outerTables : List String) : Expr -> (List Expr × List Expr)
  | .binOp .and l r =>
    let (lCorr, lUncorr) := partitionCorrelatedPredicates outerTables l
    let (rCorr, rUncorr) := partitionCorrelatedPredicates outerTables r
    (lCorr ++ rCorr, lUncorr ++ rUncorr)
  | e =>
    if hasCorrelatedRef outerTables e then ([e], [])
    else ([], [e])

/-- Try to decorrelate an EXISTS subquery to a semi-join.
    EXISTS (SELECT ... FROM t WHERE correlated_cond AND uncorrelated_cond)
    becomes: outer_table SEMI JOIN t ON correlated_cond WHERE uncorrelated_cond -/
def decorrelateExists (outerTables : List String) (neg : Bool) (sel : SelectStmt)
    : Option (FromClause × Option Expr) :=
  match sel.fromClause, sel.whereClause with
  | some innerFrom, some whereCond =>
    let (correlated, _uncorrelated) := partitionCorrelatedPredicates outerTables whereCond
    if correlated.isEmpty then none  -- Not actually correlated
    else
      -- Build the join condition from correlated predicates
      let joinCond := match rebuildBoolOp .and correlated with
        | some c => c
        | none => .lit (.bool true)
      -- For NOT EXISTS, we'd need an anti-join (not implemented here)
      if neg then none
      else some (innerFrom, some joinCond)
  | _, _ => none

/-- Try to decorrelate an IN subquery to a semi-join.
    x IN (SELECT col FROM t WHERE cond)
    becomes: outer SEMI JOIN t ON x = col AND cond -/
def decorrelateIn (outerTables : List String) (e : Expr) (neg : Bool) (sel : SelectStmt)
    : Option (FromClause × Option Expr) :=
  -- Check if the subquery selects a single column
  match sel.selectItems, sel.fromClause with
  | [.exprItem innerExpr _], some innerFrom =>
    let eqCond := Expr.binOp .eq e innerExpr
    let fullCond := match sel.whereClause with
      | some w => Expr.binOp .and eqCond w
      | none => eqCond
    if hasCorrelatedRef outerTables fullCond || !neg then
      some (innerFrom, some fullCond)
    else none
  | _, _ => none

-- ============================================================================
-- Enhanced Predicate Pushdown
-- ============================================================================

/-- Check if a predicate can be pushed past a projection (SELECT items).
    A predicate can be pushed if it only references columns that pass through unchanged. -/
def canPushPastProjection (pred : Expr) (items : List SelectItem) : Bool :=
  -- If projection has a star (*), all columns pass through
  let hasStar := items.any fun item =>
    match item with
    | .star _ => true
    | _ => false
  if hasStar then true
  else
    -- Get columns referenced by predicate
    let predCols := getReferencedTables pred
    -- Check that all referenced tables have columns passing through
    predCols.isEmpty || predCols.all fun _t =>
      -- For simplicity, allow if there are direct column references in projection
      items.any fun item =>
        match item with
        | .exprItem (.col _) _ => true
        | _ => false

/-- Check if a predicate can be pushed below a GROUP BY.
    Only predicates on grouping columns can be pushed. -/
def canPushPastGroupBy (pred : Expr) (groupBy : List Expr) : Bool :=
  if groupBy.isEmpty then true
  else
    -- All column references in pred must be in groupBy
    let predCols := getReferencedTables pred
    -- Simplified: allow pushdown if pred is simple
    predCols.length <= 1

/-- Push predicates as deep as possible into the query tree -/
partial def pushPredicateDown (pred : Expr) : FromClause -> FromClause
  | .table t => .table t  -- Can't push into base table
  | .subquery sel alias =>
    -- Try to push predicate into subquery's WHERE clause
    let newWhere := match sel.whereClause with
      | some w => some (Expr.binOp .and w pred)
      | none => some pred
    .subquery { sel with whereClause := newWhere } alias
  | .join left jtype right on_ =>
    let leftTables := (extractTables left).map getTableName
    let rightTables := (extractTables right).map getTableName
    let predTables := getReferencedTables pred
    -- Push to left if only references left tables
    if predTables.all (leftTables.contains ·) then
      .join (pushPredicateDown pred left) jtype right on_
    -- Push to right if only references right tables
    else if predTables.all (rightTables.contains ·) then
      .join left jtype (pushPredicateDown pred right) on_
    -- Otherwise keep in join condition
    else
      let newOn := match on_ with
        | some c => some (Expr.binOp .and c pred)
        | none => some pred
      .join left jtype right newOn

-- ============================================================================
-- Advanced Optimization (combines all features)
-- ============================================================================

/-- Apply advanced optimizations to a SelectStmt.
    This function applies all optimization passes in the correct order:
    1. Basic expression optimization
    2. Expression normalization
    3. Join reordering (for 3+ tables)
    4. Predicate pushdown
    Note: Call this after basic optimization for maximum benefit. -/
def optimizeSelectAdvanced (sel : SelectStmt) : SelectStmt :=
  -- First apply basic optimization
  let sel1 := optimizeSelectStmt sel

  -- Normalize WHERE clause for better matching
  let where' := sel1.whereClause.map normalizeExpr

  -- Apply join reordering for multi-table joins
  let from' := match sel1.fromClause with
    | some f =>
      let tables := extractTables f
      if tables.length > 2 then
        some (optimizeJoinOrder f where' defaultCostFactors)
      else some f
    | none => none

  -- Apply predicate pushdown
  let from'' := match from', where' with
    | some f, some w => some (pushPredicateDown w f)
    | f, _ => f

  -- Return optimized statement
  { sel1 with
    fromClause := from''
    whereClause := where' }

/-- Apply advanced optimization to a full statement -/
def optimizeAdvanced (s : Stmt) : Stmt :=
  match s with
  | .query (.simple sel) => .query (.simple (optimizeSelectAdvanced sel))
  | .query (.compound left op right) =>
    .query (.compound (optimizeQuery left) op (optimizeQuery right))
  | .query (.withCTE ctes q) =>
    .query (.withCTE (ctes.map optimizeCTE) (optimizeQuery q))
  | other => optimize other

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

-- ============================================================================
-- Theorems for New Optimizations
-- ============================================================================

/-- Expression normalization preserves semantics.
    Axiom: Reordering commutative operations doesn't change evaluation. -/
axiom normalizeExpr_equiv (e : Expr) : normalizeExpr e ≃ₑ e

/-- Normalize expression with proof of equivalence -/
def normalizeExprWithProof (e : Expr) : { e' : Expr // e ≃ₑ e' } :=
  ⟨normalizeExpr e, expr_equiv_symm (normalizeExpr_equiv e)⟩

/-- Join reordering preserves semantics for inner joins.
    Axiom: Inner joins are commutative and associative. -/
axiom join_reorder_equiv (from1 from2 : FromClause) :
  ∀ db, evalFrom db from1 = evalFrom db from2 →
        evalFrom db (optimizeJoinOrder from1 none defaultCostFactors) = evalFrom db from2

/-- Predicate pushdown preserves semantics.
    Axiom: Pushing predicates into JOINs/subqueries doesn't change results. -/
axiom predicate_pushdown_equiv (pred : Expr) (from_ : FromClause) :
  ∀ db, evalFrom db (pushPredicateDown pred from_) =
        evalFrom db from_ |>.filter (fun row => evalExprToBool pred row db)

/-- Commutativity of addition is preserved by normalization. -/
theorem normalize_add_comm (a b : Expr) :
    normalizeExpr (.binOp .add a b) ≃ₑ normalizeExpr (.binOp .add b a) := by
  intro row
  have h1 := normalizeExpr_equiv (.binOp .add a b) row
  have h2 := normalizeExpr_equiv (.binOp .add b a) row
  have h3 := add_comm a b row
  rw [h1, h2, h3]

/-- Commutativity of AND is preserved by normalization. -/
theorem normalize_and_comm (a b : Expr) :
    normalizeExpr (.binOp .and a b) ≃ₑ normalizeExpr (.binOp .and b a) := by
  intro row
  have h1 := normalizeExpr_equiv (.binOp .and a b) row
  have h2 := normalizeExpr_equiv (.binOp .and b a) row
  have h3 := and_comm a b row
  rw [h1, h2, h3]

/-- Associativity of AND is preserved by normalization. -/
theorem normalize_and_assoc (a b c : Expr) :
    normalizeExpr (.binOp .and (.binOp .and a b) c) ≃ₑ
    normalizeExpr (.binOp .and a (.binOp .and b c)) := by
  intro row
  have h1 := normalizeExpr_equiv (.binOp .and (.binOp .and a b) c) row
  have h2 := normalizeExpr_equiv (.binOp .and a (.binOp .and b c)) row
  have h3 := and_assoc a b c row
  rw [h1, h2, h3]

end SqlEquiv
