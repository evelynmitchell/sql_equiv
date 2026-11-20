/-
  Coverage of the elaborator-correctness theorem (#352).

  `SqlBridge/Correct.lean` proves `elabStmt_correct` for a fragment of SQL:
  `SELECT e₁, …, eₖ FROM t [AS a] [WHERE p]` where every expression is a literal, a column, a
  comparison, `AND`, `OR` or `NOT`. `outsideFragment stmt` lists the features that put a parsed
  statement outside that fragment, named after the roadmap steps in `docs/TYPED_CORE_PLAN.md`
  ("Elaborator correctness roadmap"). An empty list means the statement has the fragment's
  shape; `SqlCoreTest/CorrectExamples.lean` checks that this agrees with the theorem's own
  `isFragment`/`itemsFragment`/`fragmentStmt`.

  `lake exe spider_elab` prints these features for every Spider query that elaborates, and
  `tools/spider_elab_baseline.py` turns them into the coverage table of
  `benchmarks/spider/elab_report.md`: queries in the fragment today, and after each step.

  Shape only: the theorem also assumes the schema does not fold names (`fold = id`, dropped by
  #351) and that no comparison orders two booleans (`QNoBoolOrder`).
-/
import SqlEquiv

namespace SqlBridge.Coverage

open SqlEquiv

/-- Feature names, one per roadmap step or remaining gap. -/
def orderLimit := "ORDER BY/LIMIT"
def join := "join"
def aggregate := "aggregate/GROUP BY"
def unaryArith := "IS NULL/negation"
def arithmetic := "arithmetic"
def inBetween := "IN list/BETWEEN"
def distinct := "DISTINCT"
def subquery := "subquery/set operation/CTE"
def like := "LIKE"
def function := "scalar function"
def caseExpr := "CASE"
def star := "*"
def window := "window function"
def concat := "||"
def noFrom := "no FROM"

mutual

/-- Features of an expression outside the fragment (subqueries are not entered). -/
partial def exprFeatures : Expr → List String
  | .lit _ | .col _ => []
  | .binOp op a b =>
    let here := match op with
      | .eq | .ne | .lt | .le | .gt | .ge | .and | .or => []
      | .add | .sub | .mul | .div | .mod => [arithmetic]
      | .like | .likeCI => [like]
      | .concat => [concat]
    here ++ exprFeatures a ++ exprFeatures b
  | .unaryOp .not a => exprFeatures a
  | .unaryOp _ a => unaryArith :: exprFeatures a
  | .func _ args => function :: args.flatMap exprFeatures
  | .agg _ a _ => aggregate :: (a.map exprFeatures).getD []
  | .countStar => [aggregate]
  | .case bs e => caseExpr :: (bs.flatMap fun (c, r) => exprFeatures c ++ exprFeatures r) ++
      (e.map exprFeatures).getD []
  | .inList e _ vs => inBetween :: exprFeatures e ++ vs.flatMap exprFeatures
  | .between e lo hi => inBetween :: exprFeatures e ++ exprFeatures lo ++ exprFeatures hi
  | .inSubquery e _ _ => subquery :: exprFeatures e
  | .exists _ _ | .subquery _ => [subquery]
  | .windowFn _ _ _ => [window]

/-- Features of a FROM clause outside the fragment (one table, optionally aliased). -/
partial def fromFeatures : FromClause → List String
  | .table _ => []
  | .subquery _ _ => [subquery]
  | .join l _ r on_ => join :: fromFeatures l ++ fromFeatures r ++ (on_.map exprFeatures).getD []

/-- Features of a SELECT outside the fragment. -/
partial def selectFeatures (s : SelectStmt) : List String :=
  (if s.distinct then [distinct] else []) ++
  (s.items.flatMap fun
    | .star _ => [star]
    | .exprItem e _ => exprFeatures e) ++
  (match s.fromClause with
   | none => [noFrom]
   | some f => fromFeatures f) ++
  ((s.whereClause.map exprFeatures).getD []) ++
  (if s.groupBy.isEmpty && s.having.isNone then [] else [aggregate]) ++
  (s.groupBy.flatMap exprFeatures) ++ ((s.having.map exprFeatures).getD []) ++
  (if s.orderBy.isEmpty && s.limitVal.isNone && s.offsetVal.isNone then [] else [orderLimit]) ++
  (s.orderBy.flatMap fun o => exprFeatures o.expr)

/-- Features of a query outside the fragment. -/
partial def queryFeatures : Query → List String
  | .simple s => selectFeatures s
  | .compound l _ r => subquery :: queryFeatures l ++ queryFeatures r
  | .withCTE _ q => subquery :: queryFeatures q
  | .ordered q _ _ _ => orderLimit :: queryFeatures q

end

/-- The distinct features that put a statement outside the theorem's fragment, sorted;
    `[]` when it has the fragment's shape. -/
def outsideFragment : Stmt → List String
  | .query q => (queryFeatures q).eraseDups.mergeSort (· ≤ ·)
  | _ => ["not a query"]

end SqlBridge.Coverage
