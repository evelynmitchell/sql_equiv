/-
  Coverage of the elaborator-correctness theorem (#352).

  `SqlBridge/CorrectJoin.lean` proves `elabStmt_correct_join` (and `SqlBridge/CorrectAgg.lean`
  `elabStmt_correct_agg`, for aggregates without `GROUP BY`) for a fragment of SQL:
  `SELECT e₁, …, eₖ FROM f [WHERE p] [ORDER BY c₁, …] [LIMIT n] [OFFSET m]` where `f` nests
  tables (optionally aliased) under inner joins and cross joins without `ON`, every expression
  (`ON` included) is a literal, a column, a comparison, `AND`, `OR` or `NOT`, every `ORDER BY`
  key is a column reference, and, when there is an `ORDER BY`, every item is a column or has an
  alias (`itemsNamed`); or `SELECT agg₁, …, aggₖ FROM f [WHERE p]` with `COUNT(*)`,
  `COUNT([DISTINCT] e)`, `SUM(e)`, `MIN(e)`, `MAX(e)` (`AVG` is its own feature, pending the
  decision on its rounding, registry row 7); or the same grouped by columns, `GROUP BY c₁, …`,
  each item a key column or such an aggregate, with an optional `HAVING` of key columns, such
  aggregates, literals, comparisons, `AND`, `OR`, `NOT`, ordered by such aggregates with an
  optional `LIMIT`/`OFFSET`, no output name able to capture `SqlEquiv`'s sort-key columns, and
  item columns that are not grouped (bare columns, registry T9) when no `MIN`/`MAX` is written
  (`SqlBridge/CorrectGrouped.lean`, `elabStmt_correct_grouped`). `outsideFragment stmt` lists the features that put a parsed
  statement outside that fragment, named after the roadmap steps in `docs/TYPED_CORE_PLAN.md`
  ("Elaborator correctness roadmap"). An empty list means the statement has the fragment's
  shape; `SqlCoreTest/CorrectExamples.lean` checks that this agrees with the theorem's own
  `isFragment`/`itemsFragment`/`fromFragment`/`joinStmt`/`itemsNamed`/`aggItems`/`aggStmt`/
  `groupedItems`/`groupedStmt`/`havingFragment`.

  `lake exe spider_elab` prints these features for every Spider query that elaborates, and
  `tools/spider_elab_baseline.py` turns them into the coverage table of
  `benchmarks/spider/elab_report.md`: queries in the fragment today, and after each step.

  Shape only: the theorem also assumes the schema's fold keeps names equal ignoring case (Spider's
  `String.toLower` does, #351), that the untyped database answers every such spelling of a table
  name alike (`DbRel`), and that no comparison or `ORDER BY` key orders booleans
  (`QNoBoolOrder`). With bare columns, the dialect must take bare columns (Spider's schemas use
  the sqlite dialect). The fold must also identify exactly the names equal ignoring case
  (`hfoldCI`), and the schema's column names must be their own folds (`hfix`): Spider's
  lowercased names under `String.toLower` satisfy both.
-/
import SqlEquiv

namespace SqlBridge.Coverage

open SqlEquiv

/-- Feature names, one per roadmap step or remaining gap. -/
def orderKey := "ORDER BY expression"
def unnamedItem := "unnamed item with ORDER BY"
def orderCompound := "ORDER BY/LIMIT on a set operation"
def join := "outer join"
def aggregate := "aggregate/GROUP BY"
def avg := "AVG"
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

/-- Mirrors `SqlBridge.CorrectOrder.itemsNamed` (checked in `SqlCoreTest/CorrectExamples.lean`):
    every item is a column without an alias or has an alias, and the output names have no dot, so
    an `ORDER BY` key resolves to the same output column in both evaluators. -/
def itemsNamed : List SelectItem → Bool
  | [] => true
  | .exprItem (.col c) none :: rest => !c.column.contains '.' && itemsNamed rest
  | .exprItem _ (some a) :: rest => !a.contains '.' && itemsNamed rest
  | _ :: _ => false

/-- Mirrors `SqlBridge.CorrectAgg.aggFragment`'s shape (its argument's features are reported
    separately): `COUNT(*)`, `COUNT([DISTINCT] e)`, and `SUM`, `MIN`, `MAX` without `DISTINCT`. -/
def aggCallOk : Expr → Bool
  | .countStar => true
  | .agg .count (some _) _ => true
  | .agg (.sum _) (some _) false => true
  | .agg (.min _) (some _) false => true
  | .agg (.max _) (some _) false => true
  | _ => false

/-- Mirrors `SqlBridge.CorrectGroup.havingFragment`'s shape (aggregate arguments are checked
    separately): literals, key columns, aggregates, comparisons, `AND`, `OR`, `NOT`. -/
def havingOk (groupBy : List Expr) : Expr → Bool
  | .lit _ => true
  | .col c => groupBy.contains (.col c)
  | .binOp op x y =>
    (match op with
     | .eq | .ne | .lt | .le | .gt | .ge | .and | .or => true
     | _ => false) && havingOk groupBy x && havingOk groupBy y
  | .unaryOp .not x => havingOk groupBy x
  | e => aggCallOk e

mutual

/-- Features of a `HAVING` predicate in the fragment: those of its aggregates' arguments. -/
partial def havingFeatures : Expr → List String
  | .binOp _ x y => havingFeatures x ++ havingFeatures y
  | .unaryOp _ x => havingFeatures x
  | .agg _ (some a) _ => exprFeatures a
  | _ => []

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
  | .agg fn a _ =>
    (match fn with | .avg _ => [avg] | _ => []) ++ aggregate :: (a.map exprFeatures).getD []
  | .countStar => [aggregate]
  | .case bs e => caseExpr :: (bs.flatMap fun (c, r) => exprFeatures c ++ exprFeatures r) ++
      (e.map exprFeatures).getD []
  | .inList e _ vs => inBetween :: exprFeatures e ++ vs.flatMap exprFeatures
  | .between e lo hi => inBetween :: exprFeatures e ++ exprFeatures lo ++ exprFeatures hi
  | .inSubquery e _ _ => subquery :: exprFeatures e
  | .exists _ _ | .subquery _ => [subquery]
  | .windowFn _ _ _ => [window]

/-- Features of a FROM clause outside the fragment (tables, optionally aliased, under inner joins
    and cross joins without `ON`; mirrors `SqlBridge.CorrectJoin.fromFragment`). -/
partial def fromFeatures : FromClause → List String
  | .table _ => []
  | .subquery _ _ => [subquery]
  | .join l kind r on_ =>
    (match kind, on_ with
     | .inner, _ | .cross, none => []
     | _, _ => [join]) ++
    fromFeatures l ++ fromFeatures r ++ (on_.map exprFeatures).getD []

/-- Features of a SELECT outside the fragment. A SELECT of aggregates only, without `GROUP BY`,
    `HAVING`, `ORDER BY`, `LIMIT` or `OFFSET`, is in the fragment of
    `SqlBridge.CorrectAgg.elabStmt_correct_agg` (roadmap step 3a) when its arguments are. -/
partial def selectFeatures (s : SelectStmt) : List String :=
  let plainAgg := !s.distinct && s.groupBy.isEmpty && s.having.isNone && s.orderBy.isEmpty &&
    s.limitVal.isNone && s.offsetVal.isNone && !s.items.isEmpty &&
    s.items.all fun | .exprItem e _ => aggCallOk e | .star _ => false
  -- grouped (roadmap steps 3b-1 to 3b-4, mirrors `elabStmt_correct_grouped`): `GROUP BY` columns,
  -- items aggregates or columns, an optional `HAVING`, `ORDER BY` aggregates, `LIMIT`/`OFFSET`.
  -- With sort keys, no output name may capture `SqlEquiv`'s sort-key columns `__group_orderkey_k`
  -- (hypothesis `hnm`); a bare column (one not grouped) only without any `MIN`/`MAX` (`BareFirst`).
  let orderOk := s.orderBy.all (fun o => aggCallOk o.expr) &&
    (s.orderBy.isEmpty || s.items.all fun
      | .exprItem e al =>
        let nm := (al.getD (exprToName e)).toLower
        !nm.contains '.' && !nm.startsWith "__group_orderkey_"
      | .star _ => false)
  let bareOk := s.items.all (fun
      | .exprItem (.col c) _ => s.groupBy.contains (.col c)
      | _ => true) ||
    (s.items.all (fun | .exprItem e _ => (minMaxCalls e).isEmpty | .star _ => true) &&
      s.having.all (fun h => (minMaxCalls h).isEmpty) &&
      s.orderBy.all (fun o => (minMaxCalls o.expr).isEmpty))
  let plainGroup := !s.distinct && !s.groupBy.isEmpty && s.having.all (havingOk s.groupBy) &&
    orderOk && bareOk &&
    s.groupBy.all (fun | .col _ => true | _ => false) &&
    s.items.all fun
      | .exprItem e _ => aggCallOk e || (match e with | .col _ => true | _ => false)
      | .star _ => false
  (if s.distinct then [distinct] else []) ++
  (if plainAgg || plainGroup then
    s.items.flatMap fun
      | .exprItem (.agg _ (some a) _) _ => exprFeatures a
      | _ => []
  else s.items.flatMap fun
    | .star _ => [star]
    | .exprItem e _ => exprFeatures e) ++
  (match s.fromClause with
   | none => [noFrom]
   | some f => fromFeatures f) ++
  ((s.whereClause.map exprFeatures).getD []) ++
  (if (s.groupBy.isEmpty && s.having.isNone) || plainGroup then [] else [aggregate]) ++
  (s.groupBy.flatMap exprFeatures) ++
  ((s.having.map (if plainGroup then havingFeatures else exprFeatures)).getD []) ++
  (if plainGroup || s.orderBy.all (fun o => match o.expr with | .col _ => true | _ => false) then []
   else [orderKey]) ++
  (if s.orderBy.isEmpty || plainGroup || itemsNamed s.items then [] else [unnamedItem]) ++
  (s.orderBy.flatMap fun o =>
    if plainGroup then (match o.expr with | .agg _ (some a) _ => exprFeatures a | _ => [])
    else exprFeatures o.expr)

/-- Features of a query outside the fragment. -/
partial def queryFeatures : Query → List String
  | .simple s => selectFeatures s
  | .compound l _ r => subquery :: queryFeatures l ++ queryFeatures r
  | .withCTE _ q => subquery :: queryFeatures q
  | .ordered q _ _ _ => orderCompound :: queryFeatures q

end

/-- The distinct features that put a statement outside the theorem's fragment, sorted;
    `[]` when it has the fragment's shape. -/
def outsideFragment : Stmt → List String
  | .query q => (queryFeatures q).eraseDups.mergeSort (· ≤ ·)
  | _ => ["not a query"]

end SqlBridge.Coverage
