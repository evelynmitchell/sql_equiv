/-
  Coverage of the elaborator-correctness theorem (#352).

  `SqlBridge/CorrectJoin.lean` proves `elabStmt_correct_join` (and `SqlBridge/CorrectAgg.lean`
  `elabStmt_correct_agg`, for aggregates without `GROUP BY`) for a fragment of SQL:
  `SELECT e₁, …, eₖ FROM f [WHERE p] [ORDER BY c₁, …] [LIMIT n] [OFFSET m]` where `f` nests
  tables (optionally aliased) under inner joins and cross joins without `ON`, every expression
  (`ON` included) is a literal, a column, a comparison, `BETWEEN`, `AND`, `OR` or `NOT`, every `ORDER BY`
  key is a column reference, and, when there is an `ORDER BY`, every item is a column or has an
  alias (`itemsNamed`); or `SELECT agg₁, …, aggₖ FROM f [WHERE p]` with `COUNT(*)`,
  `COUNT([DISTINCT] e)`, `SUM(e)`, `MIN(e)`, `MAX(e)`, and as an item `AVG(e)` (step 3c, up to
  rounding; elsewhere `AVG` is its own feature); or the same grouped by columns, `GROUP BY c₁, …`,
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
def inList := "IN list"
def distinct := "DISTINCT"
def subquery := "subquery/set operation/CTE"
def setOpBranch := "set operation branch with ORDER BY/LIMIT, AVG or a bare column"
def hiddenName := "reference to the hidden column name ?subquery?"

/-- Whether an expression refers to a column named like the column the elaborator attaches for a
    subquery (mirrors `SqlBridge.CorrectSub.noRefTo`, negated; names fold to lowercase). -/
def refsHidden : Expr → Bool
  | .col c => c.column.toLower == "?subquery?"
  | .binOp _ a b => refsHidden a || refsHidden b
  | .unaryOp _ a => refsHidden a
  | .between e lo hi => refsHidden e || refsHidden lo || refsHidden hi
  | _ => false
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

/-- An aggregate item (mirrors `SqlBridge.CorrectGrouped.itemAggFragment`): those of `aggCallOk`,
    or `AVG` without `DISTINCT` (step 3c, items only; related up to rounding). -/
def itemCallOk : Expr → Bool
  | .agg (.avg _) (some _) false => true
  | e => aggCallOk e

/-- `AVG(c) op k` in `HAVING`, the average of a column against an integer literal (mirrors
    `SqlBridge.CorrectGroup.cmpAvgForm`). The theorem relates it under two hypotheses the shape
    cannot see (`SqlBridge.CorrectGrouped.HavingAvgOk`): no column of the schema is a decimal
    (Spider's typing has none) and `FROM` has at most `10¹⁶` rows. The count assumes both. -/
def cmpAvgOk : Expr → Bool
  | .binOp op (.agg (.avg _) (some (.col _)) false) (.lit (.int _)) =>
    match op with
    | .eq | .ne | .lt | .le | .gt | .ge => true
    | _ => false
  | _ => false

/-- Whether a predicate has such a comparison (mirrors `SqlBridge.CorrectGroup.hasCmpAvg`). -/
def hasCmpAvgOk : Expr → Bool
  | .binOp op x y => cmpAvgOk (.binOp op x y) || hasCmpAvgOk x || hasCmpAvgOk y
  | .unaryOp _ x => hasCmpAvgOk x
  | .between x lo hi => hasCmpAvgOk x || hasCmpAvgOk lo || hasCmpAvgOk hi
  | _ => false

/-- Mirrors `SqlBridge.CorrectGroup.havingFragment`'s shape (aggregate arguments are checked
    separately): literals, key columns, aggregates, comparisons, `AND`, `OR`, `NOT`. -/
def havingOk (groupBy : List Expr) : Expr → Bool
  | .lit _ => true
  | .col c => groupBy.contains (.col c)
  | .binOp op x y =>
    cmpAvgOk (.binOp op x y) ||
    ((match op with
     | .eq | .ne | .lt | .le | .gt | .ge | .and | .or => true
     | _ => false) && havingOk groupBy x && havingOk groupBy y)
  | .unaryOp .not x => havingOk groupBy x
  | .between x lo hi => havingOk groupBy x && havingOk groupBy lo && havingOk groupBy hi
  | e => aggCallOk e

/-- A SELECT of aggregates only, without `GROUP BY`, `HAVING`, `ORDER BY`, `LIMIT` or `OFFSET`
    (mirrors the shape of `SqlBridge.CorrectAgg.elabStmt_correct_agg`). -/
def plainAggOf (s : SelectStmt) : Bool :=
  !s.distinct && s.groupBy.isEmpty && s.having.isNone && s.orderBy.isEmpty &&
    s.limitVal.isNone && s.offsetVal.isNone && !s.items.isEmpty &&
    s.items.all fun | .exprItem e _ => aggCallOk e | .star _ => false

/-- `SELECT AVG(e) FROM … [WHERE …]` (mirrors `SqlBridge.CorrectSub.AvgBody`). -/
def avgBodyOf (b : SelectStmt) : Bool :=
  !b.distinct && b.groupBy.isEmpty && b.having.isNone && b.orderBy.isEmpty &&
    b.limitVal.isNone && b.offsetVal.isNone &&
    match b.items with
    | [.exprItem (.agg (.avg _) (some _) false) _] => true
    | _ => false

/-- What a grouped subquery body needs beyond being a grouped statement (mirrors the side
    conditions of `SqlBridge.CorrectSub.BodyOk.grouped`, #409): `GROUP BY`, every item column a
    key, no `AVG` item (related only up to rounding), no `AVG` comparison in `HAVING`. -/
def groupedBodyOf (b : SelectStmt) : Bool :=
  !b.groupBy.isEmpty &&
  b.items.all (fun
    | .exprItem (.col c) _ => b.groupBy.contains (.col c)
    | .exprItem (.agg (.avg _) _ _) _ => false
    | _ => true) &&
  b.having.all (fun h => !hasCmpAvgOk h)

/-- A `WHERE` with one subquery node in a position `SqlBridge.CorrectSub.HoleCtx` allows (the
    node, `a op node` for a comparison, either under `AND`): the other expressions, the
    compared one if any, and the node. -/
def holeSplit : Expr → Option (List Expr × Option Expr × Expr)
  | .binOp .and a b =>
    match holeSplit a with
    | some (xs, c, nd) => some (b :: xs, c, nd)
    | none => (holeSplit b).map fun (xs, c, nd) => (a :: xs, c, nd)
  | .binOp op a nd =>
    match op, nd with
    | .eq, .inSubquery _ _ _ | .ne, .inSubquery _ _ _
    | .lt, .inSubquery _ _ _ | .le, .inSubquery _ _ _
    | .gt, .inSubquery _ _ _ | .ge, .inSubquery _ _ _
    | .eq, .subquery (.simple _) | .ne, .subquery (.simple _) | .lt, .subquery (.simple _)
    | .le, .subquery (.simple _) | .gt, .subquery (.simple _) | .ge, .subquery (.simple _) =>
      some ([a], some a, nd)
    | _, _ => none
  | .inSubquery e neg sq => some ([], none, .inSubquery e neg sq)
  | .subquery (.simple b) => some ([], none, .subquery (.simple b))
  | _ => none

mutual

/-- Features of a `HAVING` predicate in the fragment: those of its aggregates' arguments. -/
partial def havingFeatures : Expr → List String
  | .binOp _ x y => havingFeatures x ++ havingFeatures y
  | .unaryOp _ x => havingFeatures x
  | .between x lo hi => havingFeatures x ++ havingFeatures lo ++ havingFeatures hi
  | .agg _ (some a) _ => exprFeatures a
  | _ => []

/-- Features of an expression outside the fragment (subqueries are not entered). -/
partial def exprFeatures : Expr → List String
  | .lit _ | .col _ => []
  | .binOp op a b =>
    let here := match op with
      | .eq | .ne | .lt | .le | .gt | .ge | .and | .or => []
      | .add | .sub | .mul | .div | .mod => [arithmetic]
      | .like | .likeCI => []
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
  | .inList e _ vs => inList :: exprFeatures e ++ vs.flatMap exprFeatures
  -- `BETWEEN` is in the fragment (roadmap step 4): `e >= lo AND e <= hi` in both evaluators
  | .between e lo hi => exprFeatures e ++ exprFeatures lo ++ exprFeatures hi
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
  let plainAgg := plainAggOf s
  -- grouped (roadmap steps 3b-1 to 3b-6, 3c, mirrors `elabStmt_correct_grouped`): `GROUP BY` columns,
  -- items aggregates or columns, an optional `HAVING`, `ORDER BY` aggregates or key columns,
  -- `LIMIT`/`OFFSET`.
  -- With sort keys, no output name may capture `SqlEquiv`'s sort-key columns `__group_orderkey_k`
  -- (hypothesis `hnm`); a bare column (one not grouped) without any `MIN`/`MAX`, or with exactly one
  -- (`BareOk`).
  -- a sort key: an aggregate, or a `GROUP BY` column no other item's name captures (step 3b-6,
  -- `OrderKeyOk`): every item named like it, in either evaluator, is that column
  let keyColOk : Expr → Bool := fun
    | .col c => s.groupBy.contains (.col c) && s.items.all fun
      | .exprItem e al =>
        !((al.getD (exprToName e)).toLower == c.column.toLower ||
          (al.getD (match e with | .col c' => c'.column | _ => "?column?")).toLower ==
            c.column.toLower) || e == .col c
      | .star _ => true
    | _ => false
  let orderOk := s.orderBy.all (fun o => aggCallOk o.expr || keyColOk o.expr) &&
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
      s.orderBy.all (fun o => (minMaxCalls o.expr).isEmpty)) ||
    -- one `MIN`/`MAX` call in the items and `HAVING` (not DISTINCT; `ORDER BY` adds no other):
    -- bare columns are read on the row where its argument is extreme (`atExtreme`)
    (let ih := (s.items.flatMap (fun | .exprItem e _ => minMaxCalls e | .star _ => []) ++
        (s.having.map minMaxCalls).getD []).eraseDups
     match ih with
     | [(_, m, some _, false)] =>
       m.bareRow && (ih ++ s.orderBy.flatMap (fun o => minMaxCalls o.expr)).eraseDups == ih
     | _ => false)
  -- without `GROUP BY` (step 3b-6, `elabStmt_correct_aggBare`): aggregates and bare columns, at
  -- least one aggregate, no `HAVING`, `ORDER BY`, `LIMIT` or `OFFSET`
  let plainAggBare := !s.distinct && s.groupBy.isEmpty && s.having.isNone && s.orderBy.isEmpty &&
    s.limitVal.isNone && s.offsetVal.isNone && bareOk &&
    s.items.any (fun | .exprItem e _ => itemCallOk e | .star _ => false) &&
    s.items.all fun
      | .exprItem e _ => itemCallOk e || (match e with | .col _ => true | _ => false)
      | .star _ => false
  let plainGroup := !s.distinct && !s.groupBy.isEmpty && s.having.all (havingOk s.groupBy) &&
    orderOk && bareOk &&
    s.groupBy.all (fun | .col _ => true | _ => false) &&
    s.items.all fun
      | .exprItem e _ => itemCallOk e || (match e with | .col _ => true | _ => false)
      | .star _ => false
  -- plain `DISTINCT` (roadmap step 5, `elabStmt_correct_distinct`): no `GROUP BY`, `HAVING`,
  -- `ORDER BY`, `LIMIT` or `OFFSET`; the items' own features (aggregates, `*`) still count. The
  -- rows relate up to their order.
  let plainDistinct := s.distinct && s.groupBy.isEmpty && s.having.isNone && s.orderBy.isEmpty &&
    s.limitVal.isNone && s.offsetVal.isNone
  (if s.distinct && !plainDistinct then [distinct] else []) ++
  (if plainAgg || plainAggBare || plainGroup then
    s.items.flatMap fun
      | .exprItem (.agg _ (some a) _) _ => exprFeatures a
      | _ => []
  else s.items.flatMap fun
    | .star _ => [star]
    | .exprItem e _ => exprFeatures e) ++
  (match s.fromClause with
   | none => [noFrom]
   | some f => fromFeatures f) ++
  -- a `WHERE` with one subquery node (steps 6b and 6c, `SqlBridge.CorrectSub.SubWhere`) on a
  -- plain outer query, under plain `DISTINCT`, or under aggregates without `GROUP BY`
  -- (`elabStmt_correct_inSub`, `_distinct_inSub`, `_agg_inSub`, `_aggBare_inSub`): inside when
  -- the other expressions, the probe of an `IN` and the body are; the body a plain statement,
  -- one of aggregates only, or a grouped one whose item columns are keys (`BodyOk`,
  -- `groupedBodyOf`), without `ORDER BY`; under `IN`, also a set operation over such bodies
  -- (`SubBodyOk`, #410). A scalar node assumes a dialect
  -- that takes the first row of several (sqlite, as Spider is). Under `GROUP BY` too
  -- (`elabStmt_correct_grouped_inSub`).
  -- A scalar node over an `AVG` body (`AvgWhere`): compared with a column or an integer literal.
  -- The theorem also wants that operand not a decimal (`nonDecimalIn_col`: true of a column
  -- in a schema without decimal columns, as Spider's typing is) and the average's denominator
  -- at most `10¹⁶` (`avgBound_of_rows`: true when `FROM` has at most that many rows), which
  -- the shape cannot see: the count assumes that schema and that size.
  (match s.whereClause.bind holeSplit, s.whereClause with
   | some (xs, cmp, nd), _ =>
     let probe := match nd with | .inSubquery e _ _ => exprFeatures e | _ => []
     let avgOk := match nd, cmp with
       | .subquery (.simple b), some (.col _) | .subquery (.simple b), some (.lit (.int _)) =>
         avgBodyOf b
       | _, _ => false
     if (s.groupBy.isEmpty && s.having.isNone && (!s.distinct || plainDistinct)) || plainGroup then
       xs.flatMap exprFeatures ++ (if xs.any refsHidden then [hiddenName] else []) ++ probe ++
         (match nd with
          | .inSubquery _ _ sq => inBodyFeatures sq
          | .subquery (.simple b) => bodyFeatures avgOk b
          | _ => [subquery])
     else subquery :: (xs.flatMap exprFeatures ++ probe)
   | none, some w => exprFeatures w
   | none, none => []) ++
  (if (s.groupBy.isEmpty && s.having.isNone) || plainGroup then [] else [aggregate]) ++
  (s.groupBy.flatMap exprFeatures) ++
  ((s.having.map (if plainGroup then havingFeatures else exprFeatures)).getD []) ++
  (if plainGroup || s.orderBy.all (fun o => match o.expr with | .col _ => true | _ => false) then []
   else [orderKey]) ++
  (if s.orderBy.isEmpty || plainGroup || itemsNamed s.items then [] else [unnamedItem]) ++
  (s.orderBy.flatMap fun o =>
    if plainGroup then (match o.expr with | .agg _ (some a) _ => exprFeatures a | _ => [])
    else exprFeatures o.expr)

/-- Features of a subquery body (`SqlBridge.CorrectSub.BodyOk`) outside the fragment: its own,
    and `subquery` unless it is a plain statement, one of aggregates only (or, under a scalar
    comparison, one `AVG`: `avgOk`), or a grouped one (`groupedBodyOf`), without `DISTINCT`,
    `ORDER BY`, `LIMIT` or `OFFSET`. -/
partial def bodyFeatures (avgOk : Bool) (b : SelectStmt) : List String :=
  selectFeatures b ++
  (if b.distinct || !b.orderBy.isEmpty || b.limitVal.isSome || b.offsetVal.isSome ||
      (if b.groupBy.isEmpty && b.having.isNone then
        b.items.any (fun | .exprItem e _ => itemCallOk e | .star _ => false) &&
          !plainAggOf b && !avgOk
       else !groupedBodyOf b)
   then [subquery] else [])

/-- Features of an `IN` body (`SqlBridge.CorrectSub.SubBodyOk`, #410): a body as above, or a
    set operation over such bodies. -/
partial def inBodyFeatures : SubQuery → List String
  | .simple b => bodyFeatures false b
  | .compound l _ r => inBodyFeatures l ++ inBodyFeatures r

/-- A branch of a set operation (mirrors `SqlBridge.CorrectSetOp.Leaf`): a statement of the
    earlier steps whose result is related exactly or up to order. So besides its own features:
    no `ORDER BY`, `LIMIT` or `OFFSET`, no `AVG` item (related only up to rounding), and no bare
    column without `GROUP BY` (`elabStmt_correct_aggBare` is not among the leaves). -/
partial def branchFeatures (s : SelectStmt) : List String :=
  let hasAvg := s.items.any fun
    | .exprItem (.agg (.avg _) _ _) _ => true
    | _ => false
  let bareNoGroup := !s.distinct && s.groupBy.isEmpty &&
    s.items.any (fun | .exprItem e _ => itemCallOk e | .star _ => false) &&
    s.items.any (fun | .exprItem (.col _) _ => true | _ => false)
  selectFeatures s ++
    (if !s.orderBy.isEmpty || s.limitVal.isSome || s.offsetVal.isSome || hasAvg || bareNoGroup ||
        s.having.any hasCmpAvgOk
     then [setOpBranch] else [])

/-- Features of a query outside the fragment. A set operation (`elabStmt_correct_setOp`) is in
    the fragment when its branches are; one under a trailing `ORDER BY`/`LIMIT` is not. -/
partial def queryFeatures : Query → List String
  | .simple s => selectFeatures s
  | .compound l _ r => branchQueryFeatures l ++ branchQueryFeatures r
  | .withCTE _ q => subquery :: queryFeatures q
  | .ordered q _ _ _ => orderCompound :: queryFeatures q

/-- The same for a branch of a set operation. -/
partial def branchQueryFeatures : Query → List String
  | .simple s => branchFeatures s
  | .compound l _ r => branchQueryFeatures l ++ branchQueryFeatures r
  | q => subquery :: queryFeatures q

end

/-- The distinct features that put a statement outside the theorem's fragment, sorted;
    `[]` when it has the fragment's shape. -/
def outsideFragment : Stmt → List String
  | .query q => (queryFeatures q).eraseDups.mergeSort (· ≤ ·)
  | _ => ["not a query"]

end SqlBridge.Coverage
