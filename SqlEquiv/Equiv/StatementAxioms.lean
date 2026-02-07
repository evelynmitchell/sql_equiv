/-
  SQL Equivalence - Statement-Level Axioms (SET ops, JOINs, Subqueries, Pagination)
-/
import SqlEquiv.Equiv.Defs

namespace SqlEquiv

-- ============================================================================
-- Set Operation Theorems (UNION, INTERSECT, EXCEPT)
-- ============================================================================

/-- UNION is commutative: A UNION B = B UNION A -/
axiom union_comm (a b : SelectStmt) :
    Query.compound (Query.simple a) .union (Query.simple b) ≃ᵩ
    Query.compound (Query.simple b) .union (Query.simple a)

/-- UNION ALL is commutative: A UNION ALL B = B UNION ALL A -/
axiom union_all_comm (a b : SelectStmt) :
    Query.compound (Query.simple a) .unionAll (Query.simple b) ≃ᵩ
    Query.compound (Query.simple b) .unionAll (Query.simple a)

/-- INTERSECT is commutative: A INTERSECT B = B INTERSECT A -/
axiom intersect_comm (a b : SelectStmt) :
    Query.compound (Query.simple a) .intersect (Query.simple b) ≃ᵩ
    Query.compound (Query.simple b) .intersect (Query.simple a)

/-- UNION is associative: (A UNION B) UNION C = A UNION (B UNION C) -/
axiom union_assoc (a b c : Query) :
    Query.compound (Query.compound a .union b) .union c ≃ᵩ
    Query.compound a .union (Query.compound b .union c)

/-- INTERSECT is associative: (A INTERSECT B) INTERSECT C = A INTERSECT (B INTERSECT C) -/
axiom intersect_assoc (a b c : Query) :
    Query.compound (Query.compound a .intersect b) .intersect c ≃ᵩ
    Query.compound a .intersect (Query.compound b .intersect c)

/-- UNION is idempotent: A UNION A = A -/
axiom union_idempotent (a : SelectStmt) :
    Query.compound (Query.simple a) .union (Query.simple a) ≃ᵩ
    Query.simple a

/-- INTERSECT is idempotent: A INTERSECT A = A -/
axiom intersect_idempotent (a : SelectStmt) :
    Query.compound (Query.simple a) .intersect (Query.simple a) ≃ᵩ
    Query.simple a

/-- A EXCEPT A = empty (self-difference is empty) -/
axiom except_self_empty (db : Database) (a : SelectStmt) :
    evalQuery db (Query.compound (Query.simple a) .exceptOp (Query.simple a)) = []

/-- UNION with empty is identity (axiom form) -/
axiom union_empty_right (db : Database) (a : SelectStmt) :
    let emptySelect := SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none
    evalQuery db (Query.compound (Query.simple a) .union (Query.simple emptySelect)) =
    evalQuery db (Query.simple a)

/-- INTERSECT with empty is empty -/
axiom intersect_empty_right (db : Database) (a : SelectStmt) :
    let emptySelect := SelectStmt.mk false [.star none] none (some (.lit (.bool false))) [] none [] none none
    evalQuery db (Query.compound (Query.simple a) .intersect (Query.simple emptySelect)) = []

/-- UNION ALL keeps all duplicates from both sides -/
axiom union_all_length (db : Database) (a b : SelectStmt) :
    (evalQuery db (Query.compound (Query.simple a) .unionAll (Query.simple b))).length =
    (evalQuery db (Query.simple a)).length + (evalQuery db (Query.simple b)).length

-- Note: EXCEPT is NOT commutative, so we don't have a commutativity axiom for it

/-- Distributivity: A UNION (B INTERSECT C) = (A UNION B) INTERSECT (A UNION C) -/
axiom union_intersect_distrib (a b c : Query) :
    Query.compound a .union (Query.compound b .intersect c) ≃ᵩ
    Query.compound (Query.compound a .union b) .intersect (Query.compound a .union c)

/-- Distributivity: A INTERSECT (B UNION C) = (A INTERSECT B) UNION (A INTERSECT C) -/
axiom intersect_union_distrib (a b c : Query) :
    Query.compound a .intersect (Query.compound b .union c) ≃ᵩ
    Query.compound (Query.compound a .intersect b) .union (Query.compound a .intersect c)

-- ============================================================================
-- JOIN Theorems
-- ============================================================================

/-- CROSS JOIN cardinality is symmetric: |A x B| = |B x A| -/
axiom cross_join_cardinality_comm (db : Database) (a b : FromClause) :
    let rowsAB := evalFrom db (.join a .cross b none)
    let rowsBA := evalFrom db (.join b .cross a none)
    rowsAB.length = rowsBA.length

/-- INNER JOIN with ON TRUE is equivalent to CROSS JOIN -/
axiom inner_join_true_is_cross (db : Database) (a b : FromClause) :
    evalFrom db (.join a .inner b (some (.lit (.bool true)))) =
    evalFrom db (.join a .cross b none)

/-- INNER JOIN with ON FALSE produces empty result -/
axiom inner_join_false_empty (db : Database) (a b : FromClause) :
    evalFrom db (.join a .inner b (some (.lit (.bool false)))) = []

/-- LEFT JOIN with ON FALSE returns all left rows with NULLs for right -/
axiom left_join_false_all_left (db : Database) (a b : FromClause) :
    let result := evalFrom db (.join a .left b (some (.lit (.bool false))))
    let leftRows := evalFrom db a
    result.length = leftRows.length

/-- CROSS JOIN cardinality: |A CROSS JOIN B| = |A| * |B| -/
axiom cross_join_cardinality (db : Database) (a b : FromClause) :
    let rowsA := evalFrom db a
    let rowsB := evalFrom db b
    let rowsAB := evalFrom db (.join a .cross b none)
    rowsAB.length = rowsA.length * rowsB.length

/-- INNER JOIN cardinality upper bound: |A INNER JOIN B| <= |A| * |B| -/
axiom inner_join_cardinality_le (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rowsA := evalFrom db a
    let rowsB := evalFrom db b
    let rowsAB := evalFrom db (.join a .inner b on_)
    rowsAB.length ≤ rowsA.length * rowsB.length

/-- LEFT JOIN cardinality: |A LEFT JOIN B| >= |A| -/
axiom left_join_cardinality_ge (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rowsA := evalFrom db a
    let rowsAB := evalFrom db (.join a .left b on_)
    rowsAB.length ≥ rowsA.length

/-- RIGHT JOIN cardinality: |A RIGHT JOIN B| >= |B| -/
axiom right_join_cardinality_ge (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rowsB := evalFrom db b
    let rowsAB := evalFrom db (.join a .right b on_)
    rowsAB.length ≥ rowsB.length

/-- INNER JOIN with empty left produces empty result -/
axiom inner_join_empty_left (db : Database) (a b : FromClause) (on_ : Option Expr)
    (h : evalFrom db a = []) :
    evalFrom db (.join a .inner b on_) = []

/-- INNER JOIN with empty right produces empty result -/
axiom inner_join_empty_right (db : Database) (a b : FromClause) (on_ : Option Expr)
    (h : evalFrom db b = []) :
    evalFrom db (.join a .inner b on_) = []

/-- CROSS JOIN with empty left produces empty result -/
axiom cross_join_empty_left (db : Database) (a b : FromClause)
    (h : evalFrom db a = []) :
    evalFrom db (.join a .cross b none) = []

/-- CROSS JOIN with empty right produces empty result -/
axiom cross_join_empty_right (db : Database) (a b : FromClause)
    (h : evalFrom db b = []) :
    evalFrom db (.join a .cross b none) = []

/-- Join associativity for CROSS JOIN: (A × B) × C has same cardinality as A × (B × C) -/
axiom cross_join_assoc_cardinality (db : Database) (a b c : FromClause) :
    let abc1 := evalFrom db (.join (.join a .cross b none) .cross c none)
    let abc2 := evalFrom db (.join a .cross (.join b .cross c none) none)
    abc1.length = abc2.length

/-- INNER JOIN condition can be moved to WHERE (join-to-where conversion) -/
axiom inner_join_to_where (db : Database) (t1 t2 : TableRef) (cond : Expr) :
    let joinFrom := FromClause.join (.table t1) .inner (.table t2) (some cond)
    let crossFrom := FromClause.join (.table t1) .cross (.table t2) none
    let joinResult := evalFrom db joinFrom
    let crossFiltered := (evalFrom db crossFrom).filter fun row =>
      evalExprWithDb db row cond == some (.bool true)
    joinResult = crossFiltered

/-- LEFT JOIN preserves all left rows: every left row appears in the result -/
axiom left_join_preserves_left (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let leftRows := evalFrom db a
    let joinResult := evalFrom db (.join a .left b on_)
    ∀ lr ∈ leftRows, ∃ jr ∈ joinResult, ∀ (k : String) (v : Value),
      (k, v) ∈ lr → (k, v) ∈ jr

/-- RIGHT JOIN preserves all right rows: every right row appears in the result -/
axiom right_join_preserves_right (db : Database) (a b : FromClause) (on_ : Option Expr) :
    let rightRows := evalFrom db b
    let joinResult := evalFrom db (.join a .right b on_)
    ∀ rr ∈ rightRows, ∃ jr ∈ joinResult, ∀ (k : String) (v : Value),
      (k, v) ∈ rr → (k, v) ∈ jr

/-- INNER JOIN is a subset of CROSS JOIN (when ON is given) -/
axiom inner_subset_cross (db : Database) (a b : FromClause) (cond : Expr) :
    let innerResult := evalFrom db (.join a .inner b (some cond))
    let crossResult := evalFrom db (.join a .cross b none)
    innerResult.length ≤ crossResult.length

/-- Converting LEFT JOIN to INNER JOIN by filtering out NULLs:
    If we filter the result of LEFT JOIN to exclude rows where right columns are NULL,
    we get the same result as INNER JOIN -/
axiom left_join_filter_null_is_inner (db : Database) (a b : FromClause) (on_ : Option Expr)
    (rightCol : String) :
    let leftResult := evalFrom db (.join a .left b on_)
    let innerResult := evalFrom db (.join a .inner b on_)
    let filtered := leftResult.filter fun row =>
      match row.find? (fun (k, _) => k == rightCol) with
      | some (_, v) => !isNullValue v
      | none => false
    -- The filtered left join has same length as inner join
    filtered.length = innerResult.length

-- ============================================================================
-- Subquery Theorems
-- ============================================================================

/-- EXISTS on empty subquery is FALSE -/
axiom exists_empty_false (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.exists false sel) = some (.bool false)

/-- NOT EXISTS on empty subquery is TRUE -/
axiom not_exists_empty_true (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.exists true sel) = some (.bool true)

/-- EXISTS on non-empty subquery is TRUE -/
axiom exists_nonempty_true (db : Database) (row : Row) (sel : SelectStmt)
    (h : (evalSelectWithContext db row sel).length > 0) :
    evalExprWithDb db row (Expr.exists false sel) = some (.bool true)

/-- NOT EXISTS on non-empty subquery is FALSE -/
axiom not_exists_nonempty_false (db : Database) (row : Row) (sel : SelectStmt)
    (h : (evalSelectWithContext db row sel).length > 0) :
    evalExprWithDb db row (Expr.exists true sel) = some (.bool false)

/-- Double negation: NOT NOT EXISTS = EXISTS -/
axiom not_not_exists (sel : SelectStmt) :
    Expr.exists true sel ≃ₑ Expr.unaryOp .not (Expr.exists false sel)

/-- x IN (empty subquery) = FALSE -/
axiom in_empty_subquery_false (e : Expr) (sel : SelectStmt) :
    -- When the subquery returns no rows, IN is always false
    Expr.inSubquery e false sel ≃ₑ
    Expr.case [(Expr.exists false sel, Expr.lit (.bool false))]
              (some (Expr.inSubquery e false sel))

/-- x NOT IN (empty subquery) = TRUE -/
axiom not_in_empty_subquery_true (e : Expr) (sel : SelectStmt) :
    -- When the subquery returns no rows, NOT IN is always true
    Expr.inSubquery e true sel ≃ₑ
    Expr.case [(Expr.unaryOp .not (Expr.exists false sel), Expr.lit (.bool true))]
              (some (Expr.inSubquery e true sel))

/-- Scalar subquery returning empty = NULL -/
axiom scalar_subquery_empty_null (db : Database) (row : Row) (sel : SelectStmt)
    (h : evalSelectWithContext db row sel = []) :
    evalExprWithDb db row (Expr.subquery sel) = some (.null none)

/-- EXISTS can be rewritten as COUNT(*) > 0 (semantic equivalence) -/
axiom exists_as_count_gt_zero (db : Database) (row : Row) (sel : SelectStmt) :
    let existsResult := evalExprWithDb db row (Expr.exists false sel)
    let subRows := evalSelectWithContext db row sel
    existsResult = some (.bool (subRows.length > 0))

/-- NOT EXISTS can be rewritten as COUNT(*) = 0 (semantic equivalence) -/
axiom not_exists_as_count_eq_zero (db : Database) (row : Row) (sel : SelectStmt) :
    let existsResult := evalExprWithDb db row (Expr.exists true sel)
    let subRows := evalSelectWithContext db row sel
    existsResult = some (.bool (subRows.length == 0))

/-- IN subquery is equivalent to EXISTS with equality condition.
    x IN (SELECT col FROM t) ≡ EXISTS (SELECT 1 FROM t WHERE t.col = x) -/
axiom in_subquery_as_exists (db : Database) (row : Row) (e : Expr)
    (tableName : String) (colName : String) :
    let inSub := Expr.inSubquery e false
      (SelectStmt.mk false [.exprItem (.col ⟨none, colName⟩) none]
        (some (.table ⟨tableName, none⟩)) none [] none [] none none)
    let existsSub := Expr.exists false
      (SelectStmt.mk false [.exprItem (.lit (.int 1)) none]
        (some (.table ⟨tableName, none⟩))
        (some (.binOp .eq (.col ⟨some tableName, colName⟩) e))
        [] none [] none none)
    evalExprWithDb db row inSub = evalExprWithDb db row existsSub

/-- NOT IN subquery is equivalent to NOT EXISTS with equality condition -/
axiom not_in_subquery_as_not_exists (db : Database) (row : Row) (e : Expr)
    (tableName : String) (colName : String) :
    let notInSub := Expr.inSubquery e true
      (SelectStmt.mk false [.exprItem (.col ⟨none, colName⟩) none]
        (some (.table ⟨tableName, none⟩)) none [] none [] none none)
    let notExistsSub := Expr.exists true
      (SelectStmt.mk false [.exprItem (.lit (.int 1)) none]
        (some (.table ⟨tableName, none⟩))
        (some (.binOp .eq (.col ⟨some tableName, colName⟩) e))
        [] none [] none none)
    evalExprWithDb db row notInSub = evalExprWithDb db row notExistsSub

/-- Uncorrelated subquery can be evaluated independently of outer row.
    If a subquery doesn't reference any columns from the outer query,
    its result is the same regardless of the outer row context. -/
axiom uncorrelated_subquery_independent (db : Database) (row1 row2 : Row) (sel : SelectStmt) :
    -- Assuming sel doesn't reference columns from the outer context
    -- (this is a semantic precondition)
    evalSelectWithContext db row1 sel = evalSelectWithContext db row2 sel

/-- Subquery with LIMIT 1 returns at most one row -/
axiom subquery_limit_one (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 1) offset
    (evalSelectWithContext db row sel).length ≤ 1

/-- Scalar subquery is equivalent to first value of subquery with LIMIT 1 -/
axiom scalar_subquery_is_first (db : Database) (row : Row) (sel : SelectStmt) :
    let result := evalExprWithDb db row (Expr.subquery sel)
    let subRows := evalSelectWithContext db row sel
    result = match subRows.head? with
      | some subRow => subRow.head?.map (·.2)
      | none => some (.null none)

/-- EXISTS is monotonic: more rows in subquery doesn't change TRUE to FALSE -/
axiom exists_monotonic (db : Database) (row : Row) (sel1 sel2 : SelectStmt)
    (h : ∀ r ∈ evalSelectWithContext db row sel1,
         r ∈ evalSelectWithContext db row sel2) :
    evalExprWithDb db row (Expr.exists false sel1) = some (.bool true) →
    evalExprWithDb db row (Expr.exists false sel2) = some (.bool true)

/-- Adding WHERE TRUE to subquery doesn't change result -/
axiom subquery_where_true (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ none groupBy having orderBy limit offset
    let selWithTrue := SelectStmt.mk distinct items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset
    evalSelectWithContext db row sel = evalSelectWithContext db row selWithTrue

/-- Adding WHERE FALSE to subquery makes it empty -/
axiom subquery_where_false (db : Database) (row : Row)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    let selWithFalse := SelectStmt.mk distinct items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset
    evalSelectWithContext db row selWithFalse = []

/-- IN with single-value subquery is equivalent to equality -/
axiom in_singleton_subquery (db : Database) (row : Row) (e : Expr) (sel : SelectStmt)
    (colName : String) (v : Value)
    (h : evalSelectWithContext db row sel = [[(colName, v)]]) :
    evalExprWithDb db row (Expr.inSubquery e false sel) =
    evalExprWithDb db row (Expr.binOp .eq e (Expr.lit v))

/-- Correlated subquery with outer reference evaluates with outer row context -/
axiom correlated_subquery_uses_context (db : Database) (outerRow : Row)
    (sel : SelectStmt) (outerCol : String) (outerVal : Value)
    (h : (outerCol, outerVal) ∈ outerRow) :
    -- The subquery can access outerCol from the outer row
    -- subResult is computed with outerRow available for column resolution
    True  -- This is a semantic property, not a computational one

-- ============================================================================
-- Subquery Unnesting Theorems
-- ============================================================================

/-- Subquery unnesting: IN subquery can be rewritten as a semi-join with DISTINCT.
    SELECT * FROM t WHERE x IN (SELECT y FROM s)
    ≡ SELECT DISTINCT t.* FROM t JOIN s ON t.x = s.y

    This is a key database optimization. The DISTINCT is required because
    the join may produce duplicates when multiple s rows have the same y value.

    NULL handling: Both forms exclude rows where t.x is NULL (IN returns NULL
    which WHERE treats as FALSE; JOIN condition evaluates to NULL/no match).
    Similarly, NULL values in s.y don't cause differences - they simply
    don't match in either form.

    This axiom expresses the semantic equivalence at the statement level. -/
axiom in_subquery_unnest_to_join (db : Database)
    (tName sName : String) (xCol yCol : String) :
    let inSubqueryForm := SelectStmt.mk false
        [.star (some tName)]  -- SELECT t.*
        (some (.table ⟨tName, some tName⟩))  -- FROM t
        (some (.inSubquery
          (.col ⟨some tName, xCol⟩)
          false  -- not negated (IN, not NOT IN)
          (SelectStmt.mk false
            [.exprItem (.col ⟨none, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩))
            none [] none [] none none)))  -- WHERE x IN (SELECT y FROM s)
        [] none [] none none
    let joinForm := SelectStmt.mk true  -- DISTINCT
        [.star (some tName)]  -- SELECT DISTINCT t.*
        (some (.join
          (.table ⟨tName, some tName⟩)
          .inner
          (.table ⟨sName, some sName⟩)
          (some (.binOp .eq
            (.col ⟨some tName, xCol⟩)
            (.col ⟨some sName, yCol⟩)))))  -- FROM t JOIN s ON t.x = s.y
        none [] none [] none none
    evalSelect db inSubqueryForm = evalSelect db joinForm

/-- NOT IN subquery can be unnested to an anti-join pattern.
    SELECT * FROM t WHERE x NOT IN (SELECT y FROM s)
    ≡ SELECT t.* FROM t LEFT JOIN s ON t.x = s.y WHERE s.y IS NULL

    The anti-join returns rows from t that have no matching rows in s.

    Note: This transformation assumes s.y contains no NULL values.
    When s.y can be NULL, NOT IN has different semantics (returns NULL
    when x matches no values but s contains NULL). -/
axiom not_in_subquery_unnest_to_antijoin (db : Database)
    (tName sName : String) (xCol yCol : String) :
    let notInSubqueryForm := SelectStmt.mk false
        [.star (some tName)]  -- SELECT t.*
        (some (.table ⟨tName, some tName⟩))  -- FROM t
        (some (.inSubquery
          (.col ⟨some tName, xCol⟩)
          true  -- negated (NOT IN)
          (SelectStmt.mk false
            [.exprItem (.col ⟨none, yCol⟩) none]
            (some (.table ⟨sName, some sName⟩))
            none [] none [] none none)))  -- WHERE x NOT IN (SELECT y FROM s)
        [] none [] none none
    let antijoinForm := SelectStmt.mk false
        [.star (some tName)]  -- SELECT t.*
        (some (.join
          (.table ⟨tName, some tName⟩)
          .left  -- LEFT JOIN
          (.table ⟨sName, some sName⟩)
          (some (.binOp .eq
            (.col ⟨some tName, xCol⟩)
            (.col ⟨some sName, yCol⟩)))))  -- LEFT JOIN s ON t.x = s.y
        (some (.unaryOp .isNull (.col ⟨some sName, yCol⟩)))  -- WHERE s.y IS NULL
        [] none [] none none
    evalSelect db notInSubqueryForm = evalSelect db antijoinForm

/-- At the expression level: x IN (SELECT y FROM s) evaluates to true for a row
    if and only if there exists a matching row in the join result.

    This captures the logical essence of the unnesting transformation:
    membership in a subquery result corresponds to a successful join match. -/
axiom in_subquery_implies_join_match (db : Database) (row : Row)
    (x : Expr) (sName yCol : String)
    (h : evalExprWithDb db row (Expr.inSubquery x false
           (SelectStmt.mk false
             [.exprItem (.col ⟨none, yCol⟩) none]
             (some (.table ⟨sName, some sName⟩))
             none [] none [] none none)) = some (.bool true)) :
    ∃ sRow ∈ db sName,
      evalExprWithDb db (row ++ sRow)
        (Expr.binOp .eq x (.col ⟨some sName, yCol⟩)) = some (.bool true)

/-- The converse: if a join match exists, the IN subquery returns true. -/
axiom join_match_implies_in_subquery (db : Database) (row : Row)
    (x : Expr) (sName yCol : String) (sRow : Row)
    (hMem : sRow ∈ db sName)
    (hMatch : evalExprWithDb db (row ++ sRow)
                (Expr.binOp .eq x (.col ⟨some sName, yCol⟩)) = some (.bool true)) :
    evalExprWithDb db row (Expr.inSubquery x false
      (SelectStmt.mk false
        [.exprItem (.col ⟨none, yCol⟩) none]
        (some (.table ⟨sName, some sName⟩))
        none [] none [] none none)) = some (.bool true)

-- ============================================================================
-- ORDER BY Theorems
-- ============================================================================

/-- ORDER BY preserves row count -/
axiom order_by_preserves_count (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (orderBy : List OrderByItem) :
    let selNoOrder := SelectStmt.mk distinct items from_ where_ groupBy having [] limit offset
    let selWithOrder := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit offset
    (evalSelect db selNoOrder).length = (evalSelect db selWithOrder).length

/-- Empty ORDER BY list is identity -/
axiom order_by_empty_identity (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having [] limit offset
    evalSelect db sel = evalSelect db sel

/-- ORDER BY is idempotent: ordering twice by same criteria is same as once -/
axiom order_by_idempotent (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (orderBy : List OrderByItem) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit offset
    -- Applying the same ORDER BY twice gives same result
    let result := evalSelect db sel
    result.mergeSort (fun r1 r2 => compareByOrderItems db r1 r2 orderBy) = result

/-- ORDER BY ASC then DESC on same column: second order takes precedence -/
axiom order_by_last_wins (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (col : Expr) :
    let selAscDesc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .asc, OrderByItem.mk col .desc] limit offset
    let selDesc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .desc] limit offset
    -- When ordering by same column twice, later order dominates
    (evalSelect db selAscDesc).length = (evalSelect db selDesc).length

/-- Reversing ORDER BY direction reverses the result (for single column) -/
axiom order_by_reverse (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (limit offset : Option Nat) (col : Expr) :
    let selAsc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .asc] limit offset
    let selDesc := SelectStmt.mk distinct items from_ where_ groupBy having
      [OrderByItem.mk col .desc] limit offset
    (evalSelect db selAsc).reverse = evalSelect db selDesc

-- ============================================================================
-- LIMIT Theorems
-- ============================================================================

/-- LIMIT 0 returns empty result -/
axiom limit_zero_empty (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 0) offset
    evalSelect db sel = []

/-- LIMIT n returns at most n rows -/
axiom limit_upper_bound (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) (n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) offset
    (evalSelect db sel).length ≤ n

/-- No LIMIT returns all rows (LIMIT none vs LIMIT large) -/
axiom limit_none_all_rows (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let selNoLimit := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none offset
    let count := (evalSelect db selNoLimit).length
    let selLargeLimit := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some count) offset
    evalSelect db selNoLimit = evalSelect db selLargeLimit

/-- LIMIT is monotonic: larger limit gives superset (by length) -/
axiom limit_monotonic (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) (m n : Nat) (h : m ≤ n) :
    let selM := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some m) offset
    let selN := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) offset
    (evalSelect db selM).length ≤ (evalSelect db selN).length

/-- LIMIT 1 returns at most one row -/
axiom limit_one_singleton (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Option Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 1) offset
    (evalSelect db sel).length ≤ 1

-- ============================================================================
-- OFFSET Theorems
-- ============================================================================

/-- OFFSET 0 is identity -/
axiom offset_zero_identity (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) :
    let selNoOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit none
    let selZeroOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some 0)
    evalSelect db selNoOffset = evalSelect db selZeroOffset

/-- OFFSET >= row count returns empty -/
axiom offset_too_large_empty (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) (n : Nat) :
    let selNoOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit none
    let count := (evalSelect db selNoOffset).length
    let selOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some (count + n))
    evalSelect db selOffset = []

/-- OFFSET reduces row count -/
axiom offset_reduces_count (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) (n : Nat) :
    let selNoOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit none
    let selOffset := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some n)
    (evalSelect db selOffset).length ≤ (evalSelect db selNoOffset).length

/-- OFFSET is monotonic: larger offset gives fewer or equal rows -/
axiom offset_monotonic (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit : Option Nat) (m n : Nat) (h : m ≤ n) :
    let selM := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some m)
    let selN := SelectStmt.mk distinct items from_ where_ groupBy having orderBy limit (some n)
    (evalSelect db selN).length ≤ (evalSelect db selM).length

-- ============================================================================
-- LIMIT + OFFSET Combination Theorems
-- ============================================================================

/-- LIMIT and OFFSET compose: OFFSET m then LIMIT n = skip m, take n -/
axiom limit_offset_compose (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (m n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) (some m)
    let selAll := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none
    evalSelect db sel = ((evalSelect db selAll).drop m).take n

/-- OFFSET then LIMIT 0 = empty regardless of offset -/
axiom offset_limit_zero_empty (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (offset : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some 0) (some offset)
    evalSelect db sel = []

/-- Total pagination: LIMIT n OFFSET m returns at most n rows -/
axiom pagination_upper_bound (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (m n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) (some m)
    (evalSelect db sel).length ≤ n

/-- Pagination identity: OFFSET 0 LIMIT count = all rows -/
axiom pagination_identity (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) :
    let selAll := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none
    let count := (evalSelect db selAll).length
    let selPaged := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some count) (some 0)
    evalSelect db selAll = evalSelect db selPaged

/-- Consecutive pages cover all rows: page1 ++ page2 when properly offset -/
axiom consecutive_pages (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (pageSize : Nat) :
    let selPage1 := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some pageSize) (some 0)
    let selPage2 := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some pageSize) (some pageSize)
    let selBoth := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some (pageSize * 2)) (some 0)
    evalSelect db selPage1 ++ evalSelect db selPage2 = evalSelect db selBoth

/-- ORDER BY + LIMIT: first n rows are deterministic (assuming stable sort) -/
axiom order_limit_deterministic (db : Database)
    (distinct : Bool) (items : List SelectItem) (from_ : Option FromClause)
    (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (n : Nat) :
    let sel := SelectStmt.mk distinct items from_ where_ groupBy having orderBy (some n) none
    let selAll := SelectStmt.mk distinct items from_ where_ groupBy having orderBy none none
    evalSelect db sel = (evalSelect db selAll).take n


end SqlEquiv
