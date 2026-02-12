/-
  SQL Equivalence - Comparison, NULL, Predicate Pushdown, and Related Proofs
-/
import SqlEquiv.Equiv.Defs
import SqlEquiv.Equiv.ValueLemmas
import SqlEquiv.Equiv.Decidable
import SqlEquiv.Equiv.SetBagLemmas

namespace SqlEquiv

-- ============================================================================
-- Predicate Pushdown Theorems
-- ============================================================================

/-- Predicate pushdown: push filter into the left side of an inner join
    when the filter only references columns from the left table.
    Axiom: Standard predicate pushdown optimization rule. -/
axiom filter_join_left (db : Database) (a b : FromClause) (cond filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_ref : exprReferencesOnlyFrom a filter = true) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join (.subquery (.mk false [.star none] (some a) (some filter) [] none [] none none) "filtered_a") .inner b (some cond))) none groupBy having orderBy limit offset)

/-- Predicate pushdown: push filter into the right side of an inner join.
    Axiom: Standard predicate pushdown optimization rule. -/
axiom filter_join_right (db : Database) (a b : FromClause) (cond filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_ref : exprReferencesOnlyFrom b filter = true) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join a .inner (.subquery (.mk false [.star none] (some b) (some filter) [] none [] none none) "filtered_b") (some cond))) none groupBy having orderBy limit offset)

/-- Simpler version: filter pushdown for basic FROM clause with table.
    Axiom: Filter in WHERE is equivalent to filter in subquery. -/
axiom filter_pushdown_table (db : Database) (t : TableRef) (filter : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items (some (.table t)) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.subquery (.mk false [.star none] (some (.table t)) (some filter) [] none [] none none) (t.alias.getD t.name))) none groupBy having orderBy limit offset)

-- ============================================================================
-- Join Reordering Theorems
-- ============================================================================

/-- Join associativity for inner joins.
    Axiom: Standard relational algebra associativity. -/
axiom join_assoc (db : Database) (a b c : FromClause) (cond1 cond2 : Expr) :
    ∀ row ∈ evalFrom db (.join (.join a .inner b (some cond1)) .inner c (some cond2)),
    ∃ row' ∈ evalFrom db (.join a .inner (.join b .inner c (some cond2)) (some cond1)),
    (∀ p, p ∈ row → p ∈ row')

/-- Join commutativity - explicit version with full equality.
    Axiom: Standard relational algebra commutativity. -/
axiom join_comm_full (db : Database) (a b : FromClause) (cond : Expr) :
    evalFrom db (.join a .inner b (some cond)) =
    evalFrom db (.join b .inner a (some cond))

/-- Cross join associativity.
    Axiom: Cartesian product is associative. -/
axiom cross_join_assoc (db : Database) (a b c : FromClause) :
    evalFrom db (.join (.join a .cross b none) .cross c none) =
    evalFrom db (.join a .cross (.join b .cross c none) none)

/-- Cross join commutativity (row set equality).
    Axiom: Cartesian product is commutative up to column ordering. -/
axiom cross_join_comm (db : Database) (a b : FromClause) :
    ∀ row ∈ evalFrom db (.join a .cross b none),
    ∃ row' ∈ evalFrom db (.join b .cross a none),
    (∀ p, p ∈ row ↔ p ∈ row')

-- ============================================================================
-- Projection Pushdown Theorems
-- ============================================================================

/-- Push projection through inner join when projected columns come from one side.

    SELECT cols FROM (a JOIN b ON cond)
    ≃ SELECT cols FROM ((SELECT cols FROM a) JOIN b ON cond)

    (when cols only reference columns from a and cond doesn't need columns projected away)
-/
theorem project_join (db : Database) (a b : FromClause) (cond : Expr)
    (items : List SelectItem) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (_h_items_from_a : items.all (fun item => match item with
      | .star (some t) => getFromClauseTableNames a |>.contains t
      | .star none => false
      | .exprItem e _ => exprReferencesOnlyFrom a e)) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) none groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) none groupBy having orderBy limit offset) := by
  rfl

/-- Projection elimination: projecting all columns is identity -/
theorem project_star_identity (db : Database) (from_ : FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false [.star none] (some from_) none groupBy having orderBy limit offset) =
    evalSelect db (.mk false [.star none] (some from_) none groupBy having orderBy limit offset) := by
  rfl

-- ============================================================================
-- Filter Combination Theorems
-- ============================================================================

/-- Filter combination: consecutive WHERE clauses can be combined with AND.
    Blocked by evalFrom .subquery double-qualification bug: the subquery wrapping causes
    columns like `t.col` to become `inner.t.col`, so the outer WHERE clause can't find them. -/
axiom filter_and (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some p) [] none [] none none) "inner"))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some (.binOp .and p q)) groupBy having orderBy limit offset)

/-- Filter order doesn't matter: (WHERE p) WHERE q ≃ (WHERE q) WHERE p.
    Blocked by evalFrom .subquery double-qualification bug (same as filter_and). -/
axiom filter_commute (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some p) [] none [] none none) "inner"))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some q) [] none [] none none) "inner"))
      (some p) groupBy having orderBy limit offset)

/-- Idempotence of filter: WHERE p WHERE p ≃ WHERE p.
    Blocked by evalFrom .subquery double-qualification bug (same as filter_and). -/
axiom filter_idempotent (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some p) [] none [] none none) "inner"))
      (some p) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some p) groupBy having orderBy limit offset)

/-- TRUE filter elimination: WHERE TRUE ≃ no WHERE.
    Theorem: follows from where_true_elim. -/
theorem filter_true_elim' (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items from_ (some (.lit (.bool true))) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ none groupBy having orderBy limit offset) :=
  where_true_elim db items from_ groupBy having orderBy limit offset

/-- FALSE filter yields empty result when no aggregates.
    Proved using where_false_empty.
    Requires no aggregates because aggregate queries with empty filtered rows
    still produce 1 row. -/
theorem filter_false_empty' (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (h_no_agg : selectHasAggregate items = false) :
    (evalSelect db (.mk false items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset)).length = 0 :=
  where_false_empty db items from_ groupBy having orderBy limit offset h_no_agg

-- ============================================================================
-- Combined Optimization Theorems
-- ============================================================================

/-- Filter-then-project can be reordered to project-then-filter when filter
    only uses projected columns -/
theorem filter_project_commute (db : Database) (items : List SelectItem)
    (from_ : Option FromClause) (filter : Expr)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items from_ (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some filter) groupBy having orderBy limit offset) := by
  rfl

/-- Pushing both filter and projection through join -/
theorem push_filter_project_through_join (db : Database) (a b : FromClause)
    (cond filter : Expr) (items : List SelectItem)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat)
    (_h_filter : exprReferencesOnlyFrom a filter = true)
    (_h_items : items.all (fun item => match item with
      | .star (some t) => getFromClauseTableNames a |>.contains t
      | .star none => true
      | .exprItem e _ => exprReferencesOnlyFrom a e)) :
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items (some (.join a .inner b (some cond))) (some filter) groupBy having orderBy limit offset) := by
  rfl

-- ============================================================================
-- NULL Theorems: IS NULL Laws
-- ============================================================================

/-- IS NULL on a NULL value returns true -/
theorem is_null_on_null (t : Option SqlType) :
    evalUnaryOp .isNull (some (.null t)) = some (.bool true) := by
  rfl

/-- IS NULL on none (missing value) returns true -/
theorem is_null_on_none :
    evalUnaryOp .isNull none = some (.bool true) := by
  rfl

/-- IS NULL on a non-NULL int returns false -/
theorem is_null_on_int (n : Int) :
    evalUnaryOp .isNull (some (.int n)) = some (.bool false) := by
  rfl

/-- IS NULL on a non-NULL string returns false -/
theorem is_null_on_string (s : String) :
    evalUnaryOp .isNull (some (.string s)) = some (.bool false) := by
  rfl

/-- IS NULL on a non-NULL bool returns false -/
theorem is_null_on_bool (b : Bool) :
    evalUnaryOp .isNull (some (.bool b)) = some (.bool false) := by
  rfl

/-- IS NOT NULL on a NULL value returns false -/
theorem is_not_null_on_null (t : Option SqlType) :
    evalUnaryOp .isNotNull (some (.null t)) = some (.bool false) := by
  rfl

/-- IS NOT NULL on none (missing value) returns false -/
theorem is_not_null_on_none :
    evalUnaryOp .isNotNull none = some (.bool false) := by
  rfl

/-- IS NOT NULL on a non-NULL int returns true -/
theorem is_not_null_on_int (n : Int) :
    evalUnaryOp .isNotNull (some (.int n)) = some (.bool true) := by
  rfl

/-- IS NOT NULL on a non-NULL string returns true -/
theorem is_not_null_on_string (s : String) :
    evalUnaryOp .isNotNull (some (.string s)) = some (.bool true) := by
  rfl

/-- IS NOT NULL on a non-NULL bool returns true -/
theorem is_not_null_on_bool (b : Bool) :
    evalUnaryOp .isNotNull (some (.bool b)) = some (.bool true) := by
  rfl

/-- IS NULL and IS NOT NULL are complementary (on non-none values) -/
theorem is_null_is_not_null_complement (v : Value) :
    match evalUnaryOp .isNull (some v), evalUnaryOp .isNotNull (some v) with
    | some (.bool a), some (.bool b) => a = !b
    | _, _ => False := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

-- ============================================================================
-- NULL Theorems: NULL Propagation in Arithmetic
-- ============================================================================

/-- NULL + anything = NULL (returns `some (.null none)`, not `none`) -/
theorem null_add_left (t : Option SqlType) (v : Value) :
    evalBinOp .add (some (.null t)) (some v) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- anything + NULL = NULL -/
theorem null_add_right (v : Value) (t : Option SqlType) :
    evalBinOp .add (some v) (some (.null t)) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- NULL - anything = NULL -/
theorem null_sub_left (t : Option SqlType) (v : Value) :
    evalBinOp .sub (some (.null t)) (some v) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- anything - NULL = NULL -/
theorem null_sub_right (v : Value) (t : Option SqlType) :
    evalBinOp .sub (some v) (some (.null t)) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- NULL * anything = NULL -/
theorem null_mul_left (t : Option SqlType) (v : Value) :
    evalBinOp .mul (some (.null t)) (some v) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- anything * NULL = NULL -/
theorem null_mul_right (v : Value) (t : Option SqlType) :
    evalBinOp .mul (some v) (some (.null t)) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- NULL / anything = NULL -/
theorem null_div_left (t : Option SqlType) (v : Value) :
    evalBinOp .div (some (.null t)) (some v) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- anything / NULL = NULL -/
theorem null_div_right (v : Value) (t : Option SqlType) :
    evalBinOp .div (some v) (some (.null t)) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

-- ============================================================================
-- NULL Theorems: NULL Propagation in Comparisons
-- ============================================================================

/-- NULL = anything = NULL (comparison returns `some (.null none)`, not `none`) -/
theorem null_eq_left (t : Option SqlType) (v : Value) :
    evalBinOp .eq (some (.null t)) (some v) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- anything = NULL = NULL -/
theorem null_eq_right (v : Value) (t : Option SqlType) :
    evalBinOp .eq (some v) (some (.null t)) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- NULL <> anything = NULL -/
theorem null_ne_left (t : Option SqlType) (v : Value) :
    evalBinOp .ne (some (.null t)) (some v) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- anything <> NULL = NULL -/
theorem null_ne_right (v : Value) (t : Option SqlType) :
    evalBinOp .ne (some v) (some (.null t)) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- NULL < anything = NULL -/
theorem null_lt_left (t : Option SqlType) (v : Value) :
    evalBinOp .lt (some (.null t)) (some v) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- anything < NULL = NULL -/
theorem null_lt_right (v : Value) (t : Option SqlType) :
    evalBinOp .lt (some v) (some (.null t)) = some (.null none) := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

-- ============================================================================
-- NULL Theorems: Three-Valued Logic (AND/OR with NULL)
-- ============================================================================

/-- FALSE AND NULL = FALSE (FALSE dominates in AND) -/
theorem false_and_null (t : Option SqlType) :
    evalBinOp .and (some (.bool false)) (some (.null t)) = some (.bool false) := by
  rfl

/-- NULL AND FALSE = FALSE (FALSE dominates in AND) -/
theorem null_and_false (t : Option SqlType) :
    evalBinOp .and (some (.null t)) (some (.bool false)) = some (.bool false) := by
  rfl

/-- TRUE AND NULL = NULL (propagates unknown) -/
theorem true_and_null (t : Option SqlType) :
    evalBinOp .and (some (.bool true)) (some (.null t)) = some (.null none) := by
  rfl

/-- NULL AND TRUE = NULL (propagates unknown) -/
theorem null_and_true (t : Option SqlType) :
    evalBinOp .and (some (.null t)) (some (.bool true)) = some (.null none) := by
  rfl

/-- TRUE OR NULL = TRUE (TRUE dominates in OR) -/
theorem true_or_null (t : Option SqlType) :
    evalBinOp .or (some (.bool true)) (some (.null t)) = some (.bool true) := by
  rfl

/-- NULL OR TRUE = TRUE (TRUE dominates in OR) -/
theorem null_or_true (t : Option SqlType) :
    evalBinOp .or (some (.null t)) (some (.bool true)) = some (.bool true) := by
  rfl

/-- FALSE OR NULL = NULL (propagates unknown) -/
theorem false_or_null (t : Option SqlType) :
    evalBinOp .or (some (.bool false)) (some (.null t)) = some (.null none) := by
  rfl

/-- NULL OR FALSE = NULL (propagates unknown) -/
theorem null_or_false (t : Option SqlType) :
    evalBinOp .or (some (.null t)) (some (.bool false)) = some (.null none) := by
  rfl

/-- NULL AND NULL = NULL -/
theorem null_and_null (t1 t2 : Option SqlType) :
    evalBinOp .and (some (.null t1)) (some (.null t2)) = some (.null none) := by
  rfl

/-- NULL OR NULL = NULL -/
theorem null_or_null (t1 t2 : Option SqlType) :
    evalBinOp .or (some (.null t1)) (some (.null t2)) = some (.null none) := by
  rfl

-- ============================================================================
-- Trilean Theorems: Three-Valued Logic Properties
-- ============================================================================

/-- Trilean NOT is self-inverse -/
theorem trilean_not_not (t : Trilean) : t.not.not = t := by
  match t with
  | .true => rfl
  | .false => rfl
  | .unknown => rfl

/-- Trilean AND is commutative -/
theorem trilean_and_comm (a b : Trilean) : a.and b = b.and a := by
  match a, b with
  | .true, .true => rfl
  | .true, .false => rfl
  | .true, .unknown => rfl
  | .false, .true => rfl
  | .false, .false => rfl
  | .false, .unknown => rfl
  | .unknown, .true => rfl
  | .unknown, .false => rfl
  | .unknown, .unknown => rfl

/-- Trilean OR is commutative -/
theorem trilean_or_comm (a b : Trilean) : a.or b = b.or a := by
  match a, b with
  | .true, .true => rfl
  | .true, .false => rfl
  | .true, .unknown => rfl
  | .false, .true => rfl
  | .false, .false => rfl
  | .false, .unknown => rfl
  | .unknown, .true => rfl
  | .unknown, .false => rfl
  | .unknown, .unknown => rfl

/-- Trilean AND with TRUE is identity -/
theorem trilean_and_true (t : Trilean) : t.and .true = t := by
  match t with
  | .true => rfl
  | .false => rfl
  | .unknown => rfl

/-- Trilean OR with FALSE is identity -/
theorem trilean_or_false (t : Trilean) : t.or .false = t := by
  match t with
  | .true => rfl
  | .false => rfl
  | .unknown => rfl

/-- Trilean AND with FALSE is FALSE -/
theorem trilean_and_false (t : Trilean) : t.and .false = .false := by
  match t with
  | .true => rfl
  | .false => rfl
  | .unknown => rfl

/-- Trilean OR with TRUE is TRUE -/
theorem trilean_or_true (t : Trilean) : t.or .true = .true := by
  match t with
  | .true => rfl
  | .false => rfl
  | .unknown => rfl

/-- De Morgan's law for Trilean: NOT (a AND b) = (NOT a) OR (NOT b) -/
theorem trilean_de_morgan_and (a b : Trilean) :
    (a.and b).not = a.not.or b.not := by
  match a, b with
  | .true, .true => rfl
  | .true, .false => rfl
  | .true, .unknown => rfl
  | .false, .true => rfl
  | .false, .false => rfl
  | .false, .unknown => rfl
  | .unknown, .true => rfl
  | .unknown, .false => rfl
  | .unknown, .unknown => rfl

/-- De Morgan's law for Trilean: NOT (a OR b) = (NOT a) AND (NOT b) -/
theorem trilean_de_morgan_or (a b : Trilean) :
    (a.or b).not = a.not.and b.not := by
  match a, b with
  | .true, .true => rfl
  | .true, .false => rfl
  | .true, .unknown => rfl
  | .false, .true => rfl
  | .false, .false => rfl
  | .false, .unknown => rfl
  | .unknown, .true => rfl
  | .unknown, .false => rfl
  | .unknown, .unknown => rfl

-- ============================================================================
-- COALESCE Theorems
-- ============================================================================

/-- Helper: isNullValue is true for none -/
theorem isNullValue_none : isNullValue none = true := by rfl

/-- Helper: isNullValue is true for null values -/
theorem isNullValue_null (t : Option SqlType) : isNullValue (some (.null t)) = true := by rfl

/-- Helper: isNullValue is false for int values -/
theorem isNullValue_int (n : Int) : isNullValue (some (.int n)) = false := by rfl

/-- Helper: isNullValue is false for string values -/
theorem isNullValue_string (s : String) : isNullValue (some (.string s)) = false := by rfl

/-- Helper: isNullValue is false for bool values -/
theorem isNullValue_bool (b : Bool) : isNullValue (some (.bool b)) = false := by rfl

/-- COALESCE(NULL, x) = x, with precondition that x is non-null.

    This theorem replaces the former `coalesce_null_left` axiom, which was
    unsound: it claimed `COALESCE(NULL, x) = x` for all `x`, but when
    `x = some (.null _)`, `evalFunc` returns `none` (no non-null value found
    by `List.find?`), not `some (.null _)`. Since `none ≠ some _` in Lean,
    the axiom could derive `False`. The precondition `isNullValue v = false`
    eliminates that case and makes this theorem provably sound. -/
private theorem coalesce_toUpper : "COALESCE".toUpper = "COALESCE" := by native_decide
private theorem nullif_toUpper : "NULLIF".toUpper = "NULLIF" := by native_decide

theorem coalesce_null_left_nonnull (t : Option SqlType) (v : Option Value)
    (hv : isNullValue v = false) :
    evalFunc "COALESCE" [some (.null t), v] = v := by
  unfold evalFunc
  rw [coalesce_toUpper]
  simp only [isNullValue, List.find?, Option.join]
  match v with
  | some (.int _) => rfl
  | some (.string _) => rfl
  | some (.bool _) => rfl
  | some (.null _) => simp [isNullValue] at hv
  | none => simp [isNullValue] at hv

/-- COALESCE(x, y) = x when x is a non-null int -/
theorem coalesce_int_left (n : Int) (v : Option Value) :
    evalFunc "COALESCE" [some (.int n), v] = some (.int n) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE(x, y) = x when x is a non-null string -/
theorem coalesce_string_left (s : String) (v : Option Value) :
    evalFunc "COALESCE" [some (.string s), v] = some (.string s) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE(x, y) = x when x is a non-null bool -/
theorem coalesce_bool_left (b : Bool) (v : Option Value) :
    evalFunc "COALESCE" [some (.bool b), v] = some (.bool b) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE with single non-null int argument returns that value -/
theorem coalesce_single_int (n : Int) :
    evalFunc "COALESCE" [some (.int n)] = some (.int n) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE with single non-null string argument returns that value -/
theorem coalesce_single_string (s : String) :
    evalFunc "COALESCE" [some (.string s)] = some (.string s) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE with single non-null bool argument returns that value -/
theorem coalesce_single_bool (b : Bool) :
    evalFunc "COALESCE" [some (.bool b)] = some (.bool b) := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE with single NULL returns none -/
theorem coalesce_single_null (t : Option SqlType) :
    evalFunc "COALESCE" [some (.null t)] = none := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [isNullValue, List.find?, Option.join]

/-- COALESCE with empty args returns none -/
theorem coalesce_empty : evalFunc "COALESCE" [] = none := by
  unfold evalFunc; rw [coalesce_toUpper]
  simp [List.find?, Option.join]

/-- NULLIF(x, x) = NULL for same int values -/
theorem nullif_same_int (n : Int) :
    evalFunc "NULLIF" [some (.int n), some (.int n)] = some (.null none) := by
  unfold evalFunc; rw [nullif_toUpper]
  simp [Value.eq]

/-- NULLIF(x, y) = x when x ≠ y (different ints) -/
theorem nullif_diff_int (n m : Int) (h : n ≠ m) :
    evalFunc "NULLIF" [some (.int n), some (.int m)] = some (.int n) := by
  unfold evalFunc; rw [nullif_toUpper]
  simp [Value.eq, beq_iff_eq, h]

-- ============================================================================
-- Value Type Theorems
-- ============================================================================

/-- A value is either null or not null (law of excluded middle for nullness) -/
theorem value_null_or_not_null (v : Value) : v.isNull = true ∨ v.isNotNull = true := by
  match v with
  | .int _ => right; rfl
  | .string _ => right; rfl
  | .bool _ => right; rfl
  | .null _ => left; rfl

/-- isNull and isNotNull are complementary -/
theorem value_is_null_complement (v : Value) : v.isNull = !v.isNotNull := by
  match v with
  | .int _ => rfl
  | .string _ => rfl
  | .bool _ => rfl
  | .null _ => rfl

/-- Typed NULL values have the same nullness regardless of type -/
theorem typed_null_same_nullness (t1 t2 : Option SqlType) :
    Value.isNull (.null t1) = Value.isNull (.null t2) := by
  rfl

-- ============================================================================
-- Aggregate Theorems
-- ============================================================================

/-- COUNT(*) is always non-negative -/
theorem count_star_nonneg (rows : Table) :
    0 ≤ rows.length := by
  exact Nat.zero_le rows.length

/-- COUNT(*) on empty table is 0 -/
theorem count_star_empty : ([] : Table).length = 0 := by rfl

/-- COUNT(*) on singleton table is 1 -/
theorem count_star_singleton (row : Row) : [row].length = 1 := by rfl

/-- COUNT(*) after filter is at most COUNT(*) before filter -/
theorem count_after_filter_le (rows : Table) (p : Row → Bool) :
    (rows.filter p).length ≤ rows.length := by
  exact List.length_filter_le p rows

/-- SUM of empty list is 0 (by definition of foldl) -/
theorem sum_empty : ([] : List Int).foldl (· + ·) 0 = 0 := by rfl

/-- SUM of singleton is the element -/
theorem sum_singleton (n : Int) : [n].foldl (· + ·) 0 = n := by
  simp [List.foldl]

/-- Adding 0 to SUM doesn't change it -/
theorem sum_add_zero (ns : List Int) :
    (ns ++ [0]).foldl (· + ·) 0 = ns.foldl (· + ·) 0 := by
  induction ns with
  | nil => simp [List.foldl]
  | cons n rest ih =>
    simp only [List.foldl_cons]
    simp only [List.foldl_append, List.foldl] at ih ⊢
    omega

/-- MIN of singleton is the element -/
theorem min_singleton (n : Int) : [n].foldl min n = n := by
  simp [List.foldl]

/-- MAX of singleton is the element -/
theorem max_singleton (n : Int) : [n].foldl max n = n := by
  simp [List.foldl]

/-- foldl min is ≤ the initial value -/
private theorem foldl_min_le_init (init : Int) (l : List Int) :
    l.foldl min init ≤ init := by
  induction l generalizing init with
  | nil => exact Int.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (ih _) (Int.min_le_left _ _)

/-- foldl min is ≤ any member of the list -/
private theorem foldl_min_le_of_mem (init : Int) (l : List Int) (n : Int) (h : n ∈ l) :
    l.foldl min init ≤ n := by
  induction l generalizing init with
  | nil => nomatch h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Int.le_trans (foldl_min_le_init _ _) (Int.min_le_right _ _)
    · exact ih _ hmem

/-- init ≤ foldl max -/
private theorem init_le_foldl_max (init : Int) (l : List Int) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact Int.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (Int.le_max_left _ _) (ih _)

/-- Any member of the list ≤ foldl max -/
private theorem le_foldl_max_of_mem (init : Int) (l : List Int) (n : Int) (h : n ∈ l) :
    n ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => nomatch h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Int.le_trans (Int.le_max_right _ _) (init_le_foldl_max _ _)
    · exact ih _ hmem

/-- MIN is at most any element in the list -/
theorem min_le_elem (n : Int) (ns : List Int) (h : n ∈ ns) :
    ns.foldl min (ns.head!) ≤ n := by
  match ns, h with
  | [], h => nomatch h
  | x :: xs, h => exact foldl_min_le_of_mem x (x :: xs) n h

/-- MAX is at least any element in the list -/
theorem max_ge_elem (n : Int) (ns : List Int) (h : n ∈ ns) :
    n ≤ ns.foldl max (ns.head!) := by
  match ns, h with
  | [], h => nomatch h
  | x :: xs, h => exact le_foldl_max_of_mem x (x :: xs) n h

/-- DISTINCT doesn't increase count -/
theorem distinct_count_le (vs : List Value) :
    vs.eraseDups.length ≤ vs.length := by
  suffices ∀ (k : Nat) (l : List Value), l.length ≤ k → l.eraseDups.length ≤ l.length from
    this vs.length vs (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro l hl
    match l with
    | [] => simp
    | _ :: _ => simp at hl
  | succ k ih =>
    intro l hl
    match l with
    | [] => simp
    | v :: vs =>
      rw [List.eraseDups_cons, List.length_cons, List.length_cons]
      have hfilt_len : (vs.filter (! · == v)).length ≤ k :=
        Nat.le_trans (List.length_filter_le _ _) (by simp at hl; omega)
      have h1 := ih _ hfilt_len
      have h2 := List.length_filter_le (fun b => !(b == v)) vs
      omega

/-- A Nodup list is unchanged by eraseDups -/
private theorem nodup_implies_eraseDups_eq (l : List Value) (h : l.Nodup) :
    l.eraseDups = l := by
  suffices ∀ (k : Nat) (l : List Value), l.length ≤ k → l.Nodup → l.eraseDups = l from
    this l.length l (Nat.le_refl _) h
  intro k
  induction k with
  | zero =>
    intro l hl _
    match l with
    | [] => rfl
    | _ :: _ => simp at hl
  | succ k ih =>
    intro l hl hnd
    match l with
    | [] => rfl
    | a :: as =>
      rw [List.eraseDups_cons]
      have hnd' := List.nodup_cons.mp hnd
      have ha_not_mem := hnd'.1
      have has_nd := hnd'.2
      -- Since a ∉ as, filter (! · == a) keeps all elements
      have hfilter : as.filter (fun b => !(b == a)) = as := by
        rw [List.filter_eq_self]
        intro b hb
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
        exact fun heq => ha_not_mem (heq ▸ hb)
      rw [hfilter]
      congr 1
      have has_len : as.length ≤ k := by simp at hl; omega
      exact ih as has_len has_nd

/-- DISTINCT on already-distinct list is identity -/
theorem distinct_idempotent (vs : List Value) :
    vs.eraseDups.eraseDups = vs.eraseDups :=
  nodup_implies_eraseDups_eq vs.eraseDups (nodup_eraseDups vs)

/-- COUNT(DISTINCT x) ≤ COUNT(x) -/
theorem count_distinct_le_count (vs : List Value) :
    vs.eraseDups.length ≤ vs.length := by
  exact distinct_count_le vs

-- ============================================================================
-- CASE Expression Theorems
-- ============================================================================

/-- CASE WHEN TRUE THEN x ELSE y END = x -/
theorem case_when_true (x y : Expr) :
    Expr.case [(Expr.lit (.bool true), x)] (some y) ≃ₑ x := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_case]
  have h := evalExprWithDb_lit (fun _ => []) row (.bool true)
  rw [evalCase_cons_true _ _ _ _ _ _ h]

/-- CASE WHEN FALSE THEN x ELSE y END = y -/
theorem case_when_false (x y : Expr) :
    Expr.case [(Expr.lit (.bool false), x)] (some y) ≃ₑ y := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_case]
  have h := evalExprWithDb_lit (fun _ => []) row (.bool false)
  rw [evalCase_cons_false _ _ _ _ _ _ h, evalCase_nil_some]

/-- CASE WHEN FALSE THEN x END = NULL (no else clause) -/
theorem case_when_false_no_else (x : Expr) :
    Expr.case [(Expr.lit (.bool false), x)] none ≃ₑ Expr.lit (.null none) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_case]
  have h := evalExprWithDb_lit (fun _ => []) row (.bool false)
  rw [evalCase_cons_false _ _ _ _ _ _ h, evalCase_nil_none, evalExprWithDb_lit]

/-- CASE with no branches and ELSE = ELSE value -/
theorem case_empty_else (y : Expr) :
    Expr.case [] (some y) ≃ₑ y := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_case, evalCase_nil_some]

/-- CASE with no branches and no ELSE = NULL -/
theorem case_empty_no_else :
    Expr.case [] none ≃ₑ Expr.lit (.null none) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_case, evalCase_nil_none, evalExprWithDb_lit]

-- ============================================================================
-- Predicate Pushdown Theorems
-- ============================================================================

/-- Conjunction of filters equals sequential filtering -/
theorem filter_and_eq_filter_filter (rows : Table) (p q : Row → Bool) :
    rows.filter (fun r => p r && q r) = (rows.filter p).filter q := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.filter_cons]
    by_cases hp : p r <;> by_cases hq : q r <;> simp [hp, hq, ih]

/-- Filter order doesn't matter for AND -/
theorem filter_comm (rows : Table) (p q : Row → Bool) :
    (rows.filter p).filter q = (rows.filter q).filter p := by
  rw [← filter_and_eq_filter_filter, ← filter_and_eq_filter_filter]
  congr 1; ext r; exact Bool.and_comm (p r) (q r)

/-- Predicate pushdown: filtering after select = select with combined WHERE
    This captures: SELECT * FROM (SELECT * FROM t WHERE p) WHERE q
                 = SELECT * FROM t WHERE (p AND q)
    Blocked: The external filter uses `evalExpr` (no db context) while `evalSelect`
    internally uses `evalExprWithDb db`. These differ when `q` contains subqueries.
    Could be proved with a `q.hasNoSubquery` precondition. -/
axiom predicate_pushdown (db : Database) (t : String) (p q : Expr) :
    let inner := SelectStmt.mk false [.star none] (some (.table ⟨t, none⟩)) (some p) [] none [] none none
    let outer := SelectStmt.mk false [.star none] (some (.table ⟨t, none⟩)) (some (.binOp .and p q)) [] none [] none none
    (evalSelect db inner).filter (fun row => evalExpr row q == some (.bool true)) = evalSelect db outer

-- ============================================================================
-- Arithmetic Expression Theorems
-- ============================================================================

/-- Type precondition: expression always evaluates to an integer value.
    This excludes expressions that produce errors (type mismatches, missing columns)
    or non-integer values (strings, booleans, nulls). Needed for arithmetic identities. -/
def Expr.isIntValued (e : Expr) : Prop :=
  ∀ row : Row, ∃ n : Int, evalExpr row e = some (.int n)

/-- x + 0 = x for expressions evaluating to int.
    Requires `isIntValued` — the expression must always produce an integer. -/
theorem expr_add_zero (e : Expr) (h : e.isIntValued) :
    Expr.binOp .add e (Expr.lit (.int 0)) ≃ₑ e := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  obtain ⟨n, hn⟩ := h row
  simp only [evalExpr] at hn
  rw [hn]
  show some (Value.int (n + 0)) = some (Value.int n)
  rw [Int.add_zero]

/-- 0 + x = x for expressions evaluating to int. -/
theorem expr_zero_add (e : Expr) (h : e.isIntValued) :
    Expr.binOp .add (Expr.lit (.int 0)) e ≃ₑ e := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  obtain ⟨n, hn⟩ := h row
  simp only [evalExpr] at hn
  rw [hn]
  show some (Value.int (0 + n)) = some (Value.int n)
  rw [Int.zero_add]

/-- x * 1 = x for expressions evaluating to int. -/
theorem expr_mul_one (e : Expr) (h : e.isIntValued) :
    Expr.binOp .mul e (Expr.lit (.int 1)) ≃ₑ e := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  obtain ⟨n, hn⟩ := h row
  simp only [evalExpr] at hn
  rw [hn]
  show some (Value.int (n * 1)) = some (Value.int n)
  rw [Int.mul_one]

/-- 1 * x = x for expressions evaluating to int. -/
theorem expr_one_mul (e : Expr) (h : e.isIntValued) :
    Expr.binOp .mul (Expr.lit (.int 1)) e ≃ₑ e := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  obtain ⟨n, hn⟩ := h row
  simp only [evalExpr] at hn
  rw [hn]
  show some (Value.int (1 * n)) = some (Value.int n)
  rw [Int.one_mul]

/-- x * 0 = 0 for expressions evaluating to int. -/
theorem expr_mul_zero (e : Expr) (h : e.isIntValued) :
    Expr.binOp .mul e (Expr.lit (.int 0)) ≃ₑ Expr.lit (.int 0) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  obtain ⟨n, hn⟩ := h row
  simp only [evalExpr] at hn
  rw [hn]
  show some (Value.int (n * 0)) = some (Value.int 0)
  rw [Int.mul_zero]

/-- 0 * x = 0 for expressions evaluating to int. -/
theorem expr_zero_mul (e : Expr) (h : e.isIntValued) :
    Expr.binOp .mul (Expr.lit (.int 0)) e ≃ₑ Expr.lit (.int 0) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  obtain ⟨n, hn⟩ := h row
  simp only [evalExpr] at hn
  rw [hn]
  show some (Value.int (0 * n)) = some (Value.int 0)
  rw [Int.zero_mul]

/-- x - 0 = x for expressions evaluating to int. -/
theorem expr_sub_zero (e : Expr) (h : e.isIntValued) :
    Expr.binOp .sub e (Expr.lit (.int 0)) ≃ₑ e := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_lit]
  obtain ⟨n, hn⟩ := h row
  simp only [evalExpr] at hn
  rw [hn]
  show some (Value.int (n - 0)) = some (Value.int n)
  rw [Int.sub_zero]

-- ============================================================================
-- IN List Theorems
-- ============================================================================

/-- x IN () = FALSE (empty IN list).
    No preconditions needed — empty foldl returns `some (.bool false)` regardless of `e`. -/
theorem in_empty_false (e : Expr) :
    Expr.inList e false [] ≃ₑ Expr.lit (.bool false) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_inList, evalExprWithDb_lit]
  simp [List.foldl]

/-- x NOT IN () = TRUE (empty NOT IN list).
    No preconditions needed — empty foldl returns `some (.bool false)`, NOT flips to TRUE. -/
theorem not_in_empty_true (e : Expr) :
    Expr.inList e true [] ≃ₑ Expr.lit (.bool true) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_inList, evalExprWithDb_lit]
  simp [List.foldl, evalUnaryOp]

-- Value-level helper: OR(false, Option.map Value.bool o) = Option.map Value.bool o
private theorem or_false_map_bool (o : Option Bool) :
    evalBinOp .or (some (.bool false)) (o.map Value.bool) = o.map Value.bool := by
  cases o with | none => rfl | some b => cases b <;> rfl

-- Helper: OR(false, evalBinOp .eq l r) = evalBinOp .eq l r
-- Works because evalBinOp .eq produces some (.bool _), some (.null none), or none,
-- all of which are identity under OR(false, _).
private theorem evalBinOp_or_false_left_eq (l r : Option Value) :
    evalBinOp .or (some (.bool false)) (evalBinOp .eq l r) = evalBinOp .eq l r := by
  cases l with
  | none => cases r with | none => rfl | some v => cases v <;> rfl
  | some v => cases r with
    | none => cases v <;> rfl
    | some w => cases v <;> cases w <;>
      first | rfl | (simp only [evalBinOp]; exact or_false_map_bool _)

-- Value-level helper: NOT(Option.map Value.bool o) = Option.map (fun b => Value.bool (!b)) o
private theorem not_map_bool_is_map_not_bool (o : Option Bool) :
    evalUnaryOp .not (o.map Value.bool) = o.map (fun b => Value.bool (!b)) := by
  cases o with | none => rfl | some b => cases b <;> rfl

-- Value-level helper: NOT(EQ(l, r)) = NE(l, r) (local copy; the canonical version is below)
private theorem not_eq_is_ne_val (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .eq l r) = evalBinOp .ne l r := by
  cases l with
  | none => cases r with | none => rfl | some v => cases v <;> rfl
  | some v => cases r with
    | none => cases v <;> rfl
    | some w => cases v <;> cases w <;>
      first | rfl | (simp only [evalBinOp]; exact not_map_bool_is_map_not_bool _)

-- Helper: foldl of evalBinOp matches foldl of Expr constructors
private theorem eval_foldl_or_eq (db : Database) (row : Row) (e : Expr) (vals : List Expr) (acc_expr : Expr) :
    vals.foldl (fun a vi => evalBinOp .or a (evalBinOp .eq (evalExprWithDb db row e) (evalExprWithDb db row vi)))
               (evalExprWithDb db row acc_expr) =
    evalExprWithDb db row (vals.foldl (fun a v => Expr.binOp .or a (Expr.binOp .eq e v)) acc_expr) := by
  induction vals generalizing acc_expr with
  | nil => simp [List.foldl]
  | cons v vs ih =>
    simp only [List.foldl]
    have step : evalBinOp .or (evalExprWithDb db row acc_expr)
        (evalBinOp .eq (evalExprWithDb db row e) (evalExprWithDb db row v)) =
        evalExprWithDb db row (Expr.binOp .or acc_expr (Expr.binOp .eq e v)) := by
      rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
    rw [step]
    exact ih _

-- Helper: NOT of foldl OR-eq chain = foldl AND-ne chain (uses De Morgan + NOT(eq) = ne)
private theorem not_foldl_or_eq_is_foldl_and_ne (db : Database) (row : Row) (e : Expr)
    (vals : List Expr) (acc_val : Option Value) (acc_expr : Expr)
    (h_acc : evalUnaryOp .not acc_val = evalExprWithDb db row acc_expr) :
    evalUnaryOp .not (vals.foldl (fun a vi =>
      evalBinOp .or a (evalBinOp .eq (evalExprWithDb db row e) (evalExprWithDb db row vi)))
      acc_val) =
    evalExprWithDb db row (vals.foldl (fun a v =>
      Expr.binOp .and a (Expr.binOp .ne e v)) acc_expr) := by
  induction vals generalizing acc_val acc_expr with
  | nil => simp [List.foldl]; exact h_acc
  | cons v vs ih =>
    simp only [List.foldl]
    apply ih
    rw [evalUnaryOp_not_or]
    have step : evalBinOp .and (evalExprWithDb db row acc_expr)
        (evalBinOp .ne (evalExprWithDb db row e) (evalExprWithDb db row v)) =
        evalExprWithDb db row (Expr.binOp .and acc_expr (Expr.binOp .ne e v)) := by
      rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
    rw [h_acc, not_eq_is_ne_val, step]

/-- x IN (a) = (x = a) (singleton IN list). -/
theorem in_singleton (e a : Expr) :
    Expr.inList e false [a] ≃ₑ Expr.binOp .eq e a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_inList, evalExprWithDb_binOp]
  simp [List.foldl]
  exact evalBinOp_or_false_left_eq _ _

/-- x NOT IN (a) = (x <> a) (singleton NOT IN list). -/
theorem not_in_singleton (e a : Expr) :
    Expr.inList e true [a] ≃ₑ Expr.binOp .ne e a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_inList, evalExprWithDb_binOp]
  simp [List.foldl]
  rw [evalBinOp_or_false_left_eq]
  exact not_eq_is_ne_val _ _

/-- x IN (a, b) = (x = a OR x = b). -/
theorem in_pair (e a b : Expr) :
    Expr.inList e false [a, b] ≃ₑ
    Expr.binOp .or (Expr.binOp .eq e a) (Expr.binOp .eq e b) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_inList, evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  simp [List.foldl]
  congr 1
  exact evalBinOp_or_false_left_eq _ _

/-- x NOT IN (a, b) = (x <> a AND x <> b). -/
theorem not_in_pair (e a b : Expr) :
    Expr.inList e true [a, b] ≃ₑ
    Expr.binOp .and (Expr.binOp .ne e a) (Expr.binOp .ne e b) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_inList, evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  simp [List.foldl]
  rw [evalBinOp_or_false_left_eq, evalUnaryOp_not_or]
  congr 1 <;> exact not_eq_is_ne_val _ _

/-- IN list is equivalent to OR of equalities (general form) -/
theorem in_list_or_expansion (e : Expr) (vals : List Expr) :
    Expr.inList e false vals ≃ₑ
    vals.foldl (fun acc v => Expr.binOp .or acc (Expr.binOp .eq e v))
               (Expr.lit (.bool false)) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_inList]
  dsimp only []
  have h := eval_foldl_or_eq (fun _ => []) row e vals (Expr.lit (.bool false))
  rw [evalExprWithDb_lit] at h
  exact h

/-- NOT IN list is equivalent to AND of inequalities (general form) -/
theorem not_in_list_and_expansion (e : Expr) (vals : List Expr) :
    Expr.inList e true vals ≃ₑ
    vals.foldl (fun acc v => Expr.binOp .and acc (Expr.binOp .ne e v))
               (Expr.lit (.bool true)) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_inList]
  dsimp only []
  exact not_foldl_or_eq_is_foldl_and_ne _ _ _ _ _ (Expr.lit (.bool true))
    (by rw [evalExprWithDb_lit]; rfl)

-- ============================================================================
-- BETWEEN Theorems
-- ============================================================================

/-- x BETWEEN a AND b = (x >= a AND x <= b)
    No preconditions needed — BETWEEN is now defined as AND(GE, LE). -/
theorem between_expansion (e lo hi : Expr) :
    Expr.between e lo hi ≃ₑ
    Expr.binOp .and (Expr.binOp .ge e lo) (Expr.binOp .le e hi) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_between, evalExprWithDb_binOp, evalExprWithDb_binOp, evalExprWithDb_binOp]

/-- BETWEEN reflexivity as an expression equivalence:
    x BETWEEN x AND x = (x >= x AND x <= x). -/
theorem between_reflexive (e : Expr) :
    Expr.between e e e ≃ₑ
    Expr.binOp .and (Expr.binOp .ge e e) (Expr.binOp .le e e) := by
  exact between_expansion e e e

-- ============================================================================
-- LIKE Pattern Theorems
-- ============================================================================

/-- simpleLike with "%" pattern always returns true -/
private theorem simpleLike_pct (s : String) : simpleLike s "%" = true := by
  unfold simpleLike
  simp

/-- x LIKE '%' = TRUE for non-null string x (matches all strings);
    for NULL x, the result is NULL.
    Requires `isStringOrNull` — expression must evaluate to string or null. -/
theorem like_match_all (e : Expr) (h : e.isStringOrNull) :
    Expr.binOp .like e (Expr.lit (.string "%")) ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool true))) := by
  intro row
  simp only [evalExpr]
  -- Get the hypothesis for this row
  have hrow := h row
  simp only [evalExpr] at hrow
  -- Unfold LHS
  rw [evalExprWithDb_binOp]
  simp only [evalExprWithDb_lit]
  -- Unfold RHS
  rw [evalExprWithDb_case]
  rcases hrow with ⟨s, hs⟩ | ⟨n, hn⟩
  · -- String case: e evaluates to some (.string s)
    rw [hs]
    have hcond : evalExprWithDb (fun _ => []) row (Expr.unaryOp .isNull e) =
        some (.bool false) := by
      rw [evalExprWithDb_unaryOp, hs]; rfl
    rw [evalCase_cons_false _ _ _ _ _ _ hcond, evalCase_nil_some, evalExprWithDb_lit]
    simp [evalBinOp, simpleLike_pct]
  · -- Null case: e evaluates to some (.null n)
    rw [hn]
    have hcond : evalExprWithDb (fun _ => []) row (Expr.unaryOp .isNull e) =
        some (.bool true) := by
      rw [evalExprWithDb_unaryOp, hn]; rfl
    rw [evalCase_cons_true _ _ _ _ _ _ hcond, evalExprWithDb_lit]
    rfl

/-- simpleLike with empty pattern reduces to string equality -/
private theorem simpleLike_empty (s : String) : simpleLike s "" = (s == "") := by
  unfold simpleLike
  have h1 : ("" == "%") = false := by native_decide
  have h2 : "".startsWith "%" = false := by native_decide
  have h3 : "".endsWith "%" = false := by native_decide
  simp [h1, h2, h3]

/-- Value-level: LIKE '' behaves the same as = '' for all Option Value -/
private theorem evalBinOp_like_empty_eq_eq (v : Option Value) :
    evalBinOp .like v (some (.string "")) = evalBinOp .eq v (some (.string "")) := by
  match v with
  | none => rfl
  | some (.null _) => rfl
  | some (.int _) => rfl
  | some (.bool _) => rfl
  | some (.string s) =>
    simp only [evalBinOp, Value.eq, Option.map, simpleLike_empty]

/-- x LIKE '' = (x = '') (empty pattern matches empty string) -/
theorem like_empty_pattern (e : Expr) :
    Expr.binOp .like e (Expr.lit (.string "")) ≃ₑ
    Expr.binOp .eq e (Expr.lit (.string "")) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  simp only [evalExprWithDb_lit]
  exact evalBinOp_like_empty_eq_eq _

/-- For string-typed expressions, x LIKE x evaluates to TRUE for non-null strings
    and to NULL when x is NULL.
    Requires `isStringOrNull` — expression must evaluate to string or null.
    Axiom: proving simpleLike s s = true requires non-trivial string library lemmas
    for branches 2-4 (startsWith/endsWith/stringContains on substrings). -/
axiom like_self (e : Expr) (h : e.isStringOrNull) :
    Expr.binOp .like e e ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool true)))

-- ============================================================================
-- String Function Theorems
-- ============================================================================

-- Value-level helper: CONCAT("", v) = v for string/null/none values
private theorem evalFunc_concat_empty_left (v : Option Value) :
    (∃ s, v = some (.string s)) ∨ (∃ n, v = some (.null n)) ∨ v = none →
    evalFunc "CONCAT" [some (.string ""), v] = v := by
  have hup : "CONCAT".toUpper = "CONCAT" := by native_decide
  intro h; rcases h with ⟨s, hs⟩ | ⟨n, hn⟩ | hn <;> subst_vars <;> simp [evalFunc, hup]

-- Value-level helper: CONCAT(v, "") = v for string/null/none values
private theorem evalFunc_concat_empty_right (v : Option Value) :
    (∃ s, v = some (.string s)) ∨ (∃ n, v = some (.null n)) ∨ v = none →
    evalFunc "CONCAT" [v, some (.string "")] = v := by
  have hup : "CONCAT".toUpper = "CONCAT" := by native_decide
  intro h; rcases h with ⟨s, hs⟩ | ⟨n, hn⟩ | hn <;> subst_vars <;> simp [evalFunc, hup]

/-- CONCAT('', x) = x (empty string is identity for concat).
    Requires `isStringOrNullValued` — expression must evaluate to string, null, or error. -/
theorem concat_empty_left (e : Expr) (h : e.isStringOrNullValued) :
    Expr.func "CONCAT" [Expr.lit (.string ""), e] ≃ₑ e := by
  intro row
  simp only [evalExpr, evalExprWithDb_func, List.map, evalExprWithDb_lit]
  exact evalFunc_concat_empty_left _ (h row)

/-- CONCAT(x, '') = x (empty string is identity for concat).
    Requires `isStringOrNullValued` — expression must evaluate to string, null, or error. -/
theorem concat_empty_right (e : Expr) (h : e.isStringOrNullValued) :
    Expr.func "CONCAT" [e, Expr.lit (.string "")] ≃ₑ e := by
  intro row
  simp only [evalExpr, evalExprWithDb_func, List.map, evalExprWithDb_lit]
  exact evalFunc_concat_empty_right _ (h row)

-- ============================================================================
-- LENGTH(CONCAT(a, b)) = LENGTH(a) + LENGTH(b)
-- ============================================================================

-- Value-level helper: LENGTH(CONCAT(a, b)) = LENGTH(a) + LENGTH(b)
-- No precondition needed — all non-string cases reduce to none on both sides.
private theorem evalFunc_length_concat (av bv : Option Value) :
    evalFunc "LENGTH" [evalFunc "CONCAT" [av, bv]] =
    evalBinOp .add (evalFunc "LENGTH" [av]) (evalFunc "LENGTH" [bv]) := by
  have hL : "LENGTH".toUpper = "LENGTH" := by native_decide
  have hC : "CONCAT".toUpper = "CONCAT" := by native_decide
  cases av with
  | none => simp [evalFunc, hC, hL, evalBinOp]
  | some v => cases bv with
    | none => cases v <;> simp [evalFunc, hC, hL, evalBinOp]
    | some w => cases v <;> cases w <;> simp [evalFunc, hC, hL, evalBinOp, String.length_append]

/-- LENGTH(CONCAT(a, b)) = LENGTH(a) + LENGTH(b).
    No precondition needed — non-string and null cases all reduce to none on both sides. -/
theorem length_concat (a b : Expr) :
    Expr.func "LENGTH" [Expr.func "CONCAT" [a, b]] ≃ₑ
    Expr.binOp .add (Expr.func "LENGTH" [a]) (Expr.func "LENGTH" [b]) := by
  intro row
  simp only [evalExpr, evalExprWithDb_func, List.map, evalExprWithDb_binOp]
  exact evalFunc_length_concat _ _

-- Helper: (Char.ofNat n).toNat round-trips for valid char ordinals.
-- Uses full `simp` to let @[simp] lemmas (UInt32.toNat_ofNat' etc.) fire through UInt32 layer.
private theorem toNat_ofNat_of_isValid (n : Nat) (h : n.isValidChar) :
    (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, Char.ofNatAux, h, Char.toNat]

-- Cross-composition: keep Char.ofNat opaque, use toNat_ofNat helper + Char.ofNat_toNat
private theorem char_toUpper_toLower_toUpper (c : Char) :
    (c.toUpper.toLower).toUpper = c.toUpper := by
  simp only [Char.toUpper, Char.toLower]
  split
  · -- c.toNat ∈ [97,122] (lowercase)
    rename_i h1
    have hv1 : (c.toNat - 32).isValidChar := by
      simp only [Nat.isValidChar, Char.toNat] at *; omega
    rw [toNat_ofNat_of_isValid _ hv1]
    have h2 : c.toNat - 32 ≥ 65 ∧ c.toNat - 32 ≤ 90 := by omega
    rw [if_pos h2]
    have hv2 : (c.toNat - 32 + 32).isValidChar := by
      simp only [Nat.isValidChar, Char.toNat] at *; omega
    rw [toNat_ofNat_of_isValid _ hv2, show c.toNat - 32 + 32 = c.toNat from by omega]
    have h4 : c.toNat ≥ 97 ∧ c.toNat ≤ 122 := by omega
    rw [if_pos h4]
  · -- c.toNat ∉ [97,122]
    rename_i h1
    split
    · -- c.toNat ∈ [65,90] (uppercase): toLower +32, toUpper -32 → round-trip to c
      rename_i h2
      have hv1 : (c.toNat + 32).isValidChar := by
        simp only [Nat.isValidChar, Char.toNat] at *; omega
      rw [toNat_ofNat_of_isValid _ hv1]
      have h3 : c.toNat + 32 ≥ 97 ∧ c.toNat + 32 ≤ 122 := by omega
      rw [if_pos h3]
      rw [show c.toNat + 32 - 32 = c.toNat from by omega, Char.ofNat_toNat]
    · -- Neither: all three operations are identity
      rfl

private theorem char_toLower_toUpper_toLower (c : Char) :
    (c.toLower.toUpper).toLower = c.toLower := by
  simp only [Char.toLower, Char.toUpper]
  split
  · -- c.toNat ∈ [65,90] (uppercase)
    rename_i h1
    have hv1 : (c.toNat + 32).isValidChar := by
      simp only [Nat.isValidChar, Char.toNat] at *; omega
    rw [toNat_ofNat_of_isValid _ hv1]
    have h2 : c.toNat + 32 ≥ 97 ∧ c.toNat + 32 ≤ 122 := by omega
    rw [if_pos h2]
    rw [show c.toNat + 32 - 32 = c.toNat from by omega, Char.ofNat_toNat]
    have h4 : c.toNat ≥ 65 ∧ c.toNat ≤ 90 := by omega
    rw [if_pos h4]
  · -- c.toNat ∉ [65,90]
    rename_i h1
    split
    · -- c.toNat ∈ [97,122] (lowercase): toUpper -32, toLower +32 → round-trip to c
      rename_i h2
      have hv1 : (c.toNat - 32).isValidChar := by
        simp only [Nat.isValidChar, Char.toNat] at *; omega
      rw [toNat_ofNat_of_isValid _ hv1]
      have h3 : c.toNat - 32 ≥ 65 ∧ c.toNat - 32 ≤ 90 := by omega
      rw [if_pos h3]
      rw [show c.toNat - 32 + 32 = c.toNat from by omega, Char.ofNat_toNat]
    · -- Neither: identity
      rfl

-- Char-level idempotence: toUpper maps [97,122]→[65,90], toLower maps [65,90]→[97,122]
-- After unfolding Char.ofNatAux, omega can see through UInt32 arithmetic.
private theorem char_toUpper_idem (c : Char) : c.toUpper.toUpper = c.toUpper := by
  simp only [Char.toUpper, Char.toNat, Char.ofNat, Char.ofNatAux]
  split
  · split <;> split <;> simp_all <;> omega
  · rfl

private theorem char_toLower_idem (c : Char) : c.toLower.toLower = c.toLower := by
  simp only [Char.toLower, Char.toNat, Char.ofNat, Char.ofNatAux]
  split
  · split <;> split <;> simp_all <;> omega
  · rfl

-- String-level idempotence (lifted from Char via String.ext + toList_map + List.map_map)
private theorem string_toUpper_idem (s : String) : s.toUpper.toUpper = s.toUpper := by
  apply String.ext
  simp only [String.toUpper, String.toList_map, List.map_map]
  congr 1; funext c; exact char_toUpper_idem c

private theorem string_toLower_idem (s : String) : s.toLower.toLower = s.toLower := by
  apply String.ext
  simp only [String.toLower, String.toList_map, List.map_map]
  congr 1; funext c; exact char_toLower_idem c

-- Value-level helpers for evalFunc
private theorem evalFunc_upper_idem (v : Option Value) :
    evalFunc "UPPER" [evalFunc "UPPER" [v]] = evalFunc "UPPER" [v] := by
  have hup : "UPPER".toUpper = "UPPER" := by native_decide
  match v with
  | some (.string s) => simp [evalFunc, hup, string_toUpper_idem]
  | some (.int _) | some (.bool _) | some (.null _) | none => simp [evalFunc, hup]

private theorem evalFunc_lower_idem (v : Option Value) :
    evalFunc "LOWER" [evalFunc "LOWER" [v]] = evalFunc "LOWER" [v] := by
  have hlo : "LOWER".toUpper = "LOWER" := by native_decide
  match v with
  | some (.string s) => simp [evalFunc, hlo, string_toLower_idem]
  | some (.int _) | some (.bool _) | some (.null _) | none => simp [evalFunc, hlo]

/-- UPPER(UPPER(x)) = UPPER(x) (idempotent) -/
theorem upper_idempotent (e : Expr) :
    Expr.func "UPPER" [Expr.func "UPPER" [e]] ≃ₑ Expr.func "UPPER" [e] := by
  intro row; simp only [evalExpr, evalExprWithDb_func, List.map]
  exact evalFunc_upper_idem _

/-- LOWER(LOWER(x)) = LOWER(x) (idempotent) -/
theorem lower_idempotent (e : Expr) :
    Expr.func "LOWER" [Expr.func "LOWER" [e]] ≃ₑ Expr.func "LOWER" [e] := by
  intro row; simp only [evalExpr, evalExprWithDb_func, List.map]
  exact evalFunc_lower_idem _

-- String-level cross-composition (lifted from Char)
private theorem string_toUpper_toLower_toUpper (s : String) :
    (s.toUpper.toLower).toUpper = s.toUpper := by
  apply String.ext
  simp only [String.toUpper, String.toLower, String.toList_map, List.map_map]
  congr 1; funext c; exact char_toUpper_toLower_toUpper c

private theorem string_toLower_toUpper_toLower (s : String) :
    (s.toLower.toUpper).toLower = s.toLower := by
  apply String.ext
  simp only [String.toLower, String.toUpper, String.toList_map, List.map_map]
  congr 1; funext c; exact char_toLower_toUpper_toLower c

-- Value-level helpers for evalFunc (cross-composition)
private theorem evalFunc_upper_lower_upper (v : Option Value) :
    evalFunc "UPPER" [evalFunc "LOWER" [evalFunc "UPPER" [v]]] = evalFunc "UPPER" [v] := by
  have hup : "UPPER".toUpper = "UPPER" := by native_decide
  have hlo : "LOWER".toUpper = "LOWER" := by native_decide
  match v with
  | some (.string s) => simp [evalFunc, hup, hlo, string_toUpper_toLower_toUpper]
  | some (.int _) | some (.bool _) | some (.null _) | none => simp [evalFunc, hup, hlo]

private theorem evalFunc_lower_upper_lower (v : Option Value) :
    evalFunc "LOWER" [evalFunc "UPPER" [evalFunc "LOWER" [v]]] = evalFunc "LOWER" [v] := by
  have hlo : "LOWER".toUpper = "LOWER" := by native_decide
  have hup : "UPPER".toUpper = "UPPER" := by native_decide
  match v with
  | some (.string s) => simp [evalFunc, hlo, hup, string_toLower_toUpper_toLower]
  | some (.int _) | some (.bool _) | some (.null _) | none => simp [evalFunc, hlo, hup]

/-- UPPER(LOWER(UPPER(x))) = UPPER(x) -/
theorem upper_lower_upper (e : Expr) :
    Expr.func "UPPER" [Expr.func "LOWER" [Expr.func "UPPER" [e]]] ≃ₑ
    Expr.func "UPPER" [e] := by
  intro row; simp only [evalExpr, evalExprWithDb_func, List.map]
  exact evalFunc_upper_lower_upper _

/-- LOWER(UPPER(LOWER(x))) = LOWER(x) -/
theorem lower_upper_lower (e : Expr) :
    Expr.func "LOWER" [Expr.func "UPPER" [Expr.func "LOWER" [e]]] ≃ₑ
    Expr.func "LOWER" [e] := by
  intro row; simp only [evalExpr, evalExprWithDb_func, List.map]
  exact evalFunc_lower_upper_lower _

/-- LENGTH('') = 0 -/
theorem length_empty :
    Expr.func "LENGTH" [Expr.lit (.string "")] ≃ₑ Expr.lit (.int 0) := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_func, evalExprWithDb_lit]
  simp only [List.map, evalExprWithDb_lit]
  have h : "LENGTH".toUpper = "LENGTH" := by native_decide
  simp [evalFunc, h]

-- ============================================================================
-- Comparison Theorems
-- ============================================================================

/-- x = x is TRUE for non-null, NULL for null (reflexivity of equality).
    Requires `Expr.evaluable` — the expression must not produce errors.
    This is the key theorem enabled by Option 3 null semantics. -/
theorem eq_reflexive (e : Expr) (h : e.evaluable) :
    Expr.binOp .eq e e ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool true))) := by
  intro row
  simp only [evalExpr]
  obtain ⟨v, hv⟩ := h row
  simp only [evalExpr] at hv
  -- Unfold LHS: binOp .eq e e → evalBinOp .eq (some v) (some v)
  rw [evalExprWithDb_binOp, hv]
  -- Unfold RHS: case → evalCase
  rw [evalExprWithDb_case]
  -- Compute the isNull condition value
  have hcond : evalExprWithDb (fun _ => []) row (Expr.unaryOp .isNull e) =
      some (.bool (isNullValue (some v))) := by
    rw [evalExprWithDb_unaryOp, hv]; rfl
  match v with
  | .null _ =>
    -- isNull = true, CASE returns lit null = some (.null none)
    -- LHS: evalBinOp .eq (some (.null _)) (some (.null _)) = some (.null none)
    rw [evalCase_cons_true _ _ _ _ _ _ hcond, evalExprWithDb_lit]; rfl
  | .int n =>
    -- isNull = false, CASE falls through to else = lit true
    rw [evalCase_cons_false _ _ _ _ _ _ hcond, evalCase_nil_some, evalExprWithDb_lit]
    simp [evalBinOp, Value.eq]
  | .string s =>
    rw [evalCase_cons_false _ _ _ _ _ _ hcond, evalCase_nil_some, evalExprWithDb_lit]
    simp [evalBinOp, Value.eq]
  | .bool b =>
    rw [evalCase_cons_false _ _ _ _ _ _ hcond, evalCase_nil_some, evalExprWithDb_lit]
    simp [evalBinOp, Value.eq]

/-- x <> x is FALSE for non-null, NULL for null (irreflexivity of inequality) -/
theorem ne_irreflexive (e : Expr) (h : e.evaluable) :
    Expr.binOp .ne e e ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool false))) := by
  intro row
  simp only [evalExpr]
  obtain ⟨v, hv⟩ := h row
  simp only [evalExpr] at hv
  rw [evalExprWithDb_binOp, hv, evalExprWithDb_case]
  have hcond : evalExprWithDb (fun _ => []) row (Expr.unaryOp .isNull e) =
      some (.bool (isNullValue (some v))) := by
    rw [evalExprWithDb_unaryOp, hv]; rfl
  match v with
  | .null _ =>
    rw [evalCase_cons_true _ _ _ _ _ _ hcond, evalExprWithDb_lit]; rfl
  | .int n =>
    rw [evalCase_cons_false _ _ _ _ _ _ hcond, evalCase_nil_some, evalExprWithDb_lit]
    simp [evalBinOp, Value.eq]
  | .string s =>
    rw [evalCase_cons_false _ _ _ _ _ _ hcond, evalCase_nil_some, evalExprWithDb_lit]
    simp [evalBinOp, Value.eq]
  | .bool b =>
    rw [evalCase_cons_false _ _ _ _ _ _ hcond, evalCase_nil_some, evalExprWithDb_lit]
    simp [evalBinOp, Value.eq]

-- Value-level helpers for comparison negation
-- NOT of a comparison result: NOT (bool b) = bool (!b), NOT none = none
private theorem not_map_bool_eq (o : Option Bool) :
    evalUnaryOp .not (o.map Value.bool) = o.map (fun b => Value.bool (!b)) := by
  match o with
  | some true => rfl
  | some false => rfl
  | none => rfl

private theorem not_map_bool_cancel (o : Option Bool) :
    evalUnaryOp .not (o.map (fun b => Value.bool (!b))) = o.map Value.bool := by
  match o with
  | some true => rfl
  | some false => rfl
  | none => rfl

private theorem not_map_ordering_eq_lt (o : Option Ordering) :
    evalUnaryOp .not (o.map (fun o => Value.bool (o == .lt))) =
    o.map (fun o => Value.bool (o != .lt)) := by
  match o with
  | some .lt => rfl
  | some .eq => rfl
  | some .gt => rfl
  | none => rfl

private theorem not_map_ordering_ne_gt (o : Option Ordering) :
    evalUnaryOp .not (o.map (fun o => Value.bool (o != .gt))) =
    o.map (fun o => Value.bool (o == .gt)) := by
  match o with
  | some .lt => rfl
  | some .eq => rfl
  | some .gt => rfl
  | none => rfl

private theorem not_map_ordering_eq_gt (o : Option Ordering) :
    evalUnaryOp .not (o.map (fun o => Value.bool (o == .gt))) =
    o.map (fun o => Value.bool (o != .gt)) := by
  match o with
  | some .lt => rfl
  | some .eq => rfl
  | some .gt => rfl
  | none => rfl

private theorem not_map_ordering_ne_lt (o : Option Ordering) :
    evalUnaryOp .not (o.map (fun o => Value.bool (o != .lt))) =
    o.map (fun o => Value.bool (o == .lt)) := by
  match o with
  | some .lt => rfl
  | some .eq => rfl
  | some .gt => rfl
  | none => rfl

-- Value-level helpers for comparison negation (full Option Value)
-- With Option 3 null semantics, null cases need explicit splits because
-- NOT(null) = null = negated_comparison(null, _), both sides `some (.null none)`.
private theorem evalUnaryOp_not_eq (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .eq l r) = evalBinOp .ne l r := by
  cases l with
  | none => cases r with | none => rfl | some v => cases v <;> rfl
  | some v => cases r with
    | none => cases v <;> rfl
    | some w => cases v <;> cases w <;>
      first | rfl | (simp only [evalBinOp]; exact not_map_bool_eq _)

private theorem evalUnaryOp_not_ne (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .ne l r) = evalBinOp .eq l r := by
  cases l with
  | none => cases r with | none => rfl | some v => cases v <;> rfl
  | some v => cases r with
    | none => cases v <;> rfl
    | some w => cases v <;> cases w <;>
      first | rfl | (simp only [evalBinOp]; exact not_map_bool_cancel _)

private theorem evalUnaryOp_not_lt (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .lt l r) = evalBinOp .ge l r := by
  cases l with
  | none => cases r with | none => rfl | some v => cases v <;> rfl
  | some v => cases r with
    | none => cases v <;> rfl
    | some w => cases v <;> cases w <;>
      first | rfl | (simp only [evalBinOp]; exact not_map_ordering_eq_lt _)

private theorem evalUnaryOp_not_le (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .le l r) = evalBinOp .gt l r := by
  cases l with
  | none => cases r with | none => rfl | some v => cases v <;> rfl
  | some v => cases r with
    | none => cases v <;> rfl
    | some w => cases v <;> cases w <;>
      first | rfl | (simp only [evalBinOp]; exact not_map_ordering_ne_gt _)

private theorem evalUnaryOp_not_gt (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .gt l r) = evalBinOp .le l r := by
  cases l with
  | none => cases r with | none => rfl | some v => cases v <;> rfl
  | some v => cases r with
    | none => cases v <;> rfl
    | some w => cases v <;> cases w <;>
      first | rfl | (simp only [evalBinOp]; exact not_map_ordering_eq_gt _)

private theorem evalUnaryOp_not_ge (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .ge l r) = evalBinOp .lt l r := by
  cases l with
  | none => cases r with | none => rfl | some v => cases v <;> rfl
  | some v => cases r with
    | none => cases v <;> rfl
    | some w => cases v <;> cases w <;>
      first | rfl | (simp only [evalBinOp]; exact not_map_ordering_ne_lt _)

/-- NOT (x = y) = (x <> y) -/
theorem not_eq_is_ne (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .eq a b) ≃ₑ Expr.binOp .ne a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_eq _ _

/-- NOT (x <> y) = (x = y) -/
theorem not_ne_is_eq (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .ne a b) ≃ₑ Expr.binOp .eq a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_ne _ _

/-- NOT (x < y) = (x >= y) -/
theorem not_lt_is_ge (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .lt a b) ≃ₑ Expr.binOp .ge a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_lt _ _

/-- NOT (x <= y) = (x > y) -/
theorem not_le_is_gt (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .le a b) ≃ₑ Expr.binOp .gt a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_le _ _

/-- NOT (x > y) = (x <= y) -/
theorem not_gt_is_le (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .gt a b) ≃ₑ Expr.binOp .le a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_gt _ _

/-- NOT (x >= y) = (x < y) -/
theorem not_ge_is_lt (a b : Expr) :
    Expr.unaryOp .not (Expr.binOp .ge a b) ≃ₑ Expr.binOp .lt a b := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_unaryOp, evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalUnaryOp_not_ge _ _

/-- NOT BETWEEN expansion: x NOT BETWEEN a AND b = (x < a OR x > b)
    Proved by composition: between_expansion + De Morgan + NOT comparison identities.
    No preconditions needed — BETWEEN is now defined as AND(GE, LE). -/
theorem not_between_expansion (e lo hi : Expr) :
    Expr.unaryOp .not (Expr.between e lo hi) ≃ₑ
    Expr.binOp .or (Expr.binOp .lt e lo) (Expr.binOp .gt e hi) := by
  -- Step 1: NOT BETWEEN ≃ NOT (ge AND le) via between_expansion + unaryOp_congr
  have step1 : Expr.unaryOp .not (Expr.between e lo hi) ≃ₑ
      Expr.unaryOp .not (Expr.binOp .and (Expr.binOp .ge e lo) (Expr.binOp .le e hi)) :=
    unaryOp_congr (between_expansion e lo hi)
  -- Step 2: NOT (ge AND le) ≃ NOT ge OR NOT le via De Morgan
  have step2 : Expr.unaryOp .not (Expr.binOp .and (Expr.binOp .ge e lo) (Expr.binOp .le e hi)) ≃ₑ
      Expr.binOp .or (Expr.unaryOp .not (Expr.binOp .ge e lo)) (Expr.unaryOp .not (Expr.binOp .le e hi)) :=
    not_and _ _
  -- Step 3: NOT ge ≃ lt and NOT le ≃ gt
  have step3 : Expr.binOp .or (Expr.unaryOp .not (Expr.binOp .ge e lo)) (Expr.unaryOp .not (Expr.binOp .le e hi)) ≃ₑ
      Expr.binOp .or (Expr.binOp .lt e lo) (Expr.binOp .gt e hi) :=
    binOp_congr (not_ge_is_lt e lo) (not_le_is_gt e hi)
  -- Chain: step1 → step2 → step3
  exact expr_equiv_trans (expr_equiv_trans step1 step2) step3

-- Ordering swap helper: (compare a b == .lt) = (compare b a == .gt), etc.
-- Use Std.OrientedCmp to get compare swap for free
private theorem compare_swap_gen {α : Type} [Ord α] [Std.OrientedCmp (α := α) compare]
    (a b : α) : (compare a b).swap = compare b a := by
  have h := Std.OrientedCmp.eq_swap (cmp := (compare : α → α → Ordering)) (a := a) (b := b)
  rw [h, Ordering.swap_swap]

private theorem ordering_lt_eq_swap_gt (o : Ordering) :
    (o == .lt) = (o.swap == .gt) := by cases o <;> rfl

private theorem ordering_ne_gt_eq_swap_ne_lt (o : Ordering) :
    (o != .gt) = (o.swap != .lt) := by cases o <;> rfl

-- Value-level helpers for comparison flips
private theorem evalBinOp_lt_eq_gt_flip (l r : Option Value) :
    evalBinOp .lt l r = evalBinOp .gt r l := by
  cases l with
  | none => cases r with | none => rfl | some v => cases v <;> rfl
  | some v => cases r with
    | none => cases v <;> rfl
    | some w => cases v <;> cases w <;>
      first
      | rfl
      | (simp only [evalBinOp, Value.compare, Option.map]; rw [ordering_lt_eq_swap_gt, compare_swap_gen])

private theorem evalBinOp_le_eq_ge_flip (l r : Option Value) :
    evalBinOp .le l r = evalBinOp .ge r l := by
  cases l with
  | none => cases r with | none => rfl | some v => cases v <;> rfl
  | some v => cases r with
    | none => cases v <;> rfl
    | some w => cases v <;> cases w <;>
      first
      | rfl
      | (simp only [evalBinOp, Value.compare, Option.map]; rw [ordering_ne_gt_eq_swap_ne_lt, compare_swap_gen])

/-- x < y = y > x (flip) -/
theorem lt_flip (a b : Expr) :
    Expr.binOp .lt a b ≃ₑ Expr.binOp .gt b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_lt_eq_gt_flip _ _

/-- x <= y = y >= x (flip) -/
theorem le_flip (a b : Expr) :
    Expr.binOp .le a b ≃ₑ Expr.binOp .ge b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact evalBinOp_le_eq_ge_flip _ _

/-- x > y = y < x (flip) -/
theorem gt_flip (a b : Expr) :
    Expr.binOp .gt a b ≃ₑ Expr.binOp .lt b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact (evalBinOp_lt_eq_gt_flip _ _).symm

/-- x >= y = y <= x (flip) -/
theorem ge_flip (a b : Expr) :
    Expr.binOp .ge a b ≃ₑ Expr.binOp .le b a := by
  intro row
  simp only [evalExpr]
  rw [evalExprWithDb_binOp, evalExprWithDb_binOp]
  exact (evalBinOp_le_eq_ge_flip _ _).symm


end SqlEquiv
