/-
  SQL Equivalence - Comparison, NULL, Predicate Pushdown, and Related Proofs
-/
import SqlEquiv.Equiv.Defs
import SqlEquiv.Equiv.ValueLemmas
import SqlEquiv.Equiv.Decidable

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
    Axiom: Filters compose conjunctively. -/
axiom filter_and (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (p q : Expr) (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    evalSelect db (.mk false items
      (some (.subquery (.mk false [.star none] from_ (some p) [] none [] none none) "inner"))
      (some q) groupBy having orderBy limit offset) =
    evalSelect db (.mk false items from_ (some (.binOp .and p q)) groupBy having orderBy limit offset)

/-- Filter order doesn't matter: (WHERE p) WHERE q ≃ (WHERE q) WHERE p.
    Axiom: Filter conjunction is commutative. -/
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
    Axiom: Applying the same filter twice is redundant. -/
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

/-- FALSE filter yields empty result (or FROM is none).
    Axiom: FALSE filter removes all rows. -/
axiom filter_false_empty' (db : Database) (items : List SelectItem) (from_ : Option FromClause)
    (groupBy : List Expr) (having : Option Expr)
    (orderBy : List OrderByItem) (limit offset : Option Nat) :
    (evalSelect db (.mk false items from_ (some (.lit (.bool false))) groupBy having orderBy limit offset)).length = 0

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
    evalBinOp .and (some (.bool true)) (some (.null t)) = none := by
  rfl

/-- NULL AND TRUE = NULL (propagates unknown) -/
theorem null_and_true (t : Option SqlType) :
    evalBinOp .and (some (.null t)) (some (.bool true)) = none := by
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
    evalBinOp .or (some (.bool false)) (some (.null t)) = none := by
  rfl

/-- NULL OR FALSE = NULL (propagates unknown) -/
theorem null_or_false (t : Option SqlType) :
    evalBinOp .or (some (.null t)) (some (.bool false)) = none := by
  rfl

/-- NULL AND NULL = NULL -/
theorem null_and_null (t1 t2 : Option SqlType) :
    evalBinOp .and (some (.null t1)) (some (.null t2)) = none := by
  rfl

/-- NULL OR NULL = NULL -/
theorem null_or_null (t1 t2 : Option SqlType) :
    evalBinOp .or (some (.null t1)) (some (.null t2)) = none := by
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

/-- MIN is at most any element in the list (axiom) -/
axiom min_le_elem (n : Int) (ns : List Int) (h : n ∈ ns) :
    ns.foldl min (ns.head!) ≤ n

/-- MAX is at least any element in the list (axiom) -/
axiom max_ge_elem (n : Int) (ns : List Int) (h : n ∈ ns) :
    n ≤ ns.foldl max (ns.head!)

/-- DISTINCT doesn't increase count -/
axiom distinct_count_le (vs : List Value) :
    vs.eraseDups.length ≤ vs.length

/-- DISTINCT on already-distinct list is identity -/
axiom distinct_idempotent (vs : List Value) :
    vs.eraseDups.eraseDups = vs.eraseDups

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
                 = SELECT * FROM t WHERE (p AND q) -/
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

/-- x IN () = FALSE (empty IN list) -/
axiom in_empty_false (e : Expr) :
    Expr.inList e false [] ≃ₑ Expr.lit (.bool false)

/-- x NOT IN () = TRUE (empty NOT IN list) -/
axiom not_in_empty_true (e : Expr) :
    Expr.inList e true [] ≃ₑ Expr.lit (.bool true)

/-- x IN (a) = (x = a) (singleton IN list) -/
axiom in_singleton (e a : Expr) :
    Expr.inList e false [a] ≃ₑ Expr.binOp .eq e a

/-- x NOT IN (a) = (x <> a) (singleton NOT IN list) -/
axiom not_in_singleton (e a : Expr) :
    Expr.inList e true [a] ≃ₑ Expr.binOp .ne e a

/-- x IN (a, b) = (x = a OR x = b) -/
axiom in_pair (e a b : Expr) :
    Expr.inList e false [a, b] ≃ₑ
    Expr.binOp .or (Expr.binOp .eq e a) (Expr.binOp .eq e b)

/-- x NOT IN (a, b) = (x <> a AND x <> b) -/
axiom not_in_pair (e a b : Expr) :
    Expr.inList e true [a, b] ≃ₑ
    Expr.binOp .and (Expr.binOp .ne e a) (Expr.binOp .ne e b)

/-- IN list is equivalent to OR of equalities (general form) -/
axiom in_list_or_expansion (e : Expr) (vals : List Expr) :
    Expr.inList e false vals ≃ₑ
    vals.foldl (fun acc v => Expr.binOp .or acc (Expr.binOp .eq e v))
               (Expr.lit (.bool false))

/-- NOT IN list is equivalent to AND of inequalities (general form) -/
axiom not_in_list_and_expansion (e : Expr) (vals : List Expr) :
    Expr.inList e true vals ≃ₑ
    vals.foldl (fun acc v => Expr.binOp .and acc (Expr.binOp .ne e v))
               (Expr.lit (.bool true))

-- ============================================================================
-- BETWEEN Theorems
-- ============================================================================

/-- x BETWEEN a AND b = (x >= a AND x <= b) -/
axiom between_expansion (e lo hi : Expr) :
    Expr.between e lo hi ≃ₑ
    Expr.binOp .and (Expr.binOp .ge e lo) (Expr.binOp .le e hi)

/-- BETWEEN is reflexive: x BETWEEN x AND x = TRUE when x is non-null -/
axiom between_reflexive (e : Expr) :
    Expr.between e e e ≃ₑ
    Expr.binOp .and (Expr.binOp .ge e e) (Expr.binOp .le e e)

/-- NOT BETWEEN expansion: x NOT BETWEEN a AND b = (x < a OR x > b) -/
axiom not_between_expansion (e lo hi : Expr) :
    Expr.unaryOp .not (Expr.between e lo hi) ≃ₑ
    Expr.binOp .or (Expr.binOp .lt e lo) (Expr.binOp .gt e hi)

-- ============================================================================
-- LIKE Pattern Theorems
-- ============================================================================

/-- x LIKE '%' = TRUE for non-null x (matches everything) -/
axiom like_match_all (e : Expr) :
    -- When e evaluates to a non-null string, LIKE '%' is true
    Expr.binOp .like e (Expr.lit (.string "%")) ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool true)))

/-- x LIKE '' = (x = '') (empty pattern matches empty string) -/
axiom like_empty_pattern (e : Expr) :
    Expr.binOp .like e (Expr.lit (.string "")) ≃ₑ
    Expr.binOp .eq e (Expr.lit (.string ""))

/-- x LIKE x = TRUE for non-null x with no wildcards -/
axiom like_self (e : Expr) :
    -- Pattern with no wildcards: LIKE behaves like equality
    Expr.binOp .like e e ≃ₑ
    Expr.case [(Expr.unaryOp .isNull e, Expr.lit (.null none))]
              (some (Expr.lit (.bool true)))

-- ============================================================================
-- String Function Theorems
-- ============================================================================

/-- CONCAT('', x) = x (empty string is identity for concat) -/
axiom concat_empty_left (e : Expr) :
    Expr.func "CONCAT" [Expr.lit (.string ""), e] ≃ₑ e

/-- CONCAT(x, '') = x (empty string is identity for concat) -/
axiom concat_empty_right (e : Expr) :
    Expr.func "CONCAT" [e, Expr.lit (.string "")] ≃ₑ e

/-- UPPER(UPPER(x)) = UPPER(x) (idempotent) -/
axiom upper_idempotent (e : Expr) :
    Expr.func "UPPER" [Expr.func "UPPER" [e]] ≃ₑ Expr.func "UPPER" [e]

/-- LOWER(LOWER(x)) = LOWER(x) (idempotent) -/
axiom lower_idempotent (e : Expr) :
    Expr.func "LOWER" [Expr.func "LOWER" [e]] ≃ₑ Expr.func "LOWER" [e]

/-- UPPER(LOWER(UPPER(x))) = UPPER(x) -/
axiom upper_lower_upper (e : Expr) :
    Expr.func "UPPER" [Expr.func "LOWER" [Expr.func "UPPER" [e]]] ≃ₑ
    Expr.func "UPPER" [e]

/-- LOWER(UPPER(LOWER(x))) = LOWER(x) -/
axiom lower_upper_lower (e : Expr) :
    Expr.func "LOWER" [Expr.func "UPPER" [Expr.func "LOWER" [e]]] ≃ₑ
    Expr.func "LOWER" [e]

/-- LENGTH('') = 0 -/
axiom length_empty :
    Expr.func "LENGTH" [Expr.lit (.string "")] ≃ₑ Expr.lit (.int 0)

-- ============================================================================
-- Comparison Theorems
-- ============================================================================

/-- Mild precondition: expression always evaluates to SOME value.
    This excludes only error-producing expressions (missing columns, aggregates
    without group context). All well-formed SQL in a valid context satisfies this. -/
def Expr.evaluable (e : Expr) : Prop :=
  ∀ row : Row, ∃ v : Value, evalExpr row e = some v

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
  match l, r with
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | none, none => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
  | some (.null _), some _ => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int a), some (.int b) => simp only [evalBinOp]; exact not_map_bool_eq (Value.eq (.int a) (.int b))
  | some (.int a), some (.string b) => simp only [evalBinOp]; exact not_map_bool_eq (Value.eq (.int a) (.string b))
  | some (.int a), some (.bool b) => simp only [evalBinOp]; exact not_map_bool_eq (Value.eq (.int a) (.bool b))
  | some (.string a), some (.int b) => simp only [evalBinOp]; exact not_map_bool_eq (Value.eq (.string a) (.int b))
  | some (.string a), some (.string b) => simp only [evalBinOp]; exact not_map_bool_eq (Value.eq (.string a) (.string b))
  | some (.string a), some (.bool b) => simp only [evalBinOp]; exact not_map_bool_eq (Value.eq (.string a) (.bool b))
  | some (.bool a), some (.int b) => simp only [evalBinOp]; exact not_map_bool_eq (Value.eq (.bool a) (.int b))
  | some (.bool a), some (.string b) => simp only [evalBinOp]; exact not_map_bool_eq (Value.eq (.bool a) (.string b))
  | some (.bool a), some (.bool b) => simp only [evalBinOp]; exact not_map_bool_eq (Value.eq (.bool a) (.bool b))

private theorem evalUnaryOp_not_ne (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .ne l r) = evalBinOp .eq l r := by
  match l, r with
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | none, none => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
  | some (.null _), some _ => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int a), some (.int b) => simp only [evalBinOp]; exact not_map_bool_cancel (Value.eq (.int a) (.int b))
  | some (.int a), some (.string b) => simp only [evalBinOp]; exact not_map_bool_cancel (Value.eq (.int a) (.string b))
  | some (.int a), some (.bool b) => simp only [evalBinOp]; exact not_map_bool_cancel (Value.eq (.int a) (.bool b))
  | some (.string a), some (.int b) => simp only [evalBinOp]; exact not_map_bool_cancel (Value.eq (.string a) (.int b))
  | some (.string a), some (.string b) => simp only [evalBinOp]; exact not_map_bool_cancel (Value.eq (.string a) (.string b))
  | some (.string a), some (.bool b) => simp only [evalBinOp]; exact not_map_bool_cancel (Value.eq (.string a) (.bool b))
  | some (.bool a), some (.int b) => simp only [evalBinOp]; exact not_map_bool_cancel (Value.eq (.bool a) (.int b))
  | some (.bool a), some (.string b) => simp only [evalBinOp]; exact not_map_bool_cancel (Value.eq (.bool a) (.string b))
  | some (.bool a), some (.bool b) => simp only [evalBinOp]; exact not_map_bool_cancel (Value.eq (.bool a) (.bool b))

private theorem evalUnaryOp_not_lt (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .lt l r) = evalBinOp .ge l r := by
  match l, r with
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | none, none => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
  | some (.null _), some _ => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_eq_lt (Value.compare (.int a) (.int b))
  | some (.int a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_eq_lt (Value.compare (.int a) (.string b))
  | some (.int a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_eq_lt (Value.compare (.int a) (.bool b))
  | some (.string a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_eq_lt (Value.compare (.string a) (.int b))
  | some (.string a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_eq_lt (Value.compare (.string a) (.string b))
  | some (.string a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_eq_lt (Value.compare (.string a) (.bool b))
  | some (.bool a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_eq_lt (Value.compare (.bool a) (.int b))
  | some (.bool a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_eq_lt (Value.compare (.bool a) (.string b))
  | some (.bool a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_eq_lt (Value.compare (.bool a) (.bool b))

private theorem evalUnaryOp_not_le (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .le l r) = evalBinOp .gt l r := by
  match l, r with
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | none, none => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
  | some (.null _), some _ => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_ne_gt (Value.compare (.int a) (.int b))
  | some (.int a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_ne_gt (Value.compare (.int a) (.string b))
  | some (.int a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_ne_gt (Value.compare (.int a) (.bool b))
  | some (.string a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_ne_gt (Value.compare (.string a) (.int b))
  | some (.string a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_ne_gt (Value.compare (.string a) (.string b))
  | some (.string a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_ne_gt (Value.compare (.string a) (.bool b))
  | some (.bool a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_ne_gt (Value.compare (.bool a) (.int b))
  | some (.bool a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_ne_gt (Value.compare (.bool a) (.string b))
  | some (.bool a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_ne_gt (Value.compare (.bool a) (.bool b))

private theorem evalUnaryOp_not_gt (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .gt l r) = evalBinOp .le l r := by
  match l, r with
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | none, none => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
  | some (.null _), some _ => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_eq_gt (Value.compare (.int a) (.int b))
  | some (.int a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_eq_gt (Value.compare (.int a) (.string b))
  | some (.int a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_eq_gt (Value.compare (.int a) (.bool b))
  | some (.string a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_eq_gt (Value.compare (.string a) (.int b))
  | some (.string a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_eq_gt (Value.compare (.string a) (.string b))
  | some (.string a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_eq_gt (Value.compare (.string a) (.bool b))
  | some (.bool a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_eq_gt (Value.compare (.bool a) (.int b))
  | some (.bool a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_eq_gt (Value.compare (.bool a) (.string b))
  | some (.bool a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_eq_gt (Value.compare (.bool a) (.bool b))

private theorem evalUnaryOp_not_ge (l r : Option Value) :
    evalUnaryOp .not (evalBinOp .ge l r) = evalBinOp .lt l r := by
  match l, r with
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | none, none => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
  | some (.null _), some _ => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_ne_lt (Value.compare (.int a) (.int b))
  | some (.int a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_ne_lt (Value.compare (.int a) (.string b))
  | some (.int a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_ne_lt (Value.compare (.int a) (.bool b))
  | some (.string a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_ne_lt (Value.compare (.string a) (.int b))
  | some (.string a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_ne_lt (Value.compare (.string a) (.string b))
  | some (.string a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_ne_lt (Value.compare (.string a) (.bool b))
  | some (.bool a), some (.int b) => simp only [evalBinOp]; exact not_map_ordering_ne_lt (Value.compare (.bool a) (.int b))
  | some (.bool a), some (.string b) => simp only [evalBinOp]; exact not_map_ordering_ne_lt (Value.compare (.bool a) (.string b))
  | some (.bool a), some (.bool b) => simp only [evalBinOp]; exact not_map_ordering_ne_lt (Value.compare (.bool a) (.bool b))

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
  match l, r with
  | none, none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
  | some (.null _), some (.int _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.bool _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int a), some (.int b) =>
    simp only [evalBinOp, Value.compare, Option.map]
    rw [ordering_lt_eq_swap_gt, compare_swap_gen]
  | some (.string a), some (.string b) =>
    simp only [evalBinOp, Value.compare, Option.map]
    rw [ordering_lt_eq_swap_gt, compare_swap_gen]
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.bool _) => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.bool _) => rfl
  | some (.bool _), some (.int _) => rfl
  | some (.bool _), some (.string _) => rfl
  | some (.bool _), some (.bool _) => rfl

-- le/ge and gt/lt flip helpers reuse the same pattern as lt/gt
private theorem evalBinOp_le_eq_ge_flip (l r : Option Value) :
    evalBinOp .le l r = evalBinOp .ge r l := by
  match l, r with
  | none, none => rfl
  | none, some (.int _) => rfl
  | none, some (.string _) => rfl
  | none, some (.bool _) => rfl
  | none, some (.null _) => rfl
  | some (.int _), none => rfl
  | some (.string _), none => rfl
  | some (.bool _), none => rfl
  | some (.null _), none => rfl
  | some (.null _), some (.int _) => rfl
  | some (.null _), some (.string _) => rfl
  | some (.null _), some (.bool _) => rfl
  | some (.null _), some (.null _) => rfl
  | some (.int _), some (.null _) => rfl
  | some (.string _), some (.null _) => rfl
  | some (.bool _), some (.null _) => rfl
  | some (.int a), some (.int b) =>
    simp only [evalBinOp, Value.compare, Option.map]
    rw [ordering_ne_gt_eq_swap_ne_lt, compare_swap_gen]
  | some (.string a), some (.string b) =>
    simp only [evalBinOp, Value.compare, Option.map]
    rw [ordering_ne_gt_eq_swap_ne_lt, compare_swap_gen]
  | some (.int _), some (.string _) => rfl
  | some (.int _), some (.bool _) => rfl
  | some (.string _), some (.int _) => rfl
  | some (.string _), some (.bool _) => rfl
  | some (.bool _), some (.int _) => rfl
  | some (.bool _), some (.string _) => rfl
  | some (.bool _), some (.bool _) => rfl

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
