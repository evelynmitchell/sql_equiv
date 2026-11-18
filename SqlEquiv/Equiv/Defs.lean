/-
  SQL Equivalence Definitions
-/
import SqlEquiv.Ast
import SqlEquiv.Semantics

namespace SqlEquiv

-- ============================================================================
-- Equivalence Definitions
-- ============================================================================

/-- Expression equivalence: equal results for every database and every row.
    Quantifying over `db` matters for subquery-bearing expressions
    (`EXISTS`, `IN (subquery)`, scalar subqueries), see issue #242. -/
def ExprEquiv (e1 e2 : Expr) : Prop :=
  ∀ (db : Database) (row : Row), evalExprWithDb db row e1 = evalExprWithDb db row e2
scoped infix:50 " ≃ₑ " => ExprEquiv

/-- Weaker, pre-#242 notion: equal results for every row against the EMPTY
    database only (`evalExpr = evalExprWithDb (fun _ => [])`). Kept for
    lemmas that only hold there. Every `≃ₑ` fact implies it
    (`ExprEquiv.toEmptyDb`). -/
def ExprEquivEmptyDb (e1 e2 : Expr) : Prop :=
  ∀ row : Row, evalExpr row e1 = evalExpr row e2
scoped infix:50 " ≃ₑ₀ " => ExprEquivEmptyDb

def SelectEquiv (s1 s2 : SelectStmt) : Prop :=
  ∀ db : Database, evalSelect db s1 = evalSelect db s2
scoped infix:50 " ≃ₛ " => SelectEquiv

def QueryEquiv (q1 q2 : Query) : Prop :=
  ∀ db : Database, evalQuery db q1 = evalQuery db q2
scoped infix:50 " ≃ᵩ " => QueryEquiv

/-- Bag equivalence: query results are permutations of each other.
    Weaker than ≃ᵩ (ignores ordering), stronger than ≃ˢ (preserves multiplicities).
    Appropriate for UNION ALL commutativity and UNION commutativity. -/
def QueryBagEquiv (q1 q2 : Query) : Prop :=
  ∀ db : Database, (evalQuery db q1).Perm (evalQuery db q2)
scoped infix:50 " ≃ᵇ " => QueryBagEquiv

/-- Set equivalence: query results have the same membership.
    Weakest equivalence — ignores both ordering and multiplicities.
    Appropriate for UNION idempotence, INTERSECT commutativity, distributivity. -/
def QuerySetEquiv (q1 q2 : Query) : Prop :=
  ∀ db : Database, ∀ row : Row, row ∈ evalQuery db q1 ↔ row ∈ evalQuery db q2
scoped infix:50 " ≃ˢ " => QuerySetEquiv

/-- Value-level bag equivalence (#324): the results hold the same rows with the same
    multiplicities, compared by `Row.valueKey`, i.e. by position and value, ignoring column
    names and the static type of a NULL. This is what engines guarantee for set operations,
    whose output columns are named by their first branch, so `A INTERSECT B` and
    `B INTERSECT A` name their columns differently. -/
def QueryBagEquivV (q1 q2 : Query) : Prop :=
  ∀ db : Database, ((evalQuery db q1).map Row.valueKey).Perm ((evalQuery db q2).map Row.valueKey)
scoped infix:50 " ≃ᵇᵛ " => QueryBagEquivV

/-- Value-level set equivalence (#324): the results hold the same rows, compared by
    `Row.valueKey`, ignoring order, multiplicities, column names and NULL type tags. -/
def QuerySetEquivV (q1 q2 : Query) : Prop :=
  ∀ db : Database, ∀ k : List Value,
    k ∈ (evalQuery db q1).map Row.valueKey ↔ k ∈ (evalQuery db q2).map Row.valueKey
scoped infix:50 " ≃ˢᵛ " => QuerySetEquivV

def StmtEquiv (s1 s2 : Stmt) : Prop :=
  ∀ db : Database, evalStmt db s1 = evalStmt db s2
scoped infix:50 " ≃ " => StmtEquiv

/-- Type precondition: expression always evaluates to a boolean value.
    This excludes expressions that produce errors (type mismatches, missing columns)
    or non-boolean values (ints, strings, nulls). Needed for boolean algebra identities
    (NOT NOT, AND TRUE, OR FALSE, idempotence, complement, absorption). -/
def Expr.isBoolValued (e : Expr) : Prop :=
  ∀ (db : Database) (row : Row), ∃ b : Bool, evalExprWithDb db row e = some (.bool b)

/-- Type precondition: expression always evaluates to a string, null, or error.
    Excludes int/bool values. Needed for string identity axioms
    (CONCAT('', e) = e, CONCAT(e, '') = e). -/
def Expr.isStringOrNullValued (e : Expr) : Prop :=
  ∀ (db : Database) (row : Row), (∃ s : String, evalExprWithDb db row e = some (.string s)) ∨
              (∃ n, evalExprWithDb db row e = some (.null n)) ∨
              evalExprWithDb db row e = none

/-- Stronger than isStringOrNullValued: null values must be untyped (`.null none`).
    Satisfied by any expression whose values have passed through an evaluator operation,
    since all evalBinOp/evalUnaryOp/evalFunc null arms return `some (.null none)`. -/
def Expr.isStringOrUntypedNullValued (e : Expr) : Prop :=
  ∀ (db : Database) (row : Row), (∃ s : String, evalExprWithDb db row e = some (.string s)) ∨
              evalExprWithDb db row e = some (.null none) ∨
              evalExprWithDb db row e = none

/-- Type precondition: expression always evaluates to a string or null value.
    Excludes int/bool values AND errors (none). Needed for LIKE pattern axioms
    (like_match_all, like_self) where evalBinOp .like only handles string/null inputs. -/
def Expr.isStringOrNull (e : Expr) : Prop :=
  ∀ (db : Database) (row : Row), (∃ s : String, evalExprWithDb db row e = some (.string s)) ∨
              (∃ n, evalExprWithDb db row e = some (.null n))

/-- Mild precondition: expression always evaluates to SOME value.
    This excludes only error-producing expressions (missing columns, aggregates
    without group context). All well-formed SQL in a valid context satisfies this.
    Used by eq_reflexive, between_expansion, not_between_expansion. -/
def Expr.evaluable (e : Expr) : Prop :=
  ∀ (db : Database) (row : Row), ∃ v : Value, evalExprWithDb db row e = some v


theorem expr_equiv_refl (e : Expr) : e ≃ₑ e := by intro db row; rfl
theorem expr_equiv_symm {e1 e2 : Expr} (h : e1 ≃ₑ e2) : e2 ≃ₑ e1 := by intro db row; exact (h db row).symm
theorem expr_equiv_trans {e1 e2 e3 : Expr} (h12 : e1 ≃ₑ e2) (h23 : e2 ≃ₑ e3) : e1 ≃ₑ e3 := by intro db row; rw [h12 db row, h23 db row]

/-- `≃ₑ` (all databases) implies `≃ₑ₀` (empty database only). -/
theorem ExprEquiv.toEmptyDb {e1 e2 : Expr} (h : e1 ≃ₑ e2) : e1 ≃ₑ₀ e2 :=
  fun row => h (fun _ => []) row

theorem select_equiv_refl (s : SelectStmt) : s ≃ₛ s := by intro db; rfl
theorem select_equiv_symm {s1 s2 : SelectStmt} (h : s1 ≃ₛ s2) : s2 ≃ₛ s1 := by intro db; exact (h db).symm
theorem select_equiv_trans {s1 s2 s3 : SelectStmt} (h12 : s1 ≃ₛ s2) (h23 : s2 ≃ₛ s3) : s1 ≃ₛ s3 := by intro db; rw [h12 db, h23 db]

theorem query_equiv_refl (q : Query) : q ≃ᵩ q := by intro db; rfl
theorem query_equiv_symm {q1 q2 : Query} (h : q1 ≃ᵩ q2) : q2 ≃ᵩ q1 := by intro db; exact (h db).symm
theorem query_equiv_trans {q1 q2 q3 : Query} (h12 : q1 ≃ᵩ q2) (h23 : q2 ≃ᵩ q3) : q1 ≃ᵩ q3 := by intro db; rw [h12 db, h23 db]

theorem query_bag_equiv_refl (q : Query) : q ≃ᵇ q := by intro db; exact List.Perm.refl _
theorem query_bag_equiv_symm {q1 q2 : Query} (h : q1 ≃ᵇ q2) : q2 ≃ᵇ q1 := by intro db; exact (h db).symm
theorem query_bag_equiv_trans {q1 q2 q3 : Query} (h12 : q1 ≃ᵇ q2) (h23 : q2 ≃ᵇ q3) : q1 ≃ᵇ q3 := by intro db; exact (h12 db).trans (h23 db)

theorem query_set_equiv_refl (q : Query) : q ≃ˢ q := by intro db row; exact Iff.rfl
theorem query_set_equiv_symm {q1 q2 : Query} (h : q1 ≃ˢ q2) : q2 ≃ˢ q1 := by intro db row; exact (h db row).symm
theorem query_set_equiv_trans {q1 q2 q3 : Query} (h12 : q1 ≃ˢ q2) (h23 : q2 ≃ˢ q3) : q1 ≃ˢ q3 := by intro db row; exact (h12 db row).trans (h23 db row)

/-- Exact equality implies bag equivalence -/
theorem QueryEquiv.toBagEquiv {q1 q2 : Query} (h : q1 ≃ᵩ q2) : q1 ≃ᵇ q2 := by
  intro db; rw [h db]

/-- Bag equivalence implies set equivalence -/
theorem QueryBagEquiv.toSetEquiv {q1 q2 : Query} (h : q1 ≃ᵇ q2) : q1 ≃ˢ q2 := by
  intro db row; exact (h db).mem_iff

theorem query_bag_equiv_v_refl (q : Query) : q ≃ᵇᵛ q := by intro db; exact List.Perm.refl _
theorem query_bag_equiv_v_symm {q1 q2 : Query} (h : q1 ≃ᵇᵛ q2) : q2 ≃ᵇᵛ q1 := by intro db; exact (h db).symm
theorem query_bag_equiv_v_trans {q1 q2 q3 : Query} (h12 : q1 ≃ᵇᵛ q2) (h23 : q2 ≃ᵇᵛ q3) : q1 ≃ᵇᵛ q3 := by intro db; exact (h12 db).trans (h23 db)

theorem query_set_equiv_v_refl (q : Query) : q ≃ˢᵛ q := by intro db k; exact Iff.rfl
theorem query_set_equiv_v_symm {q1 q2 : Query} (h : q1 ≃ˢᵛ q2) : q2 ≃ˢᵛ q1 := by intro db k; exact (h db k).symm
theorem query_set_equiv_v_trans {q1 q2 q3 : Query} (h12 : q1 ≃ˢᵛ q2) (h23 : q2 ≃ˢᵛ q3) : q1 ≃ˢᵛ q3 := by intro db k; exact (h12 db k).trans (h23 db k)

/-- Bag equivalence implies value-level bag equivalence -/
theorem QueryBagEquiv.toBagEquivV {q1 q2 : Query} (h : q1 ≃ᵇ q2) : q1 ≃ᵇᵛ q2 := by
  intro db; exact (h db).map _

/-- Set equivalence implies value-level set equivalence -/
theorem QuerySetEquiv.toSetEquivV {q1 q2 : Query} (h : q1 ≃ˢ q2) : q1 ≃ˢᵛ q2 := by
  intro db k; simp only [List.mem_map]
  exact ⟨fun ⟨r, hr, hk⟩ => ⟨r, (h db r).mp hr, hk⟩, fun ⟨r, hr, hk⟩ => ⟨r, (h db r).mpr hr, hk⟩⟩

/-- Value-level bag equivalence implies value-level set equivalence -/
theorem QueryBagEquivV.toSetEquivV {q1 q2 : Query} (h : q1 ≃ᵇᵛ q2) : q1 ≃ˢᵛ q2 := by
  intro db k; exact (h db).mem_iff

theorem stmt_equiv_refl (s : Stmt) : s ≃ s := by intro db; rfl
theorem stmt_equiv_symm {s1 s2 : Stmt} (h : s1 ≃ s2) : s2 ≃ s1 := by intro db; exact (h db).symm
theorem stmt_equiv_trans {s1 s2 s3 : Stmt} (h12 : s1 ≃ s2) (h23 : s2 ≃ s3) : s1 ≃ s3 := by intro db; rw [h12 db, h23 db]

end SqlEquiv
