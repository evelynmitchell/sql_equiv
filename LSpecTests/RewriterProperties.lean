/-
  Property-based tests for the Certified Expression Rewriter.

  Tests that certifiedRewrite preserves semantics, is idempotent,
  and produces structurally correct output (e.g., no BETWEEN nodes
  after rewriting, empty IN lists become FALSE, etc.).
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace RewriterProperties

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Check if an expression contains any BETWEEN node -/
private partial def containsBetween : Expr → Bool
  | .between _ _ _ => true
  | .binOp _ l r => containsBetween l || containsBetween r
  | .unaryOp _ e => containsBetween e
  | .inList e _ vals => containsBetween e ||
      vals.foldl (fun acc v => acc || containsBetween v) false
  | .«case» branches else_ =>
    branches.foldl (fun acc (c, t) => acc || containsBetween c || containsBetween t) false ||
    match else_ with | some e => containsBetween e | none => false
  | .func _ args => args.foldl (fun acc e => acc || containsBetween e) false
  | .agg _ (some e) _ => containsBetween e
  | .inSubquery e _ _ => containsBetween e
  | _ => false

-- ============================================================================
-- Semantic Equivalence
-- ============================================================================

def semanticEquivTests (cfg : Configuration) : TestSeq :=
  -- Core property: rewriting preserves evaluation
  check (cfg := cfg) "certifiedRewrite preserves semantics (BoundedGroundExpr)"
    (∀ e : BoundedGroundExpr,
      evalExpr [] (certifiedRewrite e.expr).val == evalExpr [] e.expr) $
  -- Boolean expressions
  check (cfg := cfg) "certifiedRewrite preserves semantics (BoolGroundExpr)"
    (∀ e : BoolGroundExpr,
      evalExpr [] (certifiedRewrite e.expr).val == evalExpr [] e.expr) $
  -- Integer expressions
  check (cfg := cfg) "certifiedRewrite preserves semantics (IntGroundExpr)"
    (∀ e : IntGroundExpr,
      evalExpr [] (certifiedRewrite e.expr).val == evalExpr [] e.expr)

-- ============================================================================
-- Idempotency
-- ============================================================================

def idempotencyTests (cfg : Configuration) : TestSeq :=
  -- Phase 2b recurses into all Expr subexpressions (func, case, inList, agg, windowFn, inSubquery).
  -- Only SelectStmt payloads (.exists, .subquery, .inSubquery sel) are not recursed into.
  -- Since genGroundExpr generates only lit/binOp/unaryOp/CASE (no SelectStmt nodes),
  -- structural idempotency should hold for both BoolGroundExpr and BoundedGroundExpr.
  check (cfg := cfg) "certifiedRewrite is idempotent (BoolGroundExpr)"
    (∀ e : BoolGroundExpr,
      let r1 := (certifiedRewrite e.expr).val
      (certifiedRewrite r1).val == r1) $
  check (cfg := cfg) "certifiedRewrite is idempotent (BoundedGroundExpr)"
    (∀ e : BoundedGroundExpr,
      let r1 := (certifiedRewrite e.expr).val
      (certifiedRewrite r1).val == r1) $
  check (cfg := cfg) "double rewrite preserves semantics (BoundedGroundExpr)"
    (∀ e : BoundedGroundExpr,
      let r1 := (certifiedRewrite e.expr).val
      let r2 := (certifiedRewrite r1).val
      evalExpr [] r2 == evalExpr [] e.expr)

-- ============================================================================
-- Literals are no-ops
-- ============================================================================

def literalTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "certifiedRewrite on literals is identity"
    (∀ v : Value,
      (certifiedRewrite (.lit v)).val == .lit v)

-- ============================================================================
-- AND short-circuit
-- ============================================================================

def andShortCircuitTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "e AND FALSE → FALSE"
    (∀ e : BoundedGroundExpr,
      (certifiedRewrite (.binOp .and e.expr (.lit (.bool false)))).val ==
        .lit (.bool false)) $
  check (cfg := cfg) "FALSE AND e → FALSE"
    (∀ e : BoundedGroundExpr,
      (certifiedRewrite (.binOp .and (.lit (.bool false)) e.expr)).val ==
        .lit (.bool false))

-- ============================================================================
-- OR short-circuit
-- ============================================================================

def orShortCircuitTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "e OR TRUE → TRUE"
    (∀ e : BoundedGroundExpr,
      (certifiedRewrite (.binOp .or e.expr (.lit (.bool true)))).val ==
        .lit (.bool true)) $
  check (cfg := cfg) "TRUE OR e → TRUE"
    (∀ e : BoundedGroundExpr,
      (certifiedRewrite (.binOp .or (.lit (.bool true)) e.expr)).val ==
        .lit (.bool true))

-- ============================================================================
-- NOT comparison flips (structural)
-- ============================================================================

def notComparisonFlipTests : TestSeq :=
  -- NOT(a = b) → a <> b
  test "NOT(EQ) → NE" (
    (certifiedRewrite (.unaryOp .not (.binOp .eq (.lit (.int 1)) (.lit (.int 2))))).val ==
      .binOp .ne (.lit (.int 1)) (.lit (.int 2))) $
  -- NOT(a <> b) → a = b
  test "NOT(NE) → EQ" (
    (certifiedRewrite (.unaryOp .not (.binOp .ne (.lit (.int 1)) (.lit (.int 2))))).val ==
      .binOp .eq (.lit (.int 1)) (.lit (.int 2))) $
  -- NOT(a < b) → a >= b
  test "NOT(LT) → GE" (
    (certifiedRewrite (.unaryOp .not (.binOp .lt (.lit (.int 1)) (.lit (.int 2))))).val ==
      .binOp .ge (.lit (.int 1)) (.lit (.int 2))) $
  -- NOT(a <= b) → a > b
  test "NOT(LE) → GT" (
    (certifiedRewrite (.unaryOp .not (.binOp .le (.lit (.int 1)) (.lit (.int 2))))).val ==
      .binOp .gt (.lit (.int 1)) (.lit (.int 2))) $
  -- NOT(a > b) → a <= b
  test "NOT(GT) → LE" (
    (certifiedRewrite (.unaryOp .not (.binOp .gt (.lit (.int 1)) (.lit (.int 2))))).val ==
      .binOp .le (.lit (.int 1)) (.lit (.int 2))) $
  -- NOT(a >= b) → a < b
  test "NOT(GE) → LT" (
    (certifiedRewrite (.unaryOp .not (.binOp .ge (.lit (.int 1)) (.lit (.int 2))))).val ==
      .binOp .lt (.lit (.int 1)) (.lit (.int 2)))

-- ============================================================================
-- BETWEEN always expands (no BETWEEN in output)
-- ============================================================================

def betweenExpansionTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "BETWEEN is always expanded (no BETWEEN in output)"
    (∀ e lo hi : BoundedGroundExpr,
      !containsBetween (certifiedRewrite (.between e.expr lo.expr hi.expr)).val)

-- ============================================================================
-- IN empty list
-- ============================================================================

def inListTests : TestSeq :=
  test "IN empty → FALSE" (
    (certifiedRewrite (.inList (.lit (.int 1)) false [])).val ==
      .lit (.bool false)) $
  test "NOT IN empty → TRUE" (
    (certifiedRewrite (.inList (.lit (.int 1)) true [])).val ==
      .lit (.bool true)) $
  test "IN singleton → EQ" (
    (certifiedRewrite (.inList (.lit (.int 1)) false [.lit (.int 2)])).val ==
      .binOp .eq (.lit (.int 1)) (.lit (.int 2))) $
  test "NOT IN singleton → NE" (
    (certifiedRewrite (.inList (.lit (.int 1)) true [.lit (.int 2)])).val ==
      .binOp .ne (.lit (.int 1)) (.lit (.int 2)))

-- ============================================================================
-- CASE simplifications
-- ============================================================================

def caseTests : TestSeq :=
  test "CASE WHEN TRUE THEN x ELSE y → x" (
    (certifiedRewrite (.«case» [(.lit (.bool true), .lit (.int 1))] (some (.lit (.int 2))))).val ==
      .lit (.int 1)) $
  test "CASE WHEN FALSE THEN x ELSE y → y" (
    (certifiedRewrite (.«case» [(.lit (.bool false), .lit (.int 1))] (some (.lit (.int 2))))).val ==
      .lit (.int 2)) $
  test "CASE (empty) ELSE y → y" (
    (certifiedRewrite (.«case» [] (some (.lit (.int 42))))).val ==
      .lit (.int 42)) $
  test "CASE (empty, no else) → NULL" (
    (certifiedRewrite (.«case» [] none)).val ==
      .lit (.null none))

-- ============================================================================
-- CASE semantic equivalence
-- ============================================================================

def caseSemanticTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "CASE WHEN TRUE THEN e ELSE d preserves semantics"
    (∀ e d : BoolGroundExpr,
      evalExpr [] (certifiedRewrite (.«case» [(.lit (.bool true), e.expr)] (some d.expr))).val ==
      evalExpr [] (.«case» [(.lit (.bool true), e.expr)] (some d.expr))) $
  check (cfg := cfg) "CASE WHEN FALSE THEN e ELSE d preserves semantics"
    (∀ e d : BoolGroundExpr,
      evalExpr [] (certifiedRewrite (.«case» [(.lit (.bool false), e.expr)] (some d.expr))).val ==
      evalExpr [] (.«case» [(.lit (.bool false), e.expr)] (some d.expr)))

-- ============================================================================
-- NOT(BETWEEN) special handling
-- ============================================================================

def notBetweenTests : TestSeq :=
  -- NOT(x BETWEEN 1 AND 10) → x < 1 OR x > 10
  test "NOT(BETWEEN) → OR(LT, GT)" (
    (certifiedRewrite (.unaryOp .not (.between (.lit (.int 5)) (.lit (.int 1)) (.lit (.int 10))))).val ==
      .binOp .or (.binOp .lt (.lit (.int 5)) (.lit (.int 1)))
                  (.binOp .gt (.lit (.int 5)) (.lit (.int 10)))) $
  -- NOT(BETWEEN) output has no BETWEEN
  test "NOT(BETWEEN) output contains no BETWEEN" (
    !containsBetween (certifiedRewrite (.unaryOp .not (.between (.lit (.int 5)) (.lit (.int 1)) (.lit (.int 10))))).val)

-- ============================================================================
-- LIKE empty pattern
-- ============================================================================

def likeTests : TestSeq :=
  test "LIKE '' → EQ ''" (
    (certifiedRewrite (.binOp .like (.lit (.string "hello")) (.lit (.string "")))).val ==
      .binOp .eq (.lit (.string "hello")) (.lit (.string "")))

-- ============================================================================
-- Conditional boolean identity
-- ============================================================================

def boolIdentityTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "e AND TRUE preserves semantics (BoolGroundExpr)"
    (∀ e : BoolGroundExpr,
      evalExpr [] (certifiedRewrite (.binOp .and e.expr (.lit (.bool true)))).val ==
        evalExpr [] (.binOp .and e.expr (.lit (.bool true)))) $
  check (cfg := cfg) "TRUE AND e preserves semantics (BoolGroundExpr)"
    (∀ e : BoolGroundExpr,
      evalExpr [] (certifiedRewrite (.binOp .and (.lit (.bool true)) e.expr)).val ==
        evalExpr [] (.binOp .and (.lit (.bool true)) e.expr)) $
  check (cfg := cfg) "e OR FALSE preserves semantics (BoolGroundExpr)"
    (∀ e : BoolGroundExpr,
      evalExpr [] (certifiedRewrite (.binOp .or e.expr (.lit (.bool false)))).val ==
        evalExpr [] (.binOp .or e.expr (.lit (.bool false)))) $
  check (cfg := cfg) "FALSE OR e preserves semantics (BoolGroundExpr)"
    (∀ e : BoolGroundExpr,
      evalExpr [] (certifiedRewrite (.binOp .or (.lit (.bool false)) e.expr)).val ==
        evalExpr [] (.binOp .or (.lit (.bool false)) e.expr))

-- ============================================================================
-- Conditional arithmetic identity
-- ============================================================================

def arithIdentityTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "e + 0 preserves semantics (IntGroundExpr)"
    (∀ e : IntGroundExpr,
      evalExpr [] (certifiedRewrite (.binOp .add e.expr (.lit (.int 0)))).val ==
        evalExpr [] (.binOp .add e.expr (.lit (.int 0)))) $
  check (cfg := cfg) "e * 1 preserves semantics (IntGroundExpr)"
    (∀ e : IntGroundExpr,
      evalExpr [] (certifiedRewrite (.binOp .mul e.expr (.lit (.int 1)))).val ==
        evalExpr [] (.binOp .mul e.expr (.lit (.int 1)))) $
  check (cfg := cfg) "e - 0 preserves semantics (IntGroundExpr)"
    (∀ e : IntGroundExpr,
      evalExpr [] (certifiedRewrite (.binOp .sub e.expr (.lit (.int 0)))).val ==
        evalExpr [] (.binOp .sub e.expr (.lit (.int 0))))

-- ============================================================================
-- NOT NOT
-- ============================================================================

def notNotTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "NOT NOT e preserves semantics (BoolGroundExpr)"
    (∀ e : BoolGroundExpr,
      evalExpr [] (certifiedRewrite (.unaryOp .not (.unaryOp .not e.expr))).val ==
        evalExpr [] (.unaryOp .not (.unaryOp .not e.expr)))


-- ============================================================================
-- Context sweep: rows, real databases, errors, subqueries (#AUDIT)
-- ============================================================================
-- `≃ₑ` (and therefore the kernel proof behind `certifiedRewrite`) only
-- quantifies over rows evaluated against the EMPTY database, and the
-- properties above only evaluate ground expressions with `evalExpr []`.
-- This sweep checks the compiled rewriter against the evaluator in the
-- contexts the proof does not cover: column references bound by real rows,
-- missing columns, evaluation errors (`none`), every `Value` kind, and
-- EXISTS / IN (subquery) against a non-empty database.

private def sweepSel (s : String) : SubQuery :=
  match parseSelectStr s with
  | .ok x => .simple x
  | .error e => panic! s!"sweepSel: {e}"

private def sweepCol (c : String) : Expr := .col ⟨none, c⟩

private def subqNonEmpty : SubQuery := sweepSel "SELECT a FROM t"
private def subqEmpty : SubQuery := sweepSel "SELECT a FROM t WHERE a > 100"

/-- Operands: every Value kind, identity/absorbing constants, NULLs,
    erroring expressions, bound/missing columns, EXISTS. -/
private def sweepAtoms : List Expr := [
  .lit (.int 0), .lit (.int 1), .lit (.int (-3)), .lit (.int 7),
  .lit (.string ""), .lit (.string "a"), .lit (.string "%"),
  .lit (.bool true), .lit (.bool false),
  .lit (Value.mkDecimal 15 1), .lit (Value.mkDecimal 0 0),
  .lit (.null none), .lit (.null (some .int)),
  .binOp .add (.lit (.string "x")) (.lit (.int 1)),  -- type error → none
  .binOp .div (.lit (.int 1)) (.lit (.int 0)),       -- div by zero
  sweepCol "i", sweepCol "s", sweepCol "b", sweepCol "n", sweepCol "missing",
  .«exists» false subqNonEmpty,
  .«exists» true subqEmpty ]

/-- Smaller operand set for nested shapes. -/
private def sweepSmall : List Expr := [
  .lit (.int 0), .lit (.int 1), .lit (.string "a"), .lit (.bool true),
  .lit (.bool false), .lit (.null none), .lit (Value.mkDecimal 15 1),
  .binOp .add (.lit (.string "x")) (.lit (.int 1)),
  sweepCol "i", sweepCol "b", .«exists» false subqNonEmpty ]

private def sweepBinOps : List BinOp :=
  [.add, .sub, .mul, .div, .mod, .eq, .ne, .lt, .le, .gt, .ge, .and, .or, .concat, .like]
private def sweepUnOps : List UnaryOp := [.not, .neg, .isNull, .isNotNull]

/-- Every shape a rewriter arm matches, over the operand sets above. -/
def sweepCases : List Expr := Id.run do
  let mut out : Array Expr := #[]
  for op in sweepBinOps do
    for a in sweepAtoms do
      for b in sweepAtoms do out := out.push (.binOp op a b)
  for op in sweepUnOps do
    for a in sweepAtoms do out := out.push (.unaryOp op a)
  for u in sweepUnOps do
    for op in sweepBinOps do
      for a in sweepSmall do
        for b in sweepSmall do out := out.push (.unaryOp u (.binOp op a b))
  for u in sweepUnOps do
    for u2 in sweepUnOps do
      for a in sweepSmall do out := out.push (.unaryOp u (.unaryOp u2 a))
  for op in sweepBinOps do
    for op2 in [BinOp.and, .or, .add, .mul, .eq, .lt] do
      for a in sweepSmall do
        for b in sweepSmall do
          out := out.push (.binOp op (.binOp op2 a b) (.lit (.bool true)))
          out := out.push (.binOp op (.lit (.int 0)) (.binOp op2 a b))
          out := out.push (.binOp op (.binOp op2 a b) (.lit (.int 1)))
  for a in sweepSmall do
    for lo in sweepSmall do
      for hi in sweepSmall do
        out := out.push (.between a lo hi)
        out := out.push (.unaryOp .not (.between a lo hi))
  for a in sweepAtoms do
    for neg in [false, true] do
      out := out.push (.inList a neg [])
      for v in sweepSmall do
        out := out.push (.inList a neg [v])
        out := out.push (.inList a neg [v, .lit (.int 1)])
      out := out.push (.inSubquery a neg subqNonEmpty)
      out := out.push (.inSubquery a neg subqEmpty)
  for c in sweepSmall do
    for x in sweepSmall do
      out := out.push (.«case» [] (some x))
      out := out.push (.«case» [] none)
      out := out.push (.«case» [(c, x)] (some (.lit (.int 9))))
      out := out.push (.«case» [(c, x)] none)
  for neg in [false, true] do
    for sq in [subqNonEmpty, subqEmpty] do
      out := out.push (.unaryOp .not (.«exists» neg sq))
      out := out.push (.unaryOp .not (.unaryOp .not (.«exists» neg sq)))
  for a in sweepSmall do
    out := out.push (.func "COALESCE" [.binOp .add a (.lit (.int 0)), .lit (.int 5)])
    out := out.push (.func "UPPER" [.binOp .like a (.lit (.string ""))])
  return out.toList

/-- Rows binding the sweep's columns (plus the generator's x/y/z), and an empty row. -/
def sweepRows : List Row := [
  [("i", .int 4), ("s", .string "q"), ("b", .bool true), ("n", .null none),
   ("x", .int 3), ("y", .bool false), ("z", .string "w")],
  [("i", .int 0), ("s", .string ""), ("b", .bool false), ("n", .null (some .int)),
   ("x", .null none), ("y", .int 0), ("z", .bool true)],
  [] ]

def sweepEmptyDb : Database := fun _ => []
def sweepRealDb : Database := fun n =>
  if n == "t" then [[("a", .int 1)], [("a", .int 4)], [("a", .null none)]] else []

/-- Does rewriting `e` change its value in any sweep row, under either database? -/
def rewriteMismatch (e : Expr) : Bool :=
  let e' := (certifiedRewrite e).val
  [sweepEmptyDb, sweepRealDb].any fun db =>
    sweepRows.any fun r => evalExprWithDb db r e != evalExprWithDb db r e'

def contextSweepTests : TestSeq :=
  let mismatches := sweepCases.filter rewriteMismatch
  let rewritten := (sweepCases.filter fun e => !((certifiedRewrite e).val == e)).length
  let firstBad := match mismatches.head? with
    | some e => s!" first: {e.toSql} ⇒ {(certifiedRewrite e).val.toSql}"
    | none => ""
  -- Vacuity guards: the sweep must actually trigger rewrites, and the real
  -- database must actually change subquery results.
  test s!"sweep triggers rewrites ({rewritten} of {sweepCases.length})" (rewritten ≥ 5000) $
  test "real database changes EXISTS / IN-subquery results" (
    evalExprWithDb sweepEmptyDb [] (.«exists» false subqNonEmpty) !=
      evalExprWithDb sweepRealDb [] (.«exists» false subqNonEmpty) &&
    evalExprWithDb sweepEmptyDb [] (.inSubquery (.lit (.int 4)) false subqNonEmpty) !=
      evalExprWithDb sweepRealDb [] (.inSubquery (.lit (.int 4)) false subqNonEmpty)) $
  test "sweep detects an unguarded `a AND TRUE → a` (oracle self-check)" (
    let e : Expr := .binOp .and (.lit (.int 42)) (.lit (.bool true))
    evalExprWithDb sweepEmptyDb [] e != evalExprWithDb sweepEmptyDb [] (.lit (.int 42))) $
  test s!"rewrite preserves evaluation across rows and empty/real db ({mismatches.length} mismatches){firstBad}"
    mismatches.isEmpty

/-- Wrap a random expression in each context that triggers a rewriter arm. -/
private def rewriteContexts (e : Expr) : List Expr := [
  e,
  .binOp .and e (.lit (.bool true)), .binOp .and (.lit (.bool true)) e,
  .binOp .or e (.lit (.bool false)), .binOp .or (.lit (.bool false)) e,
  .binOp .add e (.lit (.int 0)), .binOp .mul (.lit (.int 1)) e,
  .binOp .sub e (.lit (.int 0)),
  .unaryOp .not e, .unaryOp .not (.unaryOp .not e),
  .binOp .like e (.lit (.string "")),
  .inList e false [sweepCol "x"], .inList e true [sweepCol "x"],
  .between e (sweepCol "x") (.lit (.int 5)),
  .unaryOp .not (.between e (.lit (.int 0)) (sweepCol "x")),
  .«case» [(e, sweepCol "x")] (some (.lit (.int 1))),
  .inSubquery e false subqNonEmpty,
  .binOp .and e (.«exists» false subqNonEmpty) ]

def contextPropertyTests (cfg : Configuration) : TestSeq :=
  check (cfg := cfg) "rewrite preserves evaluation across rows and empty/real db (ColumnGroundExpr in rewrite contexts)"
    (∀ e : ColumnGroundExpr, (rewriteContexts e.expr).all (fun c => !rewriteMismatch c))

-- ============================================================================
-- All rewriter property tests
-- ============================================================================

def allTests (cfg : Configuration) : TestSeq :=
  group "Semantic Equivalence" (semanticEquivTests cfg) $
  group "Idempotency" (idempotencyTests cfg) $
  group "Literals" (literalTests cfg) $
  group "AND Short-Circuit" (andShortCircuitTests cfg) $
  group "OR Short-Circuit" (orShortCircuitTests cfg) $
  group "NOT Comparison Flips" notComparisonFlipTests $
  group "BETWEEN Expansion" (betweenExpansionTests cfg) $
  group "IN List" inListTests $
  group "CASE" caseTests $
  group "CASE Semantics" (caseSemanticTests cfg) $
  group "NOT(BETWEEN)" notBetweenTests $
  group "LIKE" likeTests $
  group "Boolean Identity" (boolIdentityTests cfg) $
  group "Arithmetic Identity" (arithIdentityTests cfg) $
  group "NOT NOT" (notNotTests cfg) $
  group "Context Sweep (rows, real db, subqueries)" contextSweepTests $
  group "Context Property (rows, real db)" (contextPropertyTests cfg)

end RewriterProperties
