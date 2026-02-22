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
  group "NOT NOT" (notNotTests cfg)

end RewriterProperties
