/-
  Property-based tests for optimizer correctness.

  These are the highest-value tests: optimizeExpr and normalizeExprCanonical
  are axiomatized (not proven), so SlimCheck is the primary defense against
  optimizer bugs that silently change expression semantics.
-/
import LSpec
import SqlEquiv
import LSpecTests.Generators

open LSpec SlimCheck
open SqlEquiv

namespace OptimizerEquiv

-- ============================================================================
-- optimizeExpr preserves semantics
-- ============================================================================

def optimizeExprTests : TestSeq :=
  check "optimizeExpr preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (optimizeExpr e.expr) == evalExpr [] e.expr)

-- ============================================================================
-- normalizeExprCanonical preserves semantics and is idempotent
-- ============================================================================

def normalizeTests : TestSeq :=
  check "normalizeExprCanonical preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (normalizeExprCanonical e.expr) == evalExpr [] e.expr) $
  check "normalizeExprCanonical is idempotent" (∀ e : BoundedGroundExpr,
    normalizeExprCanonical (normalizeExprCanonical e.expr) ==
    normalizeExprCanonical e.expr)

-- ============================================================================
-- Regression: identity laws must not fire on non-boolean operands
-- ============================================================================

-- Non-boolean int literals
private def intAndTrue := Expr.binOp .and (.lit (.int 4)) (.lit (.bool true))
private def trueAndInt := Expr.binOp .and (.lit (.bool true)) (.lit (.int 4))
private def intOrFalse := Expr.binOp .or (.lit (.int 4)) (.lit (.bool false))
private def falseOrInt := Expr.binOp .or (.lit (.bool false)) (.lit (.int 4))
-- NULL literals
private def nullAndTrue := Expr.binOp .and (.lit (.null none)) (.lit (.bool true))
private def trueAndNull := Expr.binOp .and (.lit (.bool true)) (.lit (.null none))
private def nullOrFalse := Expr.binOp .or (.lit (.null none)) (.lit (.bool false))
private def falseOrNull := Expr.binOp .or (.lit (.bool false)) (.lit (.null none))
-- Non-literal non-boolean (arithmetic expression)
private def arithAndTrue := Expr.binOp .and (.binOp .add (.lit (.int 1)) (.lit (.int 2))) (.lit (.bool true))
private def trueAndArith := Expr.binOp .and (.lit (.bool true)) (.binOp .add (.lit (.int 1)) (.lit (.int 2)))
private def arithOrFalse := Expr.binOp .or (.binOp .add (.lit (.int 1)) (.lit (.int 2))) (.lit (.bool false))
private def falseOrArith := Expr.binOp .or (.lit (.bool false)) (.binOp .add (.lit (.int 1)) (.lit (.int 2)))

def identityLawRegressionTests : TestSeq :=
  -- Int literals
  test "int AND TRUE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws intAndTrue) == evalExpr [] intAndTrue) $
  test "TRUE AND int: identity law must not fire" (
    evalExpr [] (applyIdentityLaws trueAndInt) == evalExpr [] trueAndInt) $
  test "int OR FALSE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws intOrFalse) == evalExpr [] intOrFalse) $
  test "FALSE OR int: identity law must not fire" (
    evalExpr [] (applyIdentityLaws falseOrInt) == evalExpr [] falseOrInt) $
  -- NULL literals
  test "NULL AND TRUE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws nullAndTrue) == evalExpr [] nullAndTrue) $
  test "TRUE AND NULL: identity law must not fire" (
    evalExpr [] (applyIdentityLaws trueAndNull) == evalExpr [] trueAndNull) $
  test "NULL OR FALSE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws nullOrFalse) == evalExpr [] nullOrFalse) $
  test "FALSE OR NULL: identity law must not fire" (
    evalExpr [] (applyIdentityLaws falseOrNull) == evalExpr [] falseOrNull) $
  -- Non-literal non-boolean (arithmetic sub-expressions)
  test "(1+2) AND TRUE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws arithAndTrue) == evalExpr [] arithAndTrue) $
  test "TRUE AND (1+2): identity law must not fire" (
    evalExpr [] (applyIdentityLaws trueAndArith) == evalExpr [] trueAndArith) $
  test "(1+2) OR FALSE: identity law must not fire" (
    evalExpr [] (applyIdentityLaws arithOrFalse) == evalExpr [] arithOrFalse) $
  test "FALSE OR (1+2): identity law must not fire" (
    evalExpr [] (applyIdentityLaws falseOrArith) == evalExpr [] falseOrArith)

-- ============================================================================
-- Regression: eliminateDoubleNegation, applyIdempotentLaws, applyComplementLaws
-- must not fire on non-boolean operands
-- ============================================================================

-- Double negation on non-boolean
private def notNotInt := Expr.unaryOp .not (.unaryOp .not (.lit (.int 42)))
private def notNotString := Expr.unaryOp .not (.unaryOp .not (.lit (.string "hi")))
private def notNotNull := Expr.unaryOp .not (.unaryOp .not (.lit (.null none)))
-- Double negation on non-literal non-boolean (CASE returning int)
private def notNotCase := Expr.unaryOp .not (.unaryOp .not
  (.case [(.lit (.bool true), .lit (.int 1))] (some (.lit (.int 2)))))
-- Idempotent on non-boolean
private def intAndInt := Expr.binOp .and (.lit (.int 5)) (.lit (.int 5))
private def intOrInt := Expr.binOp .or (.lit (.int 5)) (.lit (.int 5))
private def nullAndNull := Expr.binOp .and (.lit (.null none)) (.lit (.null none))
-- Idempotent on col ref (unknown type)
private def colAndCol := Expr.binOp .and (.col ⟨none, "x"⟩) (.col ⟨none, "x"⟩)
-- Complement on non-boolean
private def intAndNotInt := Expr.binOp .and (.lit (.int 3)) (.unaryOp .not (.lit (.int 3)))
private def intOrNotInt := Expr.binOp .or (.lit (.int 3)) (.unaryOp .not (.lit (.int 3)))
private def strAndNotStr := Expr.binOp .and (.lit (.string "x")) (.unaryOp .not (.lit (.string "x")))

def boolGuardRegressionTests : TestSeq :=
  -- eliminateDoubleNegation: check AST unchanged (eval alone can't distinguish for NULL)
  test "NOT NOT int: must not fire" (
    eliminateDoubleNegation notNotInt == notNotInt) $
  test "NOT NOT string: must not fire" (
    eliminateDoubleNegation notNotString == notNotString) $
  test "NOT NOT null: AST must stay unchanged" (
    eliminateDoubleNegation notNotNull == notNotNull) $
  test "NOT NOT (CASE int): must not fire" (
    eliminateDoubleNegation notNotCase == notNotCase) $
  -- applyIdempotentLaws
  test "int AND int: idempotent must not fire" (
    evalExpr [] (applyIdempotentLaws intAndInt) == evalExpr [] intAndInt) $
  test "int OR int: idempotent must not fire" (
    evalExpr [] (applyIdempotentLaws intOrInt) == evalExpr [] intOrInt) $
  test "null AND null: idempotent must not fire" (
    evalExpr [] (applyIdempotentLaws nullAndNull) == evalExpr [] nullAndNull) $
  test "col AND col: idempotent must not fire (unknown type)" (
    applyIdempotentLaws colAndCol == colAndCol) $
  -- applyComplementLaws
  test "int AND NOT int: complement must not fire" (
    evalExpr [] (applyComplementLaws intAndNotInt) == evalExpr [] intAndNotInt) $
  test "int OR NOT int: complement must not fire" (
    evalExpr [] (applyComplementLaws intOrNotInt) == evalExpr [] intOrNotInt) $
  test "string AND NOT string: complement must not fire" (
    evalExpr [] (applyComplementLaws strAndNotStr) == evalExpr [] strAndNotStr) $
  -- Comparisons are not definitely bool (can return none under NULL propagation)
  test "(x=1) AND NOT (x=1): complement must not fire" (
    let cmp := Expr.binOp .eq (.col ⟨none, "x"⟩) (.lit (.int 1))
    let e := Expr.binOp .and cmp (.unaryOp .not cmp)
    applyComplementLaws e == e)

-- ============================================================================
-- Regression: simplifyArithmetic null propagation / type mismatch / div-by-zero
-- ============================================================================

-- Null propagation: NULL * 0 must stay NULL, not become 0
private def nullMulZero := Expr.binOp .mul (.lit (.null none)) (.lit (.int 0))
private def zeroMulNull := Expr.binOp .mul (.lit (.int 0)) (.lit (.null none))
private def zeroDivNull := Expr.binOp .div (.lit (.int 0)) (.lit (.null none))
-- Division by zero: 0 / 0 must not become 0
private def zeroDivZero := Expr.binOp .div (.lit (.int 0)) (.lit (.int 0))
-- Type mismatches on identity arms
private def stringAddZero := Expr.binOp .add (.lit (.string "hi")) (.lit (.int 0))
private def zeroAddString := Expr.binOp .add (.lit (.int 0)) (.lit (.string "hi"))
private def boolSubZero := Expr.binOp .sub (.lit (.bool true)) (.lit (.int 0))
private def nullMulOne := Expr.binOp .mul (.lit (.null none)) (.lit (.int 1))
private def oneMulBool := Expr.binOp .mul (.lit (.int 1)) (.lit (.bool false))
private def stringDivOne := Expr.binOp .div (.lit (.string "x")) (.lit (.int 1))

-- Non-literal non-int expressions (boolean/string sub-expressions)
private def boolExprAddZero := Expr.binOp .add (.binOp .and (.lit (.bool true)) (.lit (.bool false))) (.lit (.int 0))
private def cmpExprMulOne := Expr.binOp .mul (.binOp .eq (.lit (.int 1)) (.lit (.int 1))) (.lit (.int 1))
private def concatExprAddZero := Expr.binOp .add (.binOp .concat (.lit (.string "a")) (.lit (.string "b"))) (.lit (.int 0))

def arithmeticSoundnessTests : TestSeq :=
  -- Null propagation
  test "NULL*0: annihilation must not fire" (
    evalExpr [] (simplifyArithmetic nullMulZero) == evalExpr [] nullMulZero) $
  test "0*NULL: annihilation must not fire" (
    evalExpr [] (simplifyArithmetic zeroMulNull) == evalExpr [] zeroMulNull) $
  test "0/NULL: must preserve null propagation" (
    evalExpr [] (optimizeExpr zeroDivNull) == evalExpr [] zeroDivNull) $
  -- Division by zero
  test "0/0: must not rewrite to 0" (
    evalExpr [] (optimizeExpr zeroDivZero) == evalExpr [] zeroDivZero) $
  -- Type mismatches on identity arms
  test "string+0: identity must not fire" (
    evalExpr [] (simplifyArithmetic stringAddZero) == evalExpr [] stringAddZero) $
  test "0+string: identity must not fire" (
    evalExpr [] (simplifyArithmetic zeroAddString) == evalExpr [] zeroAddString) $
  test "bool-0: identity must not fire" (
    evalExpr [] (simplifyArithmetic boolSubZero) == evalExpr [] boolSubZero) $
  test "NULL*1: identity must not fire" (
    evalExpr [] (simplifyArithmetic nullMulOne) == evalExpr [] nullMulOne) $
  test "1*bool: identity must not fire" (
    evalExpr [] (simplifyArithmetic oneMulBool) == evalExpr [] oneMulBool) $
  test "string/1: identity must not fire" (
    evalExpr [] (simplifyArithmetic stringDivOne) == evalExpr [] stringDivOne) $
  -- Non-literal non-int expressions
  test "(TRUE AND FALSE)+0: identity must not fire" (
    evalExpr [] (simplifyArithmetic boolExprAddZero) == evalExpr [] boolExprAddZero) $
  test "(1=1)*1: identity must not fire" (
    evalExpr [] (simplifyArithmetic cmpExprMulOne) == evalExpr [] cmpExprMulOne) $
  test "(\"a\"||\"b\")+0: identity must not fire" (
    evalExpr [] (simplifyArithmetic concatExprAddZero) == evalExpr [] concatExprAddZero)

-- ============================================================================
-- Individual optimizer passes
-- ============================================================================

def optimizerPassTests : TestSeq :=
  check "applyIdentityLaws preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (applyIdentityLaws e.expr) == evalExpr [] e.expr) $
  check "eliminateDoubleNegation preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (eliminateDoubleNegation e.expr) == evalExpr [] e.expr) $
  check "applyIdempotentLaws preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (applyIdempotentLaws e.expr) == evalExpr [] e.expr) $
  check "applyComplementLaws preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (applyComplementLaws e.expr) == evalExpr [] e.expr) $
  check "simplifyArithmetic preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (simplifyArithmetic e.expr) == evalExpr [] e.expr) $
  check "applyDeMorgan preserves semantics" (∀ e : BoundedGroundExpr,
    evalExpr [] (applyDeMorgan e.expr) == evalExpr [] e.expr)

-- ============================================================================
-- All optimizer tests
-- ============================================================================

def allTests : TestSeq :=
  group "optimizeExpr" optimizeExprTests $
  group "normalizeExprCanonical" normalizeTests $
  group "Identity Law Regression" identityLawRegressionTests $
  group "Bool Guard Regression" boolGuardRegressionTests $
  group "Arithmetic Soundness" arithmeticSoundnessTests $
  group "Individual Passes" optimizerPassTests

end OptimizerEquiv
