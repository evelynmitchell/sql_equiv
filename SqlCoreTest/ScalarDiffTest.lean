/-
  Typed core phase 1 (#290): differential test of `SqlCore`'s scalar operators
  against `SqlEquiv.evalBinOp` / `SqlEquiv.evalUnaryOp`.

  Operands range over well-typed pairs: both operands of one type, or NULL.
  A `SqlCore` result is mapped to `SqlEquiv`'s encoding: `ok none` is
  `some (.null none)`, `ok (some v)` is `some v`, and an error is `none`.
  Each disagreement must be one of the documented differences
  (`expectedDifference`); any other disagreement fails the test.

  Documented differences (decision 6, single-type comparison):
  * `< <= > >=` on two booleans: `SqlCore` orders `false < true`; `SqlEquiv`'s
    `Value.compare` has no boolean case, so it is an error there.
  Ill-typed operands are out of scope: `SqlCore` makes them `typeMismatch`,
  while `SqlEquiv` short-circuits `FALSE AND 1` to `FALSE` and promotes
  int↔decimal.
-/
import SqlCore
import SqlEquiv

namespace SqlCoreTest.ScalarDiff

/-- A `SqlCore` value in `SqlEquiv`'s encoding. -/
def toOld : SqlCore.Value → SqlEquiv.Value
  | .int z => .int z
  | .text s => .string s
  | .bool b => .bool b

def resToOld : Except SqlCore.EvalError SqlCore.Datum → Option SqlEquiv.Value
  | .ok none => some (.null none)
  | .ok (some v) => some (toOld v)
  | .error _ => none

def datumToOld : SqlCore.Datum → Option SqlEquiv.Value
  | none => some (.null none)
  | some v => some (toOld v)

/-- Datums per type, NULL included. -/
def ints : List SqlCore.Datum := [none] ++ ([-7, -2, -1, 0, 1, 2, 3, 7].map (some ∘ .int))
def texts : List SqlCore.Datum := [none] ++ (["", "a", "ab", "b", "B", "é"].map (some ∘ .text))
def bools : List SqlCore.Datum := [none, some (.bool false), some (.bool true)]

/-- Operator pairs: (name, SqlCore op, SqlEquiv op, operand types). -/
def binOps : List (String × SqlCore.BinOp × SqlEquiv.BinOp × List (List SqlCore.Datum)) :=
  [("+", .arith .add, .add, [ints]), ("-", .arith .sub, .sub, [ints]),
   ("*", .arith .mul, .mul, [ints]), ("/", .arith .div, .div, [ints]),
   ("%", .arith .mod, .mod, [ints]),
   ("=", .cmp .eq, .eq, [ints, texts, bools]), ("<>", .cmp .ne, .ne, [ints, texts, bools]),
   ("<", .cmp .lt, .lt, [ints, texts, bools]), ("<=", .cmp .le, .le, [ints, texts, bools]),
   (">", .cmp .gt, .gt, [ints, texts, bools]), (">=", .cmp .ge, .ge, [ints, texts, bools]),
   ("AND", .and, .and, [bools]), ("OR", .or, .or, [bools]),
   ("||", .concat, .concat, [texts])]

def unOps : List (String × SqlCore.UnOp × SqlEquiv.UnaryOp × List (List SqlCore.Datum)) :=
  [("NOT", .not, .not, [bools]), ("-", .neg, .neg, [ints]),
   ("IS NULL", .isNull, .isNull, [ints, texts, bools]),
   ("IS NOT NULL", .isNotNull, .isNotNull, [ints, texts, bools])]

def isBool : SqlCore.Datum → Bool
  | some (.bool _) => true
  | _ => false

/-- The documented differences (see the header). -/
def expectedDifference (name : String) (a b : SqlCore.Datum) : Bool :=
  ["<", "<=", ">", ">="].contains name && isBool a && isBool b

/-- Returns (cases checked, documented differences seen, unexpected disagreements). -/
def run : Nat × Nat × List String := Id.run do
  let mut n := 0
  let mut documented := 0
  let mut bad : List String := []
  for (name, newOp, oldOp, doms) in binOps do
    for dom in doms do
      for a in dom do
        for b in dom do
          n := n + 1
          let new := resToOld (SqlCore.evalBinOp newOp a b)
          let old := SqlEquiv.evalBinOp oldOp (datumToOld a) (datumToOld b)
          if new != old then
            if expectedDifference name a b then documented := documented + 1
            else bad := s!"{repr a} {name} {repr b}: SqlCore {repr new}, SqlEquiv {repr old}" :: bad
  for (name, newOp, oldOp, doms) in unOps do
    for dom in doms do
      for a in dom do
        n := n + 1
        let new := resToOld (SqlCore.evalUnOp newOp a)
        let old := SqlEquiv.evalUnaryOp oldOp (datumToOld a)
        if new != old then
          bad := s!"{name} {repr a}: SqlCore {repr new}, SqlEquiv {repr old}" :: bad
  return (n, documented, bad.reverse)

end SqlCoreTest.ScalarDiff
