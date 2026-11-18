/-
  Typed core phase 1 (#290): differential test of `SqlCore`'s scalar operators
  against `SqlEquiv.evalBinOp` / `SqlEquiv.evalUnaryOp`.

  Operands range over well-typed pairs: both operands of one type, or NULL.
  A `SqlCore` result is mapped to `SqlEquiv`'s encoding: `ok none` is
  `some (.null none)`, `ok (some v)` is `some v`, and an error is `none`.
  Each disagreement must be one of the documented differences
  (`expectedDifference`); any other disagreement fails the test.

  Numeric operands mix integers and decimals: both sides promote int to
  decimal (decision 6). A `SqlCore` decimal `q : ℚ` is compared through
  `SqlEquiv.Value.mkDecimal` at the least scale that represents it.

  Documented differences:
  * `< <= > >=` on two booleans: `SqlCore` orders `false < true`; `SqlEquiv`'s
    `Value.compare` has no boolean case, so it is an error there.
  * `%` with a decimal operand: `SqlCore` is exact (Postgres and DuckDB agree);
    `SqlEquiv` leaves decimal `%` unimplemented (#201), an error. These cases
    are checked against `refMod`, a scaled-integer `Int.tmod` reference.
  * `/` with a decimal operand: `SqlCore` is exact (phase 8d, registry T3);
    `SqlEquiv` leaves decimal `/` unimplemented (#201), an error. These cases
    are checked by multiplying back: the quotient times the divisor is the
    dividend.
  `LIKE` (and sqlite's `likeCI`) used to differ when the pattern has `_` or a
  `%` inside it, until #323 replaced `SqlEquiv`'s `simpleLike` with a port of
  `likeText`. Both now share one algorithm, so every `LIKE` case is also checked
  against `refLike`, a backtracking matcher written independently of it.
  Ill-typed operands are out of scope: `SqlCore` makes them `typeMismatch`,
  while `SqlEquiv` short-circuits `FALSE AND 1` to `FALSE`.
-/
import SqlCore
import SqlEquiv

namespace SqlCoreTest.ScalarDiff

/-- A decimal fraction as `SqlEquiv`'s canonical scaled integer: the least
scale `s` (up to 20) with `den ∣ 10^s`. -/
def ratToOld (q : ℚ) : SqlEquiv.Value :=
  match (List.range 21).find? (fun s => 10 ^ s % q.den == 0) with
  | some s => SqlEquiv.Value.mkDecimal (q.num * ((10 ^ s / q.den : Nat) : Int)) s
  | none => .null none  -- not a decimal fraction; never produced by the domain below

/-- A `SqlCore` value in `SqlEquiv`'s encoding. -/
def toOld : SqlCore.Value → SqlEquiv.Value
  | .int z => .int z
  | .text s => .string s
  | .bool b => .bool b
  | .decimal q => ratToOld q

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
def decimals : List SqlCore.Datum :=
  [(0 : ℚ), 1/2, -3/2, 2, 9/4, 15/2, -15/2, 1/10].map (some ∘ .decimal)
/-- Texts and `LIKE` patterns: wildcards, letter case, a non-ASCII letter, NULL. -/
def likeTexts : List SqlCore.Datum := [none] ++
  (["", "a", "ab", "aB", "Ab", "abc", "b", "é", "É", "%", "_", "a%", "%b", "_b", "a_", "%a%",
    "A%", "%B", "a%c", "a_c", "%%", "__", "%_%", "_%_", "a%%b", "%é"].map (some ∘ .text))
/-- Integers and decimals, NULL once. -/
def nums : List SqlCore.Datum := ints ++ decimals

/-- Operator pairs: (name, SqlCore op, SqlEquiv op, operand types). -/
def binOps : List (String × SqlCore.BinOp × SqlEquiv.BinOp × List (List SqlCore.Datum)) :=
  [("+", .arith .add, .add, [nums]), ("-", .arith .sub, .sub, [nums]),
   ("*", .arith .mul, .mul, [nums]), ("/", .arith .div, .div, [nums]),
   ("%", .arith .mod, .mod, [nums]),
   ("=", .cmp .eq, .eq, [nums, texts, bools]), ("<>", .cmp .ne, .ne, [nums, texts, bools]),
   ("<", .cmp .lt, .lt, [nums, texts, bools]), ("<=", .cmp .le, .le, [nums, texts, bools]),
   (">", .cmp .gt, .gt, [nums, texts, bools]), (">=", .cmp .ge, .ge, [nums, texts, bools]),
   ("AND", .and, .and, [bools]), ("OR", .or, .or, [bools]),
   ("||", .concat, .concat, [texts]),
   ("LIKE", .like false, .like, [likeTexts]), ("LIKE (sqlite)", .like true, .likeCI, [likeTexts])]

def unOps : List (String × SqlCore.UnOp × SqlEquiv.UnaryOp × List (List SqlCore.Datum)) :=
  [("NOT", .not, .not, [bools]), ("-", .neg, .neg, [nums]),
   ("IS NULL", .isNull, .isNull, [nums, texts, bools]),
   ("IS NOT NULL", .isNotNull, .isNotNull, [nums, texts, bools])]

def isBool : SqlCore.Datum → Bool
  | some (.bool _) => true
  | _ => false

def isDecimal : SqlCore.Datum → Bool
  | some (.decimal _) => true
  | _ => false

/-- Independent reference for decimal `%`: scale both operands by `10^k` to
integers and take `Int.tmod` (truncating, the dividend's sign), as
`SqlEquiv` does for integers. -/
def refMod (a b : SqlCore.Datum) : Option SqlCore.Datum :=
  let toQ : SqlCore.Datum → Option ℚ
    | some (.int z) => some z
    | some (.decimal q) => some q
    | _ => none
  match toQ a, toQ b with
  | some p, some q =>
    let k : ℚ := 10 ^ 6
    let (x, y) := ((p * k).num, (q * k).num)  -- exact: denominators divide 10^6
    if y = 0 then none else some (some (.decimal ((x.tmod y : ℤ) / k)))
  | _, _ => none

/-- A documented `%` difference must still match the reference. -/
def modMatchesRef (a b : SqlCore.Datum) : Bool :=
  match refMod a b, SqlCore.evalBinOp (.arith .mod) a b with
  | some r, .ok d => r == d
  | _, _ => false

/-- A documented decimal `/` difference must multiply back: `(a / b) * b = a`. -/
def divMatchesRef (a b : SqlCore.Datum) : Bool :=
  let toQ : SqlCore.Datum → Option ℚ
    | some (.int z) => some z
    | some (.decimal q) => some q
    | _ => none
  match toQ a, toQ b, SqlCore.evalBinOp (.arith .div) a b with
  | some x, some y, .ok (some (.decimal r)) => y != 0 && r * y == x
  | _, _, _ => false

/-- Independent reference for `LIKE`: backtracking over where each `%` stops, with fuel. -/
def refLikeAux (eq : Char → Char → Bool) : ℕ → List Char → List Char → Bool
  | 0, _, _ => false
  | _ + 1, [], s => s.isEmpty
  | f + 1, '%' :: p, s => (List.range (s.length + 1)).any fun k => refLikeAux eq f p (s.drop k)
  | f + 1, '_' :: p, _ :: s => refLikeAux eq f p s
  | f + 1, d :: p, c :: s => d != '_' && d != '%' && eq d c && refLikeAux eq f p s
  | _ + 1, _ :: _, [] => false

def refLike (ci : Bool) (s p : String) : Bool :=
  refLikeAux (if ci then fun a b => a.toLower == b.toLower else (· == ·)) (p.length + 1) p.toList
    s.toList

/-- A `LIKE` on two texts must match the independent reference (#323). -/
def likeMatchesRef (ci : Bool) (a b : SqlCore.Datum) : Bool :=
  match a, b with
  | some (.text s), some (.text p) =>
    SqlCore.evalBinOp (.like ci) a b == .ok (some (.bool (refLike ci s p)))
  | _, _ => false

/-- The documented differences (see the header). -/
def expectedDifference (name : String) (a b : SqlCore.Datum) : Bool :=
  (["<", "<=", ">", ">="].contains name && isBool a && isBool b) ||
  (name == "%" && (isDecimal a || isDecimal b) && modMatchesRef a b) ||
  (name == "/" && (isDecimal a || isDecimal b) && divMatchesRef a b)

/-- Whether `a LIKE b` (two texts) disagrees with the independent reference. -/
def likeRefMismatch (name : String) (a b : SqlCore.Datum) : Bool :=
  match a, b with
  | some (.text _), some (.text _) =>
    (name == "LIKE" && !likeMatchesRef false a b) ||
      (name == "LIKE (sqlite)" && !likeMatchesRef true a b)
  | _, _ => false

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
          if likeRefMismatch name a b then
            bad := s!"{repr a} {name} {repr b}: differs from refLike" :: bad
          if new != old then
            if expectedDifference name a b then
              documented := documented + 1
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
