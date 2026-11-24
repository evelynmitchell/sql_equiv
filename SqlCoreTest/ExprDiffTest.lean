/-
  Typed core phase 3 (#292): differential test of `SqlCore.Expr.eval` against
  `SqlEquiv.evalExpr`, on the rows of `users` and `items` (from
  `SqlCoreTest.SchemaExamples`).

  Expressions are generated from column and literal atoms: every unary and
  binary operator over atoms, then `AND`/`OR` over the boolean ones, `IN`
  lists and `CASE`. Only well-typed expressions (`Expr.typeOf`) are kept, so
  every disagreement is a difference of semantics, not of error handling.
  Decimal `%` and `/`, documented differences, are covered by
  `ScalarDiffTest` (against independent references) and left out here. The other documented difference, boolean ordering
  (`TRUE < FALSE`), is counted separately (`hasBoolOrder`).
-/
import SqlCoreTest.SchemaDiffTest

namespace SqlCoreTest.ExprDiff
open SqlCore SqlCoreTest.SchemaExamples SqlCoreTest.ScalarDiff

/-- An operator of `SqlEquiv`, or the function call it is there (phase 9.1, #459). -/
def unOld (op : UnOp) (e : SqlEquiv.Expr) : SqlEquiv.Expr :=
  match op with
  | .not => .unaryOp .not e | .neg => .unaryOp .neg e
  | .isNull => .unaryOp .isNull e | .isNotNull => .unaryOp .isNotNull e
  | .round d => .func "ROUND" [e, .lit (.int d)]
  | .lower => .func "LOWER" [e] | .upper => .func "UPPER" [e] | .length => .func "LENGTH" [e]
  | .toDecimal => .binOp .mul e (.lit (.decimal 10 1))

def binOld : BinOp → SqlEquiv.BinOp
  | .arith .add => .add | .arith .sub => .sub | .arith .mul => .mul
  | .arith .div => .div | .arith .mod => .mod
  | .cmp .eq => .eq | .cmp .ne => .ne | .cmp .lt => .lt | .cmp .le => .le
  | .cmp .gt => .gt | .cmp .ge => .ge
  | .and => .and | .or => .or | .concat => .concat
  | .like false => .like | .like true => .likeCI

/-- The same expression in `SqlEquiv`'s syntax, with columns by name. -/
def toOldExpr {n : ℕ} (cols : Fin n → Column) : Expr n → SqlEquiv.Expr
  | .lit v => .lit (toOld v)
  | .null _ => .lit (.null none)
  | .col i => .col ⟨none, (cols i).name⟩
  | .unary op e => unOld op (toOldExpr cols e)
  | .binary op a b => .binOp (binOld op) (toOldExpr cols a) (toOldExpr cols b)
  | .inList e vs =>
    .inList (toOldExpr cols e) false (vs.map fun d => .lit ((datumToOld d).getD (.null none)))
  | .caseWhen c a b => .«case» [(toOldExpr cols c, toOldExpr cols a)] (some (toOldExpr cols b))

def unOps : List UnOp :=
  [.not, .neg, .isNull, .isNotNull, .round 0, .round 1, .round (-1), .lower, .upper, .length,
   .toDecimal]
def binOps : List BinOp :=
  [.arith .add, .arith .sub, .arith .mul, .arith .div, .arith .mod,
   .cmp .eq, .cmp .ne, .cmp .lt, .cmp .le, .cmp .gt, .cmp .ge, .and, .or, .concat,
   .like false, .like true]

def atoms (n : ℕ) : List (Expr n) :=
  (List.finRange n).map .col ++
  [.lit (.int 0), .lit (.int 2), .lit (.int (-3)), .lit (.decimal (1/2)), .lit (.decimal 3),
   .lit (.text "Sales"), .lit (.text "Bolt"), .lit (.bool true), .null .int, .null .decimal,
   .lit (.decimal (-5/2)), .lit (.decimal (745/100)), .lit (.int 25), .lit (.int (-25)), .null .text]

/-- Well-typed expressions over `Γ`, without decimal `%` and `/`. -/
def exprs {n : ℕ} (Γ : Fin n → SqlType) : List (Expr n) :=
  let ok (e : Expr n) := (e.typeOf Γ).isSome
  let isDec (e : Expr n) := e.typeOf Γ == some .decimal
  let a := atoms n
  let bins := binOps.flatMap fun op => a.flatMap fun x => a.filterMap fun y =>
    let e := Expr.binary op x y
    if ok e && !((op == .arith .mod || op == .arith .div) && (isDec x || isDec y)) then some e
    else none
  let uns := unOps.flatMap fun op => a.filterMap fun x =>
    let e := Expr.unary op x
    if ok e then some e else none
  let preds := (bins ++ uns).filter (·.typeOf Γ == some .bool)
  let few := (List.range 12).filterMap fun k => preds[k * 7]?
  let conns := [BinOp.and, .or].flatMap fun op => few.flatMap fun p => few.map (.binary op p)
  let nots := few.map (.unary .not)
  let lists : List (List Datum) :=
    [[], [some (.int 30), none], [some (.int 25), some (.int 30)], [some (.decimal (5/2)), none],
     [some (.text "Sales"), some (.text "Marketing")], [none]]
  let ins := a.flatMap fun x => lists.filterMap fun vs =>
    let e := Expr.inList x vs
    if ok e then some e else none
  let cases := few.flatMap fun c => a.flatMap fun x => a.filterMap fun y =>
    let e := Expr.caseWhen c x y
    if ok e then some e else none
  a ++ uns ++ bins ++ conns ++ nots ++ ins ++ cases

/-- The documented difference: `< <= > >=` on two booleans (`SqlEquiv` has no boolean order). -/
def hasBoolOrder {n : ℕ} (Γ : Fin n → SqlType) : Expr n → Bool
  | .binary (.cmp op) a b =>
    ([CmpOp.lt, .le, .gt, .ge].contains op && a.typeOf Γ == some .bool) ||
      hasBoolOrder Γ a || hasBoolOrder Γ b
  | .binary _ a b => hasBoolOrder Γ a || hasBoolOrder Γ b
  | .unary _ e => hasBoolOrder Γ e
  | .inList e _ => hasBoolOrder Γ e
  | .caseWhen c a b => hasBoolOrder Γ c || hasBoolOrder Γ a || hasBoolOrder Γ b
  | _ => false

/-- (cases checked, documented differences, unexpected disagreements) for one table. -/
def runTable (t : T) : Nat × Nat × List String := Id.run do
  let cols := schema.columns t
  let es := exprs (schema.ctx t)
  let mut n := 0
  let mut documented := 0
  let mut bad : List String := []
  for r in db t do
    let old := SchemaDiff.toOldRow cols r
    for e in es do
      n := n + 1
      let new := resToOld (e.eval r)
      let o := SqlEquiv.evalExpr old (toOldExpr cols e)
      if new != o then
        if hasBoolOrder (schema.ctx t) e then documented := documented + 1 else
        bad := s!"{tableName t}: {repr e} on {repr old}: SqlCore {repr new}, SqlEquiv {repr o}" :: bad
  return (n, documented, bad.reverse)

def run : Nat × Nat × List String :=
  let (n₁, d₁, b₁) := runTable .users
  let (n₂, d₂, b₂) := runTable .items
  (n₁ + n₂, d₁ + d₂, b₁ ++ b₂)

end SqlCoreTest.ExprDiff
