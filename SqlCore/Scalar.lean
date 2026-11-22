/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/
module

public import SqlCore.Truth
public import SqlCore.Value
public import SqlCore.Except

/-!
# Scalar operators (typed core, phase 1, #290)

An operator on datums returns a datum (possibly `NULL`) or fails with an `EvalError`
(decision 2: strict errors).

* A non-null operand of the wrong type is `typeMismatch`, even when the other operand is `NULL`.
  Otherwise a `NULL` operand gives `NULL`: `NULL / 0` is `NULL`, `1 / 0` is `divisionByZero`.
* Integers are unbounded; `/` truncates toward zero (`Int.tdiv`), `%` takes the dividend's sign
  (`Int.tmod`), as in `SqlEquiv`, sqlite, Postgres and DuckDB's `//`.
* Decimals are exact (`ℚ`). With a decimal operand, `int` is promoted (decision 6): `1 + 0.5` is
  `1.5`, a decimal. `+ - *` are exact, `%` is exact with the dividend's sign (`7.5 % -2` is `1.5`),
  and `/` with a decimal operand is exact (phase 8d, #201): `1.0 / 3` is `1/3`, where engines round
  (registry T3). A zero divisor is `divisionByZero`.
* `= <> < <= > >=` need comparable operands (`SqlType.Comparable`): one type, or two numeric
  types compared as rationals (`1 = 1.0` is `TRUE`). Integers and decimals compare numerically,
  text by code point, booleans with `false < true`. The result is `TRUE`, `FALSE`, or `NULL` for
  `unknown`.
* `AND`, `OR`, `NOT` are `⊓`, `⊔`, `Truth.not` on the operands' truth values (`Datum.toTruth`).
* `IS [NOT] NULL` accepts any operand and is never `NULL`.
* `e IN (v₁, …, vₖ)` (`Datum.inList`) is the Kleene disjunction of `e = vᵢ`, from `FALSE`;
  `inList_eq_ok` is its closed form.

Each primitive (`addInt`, `divInt`, `compareText`, …) is a named function, so bounded integers or
another collation can replace it without touching the operator rules. Binary operators evaluate
both operands and report the left operand's error first.

Re-derived from cslib-frontier's `Languages/SQL/Scalar.lean` (pinned `e78796a1`). Compared with
`SqlEquiv.evalBinOp`/`evalUnaryOp`: errors are a separate type rather than sharing `none` with type
errors, `IN` keeps `unknown`, and comparisons do not promote across types. The differential test
`SqlCoreTest/ScalarDiffTest.lean` lists where the two agree and where they differ.
-/

@[expose] public section

namespace SqlCore

/-- Why an evaluation fails. -/
inductive EvalError where
  /-- A non-null operand has the wrong type. -/
  | typeMismatch
  /-- A division or remainder by zero. -/
  | divisionByZero
  /-- An operation outside the fragment. -/
  | unsupported
  /-- A scalar subquery returned more than one row (phase 8f; the standard, Postgres and DuckDB). -/
  | cardinality
  deriving DecidableEq, Repr

/-- The errors that a well-typed query can still raise: division by zero, and a scalar subquery
with several rows. -/
def EvalError.IsRuntime (e : EvalError) : Prop := e = .divisionByZero ∨ e = .cardinality

@[simp] theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f : Except ε β) = .error e := rfl

/-! ### Primitive operations -/

section Primitives

/-- Integer addition (unbounded). -/
def addInt (a b : ℤ) : ℤ := a + b

/-- Integer subtraction (unbounded). -/
def subInt (a b : ℤ) : ℤ := a - b

/-- Integer multiplication (unbounded). -/
def mulInt (a b : ℤ) : ℤ := a * b

/-- Integer negation (unbounded). -/
def negInt (a : ℤ) : ℤ := -a

/-- Integer division, truncating toward zero; a zero divisor is `divisionByZero`. -/
def divInt (a b : ℤ) : Except EvalError ℤ :=
  if b = 0 then .error .divisionByZero else .ok (a.tdiv b)

/-- Integer remainder, with the sign of the dividend; a zero divisor is `divisionByZero`. -/
def modInt (a b : ℤ) : Except EvalError ℤ :=
  if b = 0 then .error .divisionByZero else .ok (a.tmod b)

/-- Decimal addition (exact). -/
def addDec (a b : ℚ) : ℚ := a + b

/-- Decimal subtraction (exact). -/
def subDec (a b : ℚ) : ℚ := a - b

/-- Decimal multiplication (exact). -/
def mulDec (a b : ℚ) : ℚ := a * b

/-- Decimal negation. -/
def negDec (a : ℚ) : ℚ := -a

/-- Truncation toward zero. -/
def truncRat (q : ℚ) : ℤ := if q < 0 then q.ceil else q.floor

/-- Decimal division, exact (phase 8d, #201): `1.0 / 3` is the rational `1/3`; a zero divisor is
`divisionByZero`. Engines round an inexact quotient (Postgres to a variable scale, sqlite and
DuckDB to a double); the exact quotient agrees with all of them whenever it is a finite decimal
(registry T3). -/
def divDec (a b : ℚ) : Except EvalError ℚ :=
  if b = 0 then .error .divisionByZero else .ok (a / b)

/-- Decimal remainder, exact, with the sign of the dividend; a zero divisor is `divisionByZero`. -/
def modDec (a b : ℚ) : Except EvalError ℚ :=
  if b = 0 then .error .divisionByZero else .ok (a - b * truncRat (a / b))

/-- Text concatenation. -/
def concatText (s t : String) : String := s ++ t

/-! ### `LIKE`

A pattern is matched by simulating its automaton: the state is the list of pattern suffixes that the
text read so far can still be followed by. The recursion is structural (on the pattern for the
closure, on the text for the run), so `decide` evaluates it. `%` matches any sequence of
characters, `_` any one character, and every other character itself; there is no `ESCAPE`. -/

/-- The pattern suffixes reachable without reading a character: a leading `%` may match the empty
string. -/
def likeClosure : List Char → List (List Char)
  | '%' :: p => ('%' :: p) :: likeClosure p
  | p => [p]

/-- The pattern suffixes after reading `c` from the state `p`; `eq` compares a pattern character
with a text character. -/
def likeStep (eq : Char → Char → Bool) (c : Char) : List Char → List (List Char)
  | '%' :: p => likeClosure ('%' :: p)
  | '_' :: p => likeClosure p
  | d :: p => if eq d c then likeClosure p else []
  | [] => []

/-- Run the automaton over the text from a set of states; the text matches if the empty suffix
(the whole pattern used) is reachable at its end. -/
def likeRun (eq : Char → Char → Bool) : List (List Char) → List Char → Bool
  | sts, [] => sts.contains []
  | sts, c :: s => likeRun eq ((sts.flatMap (likeStep eq c)).eraseDups) s

/-- `s LIKE p`. With `ci`, ASCII letters match regardless of case and other characters exactly
(sqlite's rule; registry row 8); without it, characters match exactly (the standard, Postgres and
DuckDB). -/
def likeText (ci : Bool) (s p : String) : Bool :=
  likeRun (if ci then fun a b => a.toLower == b.toLower else fun a b => a == b)
    (likeClosure p.toList) s.toList

/-! #### Laws of `LIKE` (counterparts of `SqlEquiv`'s `like_match_all`, `like_empty_pattern` and
`like_self`) -/

/-- With no state left, nothing is accepted. -/
theorem likeRun_nil_states (eq : Char → Char → Bool) (s : List Char) : likeRun eq [] s = false := by
  induction s with
  | nil => rfl
  | cons c s ih => simpa [likeRun] using ih

/-- A run that holds the state `%` (and the empty suffix) accepts every text. -/
theorem likeRun_of_pct {eq : Char → Char → Bool} :
    ∀ (s : List Char) {sts : List (List Char)}, ['%'] ∈ sts → [] ∈ sts → likeRun eq sts s = true
  | [], _, _, h => by simpa [likeRun] using h
  | c :: s, sts, hp, _ => by
    have hstep : likeStep eq c ['%'] = [['%'], []] := rfl
    refine likeRun_of_pct s ?_ ?_ <;>
      simp only [List.mem_eraseDups, List.mem_flatMap] <;> exact ⟨['%'], hp, by simp [hstep]⟩

/-- `s LIKE '%'` holds for every text. -/
@[simp] theorem likeText_pct (ci : Bool) (s : String) : likeText ci s "%" = true :=
  likeRun_of_pct _ (by simp [likeClosure]) (by simp [likeClosure])

/-- `s LIKE ''` holds exactly for the empty text. -/
theorem likeText_empty_iff (ci : Bool) (s : String) : likeText ci s "" = true ↔ s = "" := by
  have he : ("" : String).toList = [] := String.toList_eq_nil_iff.mpr rfl
  rcases hs : s.toList with _ | ⟨c, cs⟩
  · simp [likeText, likeClosure, likeRun, he, String.toList_eq_nil_iff.mp hs]
  · have hne : s ≠ "" := fun h => by simp [h] at hs
    have hcl : likeClosure ([] : List Char) = [[]] := rfl
    have hstep : ∀ eq, (([[]] : List (List Char)).flatMap (likeStep eq c)).eraseDups = [] :=
      fun _ => rfl
    simp only [likeText, hs, he, hcl, likeRun, hstep, likeRun_nil_states, hne]
    decide

/-- Every pattern is in its own closure. -/
theorem mem_likeClosure_self (p : List Char) : p ∈ likeClosure p := by
  unfold likeClosure
  split <;> simp

/-- Reading a pattern's first character leads to the rest of the pattern: `%` reads `%`, `_` reads
`_`, and any other character itself. -/
theorem mem_likeStep_self {eq : Char → Char → Bool} (heq : ∀ c, eq c c = true) (c : Char)
    (p : List Char) : p ∈ likeStep eq c (c :: p) := by
  by_cases h₁ : c = '%'
  · subst h₁
    exact List.mem_cons_of_mem _ (mem_likeClosure_self p)
  by_cases h₂ : c = '_'
  · subst h₂
    exact mem_likeClosure_self p
  have hs : likeStep eq c (c :: p) = if eq c c then likeClosure p else [] := by
    unfold likeStep
    split <;> simp_all
  simp [hs, heq, mem_likeClosure_self]

/-- A text read from a state set holding it as a pattern is accepted. -/
theorem likeRun_self {eq : Char → Char → Bool} (heq : ∀ c, eq c c = true) :
    ∀ (s : List Char) {sts : List (List Char)}, s ∈ sts → likeRun eq sts s = true
  | [], _, h => by simpa [likeRun] using h
  | c :: s, sts, h => by
    refine likeRun_self heq s ?_
    simp only [List.mem_eraseDups, List.mem_flatMap]
    exact ⟨c :: s, h, mem_likeStep_self heq c s⟩

/-- Every text matches itself as a pattern (`SqlEquiv`'s `like_self`), in either case mode:
`%` and `_` in the pattern match themselves. -/
theorem likeText_self (ci : Bool) (s : String) : likeText ci s s = true := by
  unfold likeText
  refine likeRun_self ?_ _ (mem_likeClosure_self _)
  intro c; cases ci <;> simp

/-- Integer comparison. -/
def compareInt (a b : ℤ) : Ordering := compare a b

/-- Numeric comparison, as rationals. -/
def compareDec (a b : ℚ) : Ordering := compare a b

/-- Text comparison by code points (binary collation), lexicographically. -/
def compareText (s t : String) : Ordering := compare s t

/-- Boolean comparison, with `false < true`. -/
def compareBool (a b : Bool) : Ordering := compare a b

end Primitives

namespace Value

/-- Compare two values of comparable types (`SqlType.Comparable`): an integer is promoted when the
other operand is a decimal. Values of other types are a type error. -/
def cmp : Value → Value → Except EvalError Ordering
  | int a, int b => .ok (compareInt a b)
  | decimal p, decimal q => .ok (compareDec p q)
  | int a, decimal q => .ok (compareDec a q)
  | decimal p, int b => .ok (compareDec p b)
  | text s, text t => .ok (compareText s t)
  | bool a, bool b => .ok (compareBool a b)
  | _, _ => .error .typeMismatch

/-- Comparing in the other order swaps the outcome. -/
theorem cmp_swap (a b : Value) : cmp b a = Ordering.swap <$> cmp a b := by
  cases a <;> cases b <;>
    simp only [cmp, compareInt, compareDec, compareText, compareBool, Except.map_ok,
      Except.map_error] <;>
    exact congrArg Except.ok Std.OrientedCmp.eq_swap

/-- Two values of one type compare equal exactly when they are equal. Across numeric types this
fails: `int 1` and `decimal 1` compare equal (`cmp_int_decimal`). -/
theorem cmp_eq_ok_eq_iff {a b : Value} (h : a.type = b.type) : cmp a b = .ok .eq ↔ a = b := by
  cases a <;> cases b <;> simp_all [cmp, compareInt, compareDec, compareText, compareBool]

/-- A value compares equal to itself. -/
@[simp] theorem cmp_self (a : Value) : cmp a a = .ok .eq := (cmp_eq_ok_eq_iff rfl).mpr rfl

/-- Promotion: an integer compares with a decimal as a rational. -/
theorem cmp_int_decimal (z : ℤ) (q : ℚ) : cmp (int z) (decimal q) = .ok (compare (z : ℚ) q) :=
  rfl

/-- Two values can be compared exactly when their types are comparable. -/
theorem exists_cmp_eq_ok_iff {a b : Value} :
    (∃ o, cmp a b = .ok o) ↔ a.type.Comparable b.type := by
  cases a <;> cases b <;> simp [cmp, SqlType.Comparable, SqlType.isNumeric]

/-- Comparison fails only with a type error. -/
theorem cmp_eq_error {a b : Value} {e : EvalError} (h : cmp a b = .error e) :
    e = .typeMismatch := by
  cases a <;> cases b <;> simp_all [cmp]

end Value

/-! ### Numeric operands -/

/-- An operand of an arithmetic operator. -/
inductive Numeric where
  | int (z : ℤ)
  | decimal (q : ℚ)
  deriving DecidableEq, Repr

namespace Numeric

/-- The number as a value. -/
def toValue : Numeric → Value
  | int z => .int z
  | decimal q => .decimal q

/-- The number as a rational. -/
def toRat : Numeric → ℚ
  | int z => z
  | decimal q => q

/-- Negation, keeping the type. -/
def neg : Numeric → Numeric
  | int z => int (negInt z)
  | decimal q => decimal (negDec q)

end Numeric

/-! ### Truth values as datums -/

/-- A truth value as a datum: `TRUE`, `FALSE`, or `NULL` for `unknown`. -/
def Truth.toDatum : Truth → Datum
  | .false => some (.bool Bool.false)
  | .unknown => none
  | .true => some (.bool Bool.true)

namespace Datum

/-- The truth value of an operand of `AND`, `OR`, `NOT` or `CASE WHEN`: a boolean gives its value,
`NULL` gives `unknown`, and any other value is a type error. -/
def toTruth : Datum → Except EvalError Truth
  | none => .ok .unknown
  | some (.bool b) => .ok (.ofBool b)
  | some _ => .error .typeMismatch

/-- An operand of an arithmetic operator: `NULL`, an integer or a decimal; any other value is a
type error. -/
def asNum : Datum → Except EvalError (Option Numeric)
  | none => .ok none
  | some (.int z) => .ok (some (.int z))
  | some (.decimal q) => .ok (some (.decimal q))
  | some _ => .error .typeMismatch

/-- An operand of a text operator: `NULL` or a string, any other value is a type error. -/
def asText : Datum → Except EvalError (Option String)
  | none => .ok none
  | some (.text s) => .ok (some s)
  | some _ => .error .typeMismatch

@[simp] theorem toTruth_toDatum (t : Truth) : t.toDatum.toTruth = .ok t := by
  cases t <;> rfl

theorem toTruth_eq_ok_iff {d : Datum} {t : Truth} : d.toTruth = .ok t ↔ d = t.toDatum := by
  constructor
  · intro h
    match d, h with
    | none, h => cases h; rfl
    | some (.bool b), h => cases h; cases b <;> rfl
  · rintro rfl
    exact toTruth_toDatum t

/-- A datum has a truth value exactly when it is boolean-typed. -/
theorem exists_toTruth_eq_ok_iff {d : Datum} : (∃ t, d.toTruth = .ok t) ↔ d.HasType .bool := by
  rcases d with _ | (_ | _ | _ | _) <;> simp [toTruth]

/-- A boolean-typed datum is a truth value: `TRUE`, `FALSE`, or `NULL` for `unknown`. -/
theorem hasType_bool_iff {d : Datum} : d.HasType .bool ↔ ∃ t : Truth, d = t.toDatum := by
  simp only [← toTruth_eq_ok_iff, exists_toTruth_eq_ok_iff]

/-- A datum is an arithmetic operand exactly when it is integer- or decimal-typed. -/
theorem exists_asNum_eq_ok_iff {d : Datum} :
    (∃ x, d.asNum = .ok x) ↔ d.HasType .int ∨ d.HasType .decimal := by
  rcases d with _ | (_ | _ | _ | _) <;> simp [asNum]

/-- A datum is a text operand exactly when it is text-typed. -/
theorem exists_asText_eq_ok_iff {d : Datum} : (∃ x, d.asText = .ok x) ↔ d.HasType .text := by
  rcases d with _ | (_ | _ | _ | _) <;> simp [asText]

/-- A numeric operand is a given number exactly when the datum is that number. -/
theorem asNum_eq_ok_some_iff {d : Datum} {x : Numeric} :
    d.asNum = .ok (some x) ↔ d = some x.toValue := by
  rcases d with _ | (_ | _ | _ | _) <;> rcases x <;> simp [asNum, Numeric.toValue]

theorem toTruth_eq_error {d : Datum} {e : EvalError} (h : d.toTruth = .error e) :
    e = .typeMismatch := by
  rcases d with _ | (_ | _ | _ | _) <;> simp [toTruth] at h <;> exact h.symm

theorem asNum_eq_error {d : Datum} {e : EvalError} (h : d.asNum = .error e) :
    e = .typeMismatch := by
  rcases d with _ | (_ | _ | _ | _) <;> simp [asNum] at h <;> exact h.symm

theorem asText_eq_error {d : Datum} {e : EvalError} (h : d.asText = .error e) :
    e = .typeMismatch := by
  rcases d with _ | (_ | _ | _ | _) <;> simp [asText] at h <;> exact h.symm

end Datum

namespace Truth

@[simp] theorem toDatum_hasType (t : Truth) : t.toDatum.HasType .bool := by
  cases t <;> trivial

theorem toDatum_injective : Function.Injective toDatum := by
  intro s t h
  simpa using congrArg Datum.toTruth h

@[simp] theorem toDatum_eq_none_iff {t : Truth} : t.toDatum = none ↔ t = .unknown := by
  cases t <;> simp [toDatum]

@[simp] theorem toDatum_ofBool (b : Bool) : (ofBool b).toDatum = some (.bool b) := by
  cases b <;> rfl

end Truth

/-! ### Operators -/

/-- Unary operators. -/
inductive UnOp where
  /-- `NOT`. -/
  | not
  /-- Unary minus. -/
  | neg
  /-- `IS NULL`. -/
  | isNull
  /-- `IS NOT NULL`. -/
  | isNotNull
  deriving DecidableEq, Repr

/-- Arithmetic operators. -/
inductive ArithOp where
  /-- `+`. -/
  | add
  /-- `-`. -/
  | sub
  /-- `*`. -/
  | mul
  /-- `/`, truncating toward zero. -/
  | div
  /-- `%`, with the sign of the dividend. -/
  | mod
  deriving DecidableEq, Repr

/-- Comparison operators. -/
inductive CmpOp where
  /-- `=`. -/
  | eq
  /-- `<>`. -/
  | ne
  /-- `<`. -/
  | lt
  /-- `<=`. -/
  | le
  /-- `>`. -/
  | gt
  /-- `>=`. -/
  | ge
  deriving DecidableEq, Repr

/-- Binary operators. -/
inductive BinOp where
  /-- An arithmetic operator. -/
  | arith (op : ArithOp)
  /-- A comparison. -/
  | cmp (op : CmpOp)
  /-- `AND`. -/
  | and
  /-- `OR`. -/
  | or
  /-- Text concatenation `||`. -/
  | concat
  /-- `LIKE`; with `ci`, ASCII case-insensitive (the sqlite dialect, registry row 8). -/
  | like (ci : Bool)
  deriving DecidableEq, Repr

namespace ArithOp

/-- An integer operator on two integers. -/
def eval : ArithOp → ℤ → ℤ → Except EvalError ℤ
  | add, a, b => .ok (addInt a b)
  | sub, a, b => .ok (subInt a b)
  | mul, a, b => .ok (mulInt a b)
  | div, a, b => divInt a b
  | mod, a, b => modInt a b

/-- An arithmetic operator on two decimals (or a promoted integer). -/
def evalDec : ArithOp → ℚ → ℚ → Except EvalError ℚ
  | add, a, b => .ok (addDec a b)
  | sub, a, b => .ok (subDec a b)
  | mul, a, b => .ok (mulDec a b)
  | div, a, b => divDec a b
  | mod, a, b => modDec a b

/-- An arithmetic operator on two numeric operands: integers stay integers; with a decimal operand
the integer is promoted and the result is a decimal; `NULL` gives `NULL`. -/
def evalNum (op : ArithOp) : Option Numeric → Option Numeric → Except EvalError Datum
  | some (.int x), some (.int y) => (fun z => some (.int z)) <$> op.eval x y
  | some (.int x), some (.decimal q) => (fun r => some (.decimal r)) <$> op.evalDec x q
  | some (.decimal p), some (.int y) => (fun r => some (.decimal r)) <$> op.evalDec p y
  | some (.decimal p), some (.decimal q) => (fun r => some (.decimal r)) <$> op.evalDec p q
  | none, _ => .ok none
  | some _, none => .ok none

@[simp] theorem evalNum_none_left (op : ArithOp) (y : Option Numeric) :
    op.evalNum none y = .ok none := rfl

@[simp] theorem evalNum_none_right (op : ArithOp) (x : Option Numeric) :
    op.evalNum x none = .ok none := by
  rcases x with _ | (_ | _) <;> rfl

/-- `evalNum` is symmetric for a symmetric operator. -/
theorem evalNum_comm {op : ArithOp} (h : ∀ x y, op.eval x y = op.eval y x)
    (hd : ∀ p q, op.evalDec p q = op.evalDec q p) (x y : Option Numeric) :
    op.evalNum x y = op.evalNum y x := by
  rcases x with _ | (x | x) <;> rcases y with _ | (y | y) <;> simp only [evalNum, h, hd]

/-- Whether the operator fails on a zero divisor: `/` and `%`. -/
def isDivision : ArithOp → Bool
  | div | mod => true
  | add | sub | mul => false

/-- On integers, an operator fails only by dividing by zero. -/
theorem eval_eq_error {op : ArithOp} {a b : ℤ} {e : EvalError} (h : op.eval a b = .error e) :
    e = .divisionByZero ∧ op.isDivision ∧ b = 0 := by
  cases op <;> simp only [eval, divInt, modInt, reduceCtorEq] at h <;> split_ifs at h with hb <;>
    cases h <;> exact ⟨rfl, rfl, hb⟩

/-- On integers, an operator succeeds unless it divides by zero. -/
theorem exists_eval_eq_ok {op : ArithOp} {a b : ℤ} (h : op.isDivision → b ≠ 0) :
    ∃ z, op.eval a b = .ok z := by
  rcases hr : op.eval a b with e | z
  · obtain ⟨-, hd, hb⟩ := eval_eq_error hr
    exact absurd hb (h hd)
  · exact ⟨z, rfl⟩

end ArithOp

namespace CmpOp

/-- Whether an outcome of `compare` satisfies the comparison. -/
def test : CmpOp → Ordering → Bool
  | eq => Ordering.isEq
  | ne => Ordering.isNe
  | lt => Ordering.isLT
  | le => Ordering.isLE
  | gt => Ordering.isGT
  | ge => Ordering.isGE

/-- The comparison that holds exactly when this one fails: `NOT (a < b)` is `a >= b`. -/
def negate : CmpOp → CmpOp
  | eq => ne
  | ne => eq
  | lt => ge
  | le => gt
  | gt => le
  | ge => lt

/-- The comparison with its operands exchanged: `a < b` is `b > a`. -/
def swap : CmpOp → CmpOp
  | eq => eq
  | ne => ne
  | lt => gt
  | le => ge
  | gt => lt
  | ge => le

@[simp] theorem negate_negate (op : CmpOp) : op.negate.negate = op := by cases op <;> rfl

@[simp] theorem swap_swap (op : CmpOp) : op.swap.swap = op := by cases op <;> rfl

@[simp] theorem test_negate (op : CmpOp) (o : Ordering) : op.negate.test o = !op.test o := by
  cases op <;> cases o <;> rfl

@[simp] theorem test_swap (op : CmpOp) (o : Ordering) : op.swap.test o.swap = op.test o := by
  cases op <;> cases o <;> rfl

/-- Three-valued comparison of datums: `unknown` when either side is `NULL`, otherwise the values
must have the same type. -/
def eval (op : CmpOp) : Datum → Datum → Except EvalError Truth
  | some a, some b => (fun o => Truth.ofBool (op.test o)) <$> Value.cmp a b
  | _, _ => .ok .unknown

@[simp] theorem eval_none_left (op : CmpOp) (b : Datum) : op.eval none b = .ok .unknown := rfl

@[simp] theorem eval_none_right (op : CmpOp) (a : Datum) : op.eval a none = .ok .unknown := by
  cases a <;> rfl

theorem eval_some_some (op : CmpOp) (a b : Value) :
    op.eval (some a) (some b) = (fun o => Truth.ofBool (op.test o)) <$> Value.cmp a b := rfl

/-- The negated comparison has the negated truth value. -/
theorem eval_negate (op : CmpOp) (a b : Datum) :
    op.negate.eval a b = Truth.not <$> op.eval a b := by
  match a, b with
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b =>
    rcases Value.cmp a b with e | o <;> simp [eval_some_some, *]

/-- Exchanging the operands of the swapped comparison does not change it. -/
theorem eval_swap (op : CmpOp) (a b : Datum) : op.swap.eval b a = op.eval a b := by
  match a, b with
  | none, none => rfl
  | none, some _ => rfl
  | some _, none => rfl
  | some a, some b =>
    rw [eval_some_some, eval_some_some, Value.cmp_swap]
    rcases Value.cmp a b with e | o <;> simp

/-- Equality is symmetric. -/
theorem eval_eq_comm (a b : Datum) : eq.eval a b = eq.eval b a :=
  eval_swap eq b a

/-- Over a common type, `a = b` is `TRUE` exactly when `a` and `b` are the same value. (Across
numeric types, `1 = 1.0` is `TRUE` although the values differ.) -/
theorem eval_eq_ok_true_iff {a b : Datum} {τ : SqlType} (ha : a.HasType τ) (hb : b.HasType τ) :
    eq.eval a b = .ok .true ↔ a ≠ none ∧ a = b := by
  match a, b, ha, hb with
  | none, _, _, _ => simp
  | some _, none, _, _ => simp
  | some a, some b, ha, hb =>
    have hab : a.type = b.type := ha.trans hb.symm
    rw [eval_some_some, Except.map_eq_ok]
    constructor
    · rintro ⟨o, ho, hto⟩
      have : o = .eq := by cases o <;> simp_all [test]
      subst this
      simpa using (Value.cmp_eq_ok_eq_iff hab).mp ho
    · rintro ⟨-, h⟩
      cases h
      exact ⟨.eq, Value.cmp_self a, rfl⟩

/-- A comparison succeeds exactly when the operands have comparable types (`NULL` has every
type). -/
theorem exists_eval_eq_ok_iff {op : CmpOp} {a b : Datum} :
    (∃ t, op.eval a b = .ok t) ↔ ∃ τ σ, τ.Comparable σ ∧ a.HasType τ ∧ b.HasType σ := by
  constructor
  · rintro ⟨t, h⟩
    match a, b, h with
    | none, none, _ => exact ⟨.int, .int, .refl _, trivial, trivial⟩
    | none, some b, _ => exact ⟨b.type, b.type, .refl _, trivial, rfl⟩
    | some a, none, _ => exact ⟨a.type, a.type, .refl _, rfl, trivial⟩
    | some a, some b, h =>
      rw [eval_some_some, Except.map_eq_ok] at h
      obtain ⟨o, ho, -⟩ := h
      exact ⟨a.type, b.type, Value.exists_cmp_eq_ok_iff.mp ⟨o, ho⟩, rfl, rfl⟩
  · rintro ⟨τ, σ, hc, ha, hb⟩
    match a, b, ha, hb with
    | none, _, _, _ => exact ⟨_, rfl⟩
    | some _, none, _, _ => exact ⟨_, eval_none_right _ _⟩
    | some a, some b, ha, hb =>
      have hab : a.type.Comparable b.type := by
        simp only [Datum.hasType_some] at ha hb
        subst ha hb
        exact hc
      obtain ⟨o, ho⟩ := Value.exists_cmp_eq_ok_iff.mpr hab
      exact ⟨_, by rw [eval_some_some, ho]; rfl⟩

/-- A comparison of datums of a common type succeeds. -/
theorem exists_eval_eq_ok {op : CmpOp} {a b : Datum} {τ : SqlType} (ha : a.HasType τ)
    (hb : b.HasType τ) : ∃ t, op.eval a b = .ok t :=
  exists_eval_eq_ok_iff.mpr ⟨τ, τ, .refl τ, ha, hb⟩

/-- A comparison fails only with a type error. -/
theorem eval_eq_error {op : CmpOp} {a b : Datum} {e : EvalError} (h : op.eval a b = .error e) :
    e = .typeMismatch := by
  match a, b, h with
  | some a, some b, h =>
    simp only [eval_some_some, Except.map_eq_error] at h
    exact Value.cmp_eq_error h

end CmpOp

/-- A unary operator on a datum. -/
def evalUnOp : UnOp → Datum → Except EvalError Datum
  | .not, d => (fun t => t.not.toDatum) <$> d.toTruth
  | .neg, d => Option.map (fun x => x.neg.toValue) <$> d.asNum
  | .isNull, d => .ok (some (.bool d.isNone))
  | .isNotNull, d => .ok (some (.bool d.isSome))

/-- A binary operator on two datums. Both operands are checked, left first, before `NULL`
propagates. -/
def evalBinOp : BinOp → Datum → Datum → Except EvalError Datum
  | .arith op, a, b => do
    let x ← a.asNum
    let y ← b.asNum
    op.evalNum x y
  | .cmp op, a, b => Truth.toDatum <$> op.eval a b
  | .and, a, b => do return ((← a.toTruth) ⊓ (← b.toTruth)).toDatum
  | .or, a, b => do return ((← a.toTruth) ⊔ (← b.toTruth)).toDatum
  | .concat, a, b => do
    let x ← a.asText
    let y ← b.asText
    match x, y with
    | some s, some t => return some (.text (concatText s t))
    | _, _ => return none
  | .like ci, a, b => do
    let x ← a.asText
    let y ← b.asText
    match x, y with
    | some s, some p => return some (.bool (likeText ci s p))
    | _, _ => return none

/-! ### Laws of the operators -/

/-- `NOT (a op b)` is `a (negate op) b`; for instance `NOT (a < b)` is `a >= b`, also when an
operand is `NULL` and when the comparison fails. -/
theorem evalBinOp_cmp_negate (op : CmpOp) (a b : Datum) :
    evalBinOp (.cmp op.negate) a b = (evalBinOp (.cmp op) a b >>= evalUnOp .not) := by
  simp only [evalBinOp, CmpOp.eval_negate]
  rcases op.eval a b with e | t <;> simp [evalUnOp]

/-- `b (swap op) a` is `a op b`; for instance `b > a` is `a < b`. -/
theorem evalBinOp_cmp_swap (op : CmpOp) (a b : Datum) :
    evalBinOp (.cmp op.swap) b a = evalBinOp (.cmp op) a b := by
  simp only [evalBinOp, CmpOp.eval_swap]

/-- `a AND b` is `b AND a`, also when an operand is not boolean. -/
theorem evalBinOp_and_comm (a b : Datum) : evalBinOp .and a b = evalBinOp .and b a := by
  simp only [evalBinOp]
  rw [Except.bind_comm_of_eq_error (fun _ => Datum.toTruth_eq_error)
    (fun _ => Datum.toTruth_eq_error)]
  simp only [inf_comm]

/-- `a OR b` is `b OR a`, also when an operand is not boolean. -/
theorem evalBinOp_or_comm (a b : Datum) : evalBinOp .or a b = evalBinOp .or b a := by
  simp only [evalBinOp]
  rw [Except.bind_comm_of_eq_error (fun _ => Datum.toTruth_eq_error)
    (fun _ => Datum.toTruth_eq_error)]
  simp only [sup_comm]

/-- `NOT (NOT d)` is `d` on boolean datums. -/
theorem evalUnOp_not_not {d : Datum} (hd : d.HasType .bool) :
    (evalUnOp .not d >>= evalUnOp .not) = .ok d := by
  obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hd
  rw [Datum.toTruth_eq_ok_iff.mp ht]
  simp [evalUnOp]

/-- De Morgan: `NOT (a AND b)` is `NOT a OR NOT b`, also when an operand is not boolean. -/
theorem not_evalBinOp_and (a b : Datum) :
    (evalBinOp .and a b >>= evalUnOp .not) =
      (do evalBinOp .or (← evalUnOp .not a) (← evalUnOp .not b)) := by
  rcases ha : a.toTruth with e | s <;> rcases hb : b.toTruth with e' | t <;>
    simp [evalBinOp, evalUnOp, ha, hb]

/-- De Morgan: `NOT (a OR b)` is `NOT a AND NOT b`, also when an operand is not boolean. -/
theorem not_evalBinOp_or (a b : Datum) :
    (evalBinOp .or a b >>= evalUnOp .not) =
      (do evalBinOp .and (← evalUnOp .not a) (← evalUnOp .not b)) := by
  rcases ha : a.toTruth with e | s <;> rcases hb : b.toTruth with e' | t <;>
    simp [evalBinOp, evalUnOp, ha, hb]

/-- `NOT (d IS NULL)` is `d IS NOT NULL`. -/
theorem not_evalUnOp_isNull (d : Datum) :
    (evalUnOp .isNull d >>= evalUnOp .not) = evalUnOp .isNotNull d := by
  cases d <;> rfl

/-- `NOT (d IS NOT NULL)` is `d IS NULL`. -/
theorem not_evalUnOp_isNotNull (d : Datum) :
    (evalUnOp .isNotNull d >>= evalUnOp .not) = evalUnOp .isNull d := by
  cases d <;> rfl

/-- `a AND TRUE` is `a` on boolean datums; on any other value it is a type error. -/
theorem evalBinOp_and_true {a : Datum} (ha : a.HasType .bool) :
    evalBinOp .and a (some (.bool true)) = .ok a := by
  obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr ha
  rw [Datum.toTruth_eq_ok_iff.mp ht]
  cases t <;> rfl

/-- `a AND FALSE` is `FALSE` on boolean datums, also when `a` is `NULL`. -/
theorem evalBinOp_and_false {a : Datum} (ha : a.HasType .bool) :
    evalBinOp .and a (some (.bool false)) = .ok (some (.bool false)) := by
  obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr ha
  rw [Datum.toTruth_eq_ok_iff.mp ht]
  cases t <;> rfl

/-- `a OR FALSE` is `a` on boolean datums. -/
theorem evalBinOp_or_false {a : Datum} (ha : a.HasType .bool) :
    evalBinOp .or a (some (.bool false)) = .ok a := by
  obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr ha
  rw [Datum.toTruth_eq_ok_iff.mp ht]
  cases t <;> rfl

/-- `a OR TRUE` is `TRUE` on boolean datums, also when `a` is `NULL`. -/
theorem evalBinOp_or_true {a : Datum} (ha : a.HasType .bool) :
    evalBinOp .or a (some (.bool true)) = .ok (some (.bool true)) := by
  obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr ha
  rw [Datum.toTruth_eq_ok_iff.mp ht]
  cases t <;> rfl

private theorem evalBinOp_arith_of_asNum {op : ArithOp} {a b : Datum} {x y : Option Numeric}
    (ha : a.asNum = .ok x) (hb : b.asNum = .ok y) :
    evalBinOp (.arith op) a b = op.evalNum x y := by
  simp only [evalBinOp, ha, hb, ok_bind]

/-- A numeric datum: `NULL`, an integer or a decimal. -/
abbrev Datum.IsNumeric (d : Datum) : Prop := d.HasType .int ∨ d.HasType .decimal

/-- `NULL op a` is `NULL` for an arithmetic operator and a numeric `a`. -/
theorem evalBinOp_arith_null_left (op : ArithOp) {a : Datum} (ha : a.IsNumeric) :
    evalBinOp (.arith op) none a = .ok none := by
  obtain ⟨x, hx⟩ := Datum.exists_asNum_eq_ok_iff.mpr ha
  rw [evalBinOp_arith_of_asNum rfl hx, ArithOp.evalNum_none_left]

/-- `a op NULL` is `NULL` for an arithmetic operator and a numeric `a`; in particular `NULL / 0`
and `1 / NULL` are `NULL`. -/
theorem evalBinOp_arith_null_right (op : ArithOp) {a : Datum} (ha : a.IsNumeric) :
    evalBinOp (.arith op) a none = .ok none := by
  obtain ⟨x, hx⟩ := Datum.exists_asNum_eq_ok_iff.mpr ha
  rw [evalBinOp_arith_of_asNum hx rfl, ArithOp.evalNum_none_right]

private theorem evalBinOp_arith_comm {op : ArithOp} (hop : ∀ x y, op.eval x y = op.eval y x)
    (hd : ∀ p q, op.evalDec p q = op.evalDec q p) (a b : Datum) :
    evalBinOp (.arith op) a b = evalBinOp (.arith op) b a := by
  simp only [evalBinOp]
  rw [Except.bind_comm_of_eq_error (fun _ => Datum.asNum_eq_error) (fun _ => Datum.asNum_eq_error)]
  congr 1; funext y; congr 1; funext x
  exact ArithOp.evalNum_comm hop hd x y

/-- `a + b` is `b + a`, also when an operand is not numeric. -/
theorem evalBinOp_add_comm (a b : Datum) :
    evalBinOp (.arith .add) a b = evalBinOp (.arith .add) b a :=
  evalBinOp_arith_comm (fun x y => by simp only [ArithOp.eval, addInt, Int.add_comm])
    (fun p q => by simp only [ArithOp.evalDec, addDec, add_comm]) a b

/-- `a * b` is `b * a`, also when an operand is not numeric. -/
theorem evalBinOp_mul_comm (a b : Datum) :
    evalBinOp (.arith .mul) a b = evalBinOp (.arith .mul) b a :=
  evalBinOp_arith_comm (fun x y => by simp only [ArithOp.eval, mulInt, Int.mul_comm])
    (fun p q => by simp only [ArithOp.evalDec, mulDec, mul_comm]) a b

private theorem evalBinOp_arith_right_id {op : ArithOp} {c : ℤ} (hop : ∀ x, op.eval x c = .ok x)
    (hd : ∀ q, op.evalDec q c = .ok q) {a : Datum} (ha : a.IsNumeric) :
    evalBinOp (.arith op) a (some (.int c)) = .ok a := by
  obtain ⟨x, hx⟩ := Datum.exists_asNum_eq_ok_iff.mpr ha
  rw [evalBinOp_arith_of_asNum hx rfl]
  match a, x, hx with
  | none, _, hx => cases hx; rfl
  | some (.int z), _, hx => cases hx; simp only [ArithOp.evalNum, hop, Except.map_ok]
  | some (.decimal q), _, hx => cases hx; simp only [ArithOp.evalNum, hd, Except.map_ok]

/-- `a + 0` is `a` on numeric datums; on a text or boolean `a` it is a type error. -/
theorem evalBinOp_add_zero {a : Datum} (ha : a.IsNumeric) :
    evalBinOp (.arith .add) a (some (.int 0)) = .ok a :=
  evalBinOp_arith_right_id (fun x => by simp only [ArithOp.eval, addInt, Int.add_zero])
    (fun q => by simp [ArithOp.evalDec, addDec]) ha

/-- `a - 0` is `a` on numeric datums. -/
theorem evalBinOp_sub_zero {a : Datum} (ha : a.IsNumeric) :
    evalBinOp (.arith .sub) a (some (.int 0)) = .ok a :=
  evalBinOp_arith_right_id (fun x => by simp only [ArithOp.eval, subInt, Int.sub_zero])
    (fun q => by simp [ArithOp.evalDec, subDec]) ha

/-- `a * 1` is `a` on numeric datums. -/
theorem evalBinOp_mul_one {a : Datum} (ha : a.IsNumeric) :
    evalBinOp (.arith .mul) a (some (.int 1)) = .ok a :=
  evalBinOp_arith_right_id (fun x => by simp only [ArithOp.eval, mulInt, Int.mul_one])
    (fun q => by simp [ArithOp.evalDec, mulDec]) ha

/-- `-(-d)` is `d` on numeric datums. -/
theorem evalUnOp_neg_neg {d : Datum} (hd : d.IsNumeric) :
    (evalUnOp .neg d >>= evalUnOp .neg) = .ok d := by
  obtain ⟨x, hx⟩ := Datum.exists_asNum_eq_ok_iff.mpr hd
  match d, x, hx with
  | none, _, _ => rfl
  | some (.int z), _, hx =>
    cases hx; simp [evalUnOp, Datum.asNum, Numeric.neg, Numeric.toValue, negInt]
  | some (.decimal q), _, hx =>
    cases hx; simp [evalUnOp, Datum.asNum, Numeric.neg, Numeric.toValue, negDec]

/-! ### Three-valued membership -/

namespace Datum

/-- Three-valued `e IN (v₁, …, vₖ)`: the Kleene disjunction of the comparisons `e = vᵢ`, starting
from `FALSE`. It is strict: the comparisons are made from left to right and the first failure is
the result. `e NOT IN (v₁, …, vₖ)` is its negation `Truth.not`. -/
def inList (e : Datum) : List Datum → Except EvalError Truth
  | [] => .ok .false
  | v :: vs => do
    let t ← CmpOp.eq.eval e v
    let u ← e.inList vs
    return t ⊔ u

/-- `e IN ()` is `FALSE`, even for a `NULL` probe. -/
@[simp] theorem inList_nil (e : Datum) : e.inList [] = .ok .false := rfl

theorem inList_cons (e v : Datum) (vs : List Datum) :
    e.inList (v :: vs) = do
      let t ← CmpOp.eq.eval e v
      let u ← e.inList vs
      return t ⊔ u := rfl

/-- `e IN (v)` is `e = v`. -/
@[simp] theorem inList_singleton (e v : Datum) : e.inList [v] = CmpOp.eq.eval e v := by
  cases h : CmpOp.eq.eval e v <;> simp [inList_cons, h]

/-- Membership in a concatenation is the disjunction of the memberships. -/
theorem inList_append (e : Datum) (vs ws : List Datum) :
    e.inList (vs ++ ws) = do
      let t ← e.inList vs
      let u ← e.inList ws
      return t ⊔ u := by
  induction vs with
  | nil => cases h : e.inList ws <;> simp [h]
  | cons v vs ih =>
    simp only [List.cons_append, inList_cons, ih]
    rcases CmpOp.eq.eval e v with _ | t <;> rcases e.inList vs with _ | u <;>
      rcases e.inList ws with _ | w <;> simp [sup_assoc]

/-- Membership succeeds exactly when every comparison does. -/
theorem exists_inList_eq_ok_iff {e : Datum} {vs : List Datum} :
    (∃ t, e.inList vs = .ok t) ↔ ∀ v ∈ vs, ∃ t, CmpOp.eq.eval e v = .ok t := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [inList_cons, List.forall_mem_cons, ← ih]
    rcases CmpOp.eq.eval e v with _ | t <;> rcases e.inList vs with _ | u <;> simp

/-- Over a common type, `e = v` is `TRUE` on the same non-null value, `unknown` when one side is
`NULL`, and `FALSE` otherwise. -/
private theorem eval_eq_of_hasType {e v : Datum} {τ : SqlType} (he : e.HasType τ)
    (hv : v.HasType τ) :
    CmpOp.eq.eval e v =
      .ok (if e = none ∨ v = none then .unknown else if e = v then .true else .false) := by
  match e, v with
  | none, _ => simp
  | some _, none => simp
  | some a, some b =>
    have hab : a.type = b.type := he.trans hv.symm
    obtain ⟨o, ho⟩ := Value.exists_cmp_eq_ok_iff.mpr (.inl hab)
    rw [CmpOp.eval_some_some, ho]
    by_cases hab' : a = b
    · subst hab'
      rw [Value.cmp_self] at ho
      cases ho
      simp [CmpOp.test]
    · have : o ≠ .eq := by
        rintro rfl
        exact hab' ((Value.cmp_eq_ok_eq_iff hab).mp ho)
      cases o <;> simp_all [CmpOp.test]

/-- Over a common type, membership succeeds. -/
theorem exists_inList_eq_ok {e : Datum} {vs : List Datum} {τ : SqlType} (he : e.HasType τ)
    (hvs : ∀ v ∈ vs, v.HasType τ) : ∃ t, e.inList vs = .ok t :=
  exists_inList_eq_ok_iff.mpr fun v hv => CmpOp.exists_eval_eq_ok he (hvs v hv)

/-- Over a common type, `e IN vs` is `TRUE` exactly when `e` is non-null and occurs in `vs`. -/
theorem inList_eq_ok_true_iff {e : Datum} {vs : List Datum} {τ : SqlType} (he : e.HasType τ)
    (hvs : ∀ v ∈ vs, v.HasType τ) : e.inList vs = .ok .true ↔ e ≠ none ∧ e ∈ vs := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.forall_mem_cons] at hvs
    obtain ⟨u, hu⟩ := exists_inList_eq_ok he hvs.2
    have ih' := ih hvs.2
    rw [hu, Except.ok.injEq] at ih'
    rw [inList_cons, eval_eq_of_hasType he hvs.1, hu]
    simp only [ok_bind, pure, Except.pure, Except.ok.injEq, Truth.sup_eq_true_iff, ih',
      List.mem_cons]
    by_cases h₁ : e = none
    · simp [h₁]
    · by_cases h₂ : v = none
      · simp [h₁, h₂]
      · by_cases h₃ : e = v <;> simp [h₁, h₂, h₃]

/-- Over a common type, `e IN vs` is `FALSE` exactly when `vs` is empty, or `e` is non-null, does
not occur in `vs`, and `vs` has no `NULL`. -/
theorem inList_eq_ok_false_iff {e : Datum} {vs : List Datum} {τ : SqlType} (he : e.HasType τ)
    (hvs : ∀ v ∈ vs, v.HasType τ) :
    e.inList vs = .ok .false ↔ vs = [] ∨ (e ≠ none ∧ none ∉ vs ∧ e ∉ vs) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.forall_mem_cons] at hvs
    obtain ⟨u, hu⟩ := exists_inList_eq_ok he hvs.2
    have ih' := ih hvs.2
    rw [hu, Except.ok.injEq] at ih'
    rw [inList_cons, eval_eq_of_hasType he hvs.1, hu]
    simp only [ok_bind, pure, Except.pure, Except.ok.injEq, Truth.sup_eq_false_iff, ih',
      List.mem_cons]
    by_cases h₁ : e = none
    · simp [h₁]
    · by_cases h₂ : v = none
      · simp [h₁, h₂]
      · by_cases h₃ : e = v
        · simp [h₂, h₃]
        · rcases vs with _ | ⟨w, ws⟩
          · simp [h₁, h₂, h₃, Ne.symm h₂]
          · simp [h₁, h₂, h₃, Ne.symm h₂]

/-- The closed form of three-valued membership over a common type: `FALSE` for an empty list (even
for a `NULL` probe), `TRUE` when the non-null probe occurs, `FALSE` when moreover nothing is `NULL`,
and `unknown` otherwise. -/
theorem inList_eq_ok {e : Datum} {vs : List Datum} {τ : SqlType} (he : e.HasType τ)
    (hvs : ∀ v ∈ vs, v.HasType τ) :
    e.inList vs = .ok
      (if vs = [] then .false
      else if e ≠ none ∧ e ∈ vs then .true
      else if e = none ∨ none ∈ vs then .unknown
      else .false) := by
  obtain ⟨t, ht⟩ := exists_inList_eq_ok he hvs
  have htrue := inList_eq_ok_true_iff he hvs
  have hfalse := inList_eq_ok_false_iff he hvs
  rw [ht, Except.ok.injEq] at htrue hfalse ⊢
  split_ifs with h₁ h₂ h₃
  · exact hfalse.mpr (.inl h₁)
  · exact htrue.mpr h₂
  · cases t
    · obtain h | ⟨h, h', -⟩ := hfalse.mp rfl
      · exact absurd h h₁
      · rcases h₃ with h₃ | h₃ <;> contradiction
    · rfl
    · exact absurd (htrue.mp rfl) h₂
  · have hne : e ≠ none := fun h => h₃ (.inl h)
    exact hfalse.mpr (.inr ⟨hne, fun h => h₃ (.inr h), fun h => h₂ ⟨hne, h⟩⟩)

/-- `NOT IN` and `NOT EXISTS`. Read as filters, `e NOT IN vs` keeps a row when the negated
membership is `TRUE`, and `NOT EXISTS (SELECT … FROM vs WHERE v = e)` keeps it when no comparison
`v = e` is `TRUE`. Over a common type they agree exactly when `vs` is empty, some element matches,
or `e` is non-null and `vs` has no `NULL`. Without a common type both fail under strict
evaluation, since a comparison raises a type error. -/
theorem isTrue_not_inList_iff_iff {e : Datum} {vs : List Datum} {τ : SqlType} {t : Truth}
    (he : e.HasType τ) (hvs : ∀ v ∈ vs, v.HasType τ) (ht : e.inList vs = .ok t) :
    (t.not.isTrue = .true ↔ ¬∃ v ∈ vs, CmpOp.eq.eval v e = .ok .true) ↔
      vs = [] ∨ (∃ v ∈ vs, CmpOp.eq.eval v e = .ok .true) ∨ (e ≠ none ∧ none ∉ vs) := by
  have hmatch : (∃ v ∈ vs, CmpOp.eq.eval v e = .ok .true) ↔ e ≠ none ∧ e ∈ vs := by
    constructor
    · rintro ⟨v, hv, h⟩
      rw [CmpOp.eval_eq_comm, CmpOp.eval_eq_ok_true_iff he (hvs v hv)] at h
      obtain ⟨hne, rfl⟩ := h
      exact ⟨hne, hv⟩
    · rintro ⟨hne, hv⟩
      exact ⟨e, hv, (CmpOp.eval_eq_ok_true_iff he he).mpr ⟨hne, rfl⟩⟩
  have htrue := inList_eq_ok_true_iff he hvs
  have hfalse := inList_eq_ok_false_iff he hvs
  rw [ht, Except.ok.injEq] at htrue hfalse
  rw [hmatch, Truth.isTrue_iff, Truth.not_eq_true_iff]
  constructor
  · intro h
    by_cases hm : e ≠ none ∧ e ∈ vs
    · exact .inr (.inl hm)
    · obtain h' | ⟨hne, hnull, -⟩ := hfalse.mp (h.mpr hm)
      · exact .inl h'
      · exact .inr (.inr ⟨hne, hnull⟩)
  · rintro (h | h | ⟨hne, hnull⟩)
    · exact ⟨fun _ ⟨_, hv⟩ => by simp [h] at hv, fun _ => hfalse.mpr (.inl h)⟩
    · exact ⟨fun hf hm => by simp [htrue.mpr hm] at hf, fun hm => absurd h hm⟩
    · exact ⟨fun hf hm => by simp [htrue.mpr hm] at hf,
        fun hm => hfalse.mpr (.inr ⟨hne, hnull, fun hv => hm ⟨hne, hv⟩⟩)⟩

end Datum

end SqlCore
