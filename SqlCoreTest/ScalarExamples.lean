/-
  Typed core phase 1 (#290): kernel-checked examples of the scalar operators.
  Each `example` is closed by `decide` or `rfl`, so the definitions reduce in
  the kernel; a regression to an opaque or partial definition breaks the build.
-/
import SqlCore

namespace SqlCoreTest.ScalarExamples
open SqlCore

private def i (z : Int) : Datum := some (.int z)
private def b (x : Bool) : Datum := some (.bool x)
private def t (s : String) : Datum := some (.text s)
private def null : Datum := none

-- Three-valued logic
example : (Truth.unknown ⊓ Truth.false) = Truth.false := by decide
example : (Truth.unknown ⊔ Truth.true) = Truth.true := by decide
example : Truth.unknown.not = Truth.unknown := by decide

-- Arithmetic: truncating division, sign of the dividend for %
example : evalBinOp (.arith .div) (i (-7)) (i 2) = .ok (i (-3)) := by decide
example : evalBinOp (.arith .mod) (i (-7)) (i 2) = .ok (i (-1)) := by decide
example : evalBinOp (.arith .div) (i 1) (i 0) = .error .divisionByZero := by decide
-- NULL / 0 is NULL, not an error
example : evalBinOp (.arith .div) null (i 0) = .ok null := by decide
-- A wrong-typed operand is an error even beside NULL
example : evalBinOp (.arith .add) (b true) null = .error .typeMismatch := by decide
example : evalBinOp (.arith .add) (i 1) (t "1") = .error .typeMismatch := by decide

-- Comparisons need one type; NULL gives unknown (NULL as a datum)
example : evalBinOp (.cmp .lt) (i 1) (i 2) = .ok (b true) := by decide
example : evalBinOp (.cmp .lt) (b false) (b true) = .ok (b true) := by decide
example : evalBinOp (.cmp .eq) (i 1) null = .ok null := by decide
example : evalBinOp (.cmp .eq) (i 1) (b true) = .error .typeMismatch := by decide

-- Kleene AND / OR; NULL AND FALSE is FALSE
example : evalBinOp .and null (b false) = .ok (b false) := by decide
example : evalBinOp .or null (b true) = .ok (b true) := by decide
example : evalBinOp .and null (b true) = .ok null := by decide
example : evalBinOp .and (i 0) (b false) = .error .typeMismatch := by decide

-- IS [NOT] NULL is never NULL
example : evalUnOp .isNull null = .ok (b true) := by decide
example : evalUnOp .isNotNull (i 3) = .ok (b true) := by decide
example : evalUnOp .not null = .ok null := by decide

-- Three-valued IN
example : Datum.inList (i 1) [i 2, i 1] = .ok .true := by decide
example : Datum.inList (i 1) [i 2, i 3] = .ok .false := by decide
example : Datum.inList (i 1) [i 2, null] = .ok .unknown := by decide
example : Datum.inList (i 1) [i 1, null] = .ok .true := by decide
example : Datum.inList null [] = .ok .false := by decide
example : Datum.inList null [i 1] = .ok .unknown := by decide
example : Datum.inList (i 1) [i 2, b true] = .error .typeMismatch := by decide

-- Text
example : evalBinOp .concat (t "ab") (t "c") = .ok (t "abc") := by decide
example : evalBinOp (.cmp .lt) (t "a") (t "b") = .ok (b true) := by decide

-- Decimals (#290 part 2): exact `ℚ`, int promoted. `decide +kernel`, since
-- Mathlib's `ℚ` arithmetic is irreducible to the elaborator's `decide`.
private def d (q : ℚ) : Datum := some (.decimal q)

example : evalBinOp (.cmp .eq) (i 1) (d 1) = .ok (b true) := by decide +kernel
example : evalBinOp (.cmp .lt) (i 1) (d (3/2)) = .ok (b true) := by decide +kernel
example : evalBinOp (.cmp .eq) (d (5/2)) (d (25/10)) = .ok (b true) := by decide +kernel
example : evalBinOp (.arith .add) (d (3/2)) (i 1) = .ok (d (5/2)) := by decide +kernel
example : evalBinOp (.arith .mul) (d (1/10)) (d (2/10)) = .ok (d (2/100)) := by decide +kernel
-- an integer result of decimal arithmetic stays a decimal
example : evalBinOp (.arith .add) (d (1/2)) (d (1/2)) = .ok (d 1) := by decide +kernel
-- `%` is exact with the dividend's sign, as Postgres and DuckDB
example : evalBinOp (.arith .mod) (d (15/2)) (i 2) = .ok (d (3/2)) := by decide +kernel
example : evalBinOp (.arith .mod) (d (-15/2)) (i 2) = .ok (d (-3/2)) := by decide +kernel
example : evalBinOp (.arith .mod) (d (15/2)) (i (-2)) = .ok (d (3/2)) := by decide +kernel
-- `/` with a decimal operand is exact (phase 8d, registry T3): `1.0 / 4` is `0.25`, and `1.0 / 3`
-- is the rational `1/3`, where engines round
example : evalBinOp (.arith .div) (d 1) (i 4) = .ok (d (1/4)) := by decide +kernel
example : evalBinOp (.arith .div) (d 1) (i 3) = .ok (d (1/3)) := by decide +kernel
example : evalBinOp (.arith .div) (i 7) (d (1/2)) = .ok (d 14) := by decide +kernel
-- … and `(1.0 / 3) * 3` is exactly `1`
example : (do evalBinOp (.arith .mul) (← evalBinOp (.arith .div) (d 1) (i 3)) (i 3)) = .ok (d 1) := by
  decide +kernel
example : evalBinOp (.arith .div) (d 1) (i 0) = .error .divisionByZero := by decide +kernel
example : evalBinOp (.arith .div) null (d 0) = .ok null := by decide +kernel
example : evalUnOp .neg (d (3/2)) = .ok (d (-3/2)) := by decide +kernel
example : evalBinOp (.cmp .eq) (d 1) (t "1") = .error .typeMismatch := by decide +kernel
example : Datum.inList (i 1) [d 2, d 1] = .ok .true := by decide +kernel

end SqlCoreTest.ScalarExamples
