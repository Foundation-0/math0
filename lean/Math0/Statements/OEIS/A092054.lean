/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A092054: numerator plus denominator of the convergents of `[1; 1/2, 1/3, …]`

Source: https://oeis.org/A092054, Franklin T. Adams-Watters, Feb 02 2006 (FORMULA section).
Verbatim:
> It appears that a(n) = Sum_{k=1..n} A001511(floor((k+1)/2)). Equivalently,
> a(n) = 2n + 1 - A000120(n) - A000120(n+1) = A011371(n) + A011371(n+1).

The entry's name (Paul D. Hanna, Feb 19 2004): "Base-2 logarithm of the sum of numerator and
denominator of the convergents of the continued fraction expansion
[1; 1/2, 1/3, 1/4, ..., 1/n, ...]." Offset `1`. The entry's example: `a(4) = 6`, since
`[1; 1/2, 1/3, 1/4] = 1 + 1/(1/2 + 1/(1/3 + 1/(1/4))) = 45/19` and `45 + 19 = 2^6`.

## Encoding

* `cfEval [x₀, x₁, …, x_k] = x₀ + 1/(x₁ + 1/(⋯ + 1/x_k))` is the value of a finite
  continued fraction with (rational) partial quotients `x₀, …, x_k`, computed in `ℚ`.
  (`cfEval [] = 0` is junk and never used for `n ≥ 1`.)
* `conv n = cfEval [1, 1/2, …, 1/n]` is the `n`-th convergent `[1; 1/2, …, 1/n]` (`n ≥ 1`),
  matching the example (`conv 4 = 45/19`). `conv 1 = 1`, `conv 2 = 3`, `conv 3 = 9/7`.
  The partial denominators `1/(k+1)` and all tails are positive, so no division by zero
  occurs and `conv n > 0`. Its numerator and denominator are taken in lowest terms
  (`Rat.num`, `Rat.den`); they are A001902(n) and A092053(n) (checked in `num_data`,
  `den_data`).
* `a n = Nat.log 2 (num + den)` is the (floor) base-2 logarithm of `num + den`. The entry
  asserts (comment and first formula) that `num + den` is a power of `2`; the OEIS "base-2
  logarithm" is the real logarithm. So the conjectured "`a(n) = f(n)`" means
  `log₂(num + den) = f(n)` with the real logarithm, i.e. `num + den = 2 ^ f(n)`. In the
  statement this is expressed by the two conjuncts `2 ^ a n = num + den` (the real base-2
  logarithm of `num + den` is the integer `a n`) and `a n = f(n)`.
* Helper sequences, as in their OEIS definitions:
  - A001511 (offset 1), the ruler function: `ruler m = padicValNat 2 (2 * m)`, the exponent of
    the highest power of `2` dividing `2m`.
  - A000120 (offset 0), the binary weight: `binWeight m = (Nat.digits 2 m).sum`.
  - A011371 (offset 0): `A011371 m = m - binWeight m` ("n minus (number of 1's in binary
    expansion of n)"); this never truncates, since `binWeight m ≤ m`.
* `floor((k+1)/2)` is `(k + 1) / 2` (natural-number division); for `k ≥ 1` it is `≥ 1`, inside
  the range of A001511.
* The three claimed equalities ("a(n) = … Equivalently, a(n) = … = …") are all part of the
  statement, for every `n ≥ 1` (the offset of A092054). The middle form
  `2n + 1 - A000120(n) - A000120(n+1)` is evaluated in `ℤ`, so that no truncated subtraction
  is involved (it is in fact never negative).
* `a_data` checks all 67 listed terms `a 1, …, a 67` (kernel-checked).
-/

namespace Math0.Statements.A092054

/-- The value `x₀ + 1/(x₁ + 1/(⋯ + 1/x_k))` of the finite continued fraction
`[x₀; x₁, …, x_k]` with rational partial quotients. (`cfEval [] = 0` is junk.) -/
def cfEval : List ℚ → ℚ
  | [] => 0
  | [x] => x
  | x :: y :: ys => x + 1 / cfEval (y :: ys)

/-- The `n`-th convergent `[1; 1/2, 1/3, …, 1/n]` (for `n ≥ 1`). -/
def conv (n : ℕ) : ℚ := cfEval ((List.range n).map fun k => 1 / ((k : ℚ) + 1))

/-- The numerator of the `n`-th convergent, in lowest terms (A001902(n)). -/
def num (n : ℕ) : ℕ := (conv n).num.natAbs

/-- The denominator of the `n`-th convergent, in lowest terms (A092053(n)). -/
def den (n : ℕ) : ℕ := (conv n).den

/-- A092054: the base-2 logarithm of the sum of the numerator and the denominator of the
convergent `[1; 1/2, 1/3, …, 1/n]` (as a natural number: the floor base-2 logarithm). -/
def a (n : ℕ) : ℕ := Nat.log 2 (num n + den n)

/-- The example in the entry: `[1; 1/2, 1/3, 1/4] = 45/19`. -/
theorem conv_four : conv 4 = 45 / 19 := by decide +kernel

/-- The numerators are the terms `A001902(1), …, A001902(24)` (all listed terms from index
`1`; kernel-checked). -/
theorem num_data : (List.range 24).map (fun i => num (i + 1)) =
    [1, 3, 9, 45, 75, 175, 1225, 11025, 19845, 43659, 160083, 693693, 1288287, 2760615,
      41409225, 703956825, 1329696225, 2807136475, 10667118605, 44801898141, 85530896451,
      178837328943, 1371086188563, 11425718238025] := by
  decide +kernel

/-- The denominators are the terms `A092053(1), …, A092053(25)` (all listed terms;
kernel-checked). -/
theorem den_data : (List.range 25).map (fun i => den (i + 1)) =
    [1, 1, 7, 19, 53, 81, 823, 5359, 12923, 21877, 102061, 354883, 808865, 1433689,
      25699639, 369784999, 817787423, 1487830821, 6512750579, 23917578595, 51908057021,
      96040578001, 827937066989, 6166467806391, 13211837015707] := by
  decide +kernel

/-- The definition reproduces the 67 terms listed in OEIS, `a 1, …, a 67`
(kernel-checked). -/
theorem a_data : (List.range 67).map (fun i => a (i + 1)) =
    [1, 2, 4, 6, 7, 8, 11, 14, 15, 16, 18, 20, 21, 22, 26, 30, 31, 32, 34, 36, 37, 38, 41, 44,
      45, 46, 48, 50, 51, 52, 57, 62, 63, 64, 66, 68, 69, 70, 73, 76, 77, 78, 80, 82, 83, 84,
      88, 92, 93, 94, 96, 98, 99, 100, 103, 106, 107, 108, 110, 112, 113, 114, 120, 126, 127,
      128, 130] := by
  decide +kernel

/-- A001511, the ruler function: the exponent of the highest power of `2` dividing `2m`
(offset `1`). -/
def ruler (m : ℕ) : ℕ := padicValNat 2 (2 * m)

/-- A000120: the number of `1`'s in the binary expansion of `m` (offset `0`). -/
def binWeight (m : ℕ) : ℕ := (Nat.digits 2 m).sum

/-- A011371: `m` minus the number of `1`'s in the binary expansion of `m` (offset `0`). -/
def A011371 (m : ℕ) : ℕ := m - binWeight m

/-- `ruler` reproduces the first 34 listed terms of A001511 (kernel-checked). -/
theorem ruler_data : (List.range 34).map (fun i => ruler (i + 1)) =
    [1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2,
      1, 6, 1, 2] := by
  decide +kernel

/-- `binWeight` reproduces the first 34 listed terms of A000120 (kernel-checked). -/
theorem binWeight_data : (List.range 34).map binWeight =
    [0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4,
      4, 5, 1, 2] := by
  decide +kernel

/-- `A011371` reproduces the first 27 listed terms of A011371 (kernel-checked). -/
theorem A011371_data : (List.range 27).map A011371 =
    [0, 0, 1, 1, 3, 3, 4, 4, 7, 7, 8, 8, 10, 10, 11, 11, 15, 15, 16, 16, 18, 18, 19, 19, 22,
      22, 23] := by
  decide +kernel

/-- Conjecture (Franklin T. Adams-Watters, 2006): for every `n ≥ 1`, the base-2 logarithm of
`num + den` (for the convergent `[1; 1/2, …, 1/n] = num/den` in lowest terms) is
`a(n) = Sum_{k=1..n} A001511(floor((k+1)/2))`, i.e. `num + den` is exactly `2 ^ a n` and
`a n` equals that sum; equivalently `a(n) = 2n + 1 - A000120(n) - A000120(n+1)
= A011371(n) + A011371(n+1)`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    2 ^ a n = num n + den n ∧
    a n = ∑ k ∈ Finset.Icc 1 n, ruler ((k + 1) / 2) ∧
    (a n : ℤ) = 2 * (n : ℤ) + 1 - (binWeight n : ℤ) - (binWeight (n + 1) : ℤ) ∧
    a n = A011371 n + A011371 (n + 1)

end Math0.Statements.A092054
