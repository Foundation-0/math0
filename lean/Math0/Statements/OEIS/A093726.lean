/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A093726: imaginary parts of the convergents of `[1+i; 1+i, 1+i, …]`

Source: https://oeis.org/A093726, _Zhuorui He_, Jun 16 2026 (FORMULA section). Verbatim:
> Conjecture: a(n)/A093727(n) = A317974(n+1)/A138573(n). - _Zhuorui He_, Jun 16 2026

The entry (offset `1`) is "Given the infinite continued fraction (1+i)+1/((1+i)+1/((1+i)+...)),
where i is the square root of (-1), this is the numerator of the imaginary part of the
convergents.", with the Mathematica program
`Table[ Im[ Numerator[ FromContinuedFraction[ Table[1 + I, {n}]]]], {n, 30}]`.

## Encoding

* *Gaussian rationals.* `x + y i` with `x y : ℚ` is the pair `(x, y) : ℚ × ℚ`; `gadd` is the sum
  and `ginv` the reciprocal `1/(x + y i) = (x - y i)/(x² + y²)` (only ever applied to nonzero
  numbers here: every convergent has real part `≥ 1`, as `Re(1/z) > 0` when `Re z > 0`).
* *Convergents.* `cfValue [x₁, …, xₙ] = x₁ + 1/(x₂ + 1/(⋯ + 1/xₙ))` is Mathematica's
  `FromContinuedFraction`, and the `n`-th convergent is `conv n = cfValue (replicate n (1 + i))`
  for `n ≥ 1` (`conv 1 = 1 + i`, `conv 2 = (3 + i)/2`, `conv 3 = (8 + 4i)/5`, as in the entry's
  examples). `conv 0` (empty continued fraction) is outside the sequence and never used.
* *Numerator and denominator.* The entry's examples write each convergent as
  `(A093725(n) + a(n) i)/A093727(n)`, e.g. "(6+3*i)/4, so A093725(4)=6, a(4)=3 and
  A093727(4)=4": this is Mathematica's `Numerator`/`Denominator` of a Gaussian rational
  `z = x + y i`, namely the least `d ≥ 1` with `d z ∈ ℤ[i]` (`gden z = lcm(den x, den y)`,
  A093727) and the Gaussian integer `d z` (whose imaginary part `gnumIm z = d y` is `a(n)`).
  So `a n = gnumIm (conv n)` and `A093727 n = gden (conv n)`, both read off the reduced
  `Rat` parts. This reading matches the program `Im[Numerator[…]]`, the examples, and all
  listed terms. (The other conceivable reading of the name, the reduced numerator of
  `Im(conv n)`, gives the same listed terms but first differs at `n = 42`, where
  `den (Im (conv 42)) < lcm(den (Re (conv 42)), den (Im (conv 42)))`; it is not used.)
* `a` is `ℤ`-valued (the numerator of a rational), so nothing is truncated.
* `A317974` and `A138573` are the order-4 recurrences `u(n) = 2(u(n-1) + u(n-2) + u(n-3)) - u(n-4)`
  with initial terms `0, 0, 1, 1` resp. `0, 1, 2, 5` (offset `0` for both), taken in `ℤ`.
* `a_data` checks all 30 listed terms of A093726 in the kernel; `A093727_data`, `A317974_data`,
  `A138573_data` check listed terms of the cross-referenced sequences.
* The conjecture is stated for every `n ≥ 1` (the offset of A093726 and A093727) as an equality
  of rational numbers `a(n)/A093727(n) = A317974(n+1)/A138573(n)` (with Lean's `x / 0 = 0`
  convention; the denominators are positive anyway).
-/

namespace Math0.Statements.A093726

/-- Sum of Gaussian rationals `(x + y i) + (x' + y' i)`, written as pairs `(x, y)`. -/
def gadd (z w : ℚ × ℚ) : ℚ × ℚ := (z.1 + w.1, z.2 + w.2)

/-- Reciprocal of a Gaussian rational: `1/(x + y i) = x/(x² + y²) - (y/(x² + y²)) i`. -/
def ginv (z : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 / (z.1 * z.1 + z.2 * z.2), -z.2 / (z.1 * z.1 + z.2 * z.2))

/-- The value of the finite continued fraction `x₁ + 1/(x₂ + 1/(⋯ + 1/xₙ))` of Gaussian rationals
(Mathematica's `FromContinuedFraction`); the empty list gets the junk value `0`. -/
def cfValue : List (ℚ × ℚ) → ℚ × ℚ
  | [] => (0, 0)
  | [x] => x
  | x :: xs => gadd x (ginv (cfValue xs))

/-- The `n`-th convergent `(1+i) + 1/((1+i) + 1/(⋯ + 1/(1+i)))` (`n` partial quotients `1 + i`),
for `n ≥ 1`. -/
def conv (n : ℕ) : ℚ × ℚ := cfValue (List.replicate n (1, 1))

/-- Mathematica's `Denominator` of a Gaussian rational `z = x + y i`: the least `d ≥ 1` with
`d z ∈ ℤ[i]`, i.e. `lcm(den x, den y)`. -/
def gden (z : ℚ × ℚ) : ℕ := Nat.lcm z.1.den z.2.den

/-- The imaginary part of Mathematica's `Numerator` of a Gaussian rational `z = x + y i`: the
imaginary part `d y` of the Gaussian integer `d z`, where `d = gden z`. -/
def gnumIm (z : ℚ × ℚ) : ℤ := z.2.num * ((gden z / z.2.den : ℕ) : ℤ)

/-- A093726: the numerator of the imaginary part of the `n`-th convergent of
`(1+i) + 1/((1+i) + 1/((1+i) + ⋯))`, i.e. `Im(Numerator(conv n))` (offset `1`). -/
def a (n : ℕ) : ℤ := gnumIm (conv n)

/-- A093727: the denominator of the `n`-th convergent of `(1+i) + 1/((1+i) + ⋯)` (offset `1`). -/
def A093727 (n : ℕ) : ℕ := gden (conv n)

/-- A317974: `u(n) = 2(u(n-1) + u(n-2) + u(n-3)) - u(n-4)` for `n ≥ 4`, with initial terms
`0, 0, 1, 1` (offset `0`). -/
def A317974 : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | n + 4 => 2 * (A317974 (n + 3) + A317974 (n + 2) + A317974 (n + 1)) - A317974 n

/-- A138573: `u(n) = 2u(n-1) + 2u(n-2) + 2u(n-3) - u(n-4)` for `n ≥ 4`, with initial terms
`0, 1, 2, 5` (offset `0`). -/
def A138573 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | n + 4 => 2 * A138573 (n + 3) + 2 * A138573 (n + 2) + 2 * A138573 (n + 1) - A138573 n

/-- The definition reproduces the 30 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 30).map (fun i => a (i + 1)) =
    [1, 1, 4, 3, 11, 97, 280, 101, 2337, 2251, 19516, 14101, 163009, 16245, 30256,
      245929, 11371969, 32865601, 94983348, 22875581, 19349753, 2292794785,
      6626299912, 2393795271, 2635503517, 159951677089, 462268926316, 11517086141,
      3861059617665, 247970431013] := by
  decide +kernel

/-- The companion denominators reproduce the 28 terms listed in A093727 (kernel-checked). -/
theorem A093727_data : (List.range 28).map (fun i => A093727 (i + 1)) =
    [1, 2, 5, 4, 15, 130, 377, 136, 3145, 3030, 26269, 18980, 219413, 21866, 40725,
      331024, 15306833, 44237570, 127848949, 30790860, 26045045, 3086134658, 8919094697,
      3222082760, 3547425525, 215297250946, 622220603405, 15502163092] := by
  decide +kernel

/-- The first listed terms of A317974 (kernel-checked). -/
theorem A317974_data : (List.range 20).map A317974 =
    [0, 0, 1, 1, 4, 12, 33, 97, 280, 808, 2337, 6753, 19516, 56404, 163009, 471105,
      1361520, 3934864, 11371969, 32865601] := by
  decide +kernel

/-- The first listed terms of A138573 (kernel-checked). -/
theorem A138573_data : (List.range 20).map A138573 =
    [0, 1, 2, 5, 16, 45, 130, 377, 1088, 3145, 9090, 26269, 75920, 219413, 634114,
      1832625, 5296384, 15306833, 44237570, 127848949] := by
  decide +kernel

/-- Conjecture (Zhuorui He, A093726): for every `n ≥ 1`,
`a(n)/A093727(n) = A317974(n+1)/A138573(n)`, i.e. the imaginary part of the `n`-th convergent of
`(1+i) + 1/((1+i) + ⋯)` is `A317974(n+1)/A138573(n)`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) / (A093727 n : ℚ) = (A317974 (n + 1) : ℚ) / (A138573 n : ℚ)

end Math0.Statements.A093726
