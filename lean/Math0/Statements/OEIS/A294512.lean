/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A294512: denominators of partial sums of reciprocals of octagonal numbers

Source: https://oeis.org/A294512, _Wolfdieter Lang_, Nov 01 2017. Verbatim (FORMULA section):
> a(n) = A250400(n+1)/(n+1), n >= 0. [conjecture].

The entry's definition: "Denominators of partial sums of the reciprocals of octagonal numbers.",
with "The octagonal numbers are here A000567(k+1) = (k + 1)*(3*k + 1), k >= 0." and
"a(n) = denominator(V(3,1;n)) with V(3,1;n) = Sum_{k=0..n} 1/((k + 1)*(3*k + 1))". Offset `0`.

A250400 (offset `1`, _Colin Barker_, Nov 21 2014) is the "Numerator of the harmonic mean of the
first n octagonal numbers", i.e. the numerator, in lowest terms, of
`n / Sum_{j=1..n} 1/A000567(j)`, where A000567(j) = j*(3*j-2) (so the first octagonal numbers
are 1, 8, 21, ...; the example there: `3/(1/1+1/8+1/21) = 504/197`).

## Encoding

* `V n : ℚ` is the partial sum `∑_{k=0}^{n} 1/((k+1)(3k+1))`, and `a n` is the denominator of
  `V n` (Mathlib's `Rat.den`, i.e. in lowest terms); `a` uses the OEIS offset `0`.
* `octagonal j = j * (3 * j - 2)` is A000567 (offset `0`; the subtraction is never truncated for
  `j ≥ 1`), `harmonicMean m = m / ∑_{j=1}^{m} 1/octagonal j`, and `A250400 m` is the numerator of
  `harmonicMean m` in lowest terms (a positive integer for `m ≥ 1`, taken as a natural number via
  `Int.natAbs`); `A250400` uses the OEIS offset `1`.
* The quotient `A250400(n+1)/(n+1)` is read as an exact rational quotient, so the conjecture
  says it equals the integer `a(n)` (in particular, that `n+1` divides `A250400(n+1)`), for every
  `n ≥ 0`, i.e. every natural number `n`.
-/

namespace Math0.Statements.A294512

/-- The partial sum `V(3,1;n) = ∑_{k=0}^{n} 1/((k + 1)(3k + 1))` of the reciprocals of the
octagonal numbers `A000567(k+1) = (k + 1)(3k + 1)`. -/
def V (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), 1 / (((k : ℚ) + 1) * (3 * (k : ℚ) + 1))

/-- A294512: the denominator (in lowest terms) of the `n`-th partial sum `V n` of the reciprocals
of the octagonal numbers (offset `0`). -/
def a (n : ℕ) : ℕ := (V n).den

/-- The octagonal numbers A000567: `j * (3 * j - 2)` (offset `0`). -/
def octagonal (j : ℕ) : ℕ := j * (3 * j - 2)

/-- The harmonic mean of the first `m` octagonal numbers `octagonal 1, …, octagonal m`. -/
def harmonicMean (m : ℕ) : ℚ := (m : ℚ) / ∑ j ∈ Finset.Icc 1 m, 1 / (octagonal j : ℚ)

/-- A250400: the numerator (in lowest terms) of the harmonic mean of the first `m` octagonal
numbers (offset `1`). -/
def A250400 (m : ℕ) : ℕ := (harmonicMean m).num.natAbs

/-- The definition reproduces all 23 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 23).map (fun i => a (i + 0)) =
    [1, 8, 168, 420, 5460, 14560, 276640, 3043040, 136936800, 136936800, 4245040800,
      72165693600, 2670130663200, 2670130663200, 114815618517600, 1320379612952400,
      9242657290666800, 3080885763555600, 280080523959600, 8122335194828400,
      165154148961510800, 14533565108612950400, 973748862277067676800] := by
  decide +kernel

/-- `A250400` reproduces all 20 terms listed in OEIS A250400 (kernel-checked). -/
theorem A250400_data : (List.range 20).map (fun i => A250400 (i + 1)) =
    [1, 16, 504, 1680, 27300, 87360, 1936480, 24344320, 1232431200, 1369368000, 46695448800,
      865988323200, 34711698621600, 37381829284800, 1722234277764000, 21126073807238400,
      157125173941335600, 55455943744000800, 5321529955232400, 162446703896568000] := by
  decide +kernel

/-- The octagonal numbers start `0, 1, 8, 21, 40` (as in A000567). -/
theorem octagonal_data : (List.range 5).map octagonal = [0, 1, 8, 21, 40] := by
  decide +kernel

/-- Conjecture (Lang, A294512): for every `n ≥ 0`, `a(n) = A250400(n+1)/(n+1)`, the quotient
being taken in `ℚ`. -/
def statement : Prop :=
  ∀ n : ℕ, (A250400 (n + 1) : ℚ) / ((n : ℚ) + 1) = (a n : ℚ)

end Math0.Statements.A294512
