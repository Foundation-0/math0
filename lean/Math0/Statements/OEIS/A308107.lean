/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A308107: sum of smallest sides of scalene integer triangles with perimeter `n`

Source: https://oeis.org/A308107, _Colin Barker_, May 13 2019 (FORMULA section). Verbatim:
> Conjectures from _Colin Barker_, May 13 2019: (Start)
> G.f.: x^9*(2 + 2*x + 2*x^2 + x^3) / ((1 - x)^4*(1 + x)^3*(1 + x^2)^2*(1 + x + x^2)^2).
> a(n) = -a(n-1) + 2*a(n-3) + 4*a(n-4) + 2*a(n-5) - a(n-6) - 5*a(n-7) - 5*a(n-8) - a(n-9)
> + 2*a(n-10) + 4*a(n-11) + 2*a(n-12) - a(n-14) - a(n-15) for n>15.
> (End)

The entry (_Wesley Ivan Hurt_, May 13 2019, offset `1`) is "Sum of the smallest side lengths of
all integer-sided scalene triangles with perimeter n."

## Encoding

* *Triangles.* An integer-sided scalene triangle has three pairwise distinct positive integer
  sides; listing them in increasing order `k < i < j` identifies each triangle with exactly one
  triple, and its smallest side is `k`. For `k < i < j` the triangle inequalities reduce to
  `j < k + i` (this also forces `k ≥ 1`, since `k = 0` would give `j < i`). So
  `a n = ∑ k` over the triples `(k, i, j)` with `k < i < j < k + i` and `k + i + j = n`.
  All sides are `≤ n`, so the triples are searched in `{0, …, n}³`; `a` is computable.
* *Offset.* The entry has offset `1`. The definition also gives `a 0 = 0` (empty sum), which is
  harmless: the claimed g.f. has zero constant term, so `∑_{n ≥ 1} a(n) xⁿ = ∑_{n ≥ 0} a(n) xⁿ`.
* *Data.* `a` sums over `(n+1)³` triples, which is too slow for the kernel, so `aFast` sums
  over the pairs `(k, i)` with the third side `j = n - (k + i)`; `a_eq_aFast` proves
  `a n = aFast n` for every `n`. `a_data` checks all 61 listed terms `a(1), …, a(61)` in the
  kernel. As a separate transcription check (not about `a`), `recurrence_data` checks that the
  61 listed terms satisfy the stated recurrence for `16 ≤ n ≤ 61`, and `den_eq` shows that the
  stated denominator multiplies out to the recurrence's characteristic polynomial
  `1 + x - 2x³ - 4x⁴ - 2x⁵ + x⁶ + 5x⁷ + 5x⁸ + x⁹ - 2x¹⁰ - 4x¹¹ - 2x¹² + x¹⁴ + x¹⁵`.
* *The conjecture* (`statement`) is the conjunction of the two stated formulas:
  1. the generating function: `∑ a(n) xⁿ` equals the stated rational function, as formal power
     series over `ℚ`, using Mathlib's inverse of a power series; the denominator has constant
     coefficient `1 ≠ 0`, so this is the honest quotient (`genFun_iff` restates it as
     `A(x) · D(x) = x⁹(2 + 2x + 2x² + x³)`);
  2. the order-15 recurrence for every `n > 15` (as stated; then all indices `n - 1, …, n - 15`
     are `≥ 1`, inside the entry's domain), in `ℤ`.
-/

namespace Math0.Statements.A308107

open PowerSeries

/-- A308107: the sum of the smallest sides `k` over all integer-sided scalene triangles with
perimeter `n`, i.e. over all triples `k < i < j` with `j < k + i` and `k + i + j = n`. -/
def a (n : ℕ) : ℕ :=
  ∑ t ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun t : ℕ × ℕ × ℕ => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < t.1 + t.2.1 ∧
        t.1 + t.2.1 + t.2.2 = n),
    t.1

/-- A faster evaluator: sum over the two smaller sides `k, i`; the largest is `n - (k + i)`. -/
def aFast (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
    if k < i ∧ k + i ≤ n ∧ i < n - (k + i) ∧ n - (k + i) < k + i then k else 0

/-- The fast evaluator computes `a`. -/
theorem a_eq_aFast (n : ℕ) : a n = aFast n := by
  unfold a aFast
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j : ℕ,
      (if k < i ∧ i < j ∧ j < k + i ∧ k + i + j = n then k else 0) =
        if n - (k + i) = j then
          (if k < i ∧ k + i ≤ n ∧ i < n - (k + i) ∧ n - (k + i) < k + i then k else 0)
        else 0 := by
    intro j
    split_ifs <;> omega
  simp only [h]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]
  rw [if_pos (by omega)]

/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all 61 listed
terms `a(1), …, a(61)`. -/
theorem a_data : (List.range 61).map (fun i => a (i + 1)) =
    [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 3, 5, 3, 9, 7, 13, 12, 18, 17, 29, 23, 35, 36, 48, 43, 63,
      58, 78, 75, 95, 92, 122, 111, 141, 141, 171, 162, 204, 195, 237, 231, 273, 267, 323, 306,
      362, 360, 416, 402, 474, 460, 532, 522, 594, 584, 674, 650, 740, 735, 825] := by
  simp only [a_eq_aFast]
  decide +kernel

/-! ### The conjecture -/

/-- The 61 terms listed in the entry, `a(1), …, a(61)`, preceded by `a(0) = 0`. -/
def listed : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 3, 5, 3, 9, 7, 13, 12, 18, 17, 29, 23, 35, 36, 48, 43, 63,
    58, 78, 75, 95, 92, 122, 111, 141, 141, 171, 162, 204, 195, 237, 231, 273, 267, 323, 306,
    362, 360, 416, 402, 474, 460, 532, 522, 594, 584, 674, 650, 740, 735, 825]

/-- Transcription check (not about `a`): the listed terms satisfy the conjectured recurrence for
`16 ≤ n ≤ 61`. -/
theorem recurrence_data : ∀ n ∈ List.range' 16 46,
    listed.getD n 0 = -listed.getD (n - 1) 0 + 2 * listed.getD (n - 3) 0 +
      4 * listed.getD (n - 4) 0 + 2 * listed.getD (n - 5) 0 - listed.getD (n - 6) 0 -
      5 * listed.getD (n - 7) 0 - 5 * listed.getD (n - 8) 0 - listed.getD (n - 9) 0 +
      2 * listed.getD (n - 10) 0 + 4 * listed.getD (n - 11) 0 + 2 * listed.getD (n - 12) 0 -
      listed.getD (n - 14) 0 - listed.getD (n - 15) 0 := by
  decide

/-- The conjectured denominator `(1 - x)^4 (1 + x)^3 (1 + x^2)^2 (1 + x + x^2)^2`. -/
noncomputable def den : PowerSeries ℚ :=
  (1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2

/-- Transcription check: the denominator is the characteristic polynomial of the recurrence. -/
theorem den_eq : den = 1 + X - 2 * X ^ 3 - 4 * X ^ 4 - 2 * X ^ 5 + X ^ 6 + 5 * X ^ 7 +
    5 * X ^ 8 + X ^ 9 - 2 * X ^ 10 - 4 * X ^ 11 - 2 * X ^ 12 + X ^ 14 + X ^ 15 := by
  unfold den
  ring

/-- Barker's conjecture (both formulas):
`∑ a(n) xⁿ = x^9 (2 + 2x + 2x^2 + x^3) / ((1 - x)^4 (1 + x)^3 (1 + x^2)^2 (1 + x + x^2)^2)`, and
`a(n) = -a(n-1) + 2a(n-3) + 4a(n-4) + 2a(n-5) - a(n-6) - 5a(n-7) - 5a(n-8) - a(n-9) + 2a(n-10)
+ 4a(n-11) + 2a(n-12) - a(n-14) - a(n-15)` for all `n > 15`. -/
def statement : Prop :=
  (PowerSeries.mk (fun n => (a n : ℚ)) =
    X ^ 9 * (2 + 2 * X + 2 * X ^ 2 + X ^ 3) *
      ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2)⁻¹) ∧
  (∀ n : ℕ, 15 < n →
    (a n : ℤ) = -(a (n - 1) : ℤ) + 2 * (a (n - 3) : ℤ) + 4 * (a (n - 4) : ℤ) +
      2 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ) - 5 * (a (n - 7) : ℤ) - 5 * (a (n - 8) : ℤ) -
      (a (n - 9) : ℤ) + 2 * (a (n - 10) : ℤ) + 4 * (a (n - 11) : ℤ) + 2 * (a (n - 12) : ℤ) -
      (a (n - 14) : ℤ) - (a (n - 15) : ℤ))

theorem constantCoeff_den : PowerSeries.constantCoeff den ≠ 0 := by
  simp [den]

/-- The generating-function clause, with the denominator multiplied out. -/
theorem genFun_iff :
    PowerSeries.mk (fun n => (a n : ℚ)) =
        X ^ 9 * (2 + 2 * X + 2 * X ^ 2 + X ^ 3) *
          ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2)⁻¹ ↔
      PowerSeries.mk (fun n => (a n : ℚ)) * den = X ^ 9 * (2 + 2 * X + 2 * X ^ 2 + X ^ 3) :=
  PowerSeries.eq_mul_inv_iff_mul_eq constantCoeff_den

end Math0.Statements.A308107
