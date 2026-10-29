/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A242396
import Math0.Audit

/-!
# Stephan's conjectured g.f. for A242396 is false

We refute Ralf Stephan's conjectured rational generating function for A242396 (rows of the
unit triangular tiling meeting a circle of radius `n`).

Clearing the denominator `1 - X - X¹³ + X¹⁴`, the conjecture says that the coefficient of `X⁹⁷`
in `(∑_{n ≥ 1} a(n) Xⁿ) · (X¹⁴ - X¹³ - X + 1)`, namely `a(97) - a(96) - a(84) + a(83)`, equals
the coefficient of `X⁹⁷` in the degree-14 numerator, which is `0`. But the kernel computes
`a 97 = 226`, `a 96 = 222`, `a 84 = 194`, `a 83 = 192`, so that coefficient is `2`.

Geometrically, `a(n) = 2⌊2n/√3⌋ + 2`, a Beatty-type sequence with irrational slope, which cannot
satisfy the period-13 recurrence `a(n) = a(n-1) + a(n-13) - a(n-14)`; the first failure is at
`n = 97`, where `⌊194/√3⌋ = 112` (`3·112² = 37632 ≤ 37636 = 4·97² < 3·113²`).
-/

namespace Math0.Frontier.A242396
open Math0.Statements.A242396 PowerSeries

/-- The four values of `a` entering the coefficient of `X⁹⁷`, computed by the kernel. -/
private lemma vals : a 97 = 226 ∧ a 96 = 222 ∧ a 84 = 194 ∧ a 83 = 192 := by
  decide +kernel

/-- Stephan's conjectured g.f. for A242396 fails: comparing coefficients of `X⁹⁷` gives
`a(83) - a(84) - a(96) + a(97) = 192 - 194 - 222 + 226 = 2 ≠ 0`. -/
theorem result : ¬ statement := by
  intro h
  have e2 : (2 : ℤ⟦X⟧) = C 2 := (map_ofNat C 2).symm
  have e4 : (4 : ℤ⟦X⟧) = C 4 := (map_ofNat C 4).symm
  rw [statement, e2, e4] at h
  have h97 := congrArg (coeff 97) h
  simp only [mul_sub, mul_add, mul_one, neg_mul, map_add, map_sub, map_neg, coeff_C_mul,
    coeff_X_pow, coeff_X] at h97
  simp [mul_comm _ (X ^ _), coeff_X_pow_mul'] at h97
  obtain ⟨h1, h2, h3, h4⟩ := vals
  rw [h1, h2, h3, h4] at h97
  norm_num at h97

end Math0.Frontier.A242396

#math0_settles Math0.Frontier.A242396.result Math0.Statements.A242396.statement
