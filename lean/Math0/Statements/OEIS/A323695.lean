/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A323695: parity of the coefficients of `∑ x^n (1 - x^(n+1))^n / (1 + x^(n+1))^(n+1)`

Source: https://oeis.org/A323695, _Paul D. Hanna_, Feb 23 2019. Verbatim:
> Odd terms occur only at n = k*(k+2) for k >= 0 (conjecture);

The entry's definition (offset 0): "G.f.: Sum_{n>=0} x^n * (1 - x^(n+1))^n / (1 + x^(n+1))^(n+1)",
i.e. `a(N)` is the coefficient of `x^N` in this power series.

## Encoding

* `summand m : ℤ⟦X⟧` is `X^m * (1 - X^(m+1))^m * ((1 + X^(m+1))^(m+1))⁻¹`, the inverse being
  `PowerSeries.invOfUnit _ 1` (the factor has constant coefficient `1`); `summand_spec` records
  the defining identity `(1 + X^(m+1))^(m+1) * summand m = X^m * (1 - X^(m+1))^m`.
* `summand m` is divisible by `X^m` (`coeff_summand_of_lt`), so the series converges
  `X`-adically. `A` is its sum, defined coefficientwise as the finite sum over `m ≤ N`, and
  `hasSum_summand` proves `HasSum summand A` in the product (coefficientwise) topology on `ℤ⟦X⟧`.
* `a N` is defined by an explicit finite formula `coeffA N`, obtained by expanding
  `(1 - X^(m+1))^m = ∑_i (-1)^i C(m,i) X^((m+1) i)` with the binomial theorem and
  `(1 + X^(m+1))^(-(m+1)) = ∑_j (-1)^j C(m+j, m) X^((m+1) j)`. The theorem `a_eq_coeff` proves
  (in Lean) that `a N = coeff N A`, so `a` is exactly the OEIS definition; the explicit formula
  only serves to make `a` computable for the kernel-checked data. Only the summands with
  `m + 1 ∣ N + 1` can contribute (`term_eq_zero`), and `coeffA` skips the others to make kernel
  evaluation fast; `coeff_A` accounts for this. The terms are signed (keyword `sign`), so
  `a : ℕ → ℤ`, and `a_data` checks all 121 terms listed in the entry's data (`n = 0..120`).
* Reading of the conjecture: "odd terms occur only at `n = k*(k+2)`" is the one-directional
  claim `Odd (a n) → ∃ k, n = k * (k + 2)` for every `n ≥ 0` (offset 0), with `k : ℕ`
  (so `k ≥ 0`). The converse, `a(n*(n+2)) = 1 (mod 2)`, is listed separately in the entry's
  formula section (not marked as a conjecture there) and is not part of `statement`.
-/

namespace Math0.Statements.A323695

open PowerSeries

/-! ### The generating function -/

/-- The `m`-th summand `x^m * (1 - x^(m+1))^m / (1 + x^(m+1))^(m+1)` of the g.f., in `ℤ⟦X⟧`. -/
noncomputable def summand (m : ℕ) : PowerSeries ℤ :=
  X ^ m * (1 - X ^ (m + 1)) ^ m * invOfUnit ((1 + X ^ (m + 1)) ^ (m + 1)) 1

theorem constantCoeff_one_add_X_pow_pow (b d : ℕ) (hb : b ≠ 0) :
    constantCoeff ((1 + X ^ b : PowerSeries ℤ) ^ d) = ((1 : ℤˣ) : ℤ) := by
  simp [map_pow, zero_pow hb]

/-- `summand m` is the quotient `x^m * (1 - x^(m+1))^m / (1 + x^(m+1))^(m+1)`. -/
theorem summand_spec (m : ℕ) :
    (1 + X ^ (m + 1)) ^ (m + 1) * summand m = X ^ m * (1 - X ^ (m + 1)) ^ m := by
  rw [summand, mul_comm, mul_assoc, invOfUnit_mul _ _
    (constantCoeff_one_add_X_pow_pow _ _ (by omega)), mul_one]

/-- `summand m` is divisible by `X ^ m`. -/
theorem coeff_summand_of_lt {N m : ℕ} (h : N < m) : coeff N (summand m) = 0 := by
  rw [summand, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]

/-- The generating function `A(x) = ∑_{m ≥ 0} summand m`, defined coefficientwise
(the coefficient of `x^N` only involves the summands with `m ≤ N`, see `coeff_summand_of_lt`). -/
noncomputable def A : PowerSeries ℤ :=
  mk fun N => ∑ m ∈ Finset.range (N + 1), coeff N (summand m)

open scoped PowerSeries.WithPiTopology in
/-- `A` is the sum of the family `summand` in the coefficientwise topology of `ℤ⟦X⟧`. -/
theorem hasSum_summand : HasSum summand A := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro N
  rw [A, coeff_mk]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  exact coeff_summand_of_lt (by omega)

/-! ### An explicit formula for the coefficients -/

/-- Binomial coefficient via descending factorials (fast in the kernel); equals `Nat.choose`. -/
def binom (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

theorem binom_eq_choose (n k : ℕ) : binom n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- Contribution of `(-1)^i C(m,i) X^((m+1) i)` (from `(1 - X^(m+1))^m`) to the coefficient of
`x^N` in `summand m`: with `k = (m+1) i + m`, it is `(-1)^i C(m,i) (-1)^q C(m+q, m)` when
`N - k = (m+1) q`, and `0` otherwise. -/
def term (N m i : ℕ) : ℤ :=
  if (m + 1) * i + m ≤ N ∧ (N - ((m + 1) * i + m)) % (m + 1) = 0 then
    (-1) ^ i * (binom m i : ℤ) *
      ((-1) ^ ((N - ((m + 1) * i + m)) / (m + 1)) *
        (binom (m + (N - ((m + 1) * i + m)) / (m + 1)) m : ℤ))
  else 0

/-- `term N m i` vanishes unless `m + 1` divides `N + 1`. -/
theorem term_eq_zero {N m : ℕ} (h : (N + 1) % (m + 1) ≠ 0) (i : ℕ) : term N m i = 0 := by
  unfold term
  rw [if_neg]
  rintro ⟨h1, h2⟩
  apply h
  apply Nat.mod_eq_zero_of_dvd
  have h3 : N + 1 = (N - ((m + 1) * i + m)) + (m + 1) * (i + 1) := by
    rw [mul_add, mul_one]; omega
  rw [h3]
  exact dvd_add (Nat.dvd_of_mod_eq_zero h2) (dvd_mul_right _ _)

/-- The coefficient of `x^N` in the g.f., by the explicit formula (see `coeff_A`). Only the
summands with `m + 1 ∣ N + 1` contribute (`term_eq_zero`); the guard only speeds up evaluation. -/
def coeffA (N : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (N + 1),
    if (N + 1) % (m + 1) = 0 then ∑ i ∈ Finset.range (m + 1), term N m i else 0

/-- A323695: `a N` is the coefficient of `x^N` in
`∑_{m ≥ 0} x^m * (1 - x^(m+1))^m / (1 + x^(m+1))^(m+1)` (see `a_eq_coeff`). -/
def a (N : ℕ) : ℤ := coeffA N

/-- `(1 + X^b)^(d+1) * ∑_j (-1)^j C(d+j, d) X^(b j) = 1`. -/
theorem one_add_X_pow_pow_mul (b d : ℕ) (hb : b ≠ 0) :
    (1 + X ^ b : PowerSeries ℤ) ^ (d + 1) *
      expand b hb (evalNegHom (mk fun j => (Nat.choose (d + j) d : ℤ))) = 1 := by
  have h := congrArg (fun f => expand b hb (evalNegHom f))
    (mk_add_choose_mul_one_sub_pow_eq_one (S := ℤ) d)
  simp only [map_mul, map_pow, map_sub, map_one, evalNegHom_X, sub_neg_eq_add] at h
  rw [mul_comm]
  simpa [add_comm] using h

theorem invOfUnit_one_add_X_pow_pow (b d : ℕ) (hb : b ≠ 0) :
    invOfUnit ((1 + X ^ b : PowerSeries ℤ) ^ (d + 1)) 1 =
      expand b hb (evalNegHom (mk fun j => (Nat.choose (d + j) d : ℤ))) := by
  set φ : PowerSeries ℤ := (1 + X ^ b) ^ (d + 1)
  set E := expand b hb (evalNegHom (mk fun j => (Nat.choose (d + j) d : ℤ)))
  have h1 : φ * invOfUnit φ 1 = 1 :=
    mul_invOfUnit _ _ (constantCoeff_one_add_X_pow_pow _ _ hb)
  have h2 : φ * E = 1 := one_add_X_pow_pow_mul b d hb
  calc invOfUnit φ 1 = (E * φ) * invOfUnit φ 1 := by rw [mul_comm E, h2, one_mul]
    _ = E := by rw [mul_assoc, h1, mul_one]

theorem coeff_E (b d r : ℕ) (hb : b ≠ 0) :
    coeff r (expand b hb (evalNegHom (mk fun j => (Nat.choose (d + j) d : ℤ)))) =
      if r % b = 0 then (-1) ^ (r / b) * (Nat.choose (d + r / b) d : ℤ) else 0 := by
  rw [coeff_expand]
  by_cases h : b ∣ r
  · rw [if_pos h, if_pos (Nat.mod_eq_zero_of_dvd h)]
    simp [evalNegHom]
  · rw [if_neg h, if_neg (fun h' => h (Nat.dvd_of_mod_eq_zero h'))]

/-- The explicit formula for the coefficients of a summand. -/
theorem coeff_summand (N m : ℕ) :
    coeff N (summand m) = ∑ i ∈ Finset.range (m + 1), term N m i := by
  rw [summand, invOfUnit_one_add_X_pow_pow _ _ (by omega), sub_eq_neg_add, add_pow,
    Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hE : ∀ E : PowerSeries ℤ,
      X ^ m * ((-X ^ (m + 1)) ^ i * 1 ^ (m - i) * ((m.choose i : ℕ) : PowerSeries ℤ)) * E =
        C ((-1) ^ i * (m.choose i : ℤ)) * (X ^ ((m + 1) * i + m) * E) := by
    intro E
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [hE, coeff_C_mul, coeff_X_pow_mul', coeff_E _ _ _ (by omega), term]
  simp only [binom_eq_choose]
  split_ifs with h1 h2 h3 h3 h3
  · ring
  · exact absurd ⟨h1, h2⟩ h3
  · exact absurd h3.2 h2
  · rw [mul_zero]
  · exact absurd h3.1 h1
  · rw [mul_zero]

/-- The coefficients of the g.f. are given by `coeffA`. -/
theorem coeff_A (N : ℕ) : coeff N A = coeffA N := by
  rw [A, coeff_mk, coeffA]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_summand]
  split_ifs with h
  · rfl
  · exact Finset.sum_eq_zero fun i _ => term_eq_zero h i

/-- `a N` is the coefficient of `x^N` in the g.f. `A`, as in OEIS. -/
theorem a_eq_coeff (N : ℕ) : a N = coeff N A := by
  rw [coeff_A, a]

/-- The definition reproduces the first terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 121).map (fun i => a (i + 0)) =
    [1, 0, 2, -3, 2, 0, 2, -14, 15, 0, 2, -22, 2, 0, 84, -93, 2, 0, 2, -38, 172, 0, 2, -508, 323,
      0, 292, -54, 2, 0, 2, -1212, 444, 0, 2580, -1753, 2, 0, 628, -2396, 2, 0, 2, -86, 8142, 0, 2,
      -18554, 8991, 0, 1092, -102, 2, 0, 16724, -6716, 1372, 0, 2, -44844, 2, 0, 81846, -58747,
      33284, 0, 2, -134, 2028, 0, 2, -127882, 2, 0, 62326, -150, 268492, 0, 2, -468282, 268541, 0,
      2, -249196, 100100, 0, 3252, -26748, 2, 0, 738612, -182, 3724, 0, 157780, -2117880, 2, 0,
      2517158, -1462761, 2, 0, 2, -44508, 2003576, 0, 2, -897068, 2, 0, 5332, -4736762, 2, 0,
      344084, -230, 9352622, 0, 3769924, -15721720, 8097455] := by
  decide +kernel

/-- Conjecture (Hanna, A323695): odd terms `a n` occur only at `n = k * (k + 2)`, `k ≥ 0`. -/
def statement : Prop :=
  ∀ n : ℕ, Odd (a n) → ∃ k : ℕ, n = k * (k + 2)

end Math0.Statements.A323695
