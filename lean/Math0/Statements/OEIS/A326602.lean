/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A326602: parity of the coefficients of `∑ (x^(2n-1)+1)^n x^n / (1+x^(2n+1))^(n+1)`

Source: https://oeis.org/A326602, _Paul D. Hanna_, Aug 08 2019. Verbatim:
> a(n) is odd iff n is square (conjecture).

The entry's definition (offset 0): "G.f.: Sum_{n>=0} (x^(2*n-1) + 1)^n * x^n /
(1 + x^(2*n+1))^(n+1), an even function." and "G.f. A(x) = Sum_{n>=0} a(n)*x^(2*n)", i.e.
`a(n)` is the coefficient of `x^(2n)` in this power series (whose odd coefficients vanish).

## Encoding

* `summand n : ℤ⟦X⟧` is `(X^(2n-1) + 1)^n * X^n * ((1 + X^(2n+1))^(n+1))⁻¹`, the inverse being
  `PowerSeries.invOfUnit _ 1` (the factor has constant coefficient `1`); `summand_spec` records
  the defining identity `(1 + X^(2n+1))^(n+1) * summand n = (X^(2n-1) + 1)^n * X^n`.
  For `n = 0` the OEIS factor `(x^(-1) + 1)^0` is `1`; in `ℕ` the exponent `2*0-1` truncates to
  `0`, giving `(X^0 + 1)^0 = 1` as well.
* `summand n` is divisible by `X^n` (`coeff_summand_of_lt`), so the series converges
  `X`-adically. `A` is its sum, defined coefficientwise as the finite sum over `n ≤ N`, and
  `hasSum_summand` proves `HasSum summand A` in the product (coefficientwise) topology on `ℤ⟦X⟧`.
* `a n` is defined by an explicit finite formula, `coeffA (2 * n)`, obtained by expanding
  `(X^(2m-1) + 1)^m` with the binomial theorem and `(1 + X^(2m+1))^(-(m+1))` as
  `∑_j (-1)^j C(m+j, j) X^((2m+1) j)`. The theorem `a_eq_coeff` proves (in Lean) that
  `a n = coeff (2 * n) A`, so `a` is exactly the OEIS definition; the explicit formula only
  serves to make `a` computable for the kernel-checked data.
* The conjecture is stated for every `n ≥ 0` (offset 0), with "square" meaning `n = k * k` for
  some `k : ℕ` (`IsSquare n`), so `n = 0` counts as a square.
-/

namespace Math0.Statements.A326602

open PowerSeries

/-! ### The generating function -/

/-- The `n`-th summand `(x^(2n-1) + 1)^n * x^n / (1 + x^(2n+1))^(n+1)` of the g.f., in `ℤ⟦X⟧`.
(For `n = 0` the truncated exponent `2*0-1 = 0` is harmless: the factor is raised to the
power `0`.) -/
noncomputable def summand (n : ℕ) : PowerSeries ℤ :=
  (X ^ (2 * n - 1) + 1) ^ n * X ^ n * invOfUnit ((1 + X ^ (2 * n + 1)) ^ (n + 1)) 1

theorem constantCoeff_one_add_X_pow_pow (b d : ℕ) (hb : b ≠ 0) :
    constantCoeff ((1 + X ^ b : PowerSeries ℤ) ^ d) = ((1 : ℤˣ) : ℤ) := by
  simp [map_pow, zero_pow hb]

/-- `summand n` is the quotient `(x^(2n-1) + 1)^n * x^n / (1 + x^(2n+1))^(n+1)`. -/
theorem summand_spec (n : ℕ) :
    (1 + X ^ (2 * n + 1)) ^ (n + 1) * summand n = (X ^ (2 * n - 1) + 1) ^ n * X ^ n := by
  rw [summand, mul_comm, mul_assoc, invOfUnit_mul _ _
    (constantCoeff_one_add_X_pow_pow _ _ (by omega)), mul_one]

/-- `summand n` is divisible by `X ^ n`. -/
theorem coeff_summand_of_lt {N n : ℕ} (h : N < n) : coeff N (summand n) = 0 := by
  rw [summand, mul_comm ((X ^ (2 * n - 1) + 1) ^ n) (X ^ n), mul_assoc, coeff_X_pow_mul',
    if_neg (by omega)]

/-- The generating function `A(x) = ∑_{n ≥ 0} summand n`, defined coefficientwise
(the coefficient of `x^N` only involves the summands with `n ≤ N`, see `coeff_summand_of_lt`). -/
noncomputable def A : PowerSeries ℤ :=
  mk fun N => ∑ n ∈ Finset.range (N + 1), coeff N (summand n)

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

/-- Contribution of `C(m,i) X^((2m-1) i)` (from `(X^(2m-1)+1)^m`) to the coefficient of `x^N`
in `summand m`: with `k = (2m-1) i + m`, it is `C(m,i) (-1)^q C(m+q, q)` when
`N - k = (2m+1) q`, and `0` otherwise. -/
def term (N m i : ℕ) : ℤ :=
  if (2 * m - 1) * i + m ≤ N ∧ (N - ((2 * m - 1) * i + m)) % (2 * m + 1) = 0 then
    (-1) ^ ((N - ((2 * m - 1) * i + m)) / (2 * m + 1)) *
      ((binom m i * binom (m + (N - ((2 * m - 1) * i + m)) / (2 * m + 1))
        ((N - ((2 * m - 1) * i + m)) / (2 * m + 1)) : ℕ) : ℤ)
  else 0

/-- `term N m i = 0` unless `i ≤ iBound N m` (see `term_eq_zero`); this only speeds up the
computation of `coeffA`. -/
def iBound (N m : ℕ) : ℕ := min m ((N - m) / (2 * m - 1))

/-- The coefficient of `x^N` in the g.f., by an explicit formula (see `coeff_A`):
`∑_{m ≤ N} ∑_{i ≤ iBound N m} term N m i`. -/
def coeffA (N : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (iBound N m + 1), term N m i

theorem term_eq_zero {N m i : ℕ} (him : i ≤ m) (hi : iBound N m < i) : term N m i = 0 := by
  rw [term, if_neg]
  rintro ⟨h, -⟩
  rw [iBound] at hi
  generalize hx : (N - m) / (2 * m - 1) = x at hi
  have hm : 0 < 2 * m - 1 := by omega
  have h1 : x < i := by omega
  rw [← hx, Nat.div_lt_iff_lt_mul hm] at h1
  rw [mul_comm] at h1
  generalize (2 * m - 1) * i = y at h h1
  omega

theorem coeffA_eq (N : ℕ) :
    coeffA N = ∑ m ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (m + 1), term N m i := by
  refine Finset.sum_congr rfl fun m _ => Finset.sum_subset ?_ fun i him hi => ?_
  · intro i
    simp only [Finset.mem_range, iBound]
    omega
  · simp only [Finset.mem_range] at him hi
    exact term_eq_zero (by omega) (by omega)

/-- A326602: `a n` is the coefficient of `x^(2n)` in
`∑_{m ≥ 0} (x^(2m-1) + 1)^m * x^m / (1 + x^(2m+1))^(m+1)` (see `a_eq_coeff`). -/
def a (n : ℕ) : ℤ := coeffA (2 * n)

/-- `(1 + X^b)^(d+1) * ∑_j (-1)^j C(d+j, d) X^(b j) = 1` (from `1/(1-X)^(d+1)` by `X ↦ -X^b`). -/
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
      if r % b = 0 then (-1) ^ (r / b) * (Nat.choose (d + r / b) (r / b) : ℤ) else 0 := by
  rw [coeff_expand]
  by_cases h : b ∣ r
  · rw [if_pos h, if_pos (Nat.mod_eq_zero_of_dvd h)]
    simp [evalNegHom]
    rw [Nat.choose_symm_add]
  · rw [if_neg h, if_neg (fun h' => h (Nat.dvd_of_mod_eq_zero h'))]

/-- The explicit formula for the coefficients of a summand. -/
theorem coeff_summand (N m : ℕ) :
    coeff N (summand m) = ∑ i ∈ Finset.range (m + 1), term N m i := by
  rw [summand, invOfUnit_one_add_X_pow_pow _ _ (by omega), add_pow, Finset.sum_mul,
    Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, ← map_natCast (C (R := ℤ)), ← pow_mul,
    show ∀ f g h e : PowerSeries ℤ, f * g * h * e = g * (f * h * e) from
      fun f g h e => by ring,
    coeff_C_mul, ← pow_add, coeff_X_pow_mul', coeff_E _ _ _ (by omega), term]
  simp only [binom_eq_choose]
  split_ifs with h1 h2 h3 h3 h3
  · push_cast; ring
  · exact absurd ⟨h1, h2⟩ h3
  · exact absurd h3.2 h2
  · rw [mul_zero]
  · exact absurd h3.1 h1
  · rw [mul_zero]

/-- The coefficients of the g.f. are given by `coeffA`. -/
theorem coeff_A (N : ℕ) : coeff N A = coeffA N := by
  rw [A, coeff_mk, coeffA_eq]
  exact Finset.sum_congr rfl fun m _ => coeff_summand N m

/-- `a n` is the coefficient of `x^(2n)` in the g.f. `A`, as in OEIS. -/
theorem a_eq_coeff (n : ℕ) : a n = coeff (2 * n) A := by
  rw [coeff_A, a]

/-- The definition reproduces the first terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 68).map (fun i => a (i + 0)) =
    [1, 3, 0, 2, 9, -12, 8, 12, -10, 15, -36, 46, -18, 20, 12, -82, 101, -162, 302, -168, -100,
      92, 32, 40, -244, 351, -452, 1052, -1528, 1144, -394, -494, 948, -438, 370, -1474, 2805,
      -2860, 2560, -4762, 6554, -4104, 926, 480, -1820, 3074, -2546, 1072, -2518, 9745, -17810,
      21300, -28982, 37560, -26380, 6162, 686, 2, 2364, -12342, 30356, -39584, 19448, 7562, 9491,
      -63824, 99128, -116668] := by
  decide +kernel

/-- Sanity check of "an even function": the first odd-index coefficients of the g.f. vanish
(kernel-checked). -/
theorem coeffA_odd_data :
    (List.range 40).map (fun i => coeffA (2 * i + 1)) = List.replicate 40 0 := by
  decide +kernel

/-- Conjecture (Hanna, A326602): for every `n ≥ 0`, `a n` (the coefficient of `x^(2n)` in the
g.f., `a_eq_coeff`) is odd iff `n` is a square. -/
def statement : Prop :=
  ∀ n : ℕ, Odd (a n) ↔ IsSquare n

end Math0.Statements.A326602
