/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A120069
import Math0.Audit

/-!
# Denominators of `∑ C(k)/4^(k-1)`: Groux's and Staunton's conjectures (A120069)

We prove both conjectures for every `n ≥ 1`.

* Closed form: `r(m+1) = 4 - (2m+3) C(m+1)/4^m`, by induction from
  `(k+2) C(k+1) = 2(2k+1) C(k)`.
* Write `C(m+1) = 2^v u` with `u` odd. Since `C(m+1) ≤ 4^m` we get `v ≤ 2m`, so
  `C(m+1)/4^m = u/2^(2m-v)` and its denominator is `2^(2m-v)` (Groux's side).
* `r(m+1) = 4 - (2m+3)u/2^(2m-v)` and `(2m+3)u` is odd, so `a(m+1) = 2^(2m-v)`.
* `w(n) = (2n+1)/(n+1) c(2n) = (2n+1) C(n)/4^n`, so `2^e w(m+1)` is an integer exactly when
  `e ≥ 2m+2-v`; thus `A283208(m+1) = 2m+2-v` and `2^(A283208(m+1)-2) = 2^(2m-v) = a(m+1)`
  (Staunton's side).
-/

namespace Math0.Frontier.A120069
open Math0.Statements.A120069

/-- Closed form of the partial sums: `r(m+1) = 4 - (2m+3) C(m+1)/4^m`. -/
private theorem r_succ_closed (m : ℕ) :
    r (m + 1) = 4 - (2 * m + 3) * (catalan (m + 1) : ℚ) / 4 ^ m := by
  induction m with
  | zero => norm_num [r, catalan_one]
  | succ m ih =>
    have hs : r (m + 1 + 1) = r (m + 1) + (catalan (m + 1 + 1) : ℚ) / 4 ^ (m + 1) := by
      rw [r, r, Finset.sum_Icc_succ_top (by omega)]
      congr 1
      rw [show 2 * (m + 1 + 1 - 1) = 2 * (m + 1) by omega, pow_mul]
      norm_num
    have hc : ((m + 1 + 2 : ℕ) : ℚ) * catalan (m + 1 + 1)
        = (2 * (2 * (m + 1) + 1) : ℕ) * catalan (m + 1) := by
      exact_mod_cast succ_succ_mul_catalan (m + 1)
    rw [hs, ih]
    push_cast at hc ⊢
    rw [pow_succ]
    field_simp
    linear_combination (2 : ℚ) * hc

/-- `C(m+1) ≤ 4^m`. -/
private theorem catalan_succ_le (m : ℕ) : catalan (m + 1) ≤ 4 ^ m := by
  induction m with
  | zero => simp [catalan_one]
  | succ m ih =>
    have h := succ_succ_mul_catalan (m + 1)
    have : (m + 1 + 2) * catalan (m + 1 + 1) ≤ (m + 1 + 2) * 4 ^ (m + 1) := by
      rw [h, pow_succ]
      nlinarith
    exact Nat.le_of_mul_le_mul_left this (by omega)

/-- Catalan numbers are nonzero. -/
private theorem catalan_ne_zero' (n : ℕ) : catalan n ≠ 0 := by
  intro h
  have := succ_mul_catalan_eq_centralBinom n
  rw [h, mul_zero] at this
  exact (Nat.centralBinom_pos n).ne' this.symm

/-- An odd number over `2^k` has denominator `2^k`. -/
private theorem den_odd_div_two_pow {u : ℕ} (k : ℕ) (hu : Odd u) :
    ((u : ℚ) / 2 ^ k).den = 2 ^ k := by
  have h := Rat.den_div_eq_of_coprime (a := (u : ℤ)) (b := (2 ^ k : ℤ)) (by positivity) (by
    simp only [Int.natAbs_natCast, Int.natAbs_pow]
    exact Nat.Coprime.pow_right _ hu.coprime_two_right)
  push_cast at h
  exact_mod_cast h

/-- `w n = (2n+1) C(n)/4^n`. -/
private theorem w_eq (n : ℕ) : w n = (2 * n + 1) * (catalan n : ℚ) / 4 ^ n := by
  have h1 := four_pow_mul_vietoris n
  have h2 : ((n + 1 : ℕ) : ℚ) * catalan n = n.centralBinom := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  have hv : vietoris n = (n.centralBinom : ℚ) / 4 ^ n := by
    rw [← h1]
    field_simp
  rw [w, hv, ← h2]
  push_cast
  field_simp

/-- Both conjectures (Groux 2010, Staunton 2026) hold for every `n ≥ 1`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨v, u, hu, hCu⟩ := Nat.exists_eq_two_pow_mul_odd (catalan_ne_zero' (m + 1))
  have hv : v ≤ 2 * m := by
    have h1 : 2 ^ v ≤ catalan (m + 1) := by
      rw [hCu]
      exact Nat.le_mul_of_pos_right _ hu.pos
    have h2 := h1.trans (catalan_succ_le m)
    rw [show (4 : ℕ) ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num] at h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have h4 : (4 : ℚ) ^ m = 2 ^ (2 * m - v) * 2 ^ v := by
    rw [← pow_add, Nat.sub_add_cancel hv, pow_mul]
    norm_num
  have hkey : (catalan (m + 1) : ℚ) / 4 ^ m = (u : ℚ) / 2 ^ (2 * m - v) := by
    rw [hCu, h4]
    push_cast
    field_simp
  have hodd : Odd ((2 * m + 3) * u) := by
    refine Odd.mul ?_ hu
    exact ⟨m + 1, by ring⟩
  have hr : r (m + 1) = 4 - (((2 * m + 3) * u : ℕ) : ℚ) / 2 ^ (2 * m - v) := by
    rw [r_succ_closed, mul_div_assoc, hkey]
    push_cast
    ring
  have ha : a (m + 1) = 2 ^ (2 * m - v) := by
    rw [a, hr, Rat.ofNat_sub_den, den_odd_div_two_pow _ hodd]
  have hw : w (m + 1) = (((2 * m + 3) * u : ℕ) : ℚ) / 2 ^ (2 * m - v + 2) := by
    rw [w_eq, hCu, pow_succ, h4, pow_add]
    push_cast
    field_simp
    ring
  have hA : A283208 (m + 1) = 2 * m + 2 - v := by
    apply A283208_eq_of
    · refine ⟨(2 * m + 3) * u, ?_⟩
      rw [hw, show 2 * m + 2 - v = 2 * m - v + 2 by omega]
      field_simp
    · right
      rintro ⟨k, hk⟩
      rw [hw, show 2 * m + 2 - v - 1 = 2 * m - v + 1 by omega, pow_succ 2 (2 * m - v + 1)] at hk
      have h2 : (((2 * m + 3) * u : ℕ) : ℚ) = 2 * k := by
        rw [← hk]
        field_simp
      have h3 : (2 * m + 3) * u = 2 * k := by exact_mod_cast h2
      exact (Nat.not_even_iff_odd.mpr hodd) ⟨k, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [ha, show m + 1 - 1 = m by omega, hkey, den_odd_div_two_pow _ hu]
  · rw [ha, hA, show ((2 * m + 2 - v : ℕ) : ℤ) - 2 = ((2 * m - v : ℕ) : ℤ) by omega,
      zpow_natCast]
    push_cast
    rfl

end Math0.Frontier.A120069

#math0_settles Math0.Frontier.A120069.result Math0.Statements.A120069.statement
