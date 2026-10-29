/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A323695
import Math0.Audit

/-!
# Odd terms of A323695 occur only at `n = k*(k+2)`

We prove Hanna's conjecture: if `a n` is odd then `n + 1` is a perfect square, i.e.
`n = k * (k + 2)`.

Idea: reduce mod 2. In `(ZMod 2)⟦X⟧` we have `1 - X^(m+1) = 1 + X^(m+1)`, so the `m`-th summand
`X^m (1 - X^(m+1))^m / (1 + X^(m+1))^(m+1)` becomes `X^m / (1 + X^(m+1)) = ∑_j X^((m+1)(j+1) - 1)`
(we use `-1 = 1` once more on the coefficients of `1/(1 + X^(m+1))`). Its coefficient of `x^N`
is `1` exactly when `m + 1 ∣ N + 1`, so `a N ≡ #{divisors of N + 1} (mod 2)`. If `N + 1` is not
a square, the involution `d ↦ (N + 1)/d` on the divisors has no fixed point, so the number of
divisors is even and `a N` is even.
-/

namespace Math0.Frontier.A323695
open Math0.Statements.A323695 PowerSeries

/-- In `(ZMod 2)⟦X⟧`, `-1 = 1`. -/
private theorem neg_one_eq : (-1 : PowerSeries (ZMod 2)) = 1 := by
  ext n
  rw [map_neg, coeff_one]
  split_ifs <;> decide

/-- `E b hb = ∑_j (-1)^j X^(b j)`, the inverse of `1 + X^b` in `ℤ⟦X⟧` (the case `d = 0` of
`one_add_X_pow_pow_mul` in the statement file). -/
private noncomputable def E (b : ℕ) (hb : b ≠ 0) : PowerSeries ℤ :=
  expand b hb (evalNegHom (mk fun j => (Nat.choose (0 + j) 0 : ℤ)))

/-- Mod 2, `summand m = X^m / (1 + X^(m+1)) = X^m * E (m+1)`: since `-1 = 1` mod 2, the factor
`(1 - X^(m+1))^m` cancels against `(1 + X^(m+1))^(m+1)` up to one factor. -/
private theorem map_summand (m : ℕ) :
    map (Int.castRingHom (ZMod 2)) (summand m) =
      X ^ m * map (Int.castRingHom (ZMod 2)) (E (m + 1) (by omega)) := by
  have h1 := congrArg (map (Int.castRingHom (ZMod 2))) (summand_spec m)
  have h2 := congrArg (map (Int.castRingHom (ZMod 2))) (one_add_X_pow_pow_mul (m + 1) 0 (by omega))
  rw [← E] at h2
  simp only [map_mul, map_pow, map_add, map_sub, map_one, map_X, zero_add, pow_one] at h1 h2
  rw [sub_eq_add_neg, ← neg_one_mul (X ^ (m + 1)), neg_one_eq, one_mul] at h1
  generalize map (Int.castRingHom (ZMod 2)) (summand m) = s at h1 ⊢
  generalize map (Int.castRingHom (ZMod 2)) (E (m + 1) (by omega)) = e at h2 ⊢
  generalize (1 + X ^ (m + 1) : PowerSeries (ZMod 2)) = u at h1 h2
  calc s = (u * e) ^ (m + 1) * s := by rw [h2, one_pow, one_mul]
    _ = e ^ (m + 1) * (u ^ (m + 1) * s) := by ring
    _ = e ^ (m + 1) * (X ^ m * u ^ m) := by rw [h1]
    _ = X ^ m * e * (u * e) ^ m := by ring
    _ = X ^ m * e := by rw [h2, one_pow, mul_one]

/-- Mod 2, the coefficient of `x^N` in `summand m` is `1` if `m + 1 ∣ N + 1` (and `m ≤ N`),
and `0` otherwise. -/
private theorem coeff_map_summand (N m : ℕ) :
    coeff N (map (Int.castRingHom (ZMod 2)) (summand m)) =
      if m + 1 ∣ N + 1 ∧ m ≤ N then 1 else 0 := by
  rw [map_summand, coeff_X_pow_mul', E]
  split_ifs with h1 h2 h2
  · rw [coeff_map, coeff_E _ _ _ (by omega)]
    rw [if_pos]
    · simp
    · apply Nat.mod_eq_zero_of_dvd
      have h3 : N - m = (N + 1) - (m + 1) := by omega
      rw [h3]
      exact Nat.dvd_sub h2.1 (dvd_refl _)
  · rw [coeff_map, coeff_E _ _ _ (by omega), if_neg]
    · rfl
    · intro h3
      apply h2
      refine ⟨?_, h1⟩
      have h4 : N + 1 = (N - m) + (m + 1) := by omega
      rw [h4]
      exact dvd_add (Nat.dvd_of_mod_eq_zero h3) (dvd_refl _)
  · exact absurd h2.2 h1
  · rfl

/-- Mod 2, `a N` counts the `m ≤ N` with `m + 1 ∣ N + 1`. -/
private theorem cast_a (N : ℕ) :
    ((a N : ℤ) : ZMod 2) =
      ∑ m ∈ Finset.range (N + 1), if m + 1 ∣ N + 1 ∧ m ≤ N then (1 : ZMod 2) else 0 := by
  rw [a_eq_coeff, A, coeff_mk, Int.cast_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← coeff_map_summand, coeff_map]
  rfl

/-- If `N + 1` is not a square, the number of divisors of `N + 1` is even. -/
private theorem sum_eq_zero (N : ℕ) (hN : ∀ k : ℕ, N ≠ k * (k + 2)) :
    ∑ m ∈ Finset.range (N + 1), (if m + 1 ∣ N + 1 ∧ m ≤ N then (1 : ZMod 2) else 0) = 0 := by
  rw [← Finset.sum_filter]
  have key : ∀ m ∈ Finset.filter (fun m => m + 1 ∣ N + 1 ∧ m ≤ N) (Finset.range (N + 1)),
      ∃ c, N + 1 = (m + 1) * c ∧ 1 ≤ c ∧ (N + 1) / (m + 1) = c ∧ m ≤ N := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨c, hc⟩ := hm.2.1
    refine ⟨c, hc, ?_, ?_, hm.2.2⟩
    · rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, mul_zero] at hc; omega
      · exact h
    · rw [hc, Nat.mul_div_cancel_left _ (by omega)]
  refine Finset.sum_involution (fun m _ => (N + 1) / (m + 1) - 1) ?_ ?_ ?_ ?_
  · intro _ _
    decide
  · intro m hm _ heq
    obtain ⟨c, hc, hc1, hdiv, _⟩ := key m hm
    rw [hdiv] at heq
    apply hN m
    have hcm : c = m + 1 := by omega
    rw [hcm] at hc
    have : N + 1 = m * (m + 2) + 1 := by rw [hc]; ring
    omega
  · intro m hm
    obtain ⟨c, hc, hc1, hdiv, hmN⟩ := key m hm
    rw [hdiv, Finset.mem_filter, Finset.mem_range]
    have hcdvd : c ∣ N + 1 := ⟨m + 1, by rw [hc, mul_comm]⟩
    have hcle : c ≤ N + 1 := Nat.le_of_dvd (by omega) hcdvd
    refine ⟨by omega, ?_, by omega⟩
    rw [Nat.sub_add_cancel hc1]
    exact hcdvd
  · intro m hm
    obtain ⟨c, hc, hc1, hdiv, hmN⟩ := key m hm
    show (N + 1) / ((N + 1) / (m + 1) - 1 + 1) - 1 = m
    rw [hdiv, Nat.sub_add_cancel hc1, hc, Nat.mul_div_cancel _ (by omega)]
    omega

/-- Hanna's conjecture for A323695: odd terms `a n` occur only at `n = k * (k + 2)`. -/
theorem result : statement := by
  intro n hodd
  by_contra hne'
  have hne : ∀ k : ℕ, n ≠ k * (k + 2) := fun k hk => hne' ⟨k, hk⟩
  have h1 : ((a n : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hodd
  rw [cast_a, sum_eq_zero n hne] at h1
  exact absurd h1 (by decide)

end Math0.Frontier.A323695

#math0_settles Math0.Frontier.A323695.result Math0.Statements.A323695.statement
