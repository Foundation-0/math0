/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A091817
import Math0.Audit

/-!
# Quet's integrality conjecture for A091817 holds

For every prime `p ≥ 3`, writing `H(p-3) = N/D` in lowest terms, `p ∣ 2N - 3D`; hence every
term `a n = (2N - 3D)/p` of A091817 is an integer.

Idea: work in `ZMod p`. Put `S m = ∑_{k=1}^{m} k⁻¹ ∈ ZMod p`. For `m < p` the rational
`H m * m!` is an integer `A` with `A ≡ m! * S m (mod p)` (induction on `m`, using that
`1, …, m` are units mod `p`). Since `x ↦ x⁻¹` permutes `ZMod p`, `S (p-1) = ∑_x x⁻¹ = ∑_x x = 0`
(for `p` odd), and removing the last two terms `(-2)⁻¹ + (-1)⁻¹ = -3/2` gives
`2 * S (p-3) = 3`. From `N * m! = A * D` and `m! ≢ 0 (mod p)` we get `N ≡ S (p-3) * D`, so
`2N - 3D ≡ (2 S (p-3) - 3) D = 0 (mod p)`.
-/

namespace Math0.Frontier.A091817
open Math0.Statements.A091817

/-- The partial harmonic sum `∑_{k=1}^{m} k⁻¹` computed in `ZMod p`. -/
private def invSum (p m : ℕ) : ZMod p := ∑ k ∈ Finset.range m, ((k : ZMod p) + 1)⁻¹

/-- Recursion for the harmonic numbers: `H (m+1) = H m + 1/(m+1)`. -/
private theorem H_succ (m : ℕ) : H (m + 1) = H m + 1 / ((m : ℚ) + 1) := by
  simp [H, List.range_succ]

/-- For `m < p`, `H m * m!` is an integer `A`, and `A ≡ m! * invSum p m (mod p)`. -/
private theorem key (p : ℕ) [Fact p.Prime] : ∀ m, m < p → ∃ a : ℤ,
    H m * (m.factorial : ℚ) = a ∧ (a : ZMod p) = (m.factorial : ZMod p) * invSum p m := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, by simp [H], by simp [invSum]⟩
  | succ m ih =>
    intro hm
    obtain ⟨a, h1, h2⟩ := ih (by omega)
    refine ⟨a * (m + 1) + m.factorial, ?_, ?_⟩
    · rw [H_succ, Nat.factorial_succ]
      push_cast
      rw [← h1]
      field_simp
    · have hne : ((m : ZMod p) + 1) ≠ 0 := by
        have : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hd
          have := Nat.le_of_dvd (by omega) hd
          omega
        exact_mod_cast this
      rw [invSum, Finset.sum_range_succ, ← invSum, Nat.factorial_succ]
      push_cast
      rw [h2]
      have : ((m : ZMod p) + 1) * (m.factorial : ZMod p) * ((m : ZMod p) + 1)⁻¹
          = (m.factorial : ZMod p) := by
        rw [mul_comm ((m : ZMod p) + 1), mul_assoc, mul_inv_cancel₀ hne, mul_one]
      linear_combination (-1 : ZMod p) * this

/-- For an odd prime `p`, `∑_{k=1}^{p} k⁻¹ = 0` in `ZMod p` (the term `k = p` is `0⁻¹ = 0`):
inversion permutes `ZMod p`, and `∑_x x = 0`. -/
private theorem invSum_self (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) : invSum p p = 0 := by
  have hsum : ∑ x : ZMod p, x⁻¹ = 0 := by
    have e : ∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x :=
      Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x)
    rw [e]
    have := FiniteField.sum_pow_lt_card_sub_one (ZMod p) 1 (by
      rw [ZMod.card]; have := hp.out.two_le; omega)
    simpa using this
  have hrange : ∑ k ∈ Finset.range p, ((k : ZMod p))⁻¹ = ∑ x : ZMod p, x⁻¹ := by
    apply Finset.sum_nbij' (fun k : ℕ => (k : ZMod p)) (fun x : ZMod p => x.val)
    · intro a _; exact Finset.mem_univ _
    · intro x _; rw [Finset.mem_range]; exact ZMod.val_lt x
    · intro a ha; rw [Finset.mem_range] at ha; exact ZMod.val_cast_of_lt ha
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro a _; rfl
  rw [← hsum, ← hrange, invSum]
  have := Finset.sum_range_succ' (fun k => ((k : ZMod p))⁻¹) p
  rw [Finset.sum_range_succ] at this
  simp only [ZMod.natCast_self, inv_zero, add_zero, Nat.cast_zero] at this
  rw [this]
  simp

/-- For an odd prime `p`, `2 * ∑_{k=1}^{p-3} k⁻¹ = 3` in `ZMod p`. -/
private theorem invSum_val (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) :
    2 * invSum p (p - 3) = 3 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by have := hp.out.two_le; omega⟩
  have h0 := invSum_self (q + 3) h2
  rw [Nat.add_sub_cancel]
  rw [invSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ← invSum] at h0
  have hq : ((q : ZMod (q + 3))) = -3 := by
    have : (((q + 3 : ℕ)) : ZMod (q + 3)) = 0 := ZMod.natCast_self _
    push_cast at this; linear_combination this
  have htwo : (2 : ZMod (q + 3)) ≠ 0 := by
    have : ((2 : ℕ) : ZMod (q + 3)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    exact_mod_cast this
  have k1 : ((q : ZMod (q + 3)) + 1)⁻¹ = -2⁻¹ := by
    rw [hq, show (-3 : ZMod (q + 3)) + 1 = -2 by ring, inv_neg]
  have k2 : (((q + 1 : ℕ) : ZMod (q + 3)) + 1)⁻¹ = -1 := by
    push_cast; rw [hq, show (-3 : ZMod (q + 3)) + 1 + 1 = -1 by ring, inv_neg, inv_one]
  have k3 : (((q + 2 : ℕ) : ZMod (q + 3)) + 1)⁻¹ = 0 := by
    push_cast; rw [hq, show (-3 : ZMod (q + 3)) + 2 + 1 = 0 by ring, inv_zero]
  rw [k1, k2, k3] at h0
  have : (2 : ZMod (q + 3)) * 2⁻¹ = 1 := mul_inv_cancel₀ htwo
  linear_combination 2 * h0 + this

/-- Quet's conjecture (A091817): for every `n ≥ 1`, with `p` the `(n+1)`-th prime and
`H(p-3) = N/D` in lowest terms, `(2N - 3D)/p` is an integer. -/
theorem result : statement := by
  intro n hn
  have hp : (primeAt n).Prime := by rw [primeAt_eq_nth]; exact Nat.prime_nth_prime n
  have hp3 : 3 ≤ primeAt n := by
    rw [primeAt_eq_nth]
    have := Nat.nth_strictMono (p := Nat.Prime) Nat.infinite_setOfPred_prime (show 0 < n by omega)
    rw [Nat.nth_prime_zero_eq_two] at this
    omega
  show ∃ z : ℤ, term (primeAt n) = z
  generalize primeAt n = p at hp hp3
  have := Fact.mk hp
  obtain ⟨A, h1, h2⟩ := key p (p - 3) (by omega)
  have hND : (H (p - 3)).num * ((p - 3).factorial : ℤ) = A * (H (p - 3)).den := by
    have : ((H (p - 3)).num : ℚ) * (p - 3).factorial = A * (H (p - 3)).den := by
      rw [← h1, ← Rat.mul_den_eq_num]; ring
    exact_mod_cast this
  have hfac : ((p - 3).factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, hp.dvd_factorial]; omega
  have hz : ((2 * (H (p - 3)).num - 3 * ((H (p - 3)).den : ℤ) : ℤ) : ZMod p) = 0 := by
    have := congrArg (Int.cast : ℤ → ZMod p) hND
    push_cast at this
    rw [h2] at this
    have hS := invSum_val p (by omega)
    have hN : ((H (p - 3)).num : ZMod p) = invSum p (p - 3) * (H (p - 3)).den := by
      apply mul_right_cancel₀ hfac; linear_combination this
    push_cast
    rw [hN]; linear_combination ((H (p - 3)).den : ZMod p) * hS
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  obtain ⟨z, hz⟩ := hz
  refine ⟨z, ?_⟩
  have hq : ((2 * (H (p - 3)).num - 3 * ((H (p - 3)).den : ℤ) : ℤ) : ℚ) = (p : ℚ) * z := by
    exact_mod_cast hz
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold term
  rw [div_eq_iff hp0]
  push_cast at hq ⊢
  linear_combination hq

end Math0.Frontier.A091817

#math0_settles Math0.Frontier.A091817.result Math0.Statements.A091817.statement
