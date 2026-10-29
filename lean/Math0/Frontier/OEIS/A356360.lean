/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A356360
import Math0.Audit

/-!
# A356360: the continued-fraction denominators are 1 or prime

We prove Mohammed Bouras's conjecture: the denominator `a n` of
`1/(2-3/(3-4/(...(n-1)-n/(n+1))))` is `1` or a prime for every `n ≥ 3`.

**Closed form.** Write `n = m + 2` and `H m x = step 2 (step 3 (… (step (m+1) x)))`, so that
`cf n = 1 / H m (n+1)`. With `S m = 0! + 1! + ⋯ + (m-1)!` and `M = (m+1)x - m(m+2)`,
induction on `m` (peeling off the innermost step, `H (m+1) x = H m (step (m+2) x)`) gives
`H m x = 2M / (S m · M + (m+2)·m!)` whenever `M > 0`; the positivity of `M` is inherited by the
inner argument because `M_m(step (m+2) x) = M_{m+1}(x) / x`. For `x = n + 1` we get `M = 2m+3 =
2n-1`, hence `cf n = (S m (2m+3) + (m+2) m!) / (2 (2m+3))`.

**Arithmetic.** For `m ≥ 2` both `S m` and `m!` are even, so `cf n = K / (2m+3)` with `K ∈ ℕ`.
If `2m+3` is prime, the denominator divides it, so it is `1` or `2m+3`. If `2m+3` is composite
and `m ≥ 4`, then `2m+3 ∣ m!` (write `2m+3 = p·b` with `p` its least prime factor, `3 ≤ p ≤ b ≤ m`;
if `p < b` then `p·b ∣ m!`, and if `p = b` then `p ≥ 5`, `2p ≤ m` and `p·2p ∣ m!`), so `2m+3`
divides `2K` and, being odd, divides `K`: the denominator is `1`. The cases `n = 3, 4, 5`
(`a = 5, 7, 3`) are checked by the kernel.
-/

namespace Math0.Frontier.A356360
open Math0.Statements.A356360

/-- `S m = 0! + 1! + ⋯ + (m-1)!`. -/
private def S (m : ℕ) : ℕ := ∑ k ∈ Finset.range m, k.factorial

/-- Closed form of the continued-fraction tail `H m x = foldr step x [2, …, m+1]`, valid when
`M = (m+1)x - m(m+2) > 0`: `H m x = 2M / (S m · M + (m+2)·m!)`. -/
private lemma closed (m : ℕ) : ∀ x : ℚ, 0 < ((m : ℚ) + 1) * x - m * (m + 2) →
    (List.range' 2 m).foldr step x =
      2 * (((m : ℚ) + 1) * x - m * (m + 2)) /
        ((S m : ℚ) * (((m : ℚ) + 1) * x - m * (m + 2)) + ((m : ℚ) + 2) * m.factorial) := by
  induction m with
  | zero =>
    intro x _
    simp [S]
  | succ m ih =>
    intro x hx
    push_cast at hx
    have hxpos : 0 < x := by
      by_contra h
      push Not at h
      nlinarith
    have hxne : x ≠ 0 := hxpos.ne'
    rw [List.range'_concat, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    have key : ((m : ℚ) + 1) * step (2 + 1 * m) x - m * (m + 2) =
        (((m : ℚ) + 2) * x - (m + 1) * (m + 3)) / x := by
      simp only [step]
      push_cast
      field_simp
      ring
    have hpos : 0 < ((m : ℚ) + 1) * step (2 + 1 * m) x - m * (m + 2) := by
      rw [key]
      apply div_pos _ hxpos
      linarith
    rw [ih _ hpos, key]
    have hS : (S (m + 1) : ℚ) = S m + m.factorial := by
      simp [S, Finset.sum_range_succ]
    have hf : ((m + 1).factorial : ℚ) = (m + 1) * m.factorial := by
      push_cast [Nat.factorial_succ]
      ring
    rw [hS, hf]
    push_cast
    have hfpos : (0 : ℚ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have hS0 : (0 : ℚ) ≤ S m := by positivity
    set M := ((m : ℚ) + 2) * x - (m + 1) * (m + 3) with hM
    have hMpos : 0 < M := by rw [hM]; linarith
    rw [div_eq_div_iff]
    · field_simp
      ring
    · have : 0 < (S m : ℚ) * (M / x) + ((m : ℚ) + 2) * m.factorial := by positivity
      exact this.ne'
    · have e : ((m : ℚ) + 1 + 1) * x - (m + 1) * (m + 1 + 2) = M := by rw [hM]; ring
      rw [e]
      positivity

/-- `cf (m+2) = (S m (2m+3) + (m+2) m!) / (2 (2m+3))`. -/
private lemma cf_eq (m : ℕ) : cf (m + 2) =
    ((S m * (2 * m + 3) + (m + 2) * m.factorial : ℕ) : ℚ) / (2 * ((2 * m + 3 : ℕ) : ℚ)) := by
  unfold cf
  rw [show m + 2 - 2 = m by omega]
  have hM : ((m : ℚ) + 1) * (((m + 2 : ℕ) : ℚ) + 1) - m * (m + 2) = 2 * m + 3 := by
    push_cast; ring
  rw [closed m _ (by rw [hM]; positivity), hM, one_div_div]
  push_cast
  ring

/-- `S m = 0! + ⋯ + (m-1)!` is even for `m ≥ 2`. -/
private lemma two_dvd_S (m : ℕ) (hm : 2 ≤ m) : 2 ∣ S m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases (show m = 1 ∨ 2 ≤ m by omega) with h | h
    · subst h; decide
    · have : S (m + 1) = S m + m.factorial := by simp [S, Finset.sum_range_succ]
      rw [this]
      exact dvd_add (ih h) (Nat.dvd_factorial (by norm_num) h)

/-- If `0 < a < b ≤ m` then `a * b ∣ m!`. -/
private lemma mul_dvd_factorial {a b m : ℕ} (ha : 0 < a) (hab : a < b) (hbm : b ≤ m) :
    a * b ∣ m.factorial := by
  have h1 : a ∣ (b - 1).factorial := Nat.dvd_factorial ha (by omega)
  have h2 : (b - 1).factorial * b = b.factorial := by
    rw [mul_comm, Nat.mul_factorial_pred (by omega)]
  have h3 : a * b ∣ b.factorial := by
    rw [← h2]; exact Nat.mul_dvd_mul_right h1 b
  exact h3.trans (Nat.factorial_dvd_factorial hbm)

/-- A composite `2m+3` with `m ≥ 4` divides `m!`. -/
private lemma composite_dvd (m : ℕ) (hm : 4 ≤ m) (hp : ¬ (2 * m + 3).Prime) :
    2 * m + 3 ∣ m.factorial := by
  set c := 2 * m + 3 with hc
  set a := c.minFac with ha
  have hc1 : c ≠ 1 := by omega
  have hap : a.Prime := Nat.minFac_prime hc1
  have hadvd : a ∣ c := Nat.minFac_dvd c
  have ha2 : a ≠ 2 := by
    intro h
    rw [h] at hadvd
    omega
  have ha3 : 3 ≤ a := by
    have := hap.two_le
    omega
  have hsq : a ^ 2 ≤ c := Nat.minFac_sq_le_self (by omega) hp
  obtain ⟨b, hb⟩ := hadvd
  have hab : a ≤ b := by
    rw [hb, pow_two] at hsq
    exact Nat.le_of_mul_le_mul_left hsq (by omega)
  have hbm : b ≤ m := by nlinarith
  rcases lt_or_eq_of_le hab with h | h
  · rw [hb]; exact mul_dvd_factorial (by omega) h hbm
  · subst h
    have ha5 : 5 ≤ a := by
      by_contra h5
      have : a = 3 ∨ a = 4 := by omega
      rcases this with h' | h' <;> rw [h'] at hb <;> omega
    have h2a : 2 * a ≤ m := by nlinarith
    rw [hb]
    have : a * (2 * a) ∣ m.factorial := mul_dvd_factorial (by omega) (by omega) h2a
    exact dvd_trans (Dvd.intro 2 (by ring)) this

/-- The conjecture for `n = m + 2 ≥ 6`. -/
private lemma main (m : ℕ) (hm : 4 ≤ m) : a (m + 2) = 1 ∨ (a (m + 2)).Prime := by
  have hev : 2 ∣ S m * (2 * m + 3) + (m + 2) * m.factorial :=
    dvd_add (dvd_mul_of_dvd_left (two_dvd_S m (by omega)) _)
      (dvd_mul_of_dvd_right (Nat.dvd_factorial (by norm_num) (by omega)) _)
  obtain ⟨K, hK⟩ := hev
  have hcf : cf (m + 2) = (K : ℚ) / ((2 * m + 3 : ℕ) : ℚ) := by
    rw [cf_eq, hK]
    push_cast
    field_simp
  unfold a
  rw [hcf]
  by_cases hp : (2 * m + 3).Prime
  · have hd : (((K : ℚ) / ((2 * m + 3 : ℕ) : ℚ)).den : ℤ) ∣ ((2 * m + 3 : ℕ) : ℤ) := by
      have := Rat.den_dvd (K : ℤ) ((2 * m + 3 : ℕ) : ℤ)
      rw [Rat.divInt_eq_div] at this
      push_cast at this ⊢
      exact this
    have hd' : ((K : ℚ) / ((2 * m + 3 : ℕ) : ℚ)).den ∣ 2 * m + 3 := by exact_mod_cast hd
    rcases hp.eq_one_or_self_of_dvd _ hd' with h | h
    · left; exact h
    · right; rw [h]; exact hp
  · left
    rw [Rat.den_div_natCast_eq_one_iff _ _ (by omega)]
    have h1 : 2 * m + 3 ∣ m.factorial := composite_dvd m hm hp
    have h2 : 2 * m + 3 ∣ 2 * K := by
      rw [← hK]
      exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right h1 _)
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm
      (Nat.prime_two.coprime_iff_not_dvd.2 (by omega))) h2)

/-- Every term `a n` (`n ≥ 3`) of A356360 is `1` or a prime. -/
theorem result : statement := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rcases (show m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with h | h | h | h
  · subst h; right; rw [show a (1 + 2) = 5 by decide +kernel]; norm_num
  · subst h; right; rw [show a (2 + 2) = 7 by decide +kernel]; norm_num
  · subst h; right; rw [show a (3 + 2) = 3 by decide +kernel]; norm_num
  · exact main m h

end Math0.Frontier.A356360

#math0_settles Math0.Frontier.A356360.result Math0.Statements.A356360.statement
