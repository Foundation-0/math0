/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A342992
import Math0.Audit

/-!
# Every `n` not divisible by `5` has a multiple with only prime digits (A342992)

We prove Sariyar's conjecture: if `n ≥ 1` and `5 ∤ n`, then some positive multiple of `n` has
only the decimal digits `2` and `3`; in particular `a(n) > 0`.

Write `n = 2^e * m` with `m` odd, so `gcd(m, 10) = 1`. Put `L = φ(m) * (e + 1)`.

* *Block.* By induction on `j` there is a `j`-digit number `N_j` with digits in `{2, 3}` and
  `2^j ∣ N_j`: given `N_j = 2^j q`, append the leading digit `d ∈ {2, 3}` with `q + 5^j d`
  even; then `N_j + 10^j d = 2^j (q + 5^j d)` is divisible by `2^(j+1)`.
* *Repetition.* Let `X_t` be the block `N = N_L` written `t` times in a row, so
  `X_{t+1} = N + 10^L X_t`. Since `10^L ≡ 1 [MOD m]` (Euler), `X_t ≡ t N [MOD m]`, and
  `2^e ∣ 2^L ∣ N` gives `2^e ∣ X_t`. Hence `m ∣ X_m` and `2^e ∣ X_m`; by coprimality
  `n ∣ X_m`. The digits of `X_m` are those of the repeated block, all in `{2, 3}`.
-/

namespace Math0.Frontier.A342992
open Math0.Statements.A342992

/-- For every `j` there is a little-endian digit list of length `j` with entries in `{2, 3}`
whose value is divisible by `2^j`. -/
private lemma exists_block (j : ℕ) : ∃ l : List ℕ, l.length = j ∧ (∀ d ∈ l, d = 2 ∨ d = 3) ∧
    2 ^ j ∣ Nat.ofDigits 10 l := by
  induction j with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ j ih =>
    obtain ⟨l, hlen, hdig, q, hq⟩ := ih
    have h10 : (10 : ℕ) ^ j = 2 ^ j * 5 ^ j := by rw [← mul_pow]; norm_num
    rcases Nat.even_or_odd q with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨l ++ [2], by simp [hlen], ?_, ?_⟩
      · intro d hd
        rcases List.mem_append.1 hd with hd | hd
        · exact hdig d hd
        · simp at hd; omega
      · refine ⟨r + 5 ^ j, ?_⟩
        rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hq, hlen, h10, hr]
        ring
    · obtain ⟨s, hs⟩ : Odd (5 ^ j) := Odd.pow (by decide)
      refine ⟨l ++ [3], by simp [hlen], ?_, ?_⟩
      · intro d hd
        rcases List.mem_append.1 hd with hd | hd
        · exact hdig d hd
        · simp at hd; omega
      · refine ⟨r + 3 * s + 2, ?_⟩
        rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hq, hlen, h10, hr, hs]
        ring

/-- Repeating a block `t` times: the value is `t * N` modulo `m` when `10^L ≡ 1 [MOD m]`, and
it stays divisible by any `D` dividing the block's value. -/
private lemma rep_props (l : List ℕ) (m D : ℕ) (hm : 10 ^ l.length ≡ 1 [MOD m])
    (hD : D ∣ Nat.ofDigits 10 l) (t : ℕ) :
    Nat.ofDigits 10 (List.replicate t l).flatten ≡ t * Nat.ofDigits 10 l [MOD m] ∧
      D ∣ Nat.ofDigits 10 (List.replicate t l).flatten := by
  induction t with
  | zero => simp; rfl
  | succ t ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append]
    refine ⟨?_, dvd_add hD (dvd_mul_of_dvd_right ih.2 _)⟩
    have h1 := (hm.mul ih.1).add_left (Nat.ofDigits 10 l)
    rw [one_mul] at h1
    refine h1.trans ?_
    rw [add_mul, one_mul, add_comm]

/-- The conjecture holds: every `n ≥ 1` with `5 ∤ n` has a multiple with only prime digits. -/
theorem result : statement := by
  intro n hn h5
  rw [a_pos_iff]
  obtain ⟨e, m, hm2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 2 (by decide)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hn
    · exact h
  have hm5 : ¬ 5 ∣ m := fun h => h5 (dvd_mul_of_dvd_right h _)
  have hcop : Nat.Coprime 10 m := by
    rw [show (10 : ℕ) = 2 * 5 by rfl, Nat.coprime_mul_iff_left]
    exact ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm2,
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hm5⟩
  have hphi : 0 < Nat.totient m := Nat.totient_pos.2 hm0
  obtain ⟨l, hlen, hdig, hdvd⟩ := exists_block (Nat.totient m * (e + 1))
  have hmod : 10 ^ l.length ≡ 1 [MOD m] := by
    rw [hlen, pow_mul]
    simpa using (Nat.ModEq.pow_totient hcop).pow (e + 1)
  have hle : e ≤ Nat.totient m * (e + 1) := by nlinarith
  have hD : 2 ^ e ∣ Nat.ofDigits 10 l := (pow_dvd_pow 2 hle).trans hdvd
  obtain ⟨hX1, hX2⟩ := rep_props l m (2 ^ e) hmod hD m
  set X := Nat.ofDigits 10 (List.replicate m l).flatten with hX
  have hmX : m ∣ X := by
    have := hX1.trans (Nat.modEq_zero_iff_dvd.2 (dvd_mul_right m _))
    exact Nat.modEq_zero_iff_dvd.1 this
  have hnX : 2 ^ e * m ∣ X :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm2)) hX2 hmX
  have hmem : ∀ d ∈ (List.replicate m l).flatten, d = 2 ∨ d = 3 := by
    intro d hd
    rw [List.mem_flatten] at hd
    obtain ⟨l', hl', hd⟩ := hd
    rw [List.eq_of_mem_replicate hl'] at hd
    exact hdig d hd
  have hdigits : Nat.digits 10 X = (List.replicate m l).flatten := by
    apply Nat.digits_ofDigits 10 (by norm_num)
    · intro d hd
      rcases hmem d hd with h | h <;> omega
    · intro h
      rcases hmem _ (List.getLast_mem h) with h' | h' <;> omega
  have hne : (List.replicate m l).flatten ≠ [] := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [List.replicate_succ, List.flatten_cons]
    intro h
    have := congrArg List.length h
    simp [hlen] at this
  have hXpos : 0 < X := by
    rcases Nat.eq_zero_or_pos X with h | h
    · rw [h, Nat.digits_zero] at hdigits
      exact absurd hdigits.symm hne
    · exact h
  refine ⟨X / (2 ^ e * m), ?_⟩
  rw [Nat.div_mul_cancel hnX]
  refine ⟨hXpos, fun d hd => ?_⟩
  rw [hdigits] at hd
  rcases hmem d hd with h | h <;> subst h <;> norm_num

end Math0.Frontier.A342992

#math0_settles Math0.Frontier.A342992.result Math0.Statements.A342992.statement
