/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1000»
import Math0.Audit

/-!
# Erdős Problem 1000: `φ_A(k)/n_k` does not tend to `0`

For a strictly increasing sequence of positive integers `n_0 < n_1 < ⋯`, `φ_A(k)` counts the
`1 ≤ m ≤ n_k` such that `n_k / gcd(m, n_k)` divides no earlier `n_j` (Cassels; Erdős [Er64b],
erdosproblems.com/1000). We prove Erdős's observation, exactly as stated upstream: the ratios
`φ_A(k)/n_k` do not tend to `0`. If they did, they would eventually be `< 1/2`, say from index `K`
on, and also eventually `< 1/B!` with `B = max 2 n_K`. Since `φ_A(k) ≥ φ(n_k)` and `φ(N)/N ≥ 1/B!`
whenever all prime factors of `N` are `≤ B`, some `n_k` then has a prime factor `p > B`. At the
first index `k'` with `p ∣ n_{k'}` (necessarily `k' > K`, as `n_{k'} ≥ p > n_K`) every `m ≤ n_{k'}`
prime to `p` is counted, so `φ_A(k')/n_{k'} ≥ 1 - 1/p ≥ 1/2`, a contradiction.
-/

open Filter Topology Erdos1000

namespace Math0.Erdos1000

/-- If every prime factor of `N > 0` is at most `B`, then `φ(N)/N ≥ 1/B!`
(from `φ(N) · ∏_{p ∣ N} p = N · ∏_{p ∣ N} (p - 1) ≥ N` and `∏_{p ∣ N} p ∣ B!`). -/
theorem totient_ratio_ge_inv_factorial {N B : ℕ} (hN : 0 < N)
    (hB : ∀ p ∈ N.primeFactors, p ≤ B) :
    (1 : ℝ) / (B.factorial : ℝ) ≤ (N.totient : ℝ) / N := by
  have h1 : N ≤ N.totient * ∏ p ∈ N.primeFactors, p := by
    rw [Nat.totient_mul_prod_primeFactors]
    have : 1 ≤ ∏ p ∈ N.primeFactors, (p - 1) := by
      apply Nat.one_le_iff_ne_zero.mpr
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    nlinarith
  have h2 : ∏ p ∈ N.primeFactors, p ≤ B.factorial := by
    rw [← Finset.prod_Ico_id_eq_factorial]
    apply Nat.le_of_dvd (by rw [Finset.prod_Ico_id_eq_factorial]; exact Nat.factorial_pos B)
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have := hB p hp
    simp only [Finset.mem_Ico]
    omega
  have h3 : N ≤ N.totient * B.factorial := h1.trans (Nat.mul_le_mul_left _ h2)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B.factorial := by exact_mod_cast Nat.factorial_pos B
  rw [div_le_div_iff₀ hBr hNr]
  have : (N : ℝ) ≤ N.totient * B.factorial := by exact_mod_cast h3
  linarith

/-- If `p` is prime, `p ∣ n_k`, and `p` divides no earlier `n_j`, then
`φ_A(k)/n_k ≥ 1 - 1/p`: every `m ≤ n_k` with `p ∤ m` is counted. -/
theorem phiSeq_ratio_ge_of_new_prime (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0)
    {p k : ℕ} (hp : p.Prime) (hk : p ∣ n k) (hmin : ∀ j < k, ¬ p ∣ n j) :
    (1 : ℝ) - 1 / (p : ℝ) ≤ (phiSeq n k : ℝ) / (n k : ℝ) := by
  set N := n k with hNdef
  have hN : 0 < N := hn0.trans_le (hn.monotone (Nat.zero_le k))
  have hsub : (Finset.Icc 1 N).filter (fun m => ¬ p ∣ m) ⊆
      (Finset.Icc 1 N).filter (fun m => ∀ j < k, ¬ (N / Nat.gcd m N) ∣ n j) := by
    intro m hm
    simp only [Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, fun j hj hdvd => ?_⟩
    have hg : N = (N / Nat.gcd m N) * Nat.gcd m N :=
      (Nat.div_mul_cancel (Nat.gcd_dvd_right m N)).symm
    have hpd : p ∣ N / Nat.gcd m N := by
      have : p ∣ (N / Nat.gcd m N) * Nat.gcd m N := hg ▸ hk
      rcases (Nat.Prime.dvd_mul hp).1 this with h | h
      · exact h
      · exact absurd (h.trans (Nat.gcd_dvd_left m N)) hm.2
    exact hmin j hj (hpd.trans hdvd)
  have hcard1 : ((Finset.Icc 1 N).filter (fun m => ¬ p ∣ m)).card ≤ phiSeq n k :=
    Finset.card_le_card hsub
  have hcard2 : ((Finset.Icc 1 N).filter (fun m => p ∣ m)).card +
      ((Finset.Icc 1 N).filter (fun m => ¬ p ∣ m)).card = N := by
    rw [Finset.card_filter_add_card_filter_not]; simp
  have hcard3 : ((Finset.Icc 1 N).filter (fun m => p ∣ m)).card = N / p := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div]
    rfl
  have h1 : N ≤ phiSeq n k + N / p := by omega
  have h1r : (N : ℝ) ≤ (phiSeq n k : ℝ) + ((N / p : ℕ) : ℝ) := by exact_mod_cast h1
  have h2r : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) := Nat.cast_div_le
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [le_div_iff₀ hNr]
  have : (N : ℝ) / p = (1 / p) * N := by field_simp
  nlinarith

/-- Erdős: for a strictly increasing sequence of positive integers `n`, the ratios
`φ_A(k)/n_k` do not tend to `0`. -/
theorem not_tendsto_zero : type_of% @Erdos1000.erdos_1000.variants.not_tendsto_zero := by
  intro n hn hn0 htend
  set f := fun k : ℕ => (phiSeq n k : ℝ) / (n k : ℝ) with hf
  have hpos : ∀ k, 0 < n k := fun k => hn0.trans_le (hn.monotone (Nat.zero_le k))
  -- eventually `f k < 1/2`
  have hev : ∀ᶠ k in atTop, f k < 1 / 2 := htend.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  set B := max 2 (n K) with hB
  have hc : (0 : ℝ) < 1 / (B.factorial : ℝ) := by positivity
  have hev2 : ∀ᶠ k in atTop, f k < 1 / (B.factorial : ℝ) := htend.eventually (gt_mem_nhds hc)
  obtain ⟨k, hk⟩ := hev2.exists
  -- `n k` has a prime factor `p > B`
  have hex0 : ∃ p ∈ (n k).primeFactors, B < p := by
    by_contra hcon
    push Not at hcon
    have h1 := totient_ratio_ge_inv_factorial (hpos k) hcon
    have h2 := erdos_1000.variants.totient_le n hn hn0 k
    have h3 : ((n k).totient : ℝ) / n k ≤ f k := by
      apply div_le_div_of_nonneg_right (by exact_mod_cast h2) (by positivity)
    linarith
  obtain ⟨p, hp, hBp⟩ := hex0
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpdvd := Nat.dvd_of_mem_primeFactors hp
  have hex : ∃ i, p ∣ n i := ⟨k, hpdvd⟩
  classical
  -- the first index at which `p` appears is `≥ K`
  have hge : K ≤ Nat.find hex := by
    by_contra hlt
    push Not at hlt
    have h1 : n (Nat.find hex) ≤ n K := hn.monotone hlt.le
    have h2 := Nat.le_of_dvd (hpos _) (Nat.find_spec hex)
    have h3 : n K ≤ B := le_max_right _ _
    omega
  have h1 := phiSeq_ratio_ge_of_new_prime n hn hn0 hpp (Nat.find_spec hex)
    (fun j hj => Nat.find_min hex hj)
  have h2 : (2 : ℝ) ≤ p := by
    have : 2 ≤ B := le_max_left _ _
    exact_mod_cast (show 2 ≤ p by omega)
  have h3 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  have h4 := hK _ hge
  have h5 : f (Nat.find hex) = (phiSeq n (Nat.find hex) : ℝ) / (n (Nat.find hex) : ℝ) := rfl
  linarith

end Math0.Erdos1000

#math0_proves Math0.Erdos1000.not_tendsto_zero Erdos1000.erdos_1000.variants.not_tendsto_zero
