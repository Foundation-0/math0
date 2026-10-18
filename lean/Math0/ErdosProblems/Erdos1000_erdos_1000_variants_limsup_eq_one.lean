/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1000»
import Math0.Audit

/-!
# Erdős Problem 1000: if `liminf φ_A(k)/n_k = 0` then `limsup φ_A(k)/n_k = 1`

For a strictly increasing sequence of positive integers `n_0 < n_1 < ⋯`, `φ_A(k)` counts the
`1 ≤ m ≤ n_k` such that `n_k / gcd(m, n_k)` divides no earlier `n_j` (Cassels; Erdős,
erdosproblems.com/1000). We prove Erdős's observation, exactly as stated upstream: if the ratios
`φ_A(k)/n_k` have liminf `0`, then their limsup is `1`. Since `φ_A(k) ≥ φ(n_k)` and
`φ(N)/N ≥ 1/B!` when all prime factors of `N` are `≤ B`, a small ratio forces a prime factor
`p > max(P, n_K)` of some `n_k`; at the first index `k'` with `p ∣ n_{k'}` (necessarily `k' > K`),
every `m ≤ n_{k'}` prime to `p` is counted, so `φ_A(k')/n_{k'} ≥ 1 - 1/p ≥ 1 - 1/(P+1)`.
-/

open Filter Topology Erdos1000

namespace Math0.Erdos1000

/-- `φ_A(k) ≤ n_k`: the counted set is a subset of `[1, n_k]`. -/
theorem phiSeq_le (n : ℕ → ℕ) (k : ℕ) : phiSeq n k ≤ n k := by
  unfold phiSeq
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- If every prime factor of `N > 0` is at most `B`, then `φ(N)/N ≥ 1/B!`
(from `φ(N) · ∏_{p ∣ N} p = N · ∏_{p ∣ N} (p - 1) ≥ N` and `∏_{p ∣ N} p ∣ B!`). -/
theorem totient_ratio_ge {N B : ℕ} (hN : 0 < N) (hB : ∀ p ∈ N.primeFactors, p ≤ B) :
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
theorem ratio_ge (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) {p k : ℕ} (hp : p.Prime)
    (hk : p ∣ n k) (hmin : ∀ j < k, ¬ p ∣ n j) :
    (1 : ℝ) - 1 / (p : ℝ) ≤ (phiSeq n k : ℝ) / (n k : ℝ) := by
  set N := n k with hNdef
  have hN : 0 < N := hn0.trans_le (hn.monotone (Nat.zero_le k))
  have hsub : (Finset.Icc 1 N).filter (fun m => ¬ p ∣ m) ⊆
      (Finset.Icc 1 N).filter (fun m => ∀ j < k, ¬ (N / Nat.gcd m N) ∣ n j) := by
    intro m hm
    simp only [Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, fun j hj hdvd => ?_⟩
    have hg : N = (N / Nat.gcd m N) * Nat.gcd m N := (Nat.div_mul_cancel (Nat.gcd_dvd_right m N)).symm
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

/-- Erdős: for a strictly increasing sequence of positive integers, if
`liminf φ_A(k)/n_k = 0` then `limsup φ_A(k)/n_k = 1`. -/
theorem limsup_eq_one : type_of% @Erdos1000.erdos_1000.variants.limsup_eq_one := by
  intro n hn hn0 h
  set f := fun k : ℕ => (phiSeq n k : ℝ) / (n k : ℝ) with hf
  have hpos : ∀ k, 0 < n k := fun k => hn0.trans_le (hn.monotone (Nat.zero_le k))
  have hf0 : ∀ k, 0 ≤ f k := fun k => by positivity
  have hf1 : ∀ k, f k ≤ 1 := fun k => by
    rw [hf]
    dsimp only
    rw [div_le_one (by exact_mod_cast hpos k)]; exact_mod_cast phiSeq_le n k
  have hbdd : IsBoundedUnder (· ≤ ·) atTop f := isBoundedUnder_of ⟨1, hf1⟩
  have hbdd' : IsBoundedUnder (· ≥ ·) atTop f := isBoundedUnder_of ⟨0, hf0⟩
  have key : ∀ P K : ℕ, ∃ k ≥ K, 1 - 1 / ((P:ℝ) + 1) ≤ f k := by
    intro P K
    set B := max P (n K) with hB
    have hc : (0:ℝ) < 1 / (B.factorial : ℝ) := by positivity
    have hfreq : ∃ᶠ k in atTop, f k < 1 / (B.factorial : ℝ) := by
      apply frequently_lt_of_liminf_lt hbdd.isCoboundedUnder_flip
      rw [h]; exact hc
    obtain ⟨k, hk⟩ := hfreq.exists
    have hex0 : ∃ p ∈ (n k).primeFactors, B < p := by
      by_contra hcon
      push Not at hcon
      have h1 := totient_ratio_ge (hpos k) hcon
      have h2 := erdos_1000.variants.totient_le n hn hn0 k
      have h3 : ((n k).totient : ℝ) / n k ≤ f k := by
        apply div_le_div_of_nonneg_right (by exact_mod_cast h2) (by positivity)
      linarith
    obtain ⟨p, hp, hBp⟩ := hex0
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    have hex : ∃ i, p ∣ n i := ⟨k, hpdvd⟩
    classical
    refine ⟨Nat.find hex, ?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      have h1 : n (Nat.find hex) ≤ n K := hn.monotone hlt.le
      have h2 := Nat.le_of_dvd (hpos _) (Nat.find_spec hex)
      have h3 : n K ≤ B := le_max_right _ _
      omega
    · have h1 := ratio_ge n hn hn0 hpp (Nat.find_spec hex) (fun j hj => Nat.find_min hex hj)
      have h2 : (P:ℝ) + 1 ≤ p := by
        have : P ≤ B := le_max_left _ _
        exact_mod_cast (show P + 1 ≤ p by omega)
      have h3 : 1 / (p:ℝ) ≤ 1 / ((P:ℝ)+1) := one_div_le_one_div_of_le (by positivity) h2
      show 1 - 1 / ((P:ℝ) + 1) ≤ (phiSeq n (Nat.find hex) : ℝ) / (n (Nat.find hex) : ℝ)
      linarith
  apply le_antisymm
  · exact limsup_le_of_le hbdd'.isCoboundedUnder_flip (Eventually.of_forall hf1)
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨P, hP⟩ := exists_nat_one_div_lt hε
    have : 1 - 1/((P:ℝ)+1) ≤ limsup f atTop := by
      apply le_limsup_of_frequently_le _ hbdd
      rw [frequently_atTop]
      intro K
      exact key P K
    linarith

end Math0.Erdos1000

#math0_proves Math0.Erdos1000.limsup_eq_one Erdos1000.erdos_1000.variants.limsup_eq_one
