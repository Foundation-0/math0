/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1136»
import Math0.Audit

/-!
# Erdős Problem 1136: the multiples of three avoid powers of two and have density 1/3

Erdős Problem 1136 asks for a set `A ⊆ ℕ` of lower density greater than `1/3` such that no sum
`a + b` (`a, b ∈ A`, not necessarily distinct) is a power of two. The trivial benchmark is the set
of multiples of `3`, which has density exactly `1/3`; we prove both facts. If `3 ∣ a` and `3 ∣ b`
then `3 ∣ a + b`, while no power of two is divisible by the prime `3`. For the density, the
multiples of `3` below `b` are exactly `3k` for `k < ⌊(b+2)/3⌋`, so the count `c(b)` satisfies
`b ≤ 3 c(b) ≤ b + 2`, whence `|c(b)/b - 1/3| ≤ 2/(3b) → 0`.
-/

namespace Math0.Erdos1136

open _root_.Erdos1136 Filter Topology

/-- No two multiples of three sum to a power of two. -/
theorem avoids_multiples_of_three : AvoidsPowersOfTwo {n : ℕ | 3 ∣ n} := by
  intro a ha b hb k hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ dvd_add ha hb
  have : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
  omega

/-- The multiples of three below `b` are the images of `k < ⌊(b+2)/3⌋` under `k ↦ 3k`. -/
theorem inter_Iio_eq_image (b : ℕ) :
    ({n : ℕ | 3 ∣ n} ∩ Set.univ) ∩ Set.Iio b = (fun k => 3 * k) '' Set.Iio ((b + 2) / 3) := by
  ext n
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true, Set.mem_Iio,
    Set.mem_image]
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨dvd_mul_right 3 k, by omega⟩

/-- The number of multiples of three below `b` is `⌊(b+2)/3⌋`. -/
theorem ncard_inter_Iio (b : ℕ) :
    (({n : ℕ | 3 ∣ n} ∩ Set.univ) ∩ Set.Iio b).ncard = (b + 2) / 3 := by
  rw [inter_Iio_eq_image, Set.ncard_image_of_injective _ (mul_right_injective₀ (by norm_num)),
    Set.ncard_Iio_nat]

/-- The multiples of three have natural density `1/3`. -/
theorem density_multiples_of_three : Set.HasDensity {n : ℕ | 3 ∣ n} (1 / 3) := by
  unfold Set.HasDensity
  have hfun : (fun b : ℕ => Set.partialDensity {n : ℕ | 3 ∣ n} Set.univ b) =
      fun b => (((b + 2) / 3 : ℕ) : ℝ) / b := by
    funext b
    simp only [Set.partialDensity, ncard_inter_Iio, Set.univ_inter, Set.ncard_Iio_nat]
  rw [hfun, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N + 1, fun b hb => ?_⟩
  have hbN : (N : ℝ) + 1 ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  set c := (b + 2) / 3 with hc
  have h1 : b ≤ 3 * c := by omega
  have h2 : 3 * c ≤ b + 2 := by omega
  have h1R : (b : ℝ) ≤ 3 * c := by exact_mod_cast h1
  have h2R : (3 * c : ℝ) ≤ b + 2 := by exact_mod_cast h2
  have hεb : 1 < ε * b := by
    have h3 : 1 / ε < b := by linarith
    rw [div_lt_iff₀ hε] at h3
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hbpos]
    nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hbpos]
    nlinarith

/-- The set of multiples of three has no two (not necessarily distinct) elements summing to a
power of two, and has natural density `1/3`. -/
theorem erdos_1136_multiples_of_three :
    type_of% @_root_.Erdos1136.erdos_1136.variants.multiples_of_three :=
  ⟨avoids_multiples_of_three, density_multiples_of_three⟩

end Math0.Erdos1136

#math0_proves Math0.Erdos1136.erdos_1136_multiples_of_three Erdos1136.erdos_1136.variants.multiples_of_three
