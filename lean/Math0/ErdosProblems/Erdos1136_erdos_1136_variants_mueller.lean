/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1136»
import Math0.Audit

/-!
# Erdős Problem 1136: Müller's set avoids powers of two and has density 1/2

Erdős Problem 1136 asks for a set `A ⊆ ℕ` of large lower density such that no sum `a + b`
(`a, b ∈ A`, not necessarily distinct) is a power of two. Müller (2011) showed that the set `M`
of naturals congruent to `3 · 2^i` modulo `2^(i+2)` for some `i` works, with density `1/2`. We
prove exactly this. Elements of `M` are the numbers `2^i (4q+3)`; for `i ≤ j` the sum
`2^i (4q+3) + 2^j (4r+3)` is `2^i` times an odd number `≥ 3` (if `i < j`) or `2^(i+1)` times an
odd number `≥ 3` (if `i = j`), so it is never a power of two. For the density, the counting
function `c(b) = #(M ∩ [0, b))` satisfies `c(b) = ⌊b/4⌋ + c(⌊(b+1)/2⌋)`, from which
`2 c(b) ≤ b ≤ 2 c(b) + 2k + ⌊b/2^k⌋` for every `k`, and `c(b)/b → 1/2` follows.
-/

namespace Math0.Erdos1136

open _root_.Erdos1136 Filter Topology

/-- Membership in Müller's set: `n` is in it iff `n = 2^i (4q+3)` for some `i, q`. -/
theorem mem_muellerSet_iff (n : ℕ) :
    n ∈ muellerSet ↔ ∃ i q : ℕ, n = 2 ^ i * (4 * q + 3) := by
  constructor
  · rintro ⟨i, hi⟩
    have hlt : 3 * 2 ^ i < 2 ^ (i + 2) := by
      rw [pow_add]; have := pow_pos (by norm_num : (0:ℕ) < 2) i; omega
    have h1 : n % 2 ^ (i + 2) = 3 * 2 ^ i := by
      rw [hi, Nat.mod_eq_of_lt hlt]
    have h2 := Nat.mod_add_div n (2 ^ (i + 2))
    rw [h1] at h2
    refine ⟨i, n / 2 ^ (i + 2), ?_⟩
    generalize n / 2 ^ (i + 2) = q at h2 ⊢
    rw [← h2]; ring
  · rintro ⟨i, q, rfl⟩
    refine ⟨i, ?_⟩
    have : 2 ^ i * (4 * q + 3) = 3 * 2 ^ i + 2 ^ (i + 2) * q := by ring
    rw [this]
    exact Nat.add_mul_mod_self_left _ _ _

/-- A sum `2^i (4q+3) + 2^j (4r+3)` with `i ≤ j` is never a power of two. -/
theorem sum_ne_pow_of_le (i j q r k : ℕ) (hij : i ≤ j) :
    2 ^ i * (4 * q + 3) + 2 ^ j * (4 * r + 3) ≠ 2 ^ k := by
  intro h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hfac : 2 ^ i * (4 * q + 3 + 2 ^ d * (4 * r + 3)) = 2 ^ k := by
    rw [← h, pow_add]; ring
  have hdvd : (4 * q + 3 + 2 ^ d * (4 * r + 3)) ∣ 2 ^ k := Dvd.intro_left _ hfac
  obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rcases d with _ | d
  · rcases l with _ | _ | _ | l
    · simp at hl; omega
    · simp at hl; omega
    · simp at hl; omega
    · rw [pow_add] at hl
      simp at hl
      omega
  · rcases l with _ | l
    · simp at hl
      omega
    · have h3 : 4 * q + 3 + 2 * (2 ^ d * (4 * r + 3)) = 2 * 2 ^ l := by
        calc 4 * q + 3 + 2 * (2 ^ d * (4 * r + 3)) = 4 * q + 3 + 2 ^ (d + 1) * (4 * r + 3) := by
              ring
          _ = 2 ^ (l + 1) := hl
          _ = 2 * 2 ^ l := by ring
      generalize 2 ^ d * (4 * r + 3) = y at h3
      generalize 2 ^ l = z at h3
      omega

/-- Müller's set avoids powers of two. -/
theorem avoids : AvoidsPowersOfTwo muellerSet := by
  intro a ha b hb k
  obtain ⟨i, q, rfl⟩ := (mem_muellerSet_iff a).1 ha
  obtain ⟨j, r, rfl⟩ := (mem_muellerSet_iff b).1 hb
  rcases le_total i j with hij | hij
  · exact sum_ne_pow_of_le i j q r k hij
  · rw [add_comm]; exact sum_ne_pow_of_le j i r q k hij

/-- `0` is not in Müller's set. -/
theorem zero_not_mem : (0 : ℕ) ∉ muellerSet := by
  rw [mem_muellerSet_iff]
  rintro ⟨i, q, h⟩
  have : 2 ^ i * (4 * q + 3) ≠ 0 := by positivity
  exact this h.symm

/-- Doubling: `2m` is in Müller's set iff `m` is. -/
theorem two_mul_mem_iff (m : ℕ) : 2 * m ∈ muellerSet ↔ m ∈ muellerSet := by
  rw [mem_muellerSet_iff, mem_muellerSet_iff]
  constructor
  · rintro ⟨i, q, h⟩
    cases i with
    | zero => simp at h; omega
    | succ i =>
      refine ⟨i, q, ?_⟩
      have : 2 * m = 2 * (2 ^ i * (4 * q + 3)) := by rw [h]; ring
      omega
  · rintro ⟨i, q, h⟩
    exact ⟨i + 1, q, by rw [h, pow_succ]; ring⟩

/-- An odd number is in Müller's set iff it is `3 mod 4`. -/
theorem odd_mem_iff (m : ℕ) : 2 * m + 1 ∈ muellerSet ↔ (2 * m + 1) % 4 = 3 := by
  rw [mem_muellerSet_iff]
  constructor
  · rintro ⟨i, q, h⟩
    cases i with
    | zero => simp at h; omega
    | succ i =>
      have : 2 * m + 1 = 2 * (2 ^ i * (4 * q + 3)) := by rw [h]; ring
      omega
  · intro h
    exact ⟨0, (2 * m + 1) / 4, by simp; omega⟩

open Classical in
/-- The counting function `c(b) = #(M ∩ [0, b))` of Müller's set. -/
noncomputable def cnt (b : ℕ) : ℕ := Nat.count (· ∈ muellerSet) b

open Classical in
/-- One-step recursion for the counting function. -/
theorem cnt_succ (b : ℕ) : cnt (b + 1) = cnt b + if b ∈ muellerSet then 1 else 0 := by
  unfold cnt
  exact Nat.count_succ _ _

/-- `c(b+1) = c(b) + 1` when `b ∈ M`. -/
theorem cnt_succ_of_mem {b : ℕ} (h : b ∈ muellerSet) : cnt (b + 1) = cnt b + 1 := by
  rw [cnt_succ, if_pos h]

/-- `c(b+1) = c(b)` when `b ∉ M`. -/
theorem cnt_succ_of_not_mem {b : ℕ} (h : b ∉ muellerSet) : cnt (b + 1) = cnt b := by
  rw [cnt_succ, if_neg h, add_zero]

/-- The key recursion `c(b) = ⌊b/4⌋ + c(⌊(b+1)/2⌋)`: odd members are the numbers `≡ 3 mod 4`,
even members are the doubles of members. -/
theorem cnt_rec (b : ℕ) : cnt b = b / 4 + cnt ((b + 1) / 2) := by
  induction b with
  | zero => simp
  | succ b ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' b
    · have e1 : (2 * m + 1) / 2 = m := by omega
      have e2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [e1] at ih
      rw [e2]
      by_cases hm : m ∈ muellerSet
      · have hm' : 2 * m ∈ muellerSet := (two_mul_mem_iff m).2 hm
        rw [cnt_succ_of_mem hm', cnt_succ_of_mem hm, ih]
        omega
      · have hm' : 2 * m ∉ muellerSet := fun h => hm ((two_mul_mem_iff m).1 h)
        rw [cnt_succ_of_not_mem hm', cnt_succ_of_not_mem hm, ih]
        omega
    · have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have e2 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
      rw [e1] at ih
      rw [e2]
      by_cases hm : (2 * m + 1) % 4 = 3
      · rw [cnt_succ_of_mem ((odd_mem_iff m).2 hm), ih]
        omega
      · rw [cnt_succ_of_not_mem (fun h => hm ((odd_mem_iff m).1 h)), ih]
        omega

/-- Upper bound: `2 c(b) ≤ b`. -/
theorem two_mul_cnt_le (b : ℕ) : 2 * cnt b ≤ b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    rcases Nat.lt_or_ge b 2 with hb | hb
    · interval_cases b
      · simp [cnt]
      · rw [cnt_succ_of_not_mem zero_not_mem]; simp [cnt]
    · rw [cnt_rec b]
      have := ih ((b + 1) / 2) (by omega)
      omega

/-- An elementary inequality for floor division. -/
theorem succ_div_le (b m : ℕ) (hm : 0 < m) : (b + 1) / m ≤ b / m + 1 := by
  calc (b + 1) / m ≤ (b + m) / m := Nat.div_le_div_right (by omega)
    _ = b / m + 1 := Nat.add_div_right b hm

/-- Lower bound: for every `k`, `b ≤ 2 c(b) + 2k + ⌊b / 2^k⌋`. -/
theorem le_two_mul_cnt (k b : ℕ) : b ≤ 2 * cnt b + 2 * k + b / 2 ^ k := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    have h1 := ih ((b + 1) / 2)
    rw [Nat.div_div_eq_div_mul] at h1
    have h2 := succ_div_le b (2 * 2 ^ k) (by positivity)
    rw [cnt_rec b, pow_succ, mul_comm (2 ^ k) 2]
    generalize (b + 1) / (2 * 2 ^ k) = x at h1 h2
    generalize b / (2 * 2 ^ k) = y at h1 h2 ⊢
    omega

/-- The partial densities of Müller's set are `c(b) / b`. -/
theorem ncard_eq_cnt (b : ℕ) : ((muellerSet ∩ Set.univ) ∩ Set.Iio b).ncard = cnt b := by
  classical
  rw [cnt, Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [and_comm]

/-- Müller's set has natural density `1/2`. -/
theorem density : muellerSet.HasDensity (1 / 2) := by
  unfold Set.HasDensity
  have hfun : (fun b : ℕ => muellerSet.partialDensity Set.univ b) =
      fun b => (cnt b : ℝ) / b := by
    funext b
    simp only [Set.partialDensity, ncard_eq_cnt, Set.univ_inter, Set.ncard_Iio_nat]
  rw [hfun, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * k / ε)
  refine ⟨N + 1, fun b hb => ?_⟩
  have hbN : (N : ℝ) + 1 ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hupR : (2 * cnt b : ℝ) ≤ b := by exact_mod_cast two_mul_cnt_le b
  have hdivR : ((b / 2 ^ k : ℕ) : ℝ) ≤ (b : ℝ) * (1 / 2) ^ k := by
    have := Nat.cast_div_le (α := ℝ) (m := b) (n := 2 ^ k)
    rw [one_div_pow, ← div_eq_mul_one_div]
    simpa using this
  have hlowR : (b : ℝ) ≤ 2 * cnt b + 2 * k + b * (1 / 2) ^ k := by
    have : (b : ℝ) ≤ 2 * cnt b + 2 * k + ((b / 2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast le_two_mul_cnt k b
    linarith
  have hNb : 2 * (k : ℝ) < ε * b := by
    have h1 : 2 * (k : ℝ) / ε < b := by linarith
    rw [div_lt_iff₀ hε] at h1
    linarith
  have hpow : (b : ℝ) * (1 / 2) ^ k < b * ε := mul_lt_mul_of_pos_left hk hbpos
  have hεb : 0 < ε * b := mul_pos hε hbpos
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hbpos]
    nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hbpos]
    nlinarith

/-- Müller's theorem: the set of integers congruent to `3 · 2^i mod 2^(i+2)` for some `i` has no
two (not necessarily distinct) elements summing to a power of two, and has natural density `1/2`. -/
theorem erdos_1136_mueller : type_of% @_root_.Erdos1136.erdos_1136.variants.mueller :=
  ⟨avoids, density⟩

end Math0.Erdos1136

#math0_proves Math0.Erdos1136.erdos_1136_mueller Erdos1136.erdos_1136.variants.mueller
