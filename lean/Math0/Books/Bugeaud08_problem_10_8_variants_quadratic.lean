/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_8
import Math0.Audit

/-!
# The p-adic Littlewood conjecture for quadratic irrationals (Bugeaud 10.8, quadratic case)

Bugeaud (*Distribution modulo one and Diophantine approximation*, Problem 10.8) states the
p-adic Littlewood conjecture of de Mathan and Teulié: `inf_{q ≥ 1} q · |q|_p · ‖q ξ‖ = 0`.
We prove the formal statement `Bugeaud08.problem_10_8.variants.quadratic`: the conjecture
holds for every real `ξ` whose minimal polynomial over `ℚ` has degree two. Clearing
denominators, `s = 2 N ξ + B` satisfies `s ^ 2 = m` for a positive non-square integer `m`.
For each `k`, a nontrivial solution of the Pell equation `x ^ 2 - m p ^ (2k) y ^ 2 = 1` gives
`Y = p ^ k |y|` with `x ^ 2 - m Y ^ 2 = 1`, so `s Y` is within `1 / (|s| Y)` of `± x`; taking
`q = 2 N Y` yields `q · |q|_p · ‖q ξ‖ ≤ 2 N / (|s| p ^ k) → 0`.
-/

namespace Math0.Bugeaud08

open Polynomial

/-- A real number of degree two over `ℚ` is a root of a monic rational quadratic. -/
lemma quad_coeffs (ξ : ℝ) (hξ : (minpoly ℚ ξ).natDegree = 2) :
    ∃ c₀ c₁ : ℚ, ξ ^ 2 + (c₁ : ℝ) * ξ + c₀ = 0 := by
  have hint : IsIntegral ℚ ξ := by
    by_contra h
    rw [minpoly.eq_zero h] at hξ
    simp at hξ
  have hmon := minpoly.monic hint
  have hroot := minpoly.aeval ℚ ξ
  rw [aeval_eq_sum_range, hξ] at hroot
  have h2 : (minpoly ℚ ξ).coeff 2 = 1 := by
    have := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hξ] at this
  refine ⟨(minpoly ℚ ξ).coeff 0, (minpoly ℚ ξ).coeff 1, ?_⟩
  simp [Finset.sum_range_succ, h2, Algebra.smul_def] at hroot
  linear_combination hroot

/-- A real number of degree two over `ℚ` is not rational. -/
lemma not_rat (ξ : ℝ) (hξ : (minpoly ℚ ξ).natDegree = 2) (r : ℚ) : ξ ≠ r := by
  rintro rfl
  have : (minpoly ℚ ((r : ℝ))).natDegree = 1 := by
    rw [minpoly.natDegree_eq_one_iff]
    exact ⟨r, rfl⟩
  omega

/-- Clearing denominators: `(2 N ξ + B) ^ 2` is an integer `m` for some `N > 0`, `B ∈ ℤ`. -/
lemma int_data (ξ : ℝ) (c₀ c₁ : ℚ) (h : ξ ^ 2 + (c₁ : ℝ) * ξ + c₀ = 0) :
    ∃ (N : ℕ) (B m : ℤ), 0 < N ∧ (2 * N * ξ + B) ^ 2 = m := by
  refine ⟨c₁.den * c₀.den, c₁.num * c₀.den,
    (c₁.num * c₀.den) ^ 2 - 4 * (c₁.den * c₀.den) * (c₀.num * c₁.den), by positivity, ?_⟩
  have hB : ((c₁.den * c₀.den : ℕ) : ℝ) * c₁ = ((c₁.num * c₀.den : ℤ) : ℝ) := by
    push_cast
    rw [Rat.cast_def c₁]
    field_simp
  have hC : ((c₁.den * c₀.den : ℕ) : ℝ) * c₀ = ((c₀.num * c₁.den : ℤ) : ℝ) := by
    push_cast
    rw [Rat.cast_def c₀]
    field_simp
  set N : ℝ := ((c₁.den * c₀.den : ℕ) : ℝ)
  set B : ℝ := ((c₁.num * c₀.den : ℤ) : ℝ)
  have hm : (((c₁.num * c₀.den) ^ 2 - 4 * (c₁.den * c₀.den) * (c₀.num * c₁.den) : ℤ) : ℝ)
      = B ^ 2 - 4 * N * ((c₀.num * c₁.den : ℤ) : ℝ) := by
    simp only [N, B]
    push_cast
    ring
  rw [hm]
  linear_combination 4 * N ^ 2 * h - 4 * N * ξ * hB - 4 * N * hC

/-- For irrational `ξ`, the shifted multiple `2 N ξ + B` is nonzero. -/
lemma s_ne_zero (ξ : ℝ) (N : ℕ) (B : ℤ) (hN : 0 < N) (hirr : ∀ r : ℚ, ξ ≠ r) :
    2 * N * ξ + B ≠ 0 := by
  intro h0
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  apply hirr ((-B) / (2 * N) : ℚ)
  push_cast
  field_simp
  linarith

/-- For irrational `ξ`, `m p ^ (2k)` is never a perfect square. -/
lemma not_square (ξ : ℝ) (N : ℕ) (B m : ℤ) (hN : 0 < N) (hs : (2 * N * ξ + B) ^ 2 = m)
    (hirr : ∀ r : ℚ, ξ ≠ r) (p : ℕ) (hp : p.Prime) (k : ℕ) :
    ¬ IsSquare (m * (p : ℤ) ^ (2 * k)) := by
  rintro ⟨t, ht⟩
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hpk : (0:ℝ) < (p:ℝ) ^ k := by positivity
  have h1 : ((2 * N * ξ + B) * (p:ℝ) ^ k) ^ 2 = (t:ℝ) ^ 2 := by
    have : ((m * (p : ℤ) ^ (2 * k) : ℤ) : ℝ) = ((t * t : ℤ) : ℝ) := by rw [ht]
    push_cast at this
    rw [mul_pow, hs, ← pow_mul, mul_comm k 2, this]
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2
  · apply hirr ((t / p ^ k - B) / (2 * N) : ℚ)
    push_cast
    field_simp
    linear_combination h2
  · apply hirr ((-t / p ^ k - B) / (2 * N) : ℚ)
    push_cast
    field_simp
    linear_combination h2

/-- One of `x, -x` is within `1 / (|s| Y)` of `s Y` when `x ^ 2 - s ^ 2 Y ^ 2 = 1`. -/
lemma pell_close (s Y x : ℝ) (hY : 0 < Y) (h : x ^ 2 - s ^ 2 * Y ^ 2 = 1) :
    ∃ n : ℝ, (n = x ∨ n = -x) ∧ |s * Y - n| * (|s| * Y) ≤ 1 := by
  have huv : |x - s * Y| * |x + s * Y| = 1 := by
    rw [← abs_mul]
    have : (x - s * Y) * (x + s * Y) = 1 := by linear_combination h
    rw [this, abs_one]
  have hsum : 2 * (|s| * Y) ≤ |x - s * Y| + |x + s * Y| := by
    have := abs_sub (x + s * Y) (x - s * Y)
    have e : x + s * Y - (x - s * Y) = 2 * (s * Y) := by ring
    rw [e, abs_mul, abs_mul, abs_of_pos hY] at this
    norm_num at this
    linarith [abs_nonneg (x - s * Y)]
  by_cases hv : |s| * Y ≤ |x + s * Y|
  · refine ⟨x, Or.inl rfl, ?_⟩
    rw [abs_sub_comm]
    calc |x - s * Y| * (|s| * Y) ≤ |x - s * Y| * |x + s * Y| :=
          mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ = 1 := huv
  · refine ⟨-x, Or.inr rfl, ?_⟩
    have hu : |s| * Y ≤ |x - s * Y| := by linarith
    have e : s * Y - -x = x + s * Y := by ring
    rw [e]
    calc |x + s * Y| * (|s| * Y) ≤ |x + s * Y| * |x - s * Y| :=
          mul_le_mul_of_nonneg_left hu (abs_nonneg _)
      _ = 1 := by rw [mul_comm]; exact huv

/-- The key estimate: for each `k` some `q ≥ 1` has
`q |q|_p ‖q ξ‖ ≤ 2 N / (|2 N ξ + B| p ^ k)`, via the Pell equation for `m p ^ (2k)`. -/
lemma approx (ξ : ℝ) (N p : ℕ) (B m : ℤ) (hN : 0 < N) (hs : (2 * N * ξ + B) ^ 2 = m)
    (hd0 : ∀ k : ℕ, 0 < m * (p : ℤ) ^ (2 * k))
    (hdsq : ∀ k : ℕ, ¬ IsSquare (m * (p : ℤ) ^ (2 * k)))
    (hp : p.Prime) (hs0 : 2 * N * ξ + B ≠ 0) (k : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ (q:ℝ) * (padicNorm p q : ℝ) * distToNearestInt (q * ξ) ≤
      2 * N / (|2 * N * ξ + B| * p ^ k) := by
  obtain ⟨x, y, hxy, hy0⟩ := Pell.exists_of_not_isSquare (hd0 k) (hdsq k)
  set s : ℝ := 2 * N * ξ + B with hs_def
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hpk : (0:ℝ) < (p:ℝ) ^ k := by positivity
  set Y : ℕ := p ^ k * y.natAbs with hY_def
  have hYpos : 0 < Y := by
    have := hp.pos
    have : 0 < y.natAbs := Int.natAbs_pos.mpr hy0
    positivity
  have hYr : (0:ℝ) < Y := by exact_mod_cast hYpos
  have hYcast : (Y:ℝ) = (p:ℝ) ^ k * |(y:ℝ)| := by
    simp [Y]
  have hpell : (x:ℝ) ^ 2 - s ^ 2 * (Y:ℝ) ^ 2 = 1 := by
    have : ((x ^ 2 - m * (p : ℤ) ^ (2 * k) * y ^ 2 : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by rw [hxy]
    push_cast at this
    rw [hYcast, hs, mul_pow, sq_abs]
    rw [← this]
    ring
  obtain ⟨n, hn, hclose⟩ := pell_close s Y x hYr hpell
  set q : ℕ := 2 * N * Y with hq_def
  have hq1 : 1 ≤ q := by
    have : 0 < q := by positivity
    omega
  refine ⟨q, hq1, ?_⟩
  -- distance bound
  have hn_int : ∃ z : ℤ, (z : ℝ) = n - B * Y := by
    rcases hn with h | h
    · exact ⟨x - B * Y, by push_cast; rw [h]⟩
    · exact ⟨-x - B * Y, by push_cast; rw [h]⟩
  obtain ⟨z, hz⟩ := hn_int
  have hqξ : (q:ℝ) * ξ - z = s * Y - n := by
    rw [hz, hq_def, hs_def]
    push_cast
    ring
  have hdist : distToNearestInt (q * ξ) * (|s| * Y) ≤ 1 := by
    have h1 : distToNearestInt (q * ξ) ≤ |(q:ℝ) * ξ - z| := round_le _ _
    rw [hqξ] at h1
    have : 0 < |s| * Y := by positivity
    calc distToNearestInt (q * ξ) * (|s| * Y) ≤ |s * Y - n| * (|s| * Y) := by gcongr
      _ ≤ 1 := hclose
  -- p-adic bound
  have hpad : (padicNorm p q : ℝ) ≤ ((p:ℝ) ^ k)⁻¹ := by
    have := Fact.mk hp
    have hdvd : ((p ^ k : ℕ) : ℤ) ∣ ((q : ℕ) : ℤ) := by
      refine Int.natCast_dvd_natCast.mpr ?_
      exact ⟨2 * N * y.natAbs, by rw [hq_def, hY_def]; ring⟩
    have := padicNorm.dvd_iff_norm_le.mp hdvd
    rw [Int.cast_natCast] at this
    have h2 : ((padicNorm p q : ℚ) : ℝ) ≤ (((p : ℚ) ^ (-(k : ℤ)) : ℚ) : ℝ) := by
      exact_mod_cast this
    refine h2.trans_eq ?_
    push_cast
    rw [zpow_neg, zpow_natCast]
  have hpn0 : (0:ℝ) ≤ (padicNorm p q : ℝ) := by
    have := padicNorm.nonneg (p := p) (q : ℚ)
    exact_mod_cast this
  have hd0' : 0 ≤ distToNearestInt (q * ξ) := distToNearestInt_nonneg _
  have hsY : 0 < |s| * Y := by positivity
  have hdist' : distToNearestInt (q * ξ) ≤ 1 / (|s| * Y) := by
    rw [le_div_iff₀ hsY]; exact hdist
  calc (q:ℝ) * (padicNorm p q : ℝ) * distToNearestInt (q * ξ)
      ≤ (q:ℝ) * ((p:ℝ) ^ k)⁻¹ * (1 / (|s| * Y)) := by gcongr
    _ = 2 * N / (|s| * p ^ k) := by
      rw [hq_def]
      push_cast
      field_simp

/-- The p-adic Littlewood conjecture holds for real quadratic irrationals: for every prime `p`
and every real `ξ` of degree two over `ℚ`, `inf_{q ≥ 1} q |q|_p ‖q ξ‖ = 0`. -/
theorem problem_10_8_quadratic : type_of% @Bugeaud08.problem_10_8.variants.quadratic := by
  intro ξ p hp hξ
  obtain ⟨c₀, c₁, h⟩ := quad_coeffs ξ hξ
  obtain ⟨N, B, m, hN, hs⟩ := int_data ξ c₀ c₁ h
  have hirr := not_rat ξ hξ
  have hs0 := s_ne_zero ξ N B hN hirr
  have hm : 0 < m := by
    have : (0:ℝ) < m := by rw [← hs]; positivity
    exact_mod_cast this
  have hd0 : ∀ k : ℕ, 0 < m * (p : ℤ) ^ (2 * k) := fun k => by
    have := hp.pos
    positivity
  have hdsq := not_square ξ N B m hN hs hirr p hp
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨_, 1, le_refl _, rfl⟩
  · rintro x ⟨q, -, rfl⟩
    have := padicNorm.nonneg (p := p) (q : ℚ)
    have h1 : (0:ℝ) ≤ (padicNorm p q : ℝ) := by exact_mod_cast this
    have h2 := distToNearestInt_nonneg ((q:ℝ) * ξ)
    positivity
  · intro w hw
    set s : ℝ := 2 * N * ξ + B with hs_def
    have hsa : 0 < |s| := abs_pos.mpr hs0
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * N / (|s| * w))
    have hpk : (k : ℝ) < (p : ℝ) ^ k := by
      exact_mod_cast Nat.lt_pow_self hp.one_lt
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    have hpk0 : (0:ℝ) < (p:ℝ) ^ k := by positivity
    obtain ⟨q, hq, hle⟩ := approx ξ N p B m hN hs hd0 hdsq hp hs0 k
    refine ⟨_, ⟨q, hq, rfl⟩, hle.trans_lt ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hk
    nlinarith

end Math0.Bugeaud08

#math0_proves Math0.Bugeaud08.problem_10_8_quadratic Bugeaud08.problem_10_8.variants.quadratic
