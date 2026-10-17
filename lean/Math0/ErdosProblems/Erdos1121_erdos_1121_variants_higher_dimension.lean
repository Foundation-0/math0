/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1121»
import Math0.Audit

/-!
# Erdős Problem 1121 in higher dimensions (Goodman–Goodman)

Let `B_i = closedBall (c i) (r i)` (`r i > 0`) be finitely many balls in `ℝ^d` such that every
hyperplane disjoint from all the balls has all the centres strictly on one side. We prove the
upstream statement that all the balls lie in one ball of radius `R = ∑ r i`, as conjectured by
Erdős and proved by Goodman and Goodman (1945). The centre is the weighted centroid
`z = R⁻¹ • ∑ r i • c i`. For `p ∈ B_i` and `v = p - z ≠ 0`, project onto `v`: the balls become
intervals `[a_j - r_j‖v‖, a_j + r_j‖v‖]` with `a_j = ⟪v, c_j⟫`. The separation hypothesis forces
each gap `(e_j, U]` (with `e_j = a_j + r_j‖v‖`, `U = max e`) to be covered by the intervals with
larger right end, so a length (Lebesgue measure) bound and a weighted sum over `j` give
`U ≤ ⟪v, z⟫ + R‖v‖`; since `⟪v, p⟫ ≤ U`, this yields `‖v‖² ≤ R‖v‖`.
-/

namespace Math0.Erdos1121

/-- If a half-open interval `(x, U]` is covered by finitely many closed intervals, its length is
at most the total length of the covering intervals. -/
theorem length_le_of_cover {ι : Type*} (S : Finset ι) (lo hi : ι → ℝ)
    (hlh : ∀ l ∈ S, lo l ≤ hi l) (x U : ℝ)
    (hcov : Set.Ioc x U ⊆ ⋃ l ∈ S, Set.Icc (lo l) (hi l)) :
    U - x ≤ ∑ l ∈ S, (hi l - lo l) := by
  have h1 : MeasureTheory.volume (Set.Ioc x U) ≤
      ∑ l ∈ S, MeasureTheory.volume (Set.Icc (lo l) (hi l)) :=
    (MeasureTheory.measure_mono hcov).trans (MeasureTheory.measure_biUnion_finset_le S _)
  rw [Real.volume_Ioc] at h1
  simp only [Real.volume_Icc] at h1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun l hl => sub_nonneg.mpr (hlh l hl))] at h1
  exact (ENNReal.ofReal_le_ofReal_iff
    (Finset.sum_nonneg fun l hl => sub_nonneg.mpr (hlh l hl))).mp h1

/-- Summing `r j * r l` over ordered pairs with `e j < e l`, twice, is at most the sum over all
pairs of distinct indices. -/
theorem two_mul_sum_lt_le {n : ℕ} (r e : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) :
    2 * ∑ j, ∑ l ∈ Finset.univ.filter (fun l => e j < e l), r j * r l ≤
      (∑ i, r i) ^ 2 - ∑ i, r i ^ 2 := by
  have h1 : ∀ j l, (if e j < e l then r j * r l else 0) + (if e l < e j then r l * r j else 0) ≤
      r j * r l - if j = l then r j * r l else 0 := by
    intro j l
    by_cases hjl : j = l
    · subst hjl; simp
    · simp only [hjl, if_false, sub_zero]
      have := mul_nonneg (hr j) (hr l)
      split_ifs with h2 h3 h3
      · exact absurd h3 (lt_asymm h2)
      · linarith
      · linarith [mul_comm (r j) (r l)]
      · linarith
  have hc : ∑ j, ∑ l, (if e j < e l then r j * r l else 0) =
      ∑ j, ∑ l, (if e l < e j then r l * r j else 0) := Finset.sum_comm
  simp only [Finset.sum_filter]
  rw [two_mul]
  nth_rewrite 2 [hc]
  rw [← Finset.sum_add_distrib]
  calc ∑ j, ((∑ l, if e j < e l then r j * r l else 0) + ∑ l, if e l < e j then r l * r j else 0)
      = ∑ j, ∑ l, ((if e j < e l then r j * r l else 0) + if e l < e j then r l * r j else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_add_distrib]
    _ ≤ ∑ j, ∑ l, (r j * r l - if j = l then r j * r l else 0) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => h1 j l
    _ = (∑ i, r i) ^ 2 - ∑ i, r i ^ 2 := by
        simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, sq,
          Finset.sum_mul_sum]

/-- Goodman–Goodman in `ℝ^d`: if no hyperplane disjoint from finitely many balls separates their
centres, then all the balls lie in a single ball whose radius is the sum of their radii. -/
theorem erdos_1121_higher_dimension : type_of% @Erdos1121.erdos_1121.variants.higher_dimension := by
  intro d n c r hr hsep
  refine ⟨(∑ i, r i)⁻¹ • ∑ i, r i • c i, ?_⟩
  intro p hp
  rw [Set.mem_iUnion] at hp
  obtain ⟨i, hi⟩ := hp
  set R := ∑ i, r i with hR
  have hRpos : 0 < R := Finset.sum_pos (fun j _ => hr j) ⟨i, Finset.mem_univ _⟩
  set z := R⁻¹ • ∑ i, r i • c i with hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  set v := p - z with hv
  by_cases hv0 : v = 0
  · rw [hv0, norm_zero]; exact hRpos.le
  set N := ‖v‖ with hNdef
  have hN : 0 < N := norm_pos_iff.mpr hv0
  set a : Fin n → ℝ := fun j => inner ℝ v (c j) with ha
  set e : Fin n → ℝ := fun j => a j + r j * N with he
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ e ⟨i, Finset.mem_univ _⟩
  have hproj : ∀ j, ∀ q ∈ Metric.closedBall (c j) (r j),
      inner ℝ v q ∈ Set.Icc (a j - r j * N) (a j + r j * N) := by
    intro j q hq
    rw [Metric.mem_closedBall, dist_eq_norm] at hq
    have h1 : |inner ℝ v (q - c j)| ≤ N * ‖q - c j‖ := abs_real_inner_le_norm v (q - c j)
    have h2 : N * ‖q - c j‖ ≤ N * r j := mul_le_mul_of_nonneg_left hq hN.le
    rw [inner_sub_right] at h1
    have h3 := abs_le.mp (h1.trans h2)
    simp only [ha]
    constructor <;> nlinarith [h3.1, h3.2]
  have hcov : ∀ j, Set.Ioc (e j) (e k) ⊆
      ⋃ l ∈ Finset.univ.filter (fun l => e j < e l), Set.Icc (a l - r l * N) (a l + r l * N) := by
    intro j t ht
    by_contra hnot
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hnot
    have hmiss : ∀ l, ∀ q ∈ Metric.closedBall (c l) (r l), inner ℝ v q ≠ t := by
      intro l q hq heq
      have hpl := hproj l q hq
      rw [heq] at hpl
      by_cases hjl : e j < e l
      · exact hnot l hjl hpl
      · have : e l < t := lt_of_le_of_lt (not_lt.mp hjl) ht.1
        have : t ≤ e l := hpl.2
        linarith
    rcases hsep v t hv0 hmiss with hall | hall
    · have hak := hall k
      have hjk : e j < e k := lt_of_lt_of_le ht.1 ht.2
      apply hnot k hjk
      have : 0 ≤ r k * N := mul_nonneg (hr k).le hN.le
      exact ⟨by simp only [ha] at hak ⊢; linarith, ht.2⟩
    · have haj := hall j
      have : 0 ≤ r j * N := mul_nonneg (hr j).le hN.le
      have : e j < t := ht.1
      simp only [he, ha] at this haj
      linarith
  have hlen : ∀ j, e k - e j ≤
      ∑ l ∈ Finset.univ.filter (fun l => e j < e l), 2 * N * r l := by
    intro j
    have := length_le_of_cover (Finset.univ.filter (fun l => e j < e l))
      (fun l => a l - r l * N) (fun l => a l + r l * N)
      (fun l _ => by have := mul_nonneg (hr l).le hN.le; linarith) (e j) (e k) (hcov j)
    refine this.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hsum : ∑ j, r j * (e k - e j) ≤ N * (R ^ 2 - ∑ j, r j ^ 2) := by
    calc ∑ j, r j * (e k - e j)
        ≤ ∑ j, r j * ∑ l ∈ Finset.univ.filter (fun l => e j < e l), 2 * N * r l :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hlen j) (hr j).le
      _ = N * (2 * ∑ j, ∑ l ∈ Finset.univ.filter (fun l => e j < e l), r j * r l) := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
          ring
      _ ≤ N * (R ^ 2 - ∑ j, r j ^ 2) :=
          mul_le_mul_of_nonneg_left (two_mul_sum_lt_le r e fun i => (hr i).le) hN.le
  have hsa : ∑ j, r j * a j = R * inner ℝ v z := by
    rw [hz, inner_smul_right, inner_sum]
    simp only [inner_smul_right, ha]
    rw [← mul_assoc, mul_inv_cancel₀ hRpos.ne', one_mul]
  have hpU : inner ℝ v p ≤ e k := le_trans (hproj i p hi).2 (hk i (Finset.mem_univ _))
  have hexp : ∑ j, r j * (e k - e j) = R * e k - R * inner ℝ v z - N * ∑ j, r j ^ 2 := by
    have : ∀ j, r j * (e k - e j) = e k * r j - r j * a j - N * r j ^ 2 := by
      intro j; simp only [he]; ring
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hsa]
    ring
  have hvv : inner ℝ v p - inner ℝ v z = N ^ 2 := by
    rw [← inner_sub_right, ← hv, real_inner_self_eq_norm_sq]
  have key : R * N ^ 2 ≤ N * R ^ 2 := by nlinarith
  have : N ≤ R := by
    by_contra hcon
    push Not at hcon
    have : R * N * R < R * N * N := mul_lt_mul_of_pos_left hcon (mul_pos hRpos hN)
    nlinarith
  exact this

end Math0.Erdos1121

#math0_proves Math0.Erdos1121.erdos_1121_higher_dimension Erdos1121.erdos_1121.variants.higher_dimension
