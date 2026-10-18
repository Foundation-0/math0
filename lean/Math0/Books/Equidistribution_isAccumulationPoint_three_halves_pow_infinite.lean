/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Books.UniformDistributionOfSequences.Equidistribution
import Math0.Audit

/-!
# The fractional parts of `(3/2)^n` have infinitely many accumulation points

Kuipers and Niederreiter (*Uniform Distribution of Sequences*, Chapter 1) recall that it is
unknown whether `((3/2)^n)` is equidistributed modulo `1`; it is known (Vijayaraghavan) that
`{(3/2)^n}` has infinitely many accumulation points. We prove exactly the formal statement
`Equidistribution.isAccumulationPoint_three_halves_pow_infinite`. Write `r_n = {(3/2)^n}` and
suppose the set `L` of accumulation points is finite. By compactness and injectivity of `r`,
`r_n` is eventually within any `ε` of `L`. Since `2 r_{n+1} - 3 r_n` is an integer and the finitely
many numbers `2ℓ' - 3ℓ` (`ℓ, ℓ' ∈ L`) are isolated from the other integers, for small `ε` the
deviations `δ_n = r_n - ℓ_n` satisfy `δ_{n+1} = (3/2) δ_n` while staying below `ε`, which forces
`δ_n = 0`. Hence `r_n ∈ L` for all large `n`, contradicting injectivity of `n ↦ r_n`.
-/

namespace Math0.Equidistribution

open Filter Topology

/-- Integers are uniformly isolated from any real `d`. -/
lemma exists_int_isolated (d : ℝ) : ∃ η > 0, ∀ m : ℤ, |(m : ℝ) - d| < η → (m : ℝ) = d := by
  by_cases h : ((round d : ℤ) : ℝ) = d
  · refine ⟨1, one_pos, fun m hm => ?_⟩
    rw [← h] at hm ⊢
    have : |((m - round d : ℤ) : ℝ)| < 1 := by push_cast; exact hm
    rw [← Int.cast_abs] at this
    have h2 : |m - round d| < 1 := by exact_mod_cast this
    have : m - round d = 0 := by rw [abs_lt] at h2; omega
    have : m = round d := by omega
    rw [this]
  · refine ⟨|d - round d|, abs_pos.2 (sub_ne_zero.2 (Ne.symm h)), fun m hm => ?_⟩
    have := round_le d m
    rw [abs_sub_comm] at hm
    linarith

/-- The isolation radius can be taken arbitrarily small. -/
lemma eventually_int_isolated (d : ℝ) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ m : ℤ, |(m : ℝ) - d| < η → (m : ℝ) = d := by
  obtain ⟨η₀, hη₀, h⟩ := exists_int_isolated d
  filter_upwards [Ioo_mem_nhdsGT hη₀] with η hη m hm
  exact h m (hm.trans hη.2)

/-- The basic relation: `2 {(3/2)^(n+1)} - 3 {(3/2)^n}` is an integer. -/
lemma two_mul_fract_succ_sub (n : ℕ) :
    ∃ m : ℤ, 2 * Int.fract ((3 / 2 : ℝ) ^ (n + 1)) - 3 * Int.fract ((3 / 2 : ℝ) ^ n) = m := by
  refine ⟨3 * ⌊(3 / 2 : ℝ) ^ n⌋ - 2 * ⌊(3 / 2 : ℝ) ^ (n + 1)⌋, ?_⟩
  simp only [Int.fract, pow_succ]
  push_cast
  ring

/-- The sequence `{(3/2)^n}` of fractional parts has infinitely many accumulation points. -/
theorem isAccumulationPoint_three_halves_pow_infinite :
    type_of% @Equidistribution.isAccumulationPoint_three_halves_pow_infinite := by
  intro hL
  set r : ℕ → ℝ := fun n => Int.fract ((3 / 2 : ℝ) ^ n) with hr
  set L := {x | Equidistribution.IsAccumulationPoint x r} with hLdef
  have hinj : Function.Injective r := Equidistribution.fract_three_halves_pow_injective
  -- Step A: the sequence is eventually close to `L`.
  have hA : ∀ ε > 0, ∀ᶠ n in atTop, ∃ ℓ ∈ L, |r n - ℓ| < ε := by
    intro ε hε
    by_contra h
    rw [not_eventually] at h
    simp only [not_exists, not_and, not_lt] at h
    rw [Nat.frequently_atTop_iff_infinite] at h
    set S := {n | ∀ ℓ ∈ L, ε ≤ |r n - ℓ|}
    have hSi : (r '' S).Infinite := h.image hinj.injOn
    have hsub : r '' S ⊆ Set.Icc 0 1 := by
      rintro _ ⟨n, -, rfl⟩
      exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    obtain ⟨x, -, hx⟩ := hSi.exists_accPt_of_subset_isCompact isCompact_Icc hsub
    have hxc : x ∈ closure (r '' S \ {x}) :=
      mem_closure_iff_clusterPt.2 (accPt_principal_iff_clusterPt.1 hx)
    have hxL : x ∈ L := by
      show x ∈ closure (Set.range r \ {x})
      refine closure_mono ?_ hxc
      exact Set.sdiff_subset_sdiff_left (Set.image_subset_range _ _)
    obtain ⟨_, ⟨⟨n, hn, rfl⟩, -⟩, hd⟩ := Metric.mem_closure_iff.1 hxc ε hε
    have := hn x hxL
    rw [Real.dist_eq, abs_sub_comm] at hd
    linarith
  -- Step B: choose `ε`.
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ p ∈ L ×ˢ L,
      ∀ m : ℤ, |(m : ℝ) - (2 * p.2 - 3 * p.1)| < η → (m : ℝ) = 2 * p.2 - 3 * p.1 :=
    (hL.prod hL).eventually_all.2 fun p _ => eventually_int_isolated _
  obtain ⟨η, hη, hηpos⟩ := (hev.and self_mem_nhdsWithin).exists
  set ε := η / 5 with hεdef
  have hε : 0 < ε := by have : (0 : ℝ) < η := hηpos; positivity
  -- Step C: the linear relation between consecutive deviations.
  have hC : ∀ n, ∀ ℓ ∈ L, ∀ ℓ' ∈ L, |r n - ℓ| < ε → |r (n + 1) - ℓ'| < ε →
      2 * (r (n + 1) - ℓ') = 3 * (r n - ℓ) := by
    intro n ℓ hℓ ℓ' hℓ' h1 h2
    obtain ⟨m, hm⟩ := two_mul_fract_succ_sub n
    have key := hη (ℓ, ℓ') ⟨hℓ, hℓ'⟩ m (by
      rw [← hm]
      have e : 2 * Int.fract ((3 / 2 : ℝ) ^ (n + 1)) - 3 * Int.fract ((3 / 2 : ℝ) ^ n) -
          (2 * ℓ' - 3 * ℓ) = 2 * (r (n + 1) - ℓ') - 3 * (r n - ℓ) := by simp [hr]; ring
      rw [e]
      calc |2 * (r (n + 1) - ℓ') - 3 * (r n - ℓ)|
          ≤ |2 * (r (n + 1) - ℓ')| + |3 * (r n - ℓ)| := abs_sub _ _
        _ = 2 * |r (n + 1) - ℓ'| + 3 * |r n - ℓ| := by
            rw [abs_mul, abs_mul]; norm_num
        _ < η := by linarith)
    simp only at key
    have : 2 * r (n + 1) - 3 * r n = m := by simp only [hr]; exact hm
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hA ε hε)
  -- Step D: the sequence lies in `L` from `N` on.
  have hD : ∀ n ≥ N, r n ∈ L := by
    intro n hn
    obtain ⟨ℓ, hℓ, hd⟩ := hN n hn
    set δ := r n - ℓ with hδ
    have hind : ∀ k : ℕ, ∃ ℓk ∈ L, r (n + k) - ℓk = (3 / 2 : ℝ) ^ k * δ ∧
        |r (n + k) - ℓk| < ε := by
      intro k
      induction k with
      | zero => exact ⟨ℓ, hℓ, by simp [hδ], by simpa using hd⟩
      | succ k ih =>
        obtain ⟨ℓk, hℓk, e, hk⟩ := ih
        obtain ⟨ℓ', hℓ', h'⟩ := hN (n + k + 1) (by omega)
        refine ⟨ℓ', hℓ', ?_, h'⟩
        have := hC (n + k) ℓk hℓk ℓ' hℓ' hk h'
        rw [pow_succ, show n + (k + 1) = n + k + 1 by omega]
        linarith
    by_cases hδ0 : δ = 0
    · have : r n = ℓ := by linarith
      rw [this]; exact hℓ
    · exfalso
      have hpos : 0 < |δ| := abs_pos.2 hδ0
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (ε / |δ|) (by norm_num : (1 : ℝ) < 3 / 2)
      obtain ⟨ℓk, -, e, hlt⟩ := hind k
      rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (3 / 2) ^ k)] at hlt
      rw [div_lt_iff₀ hpos] at hk
      linarith
  -- Step E: contradiction with injectivity.
  exact Set.infinite_of_injective_forall_mem (f := fun k : ℕ => r (N + k))
    (fun a b h => by simpa using hinj h) (fun k => hD _ (by omega)) hL

end Math0.Equidistribution

#math0_proves Math0.Equidistribution.isAccumulationPoint_three_halves_pow_infinite
  Equidistribution.isAccumulationPoint_three_halves_pow_infinite
