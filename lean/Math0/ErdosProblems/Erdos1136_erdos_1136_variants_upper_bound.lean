/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1136»
import Math0.Audit

/-!
# Erdős Problem 1136: lower density at most 1/2

Erdős Problem 1136 concerns sets `A ⊆ ℕ` such that no sum `a + b` (`a, b ∈ A`, not necessarily
distinct) is a power of two. Müller (2011) showed that such a set has lower density at most
`1/2`, and we prove exactly this. Since `2^j + 2^j = 2^(j+1)`, no power of two lies in `A`.
For `n = 2^j`, the map `x ↦ x` for `x < n` and `x ↦ 2n - x` for `x > n` sends
`A ∩ [0, 2n)` injectively into `[0, n)`, because a collision would give `x + y = 2^(j+1)`.
Hence the partial density of `A` at `2^(j+1)` is at most `1/2` for every `j`, so the liminf of the
partial densities is at most `1/2`.
-/

namespace Math0.Erdos1136

open _root_.Erdos1136 Filter Topology

/-- A set avoiding sums equal to powers of two contains no power of two. -/
theorem pow_not_mem {A : Set ℕ} (hA : AvoidsPowersOfTwo A) (j : ℕ) : 2 ^ j ∉ A := by
  intro h
  exact hA _ h _ h (j + 1) (by rw [pow_succ]; ring)

/-- The counting bound `#(A ∩ [0, 2^(j+1))) ≤ 2^j`. -/
theorem ncard_le {A : Set ℕ} (hA : AvoidsPowersOfTwo A) (j : ℕ) :
    (A ∩ Set.Iio (2 * 2 ^ j)).ncard ≤ 2 ^ j := by
  set n := 2 ^ j with hn
  have hpow : 2 * n = 2 ^ (j + 1) := by rw [hn, pow_succ]; ring
  have key := Set.ncard_le_ncard_of_injOn (s := A ∩ Set.Iio (2 * n)) (t := Set.Iio n)
    (fun x => if x < n then x else 2 * n - x) ?_ ?_ (Set.finite_Iio n)
  · simpa using key
  · rintro x ⟨hxA, hx⟩
    simp only [Set.mem_Iio] at hx ⊢
    have hxn : x ≠ n := fun h => pow_not_mem hA j (by rw [← hn, ← h]; exact hxA)
    have hn0 : 0 < n := by positivity
    split_ifs with h
    · exact h
    · omega
  · rintro x ⟨hxA, hx⟩ y ⟨hyA, hy⟩ hxy
    simp only [Set.mem_Iio] at hx hy
    have hxn : x ≠ n := fun h => pow_not_mem hA j (by rw [← hn, ← h]; exact hxA)
    have hyn : y ≠ n := fun h => pow_not_mem hA j (by rw [← hn, ← h]; exact hyA)
    have hsum : x + y ≠ 2 * n := hpow ▸ hA x hxA y hyA (j + 1)
    simp only at hxy
    split_ifs at hxy with h1 h2 h2 <;> omega

/-- A set avoiding sums equal to powers of two has lower density at most `1/2`. -/
theorem upper_bound : type_of% @_root_.Erdos1136.erdos_1136.variants.upper_bound := by
  intro A hA
  unfold Set.lowerDensity
  apply liminf_le_of_frequently_le
  · rw [frequently_atTop]
    intro a
    refine ⟨2 * 2 ^ a, ?_, ?_⟩
    · have := Nat.lt_two_pow_self (n := a); omega
    · simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
      have h := ncard_le hA a
      rw [div_le_iff₀ (by positivity)]
      have : ((A ∩ Set.Iio (2 * 2 ^ a)).ncard : ℝ) ≤ (2 ^ a : ℕ) := by exact_mod_cast h
      push_cast at this ⊢
      linarith
  · exact ⟨0, eventually_map.2 (Eventually.of_forall fun b => by positivity)⟩

end Math0.Erdos1136

#math0_proves Math0.Erdos1136.upper_bound _root_.Erdos1136.erdos_1136.variants.upper_bound
